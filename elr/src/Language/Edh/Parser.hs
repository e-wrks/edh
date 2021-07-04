{-# LANGUAGE ImplicitParams #-}

module Language.Edh.Parser where

-- import Debug.Trace

import Control.Applicative hiding (many, some)
import Control.Monad
import Control.Monad.State.Strict (MonadState (get, put))
import Data.Char
import qualified Data.Char as Char
import Data.Functor (($>))
import Data.Lossless.Decimal as D (Decimal (Decimal), inf, nan)
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Language.Edh.Control
import Language.Edh.RtTypes
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Prelude

-- | To preserve original source for expr literals, this data struct is
-- passed around to collect final @[SourceSeg]@ for an expr literal.
type IntplSrcInfo = (Text, Int, [SourceSeg])

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "#") edhSkipBlockCommentNested

edhSkipBlockCommentNested :: Parser ()
edhSkipBlockCommentNested =
  try (string "{#" >> notFollowedBy (char '#'))
    >> void
      ( manyTill
          (L.skipBlockCommentNested "{#" "#}" <|> void anySingle)
          (string "#}")
      )

-- | doc comment must start with "{##", this will return effective lines of
-- the comment
docComment :: Parser [Text]
docComment = do
  void $ string "{##"
  -- treat the 1st line specially
  !s <- getInput
  !o <- getOffset
  (!o', !done) <- findEoL
  let !line = maybe "" fst $ takeN_ (o' - o) s
      !cumLines = [line | not $ T.null $ T.strip line]
  if done
    then do
      sc
      return cumLines
    else cmtLines cumLines
  where
    cmtLines :: [Text] -> Parser [Text]
    cmtLines cumLines = do
      !s <- getInput
      !o <- getOffset
      (!o', !done) <- findEoL
      let !line = maybe "" fst $ takeN_ (o' - o) s
      if done
        then do
          sc
          return
            $! reverse
              ( if T.null (T.strip line)
                  then cumLines
                  else cmtLine line : cumLines
              )
        else cmtLines $ cmtLine line : cumLines

    findEoL :: Parser (Int, Bool)
    findEoL =
      getOffset >>= \ !o ->
        choice
          [ string "#}" >> return (o, True),
            eol >> return (o, False),
            anySingle >> findEoL
          ]

    cmtLine :: Text -> Text
    cmtLine s0 =
      let s1 = T.strip s0
       in case T.stripPrefix "#" s1 of
            Nothing -> s0 -- no leading #, return original content anyway
            -- with leading #, remove 1 single leading space if present
            Just s2 -> fromMaybe s2 $ T.stripPrefix " " s2

-- | get the doc comment immediately before next non-whitespace lexeme, return
-- the last one if multiple consecutive doc comment blocks present.
immediateDocComment :: Parser [Text]
immediateDocComment = docComment >>= moreAfterSemicolons
  where
    moreAfterSemicolons gotCmt =
      optionalSemicolon >>= \case
        True -> moreAfterSemicolons gotCmt
        False -> moreAfter gotCmt
    moreAfter !gotCmt =
      (<|> return gotCmt) $
        try (sc >> docComment) >>= moreAfter

stringSrc :: Text -> Parser SrcRange
stringSrc !t = do
  !spStart <- getSourcePos
  void $ string t
  !spEnd <- getSourcePos
  return $ SrcRange (lspSrcPosFromParsec spStart) (lspSrcPosFromParsec spEnd)

symbol :: Text -> Parser Text
symbol !t = do
  !r <- string t
  !sp <- getSourcePos
  !o <- getOffset
  !s <- get
  put
    s
      { edh'parser'lexeme'end'pos = lspSrcPosFromParsec sp,
        edh'parser'lexeme'end'offset = o
      }
  sc
  return r

lexeme :: Parser a -> Parser a
lexeme !p = do
  !r <- p
  !sp <- getSourcePos
  !o <- getOffset
  !s <- get
  put
    s
      { edh'parser'lexeme'end'pos = lspSrcPosFromParsec sp,
        edh'parser'lexeme'end'offset = o
      }
  sc
  return r

lexemeEndPos :: Parser SrcPos
lexemeEndPos = do
  EdhParserState _ !lexeme'end _ <- get
  return lexeme'end

keyword :: Text -> Parser SrcRange
keyword !kw = try $ do
  !startPos <- getSourcePos
  void $ lexeme (string kw <* notFollowedBy (satisfy isIdentChar))
  !lexeme'end <- lexemeEndPos
  return $ lspSrcRangeFromParsec startPos lexeme'end

optionalComma :: Parser Bool
optionalComma = fromMaybe False <$> optional (True <$ symbol ",")

optionalSemicolon :: Parser Bool
optionalSemicolon = fromMaybe False <$> optional (True <$ symbol ";")

isIdentStart :: Char -> Bool
isIdentStart !c = c == '_' || Char.isAlpha c

isIdentChar :: Char -> Bool
isIdentChar c = c == '_' || c == '\'' || Char.isAlphaNum c

singleDot :: Parser ()
singleDot = char '.' >> notFollowedBy (char '.') >> sc

equalSign :: Parser ()
equalSign = char '=' >> notFollowedBy (satisfy isOperatorChar) >> sc

parseProgram :: Parser ([StmtSrc], OptDocCmt)
parseProgram = do
  sc
  !docCmt <- optDocCmt <$> optional docComment
  !s <- getInput
  (!ss, _) <- parseStmts (s, 0, []) []
  return (ss, docCmt)

parseStmts :: IntplSrcInfo -> [StmtSrc] -> Parser ([StmtSrc], IntplSrcInfo)
parseStmts !si !ss = do
  void optionalSemicolon
  (eof >> return (reverse ss, si)) <|> do
    (!s, !si') <- parseStmt si
    parseStmts si' (s : ss)

parseVoidStmt :: Parser Stmt
parseVoidStmt = VoidStmt <$ keyword "pass" -- same as Python

parseGoStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseGoStmt !si = do
  void $ keyword "go"
  (!expr, !si') <- parseExpr si
  return (GoStmt expr, si')

parseDeferStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseDeferStmt !si = do
  void $ keyword "defer"
  (!expr, !si') <- parseExpr si
  return (DeferStmt expr, si')

parseEffectStmt ::
  OptDocCmt ->
  IntplSrcInfo ->
  Parser (Stmt, IntplSrcInfo)
parseEffectStmt !docCmt !si = do
  void $ keyword "effect"
  (!s, !si') <- parseExpr si
  return (EffectStmt s docCmt, si')

parseExportExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseExportExpr !si = do
  void $ keyword "export"
  (!s, !si') <- parseExpr si
  return (ExportExpr s, si')

parseIncludeExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseIncludeExpr !si = do
  void $ keyword "include"
  (!se, !si') <- parseExpr si
  return (IncludeExpr se, si')

parseImportExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseImportExpr !si = do
  (!ar, !se, !si') <- pyStyle <|> jsStyle
  (<|> return (ImportExpr ar se Nothing, si')) $ do
    void $ keyword "into"
    (!intoExpr, !si'') <- parseExpr si'
    return (ImportExpr ar se (Just intoExpr), si'')
  where
    pyStyle = do
      void $ keyword "from"
      (!se, !si') <- parseExpr si
      void $ keyword "import"
      !ar <- parseArgsReceiver
      return (ar, se, si')
    jsStyle = do
      void $ keyword "import"
      !ar <- parseArgsReceiver
      void $ optional $ keyword "from"
      (!se, !si') <- parseExpr si
      return (ar, se, si')

parseLetStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseLetStmt !si = do
  -- `const` has no different semantics than `let` in Edh,
  -- merely for JavaScript src level compatibility
  void $ keyword "let" <|> keyword "const"
  void optionalComma
  (pairs, si') <- parsePairs [] si
  case pairs of
    [] -> return (VoidStmt, si')
    [StmtSrc !stmt _] -> return (stmt, si')
    !stmts -> return (flip ExprStmt NoDocCmt $ BlockExpr stmts, si')
  where
    parsePairs :: [StmtSrc] -> IntplSrcInfo -> Parser ([StmtSrc], IntplSrcInfo)
    parsePairs got si' = do
      !startPos <- getSourcePos
      !ar <- parseArgsReceiver
      choice
        [ do
            equalSign
            (!argSender, !si'') <- parseArgsSender si'
            !lexeme'end <- lexemeEndPos
            optional (symbol ",") >>= \case
              Nothing ->
                return
                  ( StmtSrc
                      (LetStmt ar argSender)
                      (lspSrcRangeFromParsec startPos lexeme'end) :
                    got,
                    si''
                  )
              Just {} -> do
                -- more assignment pairs to parse
                (got', si''') <- parsePairs got si''
                return
                  ( StmtSrc
                      (LetStmt ar argSender)
                      (lspSrcRangeFromParsec startPos lexeme'end) :
                    got',
                    si'''
                  ),
          do
            -- no rhs to assign, accept it as if not written, just for src level
            -- compatibility with JavaScript variable definition
            -- it is nothing in Edh semantics
            void $ symbol ","
            parsePairs got si',
          -- no more assignment pairs, all done
          return (got, si')
        ]
    parseArgsSender :: IntplSrcInfo -> Parser (ArgsPacker, IntplSrcInfo)
    parseArgsSender si' =
      parseArgsPacker si <|> do
        (!x, !si'') <- parseExpr si'
        return (ArgsPacker [SendPosArg x] (exprSrcSpan x), si'')

parseArgsReceiver :: Parser ArgsReceiver
parseArgsReceiver =
  packReceiver <|> dropReceiver <|> wildReceiver <|> singleReceiver
  where
    wildReceiver = do
      !startPos <- getSourcePos
      void $ symbol "*"
      choice
        [ do
            void $ keyword "as"
            SingleReceiver . RecvRestPkArgs <$> parseAttrAddrSrc,
          do
            !lexeme'end <- lexemeEndPos
            return $
              WildReceiver $ SrcRange (lspSrcPosFromParsec startPos) lexeme'end
        ]

    dropReceiver =
      SingleReceiver . RecvRestPkArgs . AttrAddrSrc (NamedAttr "_")
        <$> keyword "_"

    packReceiver = do
      !startPos <- getSourcePos
      !ars <-
        choice
          [ symbol "(" >> reverse <$> parseRestArgRecvs ")",
            -- following is for JavaScript src level compatibility
            symbol "[" >> reverse <$> parseRestArgRecvs "]",
            symbol "{" >> reverse <$> parseRestArgRecvs "}"
          ]
      !lexeme'end <- lexemeEndPos
      return $
        PackReceiver ars $ SrcRange (lspSrcPosFromParsec startPos) lexeme'end

    singleReceiver = SingleReceiver <$> parseKwRecv False

parseRestArgRecvs :: Text -> Parser [ArgReceiver]
parseRestArgRecvs !endSymbol = parseArgRecvs [] False False
  where
    parseArgRecvs :: [ArgReceiver] -> Bool -> Bool -> Parser [ArgReceiver]
    parseArgRecvs !rs !kwConsumed !posConsumed = do
      void optionalComma
      (symbol endSymbol $> rs) <|> do
        !nextArg <-
          (<* optionalComma) $
            if posConsumed
              then restPkArgs <|> restKwArgs <|> parseKwRecv True
              else nextPosArg
        case nextArg of
          RecvRestPosArgs _ -> parseArgRecvs (nextArg : rs) kwConsumed True
          RecvRestKwArgs _ -> parseArgRecvs (nextArg : rs) True posConsumed
          _ -> parseArgRecvs (nextArg : rs) kwConsumed posConsumed

    nextPosArg, restKwArgs, restPosArgs :: Parser ArgReceiver
    nextPosArg = restPkArgs <|> restKwArgs <|> restPosArgs <|> parseKwRecv True
    restPkArgs =
      -- `...` for src level compatibility with JavaScript destructuring syntax
      (RecvRestPkArgs <$>) $
        optionalArgName
          =<< lexeme (stringSrc "***" <|> stringSrc "...")
    restKwArgs =
      (RecvRestKwArgs <$>) $ optionalArgName =<< lexeme (stringSrc "**")
    restPosArgs =
      (RecvRestPosArgs <$>) $ optionalArgName =<< lexeme (stringSrc "*")
    optionalArgName src'span =
      parseAttrAddrSrc <|> return (AttrAddrSrc (NamedAttr "_") src'span)

parseKwRecv :: Bool -> Parser ArgReceiver
parseKwRecv !inPack = do
  !addr <- let ?allowKwAttr = True in parseAttrAddrSrc'
  !retgt <- optional parseRetarget >>= validateTgt
  !defExpr <- if inPack then optional parseDefaultExpr else return Nothing
  return $ RecvArg addr retgt defExpr
  where
    parseRetarget :: Parser AttrRef
    parseRetarget = do
      void $ keyword "as"
      parseAttrRef
    validateTgt :: Maybe AttrRef -> Parser (Maybe AttrRef)
    validateTgt tgt = case tgt of
      Just ThisRef {} -> fail "can not overwrite this"
      Just ThatRef {} -> fail "can not overwrite that"
      Just SuperRef {} -> fail "can not overwrite super"
      _ -> return tgt
    parseDefaultExpr :: Parser ExprSrc
    parseDefaultExpr = do
      equalSign
      -- TODO carry on 'IntplSrcInfo' in the full call chain to here,
      --      so the default value expr can be interpolated.
      !s <- getInput
      !o <- getOffset
      (!x, _si') <- parseExpr (s, o, [])
      return x

parseAttrRef :: Parser AttrRef
parseAttrRef = do
  !startPos <- getSourcePos
  let moreAddr :: AttrRef -> Parser AttrRef
      moreAddr !p1 = try more <|> return p1
        where
          more = do
            !lexeme'end <- lexemeEndPos
            let leading'span = lspSrcRangeFromParsec startPos lexeme'end
            singleDot
            after'dot <- lexemeEndPos
            missEndPos <- getSourcePos
            choice
              [ do
                  AttrAddrSrc !addr (SrcRange _ !addr'end) <-
                    let ?allowKwAttr = True in parseAttrAddrSrc'
                  moreAddr $
                    IndirectRef
                      (ExprSrc (AttrExpr p1) leading'span)
                      (AttrAddrSrc addr (SrcRange after'dot addr'end)),
                moreAddr $
                  IndirectRef
                    (ExprSrc (AttrExpr p1) leading'span)
                    ( AttrAddrSrc MissedAttrName $
                        SrcRange after'dot $ lspSrcPosFromParsec missEndPos
                    )
              ]

  leadingPart >>= moreAddr
  where
    leadingPart :: Parser AttrRef
    leadingPart =
      choice
        [ ThisRef <$> keyword "this",
          ThatRef <$> keyword "that",
          SuperRef <$> keyword "super",
          DirectRef <$> parseAttrAddrSrc
        ]

parseArgsPacker :: IntplSrcInfo -> Parser (ArgsPacker, IntplSrcInfo)
parseArgsPacker !si = do
  !startPos <- getSourcePos
  void $ symbol "("
  (_, !ss, !si') <- parseArgSends si ")" False []
  !lexeme'end <- lexemeEndPos
  return
    (ArgsPacker (reverse ss) (lspSrcRangeFromParsec startPos lexeme'end), si')

parseArgSends ::
  IntplSrcInfo ->
  Text ->
  Bool ->
  [ArgSender] ->
  Parser (Bool, [ArgSender], IntplSrcInfo)
parseArgSends !si !closeSym !commaAppeared !ss = do
  !commaAppeared' <- (commaAppeared ||) <$> optionalComma
  (symbol closeSym >> return (commaAppeared', ss, si)) <|> do
    (!arg, !si') <- nextArg
    !commaAppeared'' <- (commaAppeared' ||) <$> optionalComma
    parseArgSends si' closeSym commaAppeared'' $ arg : ss
  where
    nextArg,
      unpackPkArgs,
      unpackKwArgs,
      unpackPosArgs ::
        Parser (ArgSender, IntplSrcInfo)
    nextArg = unpackPkArgs <|> unpackKwArgs <|> unpackPosArgs <|> parse1ArgSend
    unpackPkArgs = do
      -- `...` for src level compatibility with JavaScript spread syntax
      void $ string "***" <|> string "..."
      notFollowedBy $ satisfy isOperatorChar
      sc
      (!x, !si') <- parseExpr si
      return (UnpackPkArgs x, si')
    unpackKwArgs = do
      void $ string "**"
      notFollowedBy $ satisfy isOperatorChar
      sc
      (!x, !si') <- parseExpr si
      return (UnpackKwArgs x, si')
    unpackPosArgs = do
      void $ string "*"
      notFollowedBy $ satisfy isOperatorChar
      sc
      (!x, !si') <- parseExpr si
      return (UnpackPosArgs x, si')
    parseKwArgSend :: Parser (ArgSender, IntplSrcInfo)
    parseKwArgSend = do
      !addr <- let ?allowKwAttr = True in parseAttrAddrSrc'
      equalSign
      (!x, !si') <- parseExpr si
      return (SendKwArg addr x, si')
    parse1ArgSend :: Parser (ArgSender, IntplSrcInfo)
    parse1ArgSend =
      try parseKwArgSend <|> do
        (!x, !si') <- parseExpr si
        return (SendPosArg x, si')

parseNamespaceExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseNamespaceExpr !si = do
  !startPos <- getSourcePos
  void $ keyword "namespace"
  !pn <- parseAttrAddrSrc
  (!argSender, !si') <- parseArgsPacker si
  (!body, !si'') <- parseProcBody si'
  !lexeme'end <- lexemeEndPos
  return
    ( NamespaceExpr
        ( ProcDecl
            pn
            NullaryReceiver
            body
            (lspSrcLocFromParsec startPos lexeme'end)
        )
        argSender,
      si''
    )

parseClassExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseClassExpr !si = do
  !startPos <- getSourcePos
  void $ keyword "class"
  !pn <- parseAttrAddrSrc
  (!body, !si') <- parseProcBody si
  !lexeme'end <- lexemeEndPos
  return
    ( ClassExpr $
        ProcDecl
          pn
          NullaryReceiver
          body
          (lspSrcLocFromParsec startPos lexeme'end),
      si'
    )

parseDataExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseDataExpr !si = do
  !startPos <- getSourcePos
  void $ keyword "data"
  {- HLINT ignore "Reduce duplication" -}
  !pn <- parseAttrAddrSrc
  !ar <- parseArgsReceiver
  (!body, !si') <- parseProcBody si
  !lexeme'end <- lexemeEndPos
  return
    ( ClassExpr $ ProcDecl pn ar body (lspSrcLocFromParsec startPos lexeme'end),
      si'
    )

parseExtendsStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseExtendsStmt !si = do
  void $ keyword "extends"
  (!x, !si') <- parseExpr si
  return (ExtendsStmt x, si')

parseMethodExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseMethodExpr !si = do
  !startPos <- getSourcePos
  void $ keyword "method"
  (!pd, !si') <- parseProcDecl startPos si
  return (MethodExpr pd, si')

parseGeneratorExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseGeneratorExpr !si = do
  !startPos <- getSourcePos
  void $ keyword "generator"
  (!pd, !si') <- parseProcDecl startPos si
  return (GeneratorExpr pd, si')

parsePerceiveStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parsePerceiveStmt !si = do
  void $ keyword "perceive"
  (!sink, !si') <- parseExpr si
  (!body, !si'') <- parseStmt si'
  return (PerceiveStmt sink body, si'')

parseInterpreterExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseInterpreterExpr !si = do
  !startPos <- getSourcePos
  void $ keyword "interpreter"
  (!pd, !si') <- parseProcDecl startPos si
  return (InterpreterExpr pd, si')

parseProducerExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseProducerExpr !si = do
  !startPos <- getSourcePos
  void $ keyword "producer"
  (!pd, !si') <- parseProcDecl startPos si
  return (ProducerExpr pd, si')

parseWhileExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseWhileExpr !si = do
  void $ keyword "while"
  (!cnd, !si') <- parseExpr si
  (!act, !si'') <- parseStmt si'
  return (WhileExpr cnd act, si'')

parseDoForOrWhileExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseDoForOrWhileExpr !si = do
  void $ keyword "do"
  lbStartPos <- getSourcePos
  (!bodyStmt, !si') <- parseStmt si
  choice
    [ do
        void $ keyword "for"
        !scoped <- isJust <$> optional (symbol "@")
        (!ar, !iter, !si'') <- parseLoopHead si'
        return (ForExpr scoped ar iter bodyStmt, si''),
      do
        void $ keyword "if"
        (!cond, !si'') <- parseExpr si'
        lbEnd <- lexemeEndPos
        optional (keyword "for") >>= \case
          Nothing -> return (IfExpr cond bodyStmt Nothing, si'')
          Just {} -> do
            !scoped <- isJust <$> optional (symbol "@")
            (!ar, !iter, !si''') <- parseLoopHead si''
            let !loopBodyStmt =
                  StmtSrc
                    ( ExprStmt
                        ( IfExpr
                            cond
                            bodyStmt
                            (Just $ StmtSrc ContinueStmt noSrcRange)
                        )
                        NoDocCmt
                    )
                    $ lspSrcRangeFromParsec lbStartPos lbEnd
            return (ForExpr scoped ar iter loopBodyStmt, si'''),
      do
        void $ keyword "while"
        (!cnd, !si'') <- parseExpr si'
        return (DoWhileExpr bodyStmt cnd, si'')
    ]

parseProcDecl :: SourcePos -> IntplSrcInfo -> Parser (ProcDecl, IntplSrcInfo)
parseProcDecl !startPos !si = do
  !pn <- parseAttrAddrSrc
  !ar <- parseArgsReceiver
  (!body, !si') <- parseProcBody si
  !lexeme'end <- lexemeEndPos
  return (ProcDecl pn ar body (lspSrcLocFromParsec startPos lexeme'end), si')

parseOpDeclOvrdExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseOpDeclOvrdExpr !si = do
  !startPos <- getSourcePos
  !fixity <-
    choice
      [ InfixL <$ keyword "infixl",
        InfixR <$ keyword "infixr",
        Infix <$ keyword "infix",
        Infix <$ keyword "operator"
      ]
  sc
  -- can be any integer, no space allowed between +/- sign and digit(s)
  !precDecl <- optional $ L.signed (pure ()) L.decimal <* sc
  !errRptPos <- getOffset
  opSymSrc@(OpSymSrc !opSym !opSpan) <- parseOpDeclSymSrc
  -- TODO check opSym can not be certain "reserved" keywords
  !argsErrRptPos <- getOffset
  !argsRcvr <- parseArgsReceiver
  -- valid forms of args receiver for operators:
  --  * nullary - redeclare a pre-existing procedure as operator
  --  * 2 pos-args - simple lh/rh value receiving operator
  --  * 3 pos-args - caller scope + lh/rh expr receiving operator
  case argsRcvr of
    PackReceiver ars _ | length ars `elem` [0, 2, 3] -> do
      (!body, !si') <- parseProcBody si
      !lexeme'end <- lexemeEndPos
      let !procDecl =
            ProcDecl
              (AttrAddrSrc (NamedAttr opSym) opSpan)
              argsRcvr
              body
              (lspSrcLocFromParsec startPos lexeme'end)
      ps@(EdhParserState !opPD _ _) <- get
      case precDecl of
        Nothing -> case lookupOpFromDict opSym opPD of
          Nothing -> do
            setOffset errRptPos
            fail $
              "you forget to specify the precedence for operator: ("
                <> T.unpack opSym
                <> ") ?"
          Just (origFixity, origPrec, _) ->
            return (OpOvrdExpr origFixity origPrec opSymSrc procDecl, si')
        Just opPrec -> case lookupOpFromDict opSym opPD of
          Nothing -> do
            put
              ps
                { edh'parser'op'dict =
                    insertOpIntoDict
                      opSym
                      ( fixity,
                        opPrec,
                        prettySrcLoc
                          ( SrcLoc
                              (SrcDoc (T.pack $ sourceName startPos))
                              opSpan
                          )
                      )
                      opPD
                }
            return (OpDefiExpr fixity opPrec opSymSrc procDecl, si')
          Just (origFixity, origPrec, odl) ->
            if origPrec /= opPrec
              then do
                setOffset errRptPos
                fail $
                  "redeclaring operator ("
                    <> T.unpack opSym
                    <> ") with a different precedence ("
                    <> show opPrec
                    <> " vs "
                    <> show origPrec
                    <> "), it has been declared at "
                    <> T.unpack odl
              else case fixity of
                Infix ->
                  -- follow whatever fixity orignally declared
                  return (OpOvrdExpr origFixity opPrec opSymSrc procDecl, si')
                _ ->
                  if fixity /= origFixity
                    then do
                      setOffset errRptPos
                      fail $
                        "redeclaring operator ("
                          <> T.unpack opSym
                          <> ") with a different fixity ("
                          <> show fixity
                          <> " vs "
                          <> show origFixity
                          <> "), it has been declared at "
                          <> T.unpack odl
                    else
                      return
                        (OpOvrdExpr fixity opPrec opSymSrc procDecl, si')
    _ -> do
      setOffset argsErrRptPos
      fail "invalid operator arguments receiver"
  where
    parseOpDeclSymSrc :: Parser OpSymSrc
    parseOpDeclSymSrc = do
      !startPos <- getSourcePos
      void $ symbol "("
      sc
      !opSym <-
        optional (char '~') >>= \case
          Just {} -> do
            !rest <- takeWhileP (Just "freeform operator symbol") $
              \ !c -> c == '~' || isIdentChar c || isOperatorChar c
            return $ "~" <> rest
          Nothing ->
            takeWhile1P
              (Just "some operator symbol")
              (not . (`elem` ("#(){}" :: [Char])))
      sc
      void $ char ')'
      !endPos <- getSourcePos
      !endOffs <- getOffset
      !s <- get
      put
        s
          { edh'parser'lexeme'end'pos = lspSrcPosFromParsec endPos,
            edh'parser'lexeme'end'offset = endOffs
          }
      sc
      return $
        OpSymSrc
          (T.strip opSym)
          $ SrcRange (lspSrcPosFromParsec startPos) (lspSrcPosFromParsec endPos)

parseSymbolExpr :: Parser Expr
parseSymbolExpr = do
  void $ keyword "symbol"
  void $ char '@'
  sc
  SymbolExpr <$> let ?allowKwAttr = False in parseAlphNumName

parseReturnStmt ::
  OptDocCmt ->
  IntplSrcInfo ->
  Parser (Stmt, IntplSrcInfo)
parseReturnStmt !docCmt !si = do
  void $ keyword "return"
  (!x, !si') <- parseExpr si
  return (ReturnStmt x docCmt, si')

parseThrowStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseThrowStmt !si = do
  void $ keyword "throw"
  (!x, !si') <- parseExpr si
  return (ThrowStmt x, si')

parseStmt' :: Int -> IntplSrcInfo -> Parser (StmtSrc, IntplSrcInfo)
parseStmt' !prec !si = do
  void optionalSemicolon
  !startPos <- getSourcePos
  let legalStmt = do
        !docCmt <- optDocCmt <$> optional immediateDocComment
        (!stmt, !si') <-
          choice
            [ parseGoStmt si,
              parseDeferStmt si,
              parseEffectStmt docCmt si,
              parseLetStmt si,
              parseExtendsStmt si,
              parsePerceiveStmt si,
              -- TODO validate <break> must within a loop construct
              (BreakStmt, si) <$ keyword "break",
              -- note <continue> can be the eval'ed value of a proc,
              --      carrying NotImplemented semantics as in Python
              (ContinueStmt, si) <$ keyword "continue",
              -- TODO validate fallthrough must within a branch block
              (FallthroughStmt, si) <$ keyword "fallthrough",
              (RethrowStmt, si) <$ keyword "rethrow",
              parseReturnStmt docCmt si,
              parseThrowStmt si,
              (,si) <$> parseVoidStmt,
              -- NOTE: statements above should probably all be detected by
              -- `illegalKeywrodForAttr` as invalid for attribute identifier
              do
                (ExprSrc !x _, !si') <- parseExprPrec Nothing prec si
                return (ExprStmt x docCmt, si')
            ]
        !lexeme'end <- lexemeEndPos
        return (StmtSrc stmt (lspSrcRangeFromParsec startPos lexeme'end), si')
      withIllegal !errPos !errMsg = keepTrying
        where
          keepTrying =
            choice
              [ do
                  eof
                  !endPos <- getSourcePos
                  return
                    ( StmtSrc (IllegalSegment errMsg errPos) $
                        lspSrcRangeFromParsec'' startPos endPos,
                      si
                    ),
                do
                  endPos <- getSourcePos
                  anySingle >>= \case
                    ';' -> getSourcePos >>= attemptLegal
                    ',' -> getSourcePos >>= attemptLegal
                    c | isSpace c -> attemptLegal endPos
                    _ -> keepTrying
              ]
          attemptLegal !endPos = do
            sc
            observing (try legalStmt) >>= \case
              Left _err -> keepTrying
              Right (stmt@(StmtSrc _ !legal'span), !si') ->
                return
                  ( StmtSrc
                      ( ExprStmt
                          ( BlockExpr
                              [ StmtSrc (IllegalSegment errMsg errPos) $
                                  lspSrcRangeFromParsec'' startPos endPos,
                                stmt
                              ]
                          )
                          NoDocCmt
                      )
                      legal'span {src'start = lspSrcPosFromParsec startPos},
                    si'
                  )
  observing (try legalStmt) >>= \case
    Right !result -> return result
    Left !err -> do
      let err'offs = errorOffset err
      !offs <- getOffset
      void $ takeP (Just "illegal part") $ err'offs - offs
      !errPos <- getSourcePos
      withIllegal (lspSrcPosFromParsec errPos) $
        T.pack $ parseErrorTextPretty err

parseStmt :: IntplSrcInfo -> Parser (StmtSrc, IntplSrcInfo)
parseStmt !si = parseStmt' (-10) si

-- procedure bodies are statements, for procedures to include ($=> -2)
-- and (@=> -2) in their bodies, and to be applied by ($ -5) or (| -5)
-- without necessarity to be curly quoted, we use precedence (-3) to
-- parse expressions for statements
parseProcBody :: IntplSrcInfo -> Parser (StmtSrc, IntplSrcInfo)
parseProcBody !si = parseStmt' (-3) si

parseIfExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseIfExpr !si = do
  void $ keyword "if"
  (!cond, !si') <- parseExpr si
  void $ optional $ keyword "then"
  (!cseq, !si2) <- parseStmt si'
  (!alt, !si3) <-
    {- HLINT ignore "Use first" -}
    fmap (maybe (Nothing, si2) (\(alt, si3) -> (Just alt, si3))) $
      optional $ do
        void $ keyword "else"
        parseStmt si2
  return (IfExpr cond cseq alt, si3)

parseCaseExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseCaseExpr !si = do
  void $ keyword "case"
  (!tgt, !si') <- parseExpr si
  void $ keyword "of"
  (!branches, !si'') <- parseExpr si'
  return (CaseExpr tgt branches, si'')

parseYieldExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseYieldExpr !si = do
  void $ keyword "yield"
  (!x, !si') <- parseExpr si
  return (YieldExpr x, si')

parseForExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseForExpr !si = do
  void $ keyword "for"
  !scoped <- isJust <$> optional (symbol "@")
  (!ar, !iter, !si') <- parseLoopHead si
  void $ optional $ keyword "do"
  (!bodyStmt, !si'') <- parseStmt si'
  return (ForExpr scoped ar iter bodyStmt, si'')

parseLoopHead :: IntplSrcInfo -> Parser (ArgsReceiver, ExprSrc, IntplSrcInfo)
parseLoopHead !si = do
  !startPos <- getSourcePos
  choice
    [ symbol "(" -- possible JavaScript syntax
        >> choice
          [ do
              -- js compatible syntax
              void $ keyword "let" <|> keyword "const"
              !ar <- parseArgsReceiver
              choice
                [ do
                    void $ keyword "of" <|> keyword "in"
                    (!iter, !si') <- parseExpr si
                    void $ symbol ")"
                    return (ar, iter, si'),
                  do
                    void equalSign
                    (!iter, !si') <- parseExpr si
                    -- todo `iter` is semantically in js the initial value, not
                    --      the source, here only the syntax is accepted, the
                    --      semantics is weird. to support `for(;;)` semantics?
                    let dropRest si'' =
                          optionalSemicolon >>= \case
                            True -> do
                              (_, !si''') <- parseExpr si''
                              dropRest si'''
                            False -> return si''
                    !si'' <- dropRest si'
                    void $ symbol ")"
                    return (ar, iter, si'')
                ],
            do
              -- Edh or Python-like syntax
              ars <- parseRestArgRecvs ")"
              !lexeme'end <- lexemeEndPos
              void $ keyword "from" <|> keyword "in"
              (!iter, !si') <- parseExpr si
              return
                ( PackReceiver (reverse $! ars) $
                    SrcRange (lspSrcPosFromParsec startPos) lexeme'end,
                  iter,
                  si'
                )
          ],
      do
        -- drop receiver, exclusively Edh syntax
        !src'span <- keyword "_"
        let !ar =
              SingleReceiver $
                RecvRestPkArgs $ AttrAddrSrc (NamedAttr "_") src'span
        void $ keyword "from"
        (!iter, !si') <- parseExpr si
        return (ar, iter, si'),
      do
        -- wild arg receiver, exclusively Edh syntax
        void $ symbol "*"
        !ar <-
          choice
            [ do
                void $ keyword "as"
                SingleReceiver . RecvRestPkArgs <$> parseAttrAddrSrc,
              do
                !lexeme'end <- lexemeEndPos
                return $
                  WildReceiver $
                    SrcRange (lspSrcPosFromParsec startPos) lexeme'end
            ]
        void $ keyword "from"
        (!iter, !si') <- parseExpr si
        return (ar, iter, si'),
      do
        -- single arg receiver, Edh or Python-like syntax
        !singleArg <- parseKwRecv False
        void $ keyword "from" <|> keyword "in"
        (!iter, !si') <- parseExpr si
        return (SingleReceiver singleArg, iter, si')
    ]

parseEffExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseEffExpr !si =
  choice $
    parseEff
      <$> [ ("perform", Perform),
            ("behave", Behave),
            ("fallback", Fallback)
          ]
  where
    parseEff (!kw, !eff) = do
      void $ keyword kw
      !addr <- parseAttrAddrSrc
      return (EffExpr $ eff addr, si)

parseListExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseListExpr !si = do
  void $ symbol "["
  (!es, !si') <- parseElem si []
  return (ListExpr $ reverse es, si')
  where
    parseElem :: IntplSrcInfo -> [ExprSrc] -> Parser ([ExprSrc], IntplSrcInfo)
    parseElem si' es = do
      void optionalComma
      (symbol "]" >> return (es, si')) <|> do
        (!x, !si'') <- parseExpr si'
        void optionalComma
        parseElem si'' (x : es)

parseStringLit :: Parser Text
parseStringLit = lexeme $ do
  !delim <-
    choice
      [ string "'''",
        string "'",
        string "```",
        string "`",
        string "\"\"\"",
        string "\""
      ]
  T.pack <$> manyTill charLiteral (string delim)
  where
    charLiteral :: Parser Char
    charLiteral =
      label "literal character" $
        anySingle >>= \case
          '\\' ->
            anySingle >>= \case
              '\\' -> return '\\'
              '"' -> return '"'
              '\'' -> return '\''
              '`' -> return '`'
              'n' -> return '\n'
              't' -> return '\t'
              'r' -> return '\r'
              'u' -> unicodeDigs 4
              'U' -> unicodeDigs 8
              -- todo support more? e.g. \b \g
              !c -> return c
          !c -> return c

    unicodeDigs :: Int -> Parser Char
    unicodeDigs !maxDigs = label "unicode digits" $ go maxDigs 0
      where
        go :: Int -> Int -> Parser Char
        go d v
          | d <= 0 = return $ toEnum v
          | otherwise =
            (<|> return (toEnum v)) $
              satisfy Char.isHexDigit >>= \ !c ->
                go (d - 1) $ v * 16 + fromIntegral (Char.digitToInt c)

parseBoolLit :: Parser Bool
parseBoolLit = (keyword "true" $> True) <|> (keyword "false" $> False)

-- todo support HEX/OCT ?
parseDecLit :: Parser Decimal
parseDecLit = lexeme $ do
  (!n, !e) <- b10Dec
  return $ Decimal 1 e n
  where
    b10Dec :: Parser (Integer, Integer)
    b10Dec = try $ do
      !sign'n <- signNum
      !n <- b10Int =<< b10Dig
      choice
        [ try $ do
            void $ char 'e' <|> char 'E'
            !sign'e <- signNum
            !e <- b10Int =<< b10Dig
            return (sign'n * n, sign'e * e),
          try $ do
            singleDot
            !d <- b10Dig
            (n', e') <- b10DecPoints (n * 10 + d) (-1)
            return (sign'n * n', e'),
          return (sign'n * n, 0)
        ]

    b10DecPoints :: Integer -> Integer -> Parser (Integer, Integer)
    b10DecPoints !n !e =
      choice
        [ do
            !d <- b10Dig
            b10DecPoints (n * 10 + d) (e - 1),
          try $ do
            void $ char 'e' <|> char 'E'
            !sign'e <- signNum
            !e' <- b10Int =<< b10Dig
            return (n, e + sign'e * e'),
          return (n, e)
        ]

    signNum :: Parser Integer
    signNum =
      choice
        [ char '+' >> sc >> return 1,
          char '-' >> sc >> return (-1),
          return 1
        ]

    b10Int :: Integer -> Parser Integer
    b10Int !n = tryMoreDig n <|> return n

    tryMoreDig :: Integer -> Parser Integer
    tryMoreDig !n =
      -- todo validate for `_` to appear at certain pos only?
      (char '_' >> tryMoreDig n) <|> do
        !d <- b10Dig
        b10Int $ n * 10 + d

    b10Dig :: Parser Integer
    b10Dig = do
      {- HLINT ignore "Use isDigit" -}
      !c <- satisfy $ \ !c -> c >= '0' && c <= '9'
      return $ toInteger (fromEnum c - fromEnum '0')

parseLitExpr :: Parser Literal
parseLitExpr =
  choice
    [ NilLiteral <$ litKw "nil",
      BoolLiteral <$> parseBoolLit,
      StringLiteral <$> parseStringLit,
      SinkCtor <$ litKw "sink",
      DecLiteral D.nan <$ litKw "nan",
      DecLiteral D.inf <$ litKw "inf",
      ValueLiteral edhNone <$ litKw "None",
      ValueLiteral edhNothing <$ litKw "Nothing",
      ValueLiteral edhNA <$ litKw "NA",
      ValueLiteral (EdhOrd EQ) <$ litKw "EQ",
      ValueLiteral (EdhOrd LT) <$ litKw "LT",
      ValueLiteral (EdhOrd GT) <$ litKw "GT",
      -- allow `pass` to appear as an expr in addition to stmt
      NilLiteral <$ litKw "pass",
      DecLiteral <$> parseDecLit
    ]
  where
    litKw = hidden . keyword

parseAttrAddrSrc :: Parser AttrAddrSrc
parseAttrAddrSrc = let ?allowKwAttr = False in parseAttrAddrSrc'

parseAttrAddrSrc' :: (?allowKwAttr :: Bool) => Parser AttrAddrSrc
parseAttrAddrSrc' = do
  !startPos <- getSourcePos
  !addr <- parseAttrAddr
  !lexeme'end <- lexemeEndPos
  return $ AttrAddrSrc addr $ SrcRange (lspSrcPosFromParsec startPos) lexeme'end

parseAttrAddr :: (?allowKwAttr :: Bool) => Parser AttrAddr
parseAttrAddr = parseAtNotation <|> NamedAttr <$> parseAttrName
  where
    parseAtNotation :: Parser AttrAddr
    parseAtNotation = do
      void $ char '@'
      sc
      choice
        [ between (symbol "(") (symbol ")") parseIntplSymAttr,
          QuaintAttr <$> parseStringLit,
          SymbolicAttr <$> parseAlphNumName,
          pure MissedAttrSymbol
        ]

    parseIntplSymAttr :: Parser AttrAddr
    parseIntplSymAttr = do
      !s <- getInput
      !o <- getOffset
      (!x, _) <- parseExprPrec Nothing (-20) (s, o, [])
      !o' <- getOffset
      let !src = maybe "" (T.stripEnd . fst) $ takeN_ (o' - o) s
      return $ IntplSymAttr src x

parseAttrName :: (?allowKwAttr :: Bool) => Parser Text
parseAttrName = parseMagicName <|> parseAlphNumName
  where
    -- a magic method name includes the quoting "()" pair, with inner /
    -- surrounding whitespaces stripped
    parseMagicName :: Parser Text
    parseMagicName =
      ("(" <>) . (<> ")")
        <$> between (symbol "(") (symbol ")") (indexMagic <|> nonIdxMagic)
    indexMagic =
      -- indexing (assignments) e.g. ([]) ([=]) ([+=])
      ("[" <>) . (<> "]")
        <$> between
          (symbol "[")
          (symbol "]")
          (fromMaybe "" <$> optional parseOpLit)
    nonIdxMagic =
      parseOpLit >>= \ !opLit ->
        optional (symbol ".") >>= \case
          Nothing -> return opLit
          -- right-hand-side operator overriding e.g. (-.) (/.)
          Just {} -> return $ opLit <> "."

parseAlphNumName :: (?allowKwAttr :: Bool) => Parser AttrName
parseAlphNumName = (detectIllegalIdent >>) $
  lexeme $ do
    !anStart <- takeWhile1P (Just "attribute name") isIdentStart
    !anRest <- takeWhileP Nothing isIdentChar
    return $ anStart <> anRest
  where
    detectIllegalIdent = do
      !eps <- get -- save parsing states
      !illIdent <- lookAhead illegalIdentifier
      put eps -- restore parsing states (esp. lexeme end)
      case illIdent of
        Just !ident -> fail $ "illegal identifier `" <> T.unpack ident <> "`"
        Nothing -> pure ()
    illegalIdentifier :: (?allowKwAttr :: Bool) => Parser (Maybe Text)
    illegalIdentifier =
      choice
        [ Just <$> kwIdent "this",
          Just <$> kwIdent "that",
          Just <$> kwIdent "super",
          Just . T.pack . show <$> parseLitExpr,
          -- allow dot-notation to use keywords here. disallowing such keywords,
          -- one occurrence willl parse as missing attr followed by another
          -- statement initiated by that very keyword, esp. when written on a
          -- single line, the error reporting can appear even more confusing.
          if ?allowKwAttr
            then return Nothing
            else illegalKeywrodForAttr <|> return Nothing
        ]
    kwIdent :: Text -> Parser Text
    kwIdent !kw = keyword kw >> return kw

-- NOTE: keywords for statements or other constructs will parse as identifier
--       for attribute access, if not forbidden here.
illegalKeywrodForAttr :: Parser (Maybe Text)
illegalKeywrodForAttr = do
  EdhParserState (GlobalOpDict _decls !quaint'ops) _ _ <- get
  Just
    <$> choice
      ( [ illegalWord "go",
          illegalWord "defer",
          illegalWord "effect",
          illegalWord "let",
          illegalWord "const", -- reserved for JavaScript src compatibility
          illegalWord "as",
          illegalWord "then",
          illegalWord "else",
          illegalWord "extends",
          illegalWord "perceive",
          illegalWord "of",
          illegalWord "break",
          illegalWord "continue",
          illegalWord "fallthrough",
          illegalWord "return",
          illegalWord "throw"
        ]
          ++ (illegalWord <$> quaint'ops)
      )
    <|> return Nothing
  where
    illegalWord !wd = wd <$ keyword wd

parseOpSrc :: Parser OpSymSrc
parseOpSrc = do
  !startPos <- getSourcePos
  !opSym <- parseOpLit
  !lexeme'end <- lexemeEndPos
  return $ OpSymSrc opSym $ SrcRange (lspSrcPosFromParsec startPos) lexeme'end

parseOpLit :: Parser Text
parseOpLit = choice [quaintOpLit, freeformOpLit, stdOpLit]
  where
    quaintOpLit = do
      EdhParserState (GlobalOpDict _decls !quaint'ops) _ _ <- get
      choice $ quaintOp <$> reverse quaint'ops
      where
        quaintOp :: OpSymbol -> Parser OpSymbol
        quaintOp !sym =
          lexeme $
            if isIdentChar $ T.last sym
              then try $ string sym <* notFollowedBy (satisfy isIdentChar)
              else string sym
    freeformOpLit = lexeme $ do
      void $ char '~'
      !rest <- takeWhileP (Just "freeform operator symbol") $
        \ !c -> c == '~' || isIdentChar c || isOperatorChar c
      return $ "~" <> rest
    stdOpLit =
      try $
        lexeme $
          takeWhile1P (Just "some operator symbol") isOperatorChar
            -- or it's an augmented closing brace
            <* notFollowedBy (char '}')

parseScopedBlock :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseScopedBlock !si0 = void (symbol "{@") >> parseRest [] si0
  where
    parseRest :: [StmtSrc] -> IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
    parseRest !t !si =
      optionalSemicolon
        *> choice
          [ (void (symbol "@}") <|> eof)
              >> return (ScopedBlockExpr $ reverse t, si),
            do
              (!ss, !si') <- parseStmt si
              parseRest (ss : t) si'
          ]

parseDictOrBlock :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseDictOrBlock !si0 =
  symbol "{"
    *> choice [try $ parseDictEntries si0 [], parseBlockRest [] si0]
  where
    entryColon :: Parser ()
    entryColon = char ':' >> notFollowedBy (satisfy isOperatorChar) >> sc

    parseBlockRest :: [StmtSrc] -> IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
    parseBlockRest !t !si =
      optionalSemicolon
        *> choice
          [ (void (symbol "}") <|> eof) >> return (BlockExpr $ reverse t, si),
            do
              (!ss, !si') <- parseStmt si
              parseBlockRest (ss : t) si'
          ]
    parseDictEntries ::
      IntplSrcInfo -> [(DictKeyExpr, ExprSrc)] -> Parser (Expr, IntplSrcInfo)
    parseDictEntries !si !es =
      optionalSemicolon >>= \case
        True -> fail "should be block instead of dict"
        -- note: keep the order of entries reversed here as written in source
        False -> do
          void optionalComma
          (symbol "}" $> (DictExpr es, si)) <|> do
            (!e, !si') <- nextEntry
            parseDictEntries si' (e : es)
      where
        nextEntry,
          litEntry,
          addrEntry,
          exprEntry ::
            Parser ((DictKeyExpr, ExprSrc), IntplSrcInfo)
        nextEntry = (litEntry <|> addrEntry <|> exprEntry) <* optionalComma
        litEntry = try $ do
          !k <- parseLitExpr
          entryColon
          (!v, !si') <- parseExpr si
          return ((LitDictKey k, v), si')
        addrEntry = try $ do
          !k <- let ?allowKwAttr = True in parseAttrAddrSrc'
          entryColon
          (!v, !si') <- parseExpr si
          return ((AddrDictKey k, v), si')
        exprEntry = try $ do
          -- (:) should be infixl 5, cross check please
          (!k, !si') <-
            parseExprPrec
              (Just (OpSymSrc ":" noSrcRange, InfixL))
              5
              si
          entryColon
          (!v, !si'') <- parseExpr si'
          return ((ExprDictKey k, v), si'')

parseOpAddrOrApkOrParen :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseOpAddrOrApkOrParen !si = do
  !startPos <- getSourcePos
  void $ symbol "("
  (<|> parseApkRest startPos si ")" False) $
    try $ do
      !opSym <- parseOpLit
      void $ symbol ")"
      !lexeme'end <- lexemeEndPos
      return
        ( AttrExpr $
            DirectRef $
              AttrAddrSrc
                (NamedAttr opSym)
                (lspSrcRangeFromParsec startPos lexeme'end),
          si
        )

parseApkRest ::
  SourcePos -> IntplSrcInfo -> Text -> Bool -> Parser (Expr, IntplSrcInfo)
parseApkRest !startPos !si !closeSym !mustApk = do
  !mustApk' <-
    optionalComma >>= \case
      True -> return True
      False -> return mustApk
  (!mustApk'', !ss, !si') <- parseArgSends si closeSym mustApk' []
  !lexeme'end <- lexemeEndPos
  return $
    (,si') $ case ss of
      [SendPosArg singleExpr@(ExprSrc !x _)]
        | not mustApk'' ->
          if closeSym == ")" then ParenExpr singleExpr else x
      _ ->
        ArgsPackExpr $
          ArgsPacker (reverse ss) (lspSrcRangeFromParsec startPos lexeme'end)

parseIndexer :: IntplSrcInfo -> Parser (ExprSrc, IntplSrcInfo)
parseIndexer !si = do
  !startPos <- getSourcePos
  void $ symbol "["
  (!x, !si') <- parseApkRest startPos si "]" False
  !lexeme'end <- lexemeEndPos
  return (ExprSrc x (lspSrcRangeFromParsec startPos lexeme'end), si')

-- Notes:
--  * (+)/(-) prefix should have highest precedence below Call/Index
--  * (not) should have a precedence slightly higher than (&&) (||)
--  * guard (|) should have a precedence no smaller than the branch op (->)
--  * default seem can just have normal precedence

parsePrefixExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parsePrefixExpr !si =
  choice
    [ try $
        prefixOp "+" >> do
          (!x, !si') <- parseExprPrec Nothing 9 si
          return (PrefixExpr PrefixPlus x, si'),
      try $
        prefixOp "-" >> do
          (!x, !si') <- parseExprPrec Nothing 9 si
          return (PrefixExpr PrefixMinus x, si'),
      keyword "not" >> do
        (!x, !si') <- parseExprPrec Nothing 4 si
        return (PrefixExpr Not x, si'),
      try $
        prefixOp "|" >> sc >> do
          (!x, !si') <- parseExprPrec Nothing 1 si
          return (PrefixExpr Guard x, si'),
      keyword "void" >> do
        (!x, !si') <- parseExpr si
        return (VoidExpr x, si'),
      keyword "ai" >> do
        (!x, !si') <- parseExpr si
        return (AtoIsoExpr x, si'),
      keyword "default" >> do
        (!apkr, !si') <-
          optional (parseArgsPacker si) >>= \case
            Nothing -> return (Nothing, si)
            Just (!apkr'', !si'') -> return (Just apkr'', si'')
        !x <- parseExprWithSrc
        return (DefaultExpr apkr x, si'),
      -- technically accept the `new` and `try keyword anywhere as an expr
      -- prefix, to better inter-op with some other languages like JavaScript
      do
        void $ keyword "new" <|> keyword "try"
        (ExprSrc !x _, !si') <- parseExpr si
        return (x, si')
    ]
  where
    prefixOp :: Text -> Parser ()
    prefixOp !opSym = string opSym >> notFollowedBy (satisfy isOperatorChar)

-- besides hardcoded prefix operators, all other operators are infix binary
-- operators, they can be declared and further overridden everywhere

parseExprLit :: Parser ExprSrc
parseExprLit = do
  !startPos <- getSourcePos
  void $ keyword "expr"
  parseExprWithSrc' startPos

parseExprWithSrc :: Parser ExprSrc
parseExprWithSrc = getSourcePos >>= parseExprWithSrc'

parseExprWithSrc' :: SourcePos -> Parser ExprSrc
parseExprWithSrc' !startPos = do
  !s <- getInput
  !o <- getOffset
  (!x, (!s', !o', !sss)) <- parseExprPrec Nothing (-20) (s, o, [])
  EdhParserState _ !lexeme'end !lexeme'end'offs <- get
  !sss' <-
    if lexeme'end'offs <= o'
      then return sss
      else do
        let !src = maybe "" fst $ takeN_ (lexeme'end'offs - o') s'
        return $ SrcSeg src : sss
  return $
    ExprSrc
      (ExprWithSrc x $ reverse sss')
      (lspSrcRangeFromParsec startPos lexeme'end)

parseIntplExpr :: IntplSrcInfo -> Parser (ExprSrc, IntplSrcInfo)
parseIntplExpr (s, o, sss) = do
  !startPos <- getSourcePos
  !o' <- getOffset
  void $ symbol "{$"
  !ie's <- getInput
  !ie'o <- getOffset
  (!x, (!ie's', !ie'o', !ie'sss)) <-
    parseExprPrec
      Nothing
      (-30)
      (ie's, ie'o, [])
  let !sss' =
        if o' > o
          then SrcSeg (maybe "" fst $ takeN_ (o' - o) s) : sss
          else sss
      !sss'' = IntplSeg x : sss'
  -- todo anything to do with the interpolated expr src segs ?
  let _ie'sss' =
        if ie'o' > ie'o
          then SrcSeg (maybe "" fst $ takeN_ (ie'o' - ie'o) ie's') : ie'sss
          else ie'sss
  -- 'string' used here to reserve spaces following this, as in original
  -- source of the outer expr
  void $ string "$}"
  !s' <- getInput
  !o'' <- getOffset
  !lexeme'end <- lexemeEndPos
  void $ optional sc -- but consume the optional spaces wrt parsing
  return
    ( ExprSrc
        (IntplExpr x)
        (lspSrcRangeFromParsec startPos lexeme'end),
      (s', o'', sss'')
    )

parseExprPrec ::
  Maybe (OpSymSrc, OpFixity) ->
  Precedence ->
  IntplSrcInfo ->
  Parser (ExprSrc, IntplSrcInfo)
parseExprPrec !precedingOp !prec !si =
  (parseExpr1st >>= \(!x, !si') -> parseMoreOps precedingOp si' x) <|> do
    !missed'start <- lexemeEndPos
    !missed'end <- getSourcePos
    let !missed'span = lspSrcRangeFromParsec' missed'start missed'end
        !missedExpr =
          ExprSrc
            ( AttrExpr
                (DirectRef (AttrAddrSrc MissedAttrName missed'span))
            )
            missed'span
    case precedingOp of
      Nothing ->
        parseMoreInfix Nothing si missedExpr >>= \case
          ( ExprSrc
              ( AttrExpr
                  (DirectRef (AttrAddrSrc MissedAttrName _))
                )
              _,
            _
            ) -> empty
          !lhsMissedResult -> return lhsMissedResult
      Just {} -> return (missedExpr, si)
  where
    parseExpr1st :: Parser (ExprSrc, IntplSrcInfo)
    parseExpr1st =
      ((,si) <$> parseExprLit) <|> parseIntplExpr si <|> do
        !startPos <- getSourcePos
        (!x, !si') <-
          choice
            [ (,si) . LitExpr <$> parseLitExpr,
              (,si) <$> parseSymbolExpr,
              parsePrefixExpr si,
              parseYieldExpr si,
              parseForExpr si,
              parseDoForOrWhileExpr si,
              parseWhileExpr si,
              parseIfExpr si,
              parseCaseExpr si,
              parseEffExpr si,
              parseListExpr si,
              parseScopedBlock si,
              parseDictOrBlock si,
              parseOpAddrOrApkOrParen si,
              parseExportExpr si,
              parseIncludeExpr si,
              parseImportExpr si,
              parseNamespaceExpr si,
              parseClassExpr si,
              parseDataExpr si,
              parseMethodExpr si,
              parseGeneratorExpr si,
              parseInterpreterExpr si,
              parseProducerExpr si,
              parseOpDeclOvrdExpr si,
              (,si) . AttrExpr <$> parseAttrRef
            ]
        !lexeme'end <- lexemeEndPos
        return (ExprSrc x (lspSrcRangeFromParsec startPos lexeme'end), si')

    parseMoreOps ::
      Maybe (OpSymSrc, OpFixity) ->
      IntplSrcInfo ->
      ExprSrc ->
      Parser (ExprSrc, IntplSrcInfo)
    parseMoreOps !pOp !si' !expr =
      choice
        [ parseIndexer si' >>= \(!idx, !si'') ->
            parseMoreOps pOp si'' $
              ExprSrc
                (IndexExpr idx expr)
                (SrcRange (exprSrcStart expr) (exprSrcEnd idx)),
          parseArgsPacker si' >>= \(!aps, !si'') -> do
            !lexeme'end <- lexemeEndPos
            parseMoreOps pOp si'' $
              ExprSrc
                (CallExpr expr aps)
                (SrcRange (exprSrcStart expr) lexeme'end),
          parseIndirectRef pOp si' expr,
          parseMoreInfix pOp si' expr
        ]

    parseIndirectRef ::
      Maybe (OpSymSrc, OpFixity) ->
      IntplSrcInfo ->
      ExprSrc ->
      Parser (ExprSrc, IntplSrcInfo)
    parseIndirectRef !pOp !si' !tgtExpr = try $ do
      singleDot
      addr@(AttrAddrSrc _ !addr'span) <-
        let ?allowKwAttr = True in parseAttrAddrSrc'
      parseMoreOps pOp si' $
        flip ExprSrc (SrcRange (exprSrcStart tgtExpr) (src'end addr'span)) $
          AttrExpr $ IndirectRef tgtExpr addr

    parseMoreInfix ::
      Maybe (OpSymSrc, OpFixity) ->
      IntplSrcInfo ->
      ExprSrc ->
      Parser (ExprSrc, IntplSrcInfo)
    parseMoreInfix !pOp !si' !leftExpr =
      tighterOp prec >>= \case
        Nothing -> return (leftExpr, si')
        Just (!opFixity, !opPrec, !opSym) -> do
          (!rightExpr, !si'') <-
            parseExprPrec (Just (opSym, opFixity)) opPrec si'
          parseMoreInfix pOp si'' $
            ExprSrc
              (InfixExpr opSym leftExpr rightExpr)
              (SrcRange (exprSrcStart leftExpr) (exprSrcEnd rightExpr))
      where
        tighterOp ::
          Precedence ->
          Parser (Maybe (OpFixity, Precedence, OpSymSrc))
        tighterOp prec' = do
          !beforeOp <- getParserState
          !errRptPos <- getOffset
          optional (try parseInfixOp) >>= \case
            Nothing -> return Nothing
            Just opSymSrc@(OpSymSrc !opSym _opSpan) -> do
              EdhParserState !opPD _ _ <- get
              case lookupOpFromDict opSym opPD of
                Nothing -> do
                  setOffset errRptPos
                  fail $ "undeclared operator: " <> T.unpack opSym
                Just (opFixity, opPrec, _) ->
                  if opPrec == prec'
                    then case opFixity of
                      InfixL -> do
                        -- leave this op to be encountered later, i.e.
                        -- after left-hand expr collapsed into one
                        setParserState beforeOp
                        return Nothing
                      InfixR -> return $ Just (opFixity, opPrec, opSymSrc)
                      Infix -> case pOp of
                        Nothing -> return $ Just (opFixity, opPrec, opSymSrc)
                        Just (_opSym, !pFixity) -> case pFixity of
                          Infix ->
                            fail $
                              "cannot mix [infix "
                                <> show prec'
                                <> " ("
                                <> T.unpack opSym
                                <> ")] and [infix "
                                <> show opPrec
                                <> " ("
                                <> T.unpack opSym
                                <> ")] in the same infix expression"
                          _ -> do
                            -- leave this op to be encountered later, i.e.
                            -- after left-hand expr collapsed into one
                            setParserState beforeOp
                            return Nothing
                    else
                      if opPrec > prec'
                        then return $ Just (opFixity, opPrec, opSymSrc)
                        else do
                          -- leave this op to be encountered later, i.e.
                          -- after left-hand expr collapsed into one
                          setParserState beforeOp
                          return Nothing

parseInfixOp :: Parser OpSymSrc
parseInfixOp = do
  !startPos <- getSourcePos
  !opSym <- parseOpLit
  !lexeme'end <- lexemeEndPos
  return $ OpSymSrc opSym $ SrcRange (lspSrcPosFromParsec startPos) lexeme'end

parseExpr :: IntplSrcInfo -> Parser (ExprSrc, IntplSrcInfo)
parseExpr = parseExprPrec Nothing (-10)
