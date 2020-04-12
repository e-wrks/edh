
module Language.Edh.Parser where

import           Prelude
-- import           Debug.Trace

import           Control.Applicative     hiding ( many
                                                , some
                                                )
import           Control.Monad
import           Control.Monad.State.Strict

import           Data.Functor
import qualified Data.Char                     as Char
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Scientific
import qualified Data.HashMap.Strict           as Map

import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

import           Data.Lossless.Decimal         as D

import           Language.Edh.Control
import           Language.Edh.Details.RtTypes


-- | To preserve original source for expr literals, this data struct is
-- passed around to collect final @[SourceSeg]@ for an expr literal.
type IntplSrcInfo = (Text, Int, [SourceSeg])

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "{#" "#}")

symbol :: Text -> Parser Text
symbol = L.symbol sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

keyword :: Text -> Parser Text
keyword kw = try $ lexeme (string kw <* notFollowedBy (satisfy isIdentChar))

trailingComma :: Parser ()
trailingComma = void $ optional $ symbol ","

optionalSemicolon :: Parser ()
optionalSemicolon = void $ optional $ symbol ";"


isLetter :: Char -> Bool
isLetter = flip elem $ '_' : ['a' .. 'z'] ++ ['A' .. 'Z']

isIdentChar :: Char -> Bool
isIdentChar c = isLetter c || isDigit c || c == '\''

isDigit :: Char -> Bool
isDigit = flip elem ['0' .. '9']

isOperatorChar :: Char -> Bool
isOperatorChar c = if c > toEnum 128
  then Char.isSymbol c
  else elem c ("=~!@#$%^&|:<>?+-*/" :: [Char])

parseProgram :: Parser [StmtSrc]
parseProgram = do
  s <- getInput
  void sc
  (ss, _) <- parseStmts (s, 0, []) []
  return ss

parseStmts :: IntplSrcInfo -> [StmtSrc] -> Parser ([StmtSrc], IntplSrcInfo)
parseStmts si ss = (eof >> return (reverse ss, si)) <|> do
  optionalSemicolon
  (s, si') <- parseStmt si
  parseStmts si' (s : ss)

parseVoidStmt :: Parser Stmt
parseVoidStmt = VoidStmt <$ symbol "pass" -- same as Python

parseAtoIsoStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseAtoIsoStmt si =
  keyword "ai" >> parseExpr si >>= \(x, si') -> return (AtoIsoStmt x, si')

parseGoStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseGoStmt si = do
  void $ keyword "go"
  errRptPos   <- getOffset
  (expr, si') <- parseExpr si
  case expr of
    BlockExpr{} -> return ()
    CaseExpr{}  -> return ()
    CallExpr{}  -> return ()
    ForExpr{}   -> return ()
    _           -> do
      setOffset errRptPos
      fail "A block, case, call or for loop should be here"
  return (GoStmt expr, si')

parseDeferStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseDeferStmt si = do
  void $ keyword "defer"
  errRptPos   <- getOffset
  (expr, si') <- parseExpr si
  case expr of
    BlockExpr{} -> return ()
    CaseExpr{}  -> return ()
    CallExpr{}  -> return ()
    ForExpr{}   -> return ()
    _           -> do
      setOffset errRptPos
      fail "A block, case, call or for loop should be here"
  return (DeferStmt expr, si')

parseImportStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseImportStmt si = do
  void $ keyword "import"
  ar        <- parseArgsReceiver
  (se, si') <- parseExpr si
  return (ImportStmt ar se, si')

parseLetStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseLetStmt si = do
  void $ keyword "let"
  ar <- parseArgsReceiver
  void $ symbol "="
  (argSender, si') <- parseArgsSender si
  return (LetStmt ar argSender, si')


parseArgsReceiver :: Parser ArgsReceiver
parseArgsReceiver = (symbol "*" $> WildReceiver) <|> parsePackReceiver <|> do
  singleArg <- parseKwRecv False
  return $ SingleReceiver singleArg

parsePackReceiver :: Parser ArgsReceiver
parsePackReceiver = between
  (symbol "(")
  (symbol ")")
  (parseArgRecvs [] False False >>= return . PackReceiver . reverse)

parseArgRecvs :: [ArgReceiver] -> Bool -> Bool -> Parser [ArgReceiver]
parseArgRecvs rs kwConsumed posConsumed =
  (lookAhead (symbol ")") >> return rs) <|> do
    nextArg <-
      (if posConsumed
          then restPkArgs <|> restKwArgs <|> parseKwRecv True
          else nextPosArg
        )
        <* trailingComma
    case nextArg of
      RecvRestPosArgs _ -> parseArgRecvs (nextArg : rs) kwConsumed True
      RecvRestKwArgs  _ -> parseArgRecvs (nextArg : rs) True posConsumed
      _                 -> parseArgRecvs (nextArg : rs) kwConsumed posConsumed
 where
  nextPosArg, restKwArgs, restPosArgs :: Parser ArgReceiver
  nextPosArg = restPkArgs <|> restKwArgs <|> restPosArgs <|> parseKwRecv True
  restPkArgs = do
    void $ symbol "***"
    RecvRestPkArgs <$> parseAttrName
  restKwArgs = do
    void $ symbol "**"
    RecvRestKwArgs <$> parseAttrName
  restPosArgs = do
    void $ symbol "*"
    RecvRestPosArgs <$> parseAttrName

parseRetarget :: Parser AttrAddr
parseRetarget = do
  void $ keyword "as"
  parseAttrAddr

parseKwRecv :: Bool -> Parser ArgReceiver
parseKwRecv inPack = do
  aname   <- parseAttrName
  retgt   <- optional parseRetarget
  defExpr <- if inPack then optional parseDefaultExpr else return Nothing
  return $ RecvArg aname (validateTgt retgt) defExpr
 where
  validateTgt :: Maybe AttrAddr -> Maybe AttrAddr
  validateTgt tgt = case tgt of
    Nothing      -> Nothing
    Just ThisRef -> fail "Can not overwrite this"
    Just ThatRef -> fail "Can not overwrite that"
    _            -> tgt
  parseDefaultExpr :: Parser Expr
  parseDefaultExpr = do
    void $ symbol "="
    -- TODO carry on 'IntplSrcInfo' in the full call chain to here,
    --      so the default value expr can be interpolated.
    s         <- getInput
    o         <- getOffset
    (x, _si') <- parseExpr (s, o, [])
    return x


parseAttrAddr :: Parser AttrAddr
parseAttrAddr = do
  p1 <- leadingPart
  moreAddr p1
 where
  leadingPart :: Parser Expr
  leadingPart = choice
    [ AttrExpr ThisRef <$ keyword "this"
    , AttrExpr ThatRef <$ keyword "that"
    , AttrExpr SuperRef <$ keyword "super"
    , AttrExpr . DirectRef . SymbolicAttr <$> parseAttrSym
    , AttrExpr . DirectRef . NamedAttr <$> parseAttrName
    ]
  followingPart :: Parser Expr
  followingPart = choice
    [ keyword "this" *> fail "Unexpected this reference"
    , AttrExpr . DirectRef . SymbolicAttr <$> parseAttrSym
    , AttrExpr . DirectRef . NamedAttr <$> parseAttrName
    ]
  moreAddr :: Expr -> Parser AttrAddr
  moreAddr p1 =
    (symbol "." *> followingPart >>= \case
        AttrExpr (DirectRef addr) ->
          let r1 = IndirectRef p1 addr in moreAddr (AttrExpr r1) <|> return r1
        _ -> error "bug"
      )
      <|> case p1 of
            AttrExpr ThisRef -> return ThisRef
            AttrExpr ThatRef -> return ThatRef
            AttrExpr r1      -> return r1
            _                -> error "bug"


parseArgsSender :: IntplSrcInfo -> Parser (ArgsSender, IntplSrcInfo)
parseArgsSender si = parsePackSender si <|> do
  (x, si') <- parseExpr si
  return ([SendPosArg x], si')

parsePackSender :: IntplSrcInfo -> Parser (ArgsSender, IntplSrcInfo)
parsePackSender si = between (symbol "(") (symbol ")") $ do
  (ss, si') <- parseArgSends si []
  return (reverse ss, si')

parseArgSends
  :: IntplSrcInfo -> [ArgSender] -> Parser ([ArgSender], IntplSrcInfo)
parseArgSends si ss = (lookAhead (symbol ")") >> return (ss, si)) <|> do
  (arg, si') <- nextArg <* trailingComma
  parseArgSends si' $ arg : ss
 where
  nextArg, unpackPkArgs, unpackKwArgs, unpackPosArgs
    :: Parser (ArgSender, IntplSrcInfo)
  nextArg      = unpackPkArgs <|> unpackKwArgs <|> unpackPosArgs <|> parseKwSend
  unpackPkArgs = do
    void $ symbol "***"
    (x, si') <- parseExpr si
    return (UnpackPkArgs x, si')
  unpackKwArgs = do
    void $ symbol "**"
    (x, si') <- parseExpr si
    return (UnpackKwArgs x, si')
  unpackPosArgs = do
    void $ symbol "*"
    (x, si') <- parseExpr si
    return (UnpackPosArgs x, si')
  parseKwSend :: Parser (ArgSender, IntplSrcInfo)
  parseKwSend = do
    errRptPos <- getOffset
    (x, si')  <- parseExpr si
    case x of
      InfixExpr "=" nExpr vExpr -> case nExpr of
        AttrExpr (DirectRef (NamedAttr attrName)) ->
          return (SendKwArg attrName vExpr, si')
        _ -> do
          setOffset errRptPos
          fail $ "Invalid argument name: " <> show nExpr
      vExpr -> return (SendPosArg vExpr, si')


parseClassStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseClassStmt si = do
  void $ keyword "class"
  cn          <- parseAlphaName
  (body, si') <- parseStmt si
  return (ClassStmt $ ProcDecl cn (PackReceiver []) (Left body), si')

parseExtendsStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseExtendsStmt si = do
  void $ keyword "extends"
  (x, si') <- parseExpr si
  return (ExtendsStmt x, si')

parseMethodStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseMethodStmt si = do
  void $ keyword "method"
  (pd, si') <- parseProcDecl si
  return (MethodStmt pd, si')

parseGeneratorStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseGeneratorStmt si = do
  void $ keyword "generator"
  (pd, si') <- parseProcDecl si
  return (GeneratorStmt pd, si')


parsePerceiveStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parsePerceiveStmt si = do
  void $ keyword "perceive"
  addr     <- parseAttrAddr
  (x, si') <- parseExpr si
  return (PerceiveStmt addr x, si')

parseInterpreterStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseInterpreterStmt si = do
  void $ keyword "interpreter"
  (pd, si') <- parseProcDecl si
  return (InterpreterStmt pd, si')

parseProducerStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseProducerStmt si = do
  void $ keyword "producer"
  (pd, si') <- parseProcDecl si
  return (ProducerStmt pd, si')

parseWhileStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseWhileStmt si = do
  void $ keyword "while"
  (cnd, si' ) <- parseExpr si
  (act, si'') <- parseExpr si'
  return (WhileStmt cnd act, si'')

parseProcDecl :: IntplSrcInfo -> Parser (ProcDecl, IntplSrcInfo)
parseProcDecl si = do
  pn          <- parseMagicProcName <|> parseAlphaName
  ar          <- parseArgsReceiver
  (body, si') <- parseStmt si
  return (ProcDecl pn ar (Left body), si')

parseMagicProcName :: Parser Text
parseMagicProcName = between (symbol "(") (symbol ")") $ lexeme $ takeWhile1P
  (Just "magic procedure name")
  isMagicProcChar

-- to allow magic method names like ([]) ([=]) etc.
isMagicProcChar :: Char -> Bool
isMagicProcChar c = isOperatorChar c || elem c ("[]" :: [Char])

parseOpDeclOvrdStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseOpDeclOvrdStmt si = do
  void $ keyword "operator"
  srcPos      <- getSourcePos
  errRptPos   <- getOffset
  opSym       <- parseOpLit
  precDecl    <- optional $ L.decimal <* sc
  -- todo restrict forms of valid args receiver for operators, e.g. 
  --  * 2 pos-args - simple lh/rh value receiving operator
  --  * 3 pos-args - caller scope + lh/rh expr receiving operator
  argRcvr     <- parseArgsReceiver
  (body, si') <- parseStmt si
  let procDecl = ProcDecl opSym argRcvr (Left body)
  opPD <- get
  case precDecl of
    Nothing -> case Map.lookup opSym opPD of
      Nothing -> do
        setOffset errRptPos
        fail
          $  "You forget to specify the precedence for operator: "
          <> T.unpack opSym
          <> " ?"
      Just (opPrec, _) -> return (OpOvrdStmt opSym procDecl opPrec, si')
    Just opPrec -> do
      when (opPrec < 0 || opPrec >= 10) $ do
        setOffset errRptPos
        fail $ "Invalid operator precedence: " <> show opPrec
      case Map.lookup opSym opPD of
        Nothing       -> return ()
        Just (_, odl) -> do
          setOffset errRptPos
          fail
            $  "Redeclaring operator "
            <> T.unpack opSym
            <> " which has been declared at "
            <> T.unpack odl
            <> ", omit the precedence if you mean to override it."
      put $ Map.insert opSym (opPrec, T.pack $ sourcePosPretty srcPos) opPD
      return (OpDeclStmt opSym opPrec procDecl, si')

parseReturnStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseReturnStmt si = do
  void $ keyword "return"
  (x, si') <- parseExpr si
  return (ReturnStmt x, si')

parseThrowStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseThrowStmt si = do
  void $ keyword "throw"
  (x, si') <- parseExpr si
  return (ThrowStmt x, si')


parseStmt :: IntplSrcInfo -> Parser (StmtSrc, IntplSrcInfo)
parseStmt si = do
  srcPos      <- getSourcePos
  (stmt, si') <-
    choice
        [ parseAtoIsoStmt si
        , parseGoStmt si
        , parseDeferStmt si
        , parseImportStmt si
        , parseLetStmt si
        , parseClassStmt si
        , parseExtendsStmt si
        , parseMethodStmt si
        , parseGeneratorStmt si
        , parsePerceiveStmt si
        , parseInterpreterStmt si
        , parseProducerStmt si
        , parseWhileStmt si
          -- TODO validate <break> must within a loop construct
        , (BreakStmt, si) <$ keyword "break"
          -- note <continue> can be the eval'ed value of a proc,
          --      carrying NotImplemented semantics as in Python
        , (ContinueStmt, si) <$ keyword "continue"
          -- TODO validate fallthrough must within a branch block
        , (FallthroughStmt, si) <$ keyword "fallthrough"
        , parseOpDeclOvrdStmt si
          -- TODO validate yield must within a generator procedure
        , parseReturnStmt si
        , parseThrowStmt si
        , (, si) <$> parseVoidStmt

          -- NOTE: statements above should probably all be detected by
          -- `illegalExprStart` as invalid start for an expr
        , parseExpr si >>= \(x, si') -> return (ExprStmt x, si')
        ]
      <* optionalSemicolon
  return (StmtSrc (srcPos, stmt), si')


parseIfExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseIfExpr si = do
  void $ keyword "if"
  (cond, si') <- parseExpr si
  void $ keyword "then"
  (cseq, si2) <- parseExpr si'
  (alt , si3) <-
    fmap (maybe (Nothing, si2) (\(alt, si3) -> (Just alt, si3))) $ optional $ do
      void $ keyword "else"
      parseExpr si2
  return (IfExpr cond cseq alt, si3)

parseCaseExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseCaseExpr si = do
  void $ keyword "case"
  (tgt, si') <- parseExpr si
  void $ keyword "of"
  (branches, si'') <- parseExpr si'
  return (CaseExpr tgt branches, si'')

parseYieldExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseYieldExpr si = do
  void $ keyword "yield"
  (x, si') <- parseExpr si
  return (YieldExpr x, si')

parseForExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseForExpr si = do
  void $ keyword "for"
  ar <- parseArgsReceiver
  void $ keyword "from"
  (iter, si') <- parseExpr si
  void $ keyword "do"
  (doX, si'') <- parseExpr si'
  return (ForExpr ar iter doX, si'')

parseListExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseListExpr si = do
  (es, si') <- between (symbol "[") (symbol "]") (parseElem si [])
  return (ListExpr $ reverse es, si')
 where
  parseElem :: IntplSrcInfo -> [Expr] -> Parser ([Expr], IntplSrcInfo)
  parseElem si' es = do
    (x, si'') <- parseExpr si'
    trailingComma
    parseElem si'' (x : es)

parseStringLit :: Parser Text
parseStringLit = lexeme $ do
  delim <- char '\"' <|> char '\'' <|> char '`'
  T.pack <$> manyTill L.charLiteral (char delim)

parseBoolLit :: Parser Bool
parseBoolLit =
  (keyword "true" *> return True) <|> (keyword "false" *> return False)

parseDecLit :: Parser Decimal
parseDecLit = lexeme $ do -- todo support HEX/OCT ?
  sn <- L.signed (return ()) L.scientific
  return $ Decimal 1 (fromIntegral $ base10Exponent sn) (coefficient sn)

parseLitExpr :: Parser Literal
parseLitExpr = choice
  [ NilLiteral <$ litKw "nil"
  , BoolLiteral <$> parseBoolLit
  , StringLiteral <$> parseStringLit
  , SinkCtor <$ litKw "sink"
  , DecLiteral D.nan <$ litKw "nan"
  , DecLiteral D.inf <$ litKw "inf"
  , DecLiteral <$> parseDecLit
  , TypeLiteral DecimalType <$ litKw "DecimalType"
  , TypeLiteral BoolType <$ litKw "BoolType"
  , TypeLiteral StringType <$ litKw "StringType"
  , TypeLiteral SymbolType <$ litKw "SymbolType"
  , TypeLiteral ObjectType <$ litKw "ObjectType"
  , TypeLiteral DictType <$ litKw "DictType"
  , TypeLiteral ListType <$ litKw "ListType"
  , TypeLiteral PairType <$ litKw "PairType"
  , TypeLiteral TupleType <$ litKw "TupleType"
  , TypeLiteral ArgsPackType <$ litKw "ArgsPackType"
  , TypeLiteral BlockType <$ litKw "BlockType"
  , TypeLiteral IntrinsicType <$ litKw "IntrinsicType"
  , TypeLiteral HostClassType <$ litKw "HostClassType"
  , TypeLiteral HostMethodType <$ litKw "HostMethodType"
  , TypeLiteral HostOperType <$ litKw "HostOperType"
  , TypeLiteral HostGenrType <$ litKw "HostGenrType"
  , TypeLiteral ClassType <$ litKw "ClassType"
  , TypeLiteral MethodType <$ litKw "MethodType"
  , TypeLiteral OperatorType <$ litKw "OperatorType"
  , TypeLiteral GeneratorType <$ litKw "GeneratorType"
  , TypeLiteral InterpreterType <$ litKw "InterpreterType"
  , TypeLiteral ProducerType <$ litKw "ProducerType"
  , TypeLiteral BreakType <$ litKw "BreakType"
  , TypeLiteral ContinueType <$ litKw "ContinueType"
  , TypeLiteral CaseCloseType <$ litKw "CaseCloseType"
  , TypeLiteral FallthroughType <$ litKw "FallthroughType"
  , TypeLiteral YieldType <$ litKw "YieldType"
  , TypeLiteral ReturnType <$ litKw "ReturnType"
  , TypeLiteral SinkType <$ litKw "SinkType"
  , TypeLiteral ExprType <$ litKw "ExprType"
  , TypeLiteral TypeType <$ litKw "TypeType"
  ]
  where
        -- | there're just too many of them,
        -- annoying if all listed in err rpt
        litKw = hidden . keyword

parseAttrName :: Parser Text
parseAttrName = parseOpName <|> parseAlphaName

parseAttrSym :: Parser AttrName
parseAttrSym = char '@' *> parseAlphaName

parseAlphaName :: Parser AttrName
parseAlphaName = lexeme $ do
  anStart <- takeWhile1P (Just "attribute name") isLetter
  anRest  <- takeWhileP Nothing isIdentChar
  return $ anStart <> anRest

parseOpName :: Parser Text
parseOpName = between (symbol "(") (symbol ")") parseOpLit

parseOpLit :: Parser Text
parseOpLit = lexeme $ takeWhile1P (Just "operator symbol") isOperatorChar

parseBlockOrDict :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseBlockOrDict si = choice [try $ parseBlock si, parseDict si]

parseBlock :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseBlock si =
  symbol "{" *> notFollowedBy (symbol ",") *> parseBlockRest False [] si
 where
  parseBlockRest
    :: Bool -> [StmtSrc] -> IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
  parseBlockRest mustBlock t si' = do
    mustBlock' <- optional (symbol ";") >>= \case
      Nothing -> return mustBlock
      _       -> return True
    choice
      [ symbol "}" $> (, si')
        (case t of
          [] | mustBlock' -> BlockExpr []
         -- let {} parse as empty dict instead of empty block
          []              -> DictExpr []
         -- single k:v pair without comma will reach here
          [StmtSrc (_, ExprStmt pairExpr@(InfixExpr ":" _ _))]
            | not mustBlock' -> DictExpr [pairExpr]
          _ -> BlockExpr (reverse t)
        )
      , do
        (ss, si'') <- parseStmt si'
        parseBlockRest mustBlock' (ss : t) si''
      ]

parseDict :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseDict si = symbol "{" *> parseDictRest [] si
 where
  parseDictRest :: [Expr] -> IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
  parseDictRest t si' = optional (symbol ",") *> choice
    [ symbol "}" $> (DictExpr (reverse t), si')
    , parseKeyValPair si' >>= \(p, si'') -> parseDictRest (p : t) si''
    ]
  parseKeyValPair :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
  parseKeyValPair si' = do
    (pairExpr, si'') <- parseExpr si'
    trailingComma
    case pairExpr of
      InfixExpr ":" _ _ -> return (pairExpr, si'')
      _                 -> fail $ "Invalid dict entry: " <> show pairExpr


parseOpAddrOrTupleOrParen :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseOpAddrOrTupleOrParen si =
  symbol "("
    *> (fmap (, si)
             (AttrExpr . DirectRef . NamedAttr <$> (parseOpLit <* symbol ")"))
       <|> parseTupleRest si ")" False []
       )

parseTupleRest
  :: IntplSrcInfo -> Text -> Bool -> [Expr] -> Parser (Expr, IntplSrcInfo)
parseTupleRest si closeSym mustTuple t = do
  mustTuple' <- optional (symbol ",") >>= \case
    Nothing -> return mustTuple
    _       -> return True
  choice
    [ symbol closeSym $> (, si)
      (case t of
        [singleExpr] | not mustTuple' ->
          if closeSym == ")" then ParenExpr singleExpr else singleExpr
        _ -> TupleExpr (reverse t)
      )
    , parseExpr si
      >>= \(e, si') -> parseTupleRest si' closeSym mustTuple' $ e : t
    ]

parseIndexer :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseIndexer si = symbol "[" *> parseTupleRest si "]" False []


-- Notes:
--  * (+)/(-) prefix should have highest precedence below Call/Index
--  * (not) should have a precedence slightly higher than (&&) (||)
--  * guard (|) should have a precedence no smaller than the branch op (->)

parsePrefixExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parsePrefixExpr si = choice
  [ (symbol "+" >> notFollowedBy (satisfy isOperatorChar)) >> do
    (x, si') <- parseExprPrec 9 si
    return (PrefixExpr PrefixPlus x, si')
  , (symbol "-" >> notFollowedBy (satisfy isOperatorChar)) >> do
    (x, si') <- parseExprPrec 9 si
    return (PrefixExpr PrefixMinus x, si')
  , keyword "not" >> do
    (x, si') <- parseExprPrec 4 si
    return (PrefixExpr Not x, si')
  , (symbol "|" >> notFollowedBy (satisfy isOperatorChar)) >> do
    (x, si') <- parseExprPrec 1 si
    return (PrefixExpr Guard x, si')
  ]


-- NOTE: a keyword for statement will parse as identifier in an expr,
--       if not forbidden here.
illegalExprStart :: Parser Bool
illegalExprStart =
  True
    <$  choice
          [ keyword "ai"
          , keyword "go"
          , keyword "defer"
          , keyword "import"
          , keyword "let"
          , keyword "class"
          , keyword "extends"
          , keyword "method"
          , keyword "generator"
          , keyword "perceive"
          , keyword "interpreter"
          , keyword "producer"
          , keyword "while"
          , keyword "break"
          , keyword "continue"
          , keyword "fallthrough"
          , keyword "operator"
          , keyword "return"
          , keyword "throw"
          , keyword "pass"
          ]
    <|> return False


-- besides hardcoded prefix operators, all other operators are infix binary
-- operators, they can be declared and further overridden everywhere,
-- while they are left-assosciative only

parseExprLit :: Parser Expr
parseExprLit = do
  void $ keyword "expr"
  s                  <- getInput
  o                  <- getOffset
  (x, (s', o', sss)) <- parseExprPrec (-20) (s, o, [])
  o''                <- getOffset
  sss'               <- if o'' <= o'
    then return sss
    else do
      let !src = maybe "" fst $ takeN_ (o'' - o') s'
      return $ SrcSeg src : sss
  return $ ExprWithSrc x $ reverse sss'

parseIntplExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseIntplExpr (s, o, sss) = do
  o' <- getOffset
  void $ symbol "{$"
  ie's                        <- getInput
  ie'o                        <- getOffset
  (x, (ie's', ie'o', ie'sss)) <- parseExprPrec (-30) (ie's, ie'o, [])
  let !sss' = if o' > o
        then SrcSeg (maybe "" fst $ takeN_ (o' - o) s) : sss
        else sss
      !sss'' = IntplSeg x : sss'
  -- todo anything to do with the interpolated expr src segs ?
  let _ie'sss' = if ie'o' > ie'o
        then SrcSeg (maybe "" fst $ takeN_ (ie'o' - ie'o) ie's') : ie'sss
        else ie'sss
  -- 'string' used here to reserve spaces following this, as in original
  -- source of the outer expr
  void $ string "$}"
  s'  <- getInput
  o'' <- getOffset
  void $ optional sc -- but consume the optional spaces wrt parsing
  return (IntplExpr x, (s', o'', sss''))

parseExprPrec :: Precedence -> IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseExprPrec prec si = lookAhead illegalExprStart >>= \case
  True  -> fail "Illegal expression"
  False -> ((, si) <$> parseExprLit) <|> parseIntplExpr si <|> do
    (x, si') <- choice
      [ parsePrefixExpr si
      , parseYieldExpr si
      , parseForExpr si
      , parseIfExpr si
      , parseCaseExpr si
      , parseListExpr si
      , parseBlockOrDict si
      , parseOpAddrOrTupleOrParen si
      , (, si) . LitExpr <$> parseLitExpr
      , (, si) . AttrExpr <$> parseAttrAddr
      ]
    parseMoreOps si' x
 where
  parseMoreOps :: IntplSrcInfo -> Expr -> Parser (Expr, IntplSrcInfo)
  parseMoreOps si' expr = choice
    [ parseIndexer si'
      >>= \(idx, si'') -> parseMoreOps si'' $ IndexExpr idx expr
    , parsePackSender si'
      >>= \(aps, si'') -> parseMoreOps si'' $ CallExpr expr aps
    , parseMoreInfix si' expr
    ]
  parseMoreInfix :: IntplSrcInfo -> Expr -> Parser (Expr, IntplSrcInfo)
  parseMoreInfix si' leftExpr = choice
    [ lookAhead (symbol "$}") >> return (leftExpr, si')
    , higherOp prec >>= \case
      Nothing              -> return (leftExpr, si')
      Just (opPrec, opSym) -> do
        (rightExpr, si'') <- parseExprPrec opPrec si'
        parseMoreInfix si'' $ InfixExpr opSym leftExpr rightExpr
    ]

  higherOp :: Precedence -> Parser (Maybe (Precedence, OpSymbol))
  higherOp prec' = do
    beforeOp  <- getParserState
    errRptPos <- getOffset
    optional parseOpLit >>= \case
      Nothing    -> return Nothing
      Just opSym -> do
        opPD <- get
        case Map.lookup opSym opPD of
          Nothing -> do
            setOffset errRptPos
            fail $ "Undeclared operator: " <> T.unpack opSym
          Just (opPrec, _) -> if opPrec > prec'
            then return $ Just (opPrec, opSym)
            else do
              -- leave this op to be encountered later, i.e.
              -- after left-hand expr collapsed into one
              setParserState beforeOp
              return Nothing


parseExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseExpr = parseExprPrec (-10)
