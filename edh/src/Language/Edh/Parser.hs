
module Language.Edh.Parser where

import           Prelude
-- import           Debug.Trace

import           Control.Applicative     hiding ( many
                                                , some
                                                )
import           Control.Monad
import           Control.Monad.State.Strict

import           Data.Maybe
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

optionalComma :: Parser Bool
optionalComma = fromMaybe False <$> optional (True <$ symbol ",")

optionalSemicolon :: Parser Bool
optionalSemicolon = fromMaybe False <$> optional (True <$ symbol ";")

-- TODO support more Unicode ranges as valid identifier chars
isIdentStart :: Char -> Bool
isIdentStart = flip elem validChars
  where !validChars = '_' : ['a' .. 'z'] ++ ['A' .. 'Z']

isIdentChar :: Char -> Bool
isIdentChar c = isIdentStart c || isDigit c || c == '\''

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
parseStmts !si !ss = (eof >> return (reverse ss, si)) <|> do
  void optionalSemicolon
  (s, si') <- parseStmt si
  parseStmts si' (s : ss)

parseVoidStmt :: Parser Stmt
parseVoidStmt = VoidStmt <$ symbol "pass" -- same as Python

parseAtoIsoStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseAtoIsoStmt !si =
  keyword "ai" >> parseExpr si >>= \(x, si') -> return (AtoIsoStmt x, si')

parseGoStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseGoStmt !si = do
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
parseDeferStmt !si = do
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

parseEffectStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseEffectStmt !si = do
  void $ keyword "effect"
  (s, si') <- parseExpr si
  return (EffectStmt s, si')

parseExportExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseExportExpr !si = do
  void $ keyword "export"
  (s, si') <- parseExpr si
  return (ExportExpr s, si')

parseImportExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseImportExpr !si = do
  void $ keyword "import"
  ar        <- parseArgsReceiver
  (se, si') <- parseExpr si
  (<|> return (ImportExpr ar se Nothing, si')) $ do
    void $ keyword "into"
    (intoExpr, si'') <- parseExpr si'
    return (ImportExpr ar se (Just intoExpr), si'')


parseLetStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseLetStmt !si = do
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
parsePackReceiver =
  symbol "(" *> (PackReceiver . reverse <$> parseArgRecvs [] False False)

parseArgRecvs :: [ArgReceiver] -> Bool -> Bool -> Parser [ArgReceiver]
parseArgRecvs !rs !kwConsumed !posConsumed = (symbol ")" $> rs) <|> do
  nextArg <-
    (if posConsumed
        then restPkArgs <|> restKwArgs <|> parseKwRecv True
        else nextPosArg
      )
      <* optionalComma
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
    RecvRestKwArgs . fromMaybe "" <$> optional parseAttrName
  restPosArgs = do
    void $ symbol "*"
    RecvRestPosArgs <$> parseAttrName

parseRetarget :: Parser AttrAddr
parseRetarget = do
  void $ keyword "as"
  parseAttrAddr

parseKwRecv :: Bool -> Parser ArgReceiver
parseKwRecv !inPack = do
  addr    <- parseAttrAddressor
  retgt   <- optional parseRetarget
  defExpr <- if inPack then optional parseDefaultExpr else return Nothing
  return $ RecvArg addr (validateTgt retgt) defExpr
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


parseArgsSender :: IntplSrcInfo -> Parser (ArgsPacker, IntplSrcInfo)
parseArgsSender !si = parseArgsPacker si <|> do
  (x, si') <- parseExpr si
  return ([SendPosArg x], si')

parseArgsPacker :: IntplSrcInfo -> Parser (ArgsPacker, IntplSrcInfo)
parseArgsPacker !si = do
  void $ symbol "("
  (_, ss, si') <- parseArgSends si ")" False []
  return (reverse ss, si')

parseArgSends
  :: IntplSrcInfo
  -> Text
  -> Bool
  -> [ArgSender]
  -> Parser (Bool, [ArgSender], IntplSrcInfo)
parseArgSends !si !closeSym !commaAppeared !ss =
  (symbol closeSym >> return (commaAppeared, ss, si)) <|> do
    (arg, si') <- nextArg
    commaHere  <- optionalComma
    parseArgSends si' closeSym (commaAppeared || commaHere) $ arg : ss
 where
  nextArg, unpackPkArgs, unpackKwArgs, unpackPosArgs
    :: Parser (ArgSender, IntplSrcInfo)
  nextArg = unpackPkArgs <|> unpackKwArgs <|> unpackPosArgs <|> parse1ArgSend
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
  parseKwArgSend :: Parser (ArgSender, IntplSrcInfo)
  parseKwArgSend = do
    addr <- parseAttrAddressor
    void $ symbol "="
    (x, si') <- parseExpr si
    return (SendKwArg addr x, si')
  parse1ArgSend :: Parser (ArgSender, IntplSrcInfo)
  parse1ArgSend = try parseKwArgSend <|> do
    (x, si') <- parseExpr si
    return (SendPosArg x, si')


parseNamespaceExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseNamespaceExpr !si = do
  void $ keyword "namespace"
  pn <- choice
    [ SymbolicAttr <$> parseAttrSym
    , NamedAttr <$> parseMagicProcName
    , NamedAttr <$> parseAlphaName
    ]
  (argSender, si' ) <- parseArgsSender si
  (body     , si'') <- parseProcBody si'
  return (NamespaceExpr (ProcDecl pn WildReceiver (Left body)) argSender, si'')

parseClassExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseClassExpr !si = do
  void $ keyword "class"
  pn <- choice
    [ SymbolicAttr <$> parseAttrSym
    , NamedAttr <$> parseMagicProcName
    , NamedAttr <$> parseAlphaName
    ]
  (body, si') <- parseProcBody si
  return (ClassExpr $ ProcDecl pn (PackReceiver []) (Left body), si')

parseExtendsStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseExtendsStmt !si = do
  void $ keyword "extends"
  (x, si') <- parseExpr si
  return (ExtendsStmt x, si')

parseMethodExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseMethodExpr !si = do
  void $ keyword "method"
  (pd, si') <- parseProcDecl si
  return (MethodExpr pd, si')

parseGeneratorExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseGeneratorExpr !si = do
  void $ keyword "generator"
  (pd, si') <- parseProcDecl si
  return (GeneratorExpr pd, si')


parsePerceiveStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parsePerceiveStmt !si = do
  void $ keyword "perceive"
  (sink, si' ) <- parseExpr si
  (body, si'') <- parseExpr si'
  return (PerceiveStmt sink body, si'')

parseInterpreterExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseInterpreterExpr !si = do
  void $ keyword "interpreter"
  (pd, si') <- parseProcDecl si
  return (InterpreterExpr pd, si')

parseProducerExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseProducerExpr !si = do
  void $ keyword "producer"
  (pd, si') <- parseProcDecl si
  return (ProducerExpr pd, si')

parseWhileStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseWhileStmt !si = do
  void $ keyword "while"
  (cnd, si' ) <- parseExpr si
  (act, si'') <- parseStmt si'
  return (WhileStmt cnd act, si'')

parseProcDecl :: IntplSrcInfo -> Parser (ProcDecl, IntplSrcInfo)
parseProcDecl !si = do
  pn <- choice
    [ SymbolicAttr <$> parseAttrSym
    , NamedAttr <$> parseMagicProcName
    , NamedAttr <$> parseAlphaName
    ]
  ar          <- parseArgsReceiver
  (body, si') <- parseProcBody si
  return (ProcDecl pn ar (Left body), si')

parseMagicProcName :: Parser Text
parseMagicProcName = between (symbol "(") (symbol ")") $ lexeme $ takeWhile1P
  (Just "magic procedure name")
  isMagicProcChar

-- to allow magic method names like ([]) ([=]) etc.
isMagicProcChar :: Char -> Bool
isMagicProcChar c = isOperatorChar c || elem c ("[]" :: [Char])

parseOpDeclOvrdExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseOpDeclOvrdExpr !si = do
  void $ keyword "operator"
  srcPos      <- getSourcePos
  errRptPos   <- getOffset
  opSym       <- parseOpLit
  precDecl    <- optional $ L.decimal <* sc
  -- todo restrict forms of valid args receiver for operators, e.g. 
  --  * 2 pos-args - simple lh/rh value receiving operator
  --  * 3 pos-args - caller scope + lh/rh expr receiving operator
  argRcvr     <- parseArgsReceiver
  (body, si') <- parseProcBody si
  let procDecl = ProcDecl (NamedAttr opSym) argRcvr (Left body)
  opPD <- get
  case precDecl of
    Nothing -> case Map.lookup opSym opPD of
      Nothing -> do
        setOffset errRptPos
        fail
          $  "You forget to specify the precedence for operator: "
          <> T.unpack opSym
          <> " ?"
      Just (opPrec, _) -> return (OpOvrdExpr opSym procDecl opPrec, si')
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
      return (OpDeclExpr opSym opPrec procDecl, si')

parseReturnStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseReturnStmt !si = do
  void $ keyword "return"
  (x, si') <- parseExpr si
  return (ReturnStmt x, si')

parseThrowStmt :: IntplSrcInfo -> Parser (Stmt, IntplSrcInfo)
parseThrowStmt !si = do
  void $ keyword "throw"
  (x, si') <- parseExpr si
  return (ThrowStmt x, si')


parseStmt' :: Int -> IntplSrcInfo -> Parser (StmtSrc, IntplSrcInfo)
parseStmt' !prec !si = do
  void optionalSemicolon
  srcPos      <- getSourcePos
  (stmt, si') <- choice
    [ parseAtoIsoStmt si
    , parseGoStmt si
    , parseDeferStmt si
    , parseEffectStmt si
    , parseLetStmt si
    , parseExtendsStmt si
    , parsePerceiveStmt si
    , parseWhileStmt si
          -- TODO validate <break> must within a loop construct
    , (BreakStmt, si) <$ keyword "break"
          -- note <continue> can be the eval'ed value of a proc,
          --      carrying NotImplemented semantics as in Python
    , (ContinueStmt, si) <$ keyword "continue"
          -- TODO validate fallthrough must within a branch block
    , (FallthroughStmt, si) <$ keyword "fallthrough"
    , (RethrowStmt, si) <$ keyword "rethrow"
    , parseReturnStmt si
    , parseThrowStmt si
    , (, si) <$> parseVoidStmt

          -- NOTE: statements above should probably all be detected by
          -- `illegalExprStart` as invalid start for an expr
    , parseExprPrec prec si >>= \(x, si') -> return (ExprStmt x, si')
    ]
  return (StmtSrc (srcPos, stmt), si')

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
  (cond, si') <- parseExpr si
  void $ keyword "then"
  (cseq, si2) <- parseExpr si'
  (alt , si3) <-
    fmap (maybe (Nothing, si2) (\(alt, si3) -> (Just alt, si3))) $ optional $ do
      void $ keyword "else"
      parseExpr si2
  return (IfExpr cond cseq alt, si3)

parseCaseExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseCaseExpr !si = do
  void $ keyword "case"
  (tgt, si') <- parseExpr si
  void $ keyword "of"
  (branches, si'') <- parseExpr si'
  return (CaseExpr tgt branches, si'')

parseYieldExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseYieldExpr !si = do
  void $ keyword "yield"
  (x, si') <- parseExpr si
  return (YieldExpr x, si')

parseForExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseForExpr !si = do
  void $ keyword "for"
  ar <- parseArgsReceiver
  void $ keyword "from"
  (iter, si') <- parseExpr si
  void $ keyword "do"
  (doX, si'') <- parseExpr si'
  return (ForExpr ar iter doX, si'')

parsePerformExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parsePerformExpr !si = do
  void $ keyword "perform"
  addr <- parseAttrAddressor
  return (PerformExpr addr, si)

parseBehaveExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseBehaveExpr !si = do
  void $ keyword "behave"
  addr <- parseAttrAddressor
  return (BehaveExpr addr, si)

parseListExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseListExpr !si = do
  void $ symbol "["
  (es, si') <- parseElem si []
  return (ListExpr $ reverse es, si')
 where
  parseElem :: IntplSrcInfo -> [Expr] -> Parser ([Expr], IntplSrcInfo)
  parseElem si' es = (symbol "]" >> return (es, si')) <|> do
    (x, si'') <- parseExpr si'
    void optionalComma
    parseElem si'' (x : es)

parseStringLit :: Parser Text
parseStringLit = lexeme $ do
  delim <- choice
    [ string "'''"
    , string "'"
    , string "```"
    , string "`"
    , string "\"\"\""
    , string "\""
    ]
  T.pack <$> manyTill L.charLiteral (string delim)

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
  , TypeLiteral BlobType <$ litKw "BlobType"
  , TypeLiteral SymbolType <$ litKw "SymbolType"
  , TypeLiteral ObjectType <$ litKw "ObjectType"
  , TypeLiteral DictType <$ litKw "DictType"
  , TypeLiteral ListType <$ litKw "ListType"
  , TypeLiteral PairType <$ litKw "PairType"
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
  , TypeLiteral DescriptorType <$ litKw "DescriptorType"
  , TypeLiteral BreakType <$ litKw "BreakType"
  , TypeLiteral ContinueType <$ litKw "ContinueType"
  , TypeLiteral CaseCloseType <$ litKw "CaseCloseType"
  , TypeLiteral CaseOtherType <$ litKw "CaseOtherType"
  , TypeLiteral FallthroughType <$ litKw "FallthroughType"
  , TypeLiteral RethrowType <$ litKw "RethrowType"
  , TypeLiteral YieldType <$ litKw "YieldType"
  , TypeLiteral ReturnType <$ litKw "ReturnType"
  , TypeLiteral DefaultType <$ litKw "DefaultType"
  , TypeLiteral SinkType <$ litKw "SinkType"
  , TypeLiteral ExprType <$ litKw "ExprType"
  , TypeLiteral TypeType <$ litKw "TypeType"
  ]
  where
        -- | there're just too many of them,
        -- annoying if all listed in err rpt
        litKw = hidden . keyword

parseAttrAddressor :: Parser AttrAddressor
parseAttrAddressor =
  choice [SymbolicAttr <$> parseAttrSym, NamedAttr <$> parseAttrName]

parseAttrName :: Parser Text
parseAttrName = parseOpName <|> parseAlphaName

parseAttrSym :: Parser AttrName
parseAttrSym = char '@' *> optional sc *> parseAlphaName

parseAlphaName :: Parser AttrName
parseAlphaName = lexeme $ do
  anStart <- takeWhile1P (Just "attribute name") isIdentStart
  anRest  <- takeWhileP Nothing isIdentChar
  return $ anStart <> anRest

parseOpName :: Parser Text
parseOpName = between (symbol "(") (symbol ")") parseOpLit

parseOpLit :: Parser Text
parseOpLit = choice
  [ lexeme $ takeWhile1P (Just "operator symbol") isOperatorChar
  , keyword "is not"
  , keyword "is"
  , keyword "not is"
  ]

parseDictOrBlock :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseDictOrBlock !si0 = symbol "{"
  *> choice [try $ parseDictEntries si0 [], parseBlockRest [] si0]
 where
  parseBlockRest :: [StmtSrc] -> IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
  parseBlockRest !t !si = optionalSemicolon *> choice
    [ symbol "}" $> (BlockExpr $ reverse t, si)
    , do
      (ss, si') <- parseStmt si
      parseBlockRest (ss : t) si'
    ]
  parseDictEntries
    :: IntplSrcInfo -> [(DictKeyExpr, Expr)] -> Parser (Expr, IntplSrcInfo)
  parseDictEntries !si !es = optionalSemicolon >>= \case
    True  -> fail "should be block instead of dict"
    -- note: keep the order of entries reversed here as written in source
    False -> optionalComma *> (symbol "}" $> (DictExpr es, si)) <|> do
      (e, si') <- nextEntry
      parseDictEntries si' (e : es)
   where
    nextEntry, litEntry, addrEntry, exprEntry
      :: Parser ((DictKeyExpr, Expr), IntplSrcInfo)
    nextEntry = (litEntry <|> addrEntry <|> exprEntry) <* optionalComma
    litEntry  = try $ do
      k <- parseLitExpr
      void $ symbol ":"
      (v, si') <- parseExpr si
      return ((LitDictKey k, v), si')
    addrEntry = try $ do
      k <- parseAttrAddr
      void $ symbol ":"
      (v, si') <- parseExpr si
      return ((AddrDictKey k, v), si')
    exprEntry = try $ do
      -- assuming (:) has precedence of 2
      (k, si') <- parseExprPrec 2 si
      void $ symbol ":"
      (v, si'') <- parseExpr si'
      return ((ExprDictKey k, v), si'')

parseOpAddrOrApkOrParen :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseOpAddrOrApkOrParen !si = symbol "(" *> choice
  [ (, si)
    <$> (AttrExpr . DirectRef . NamedAttr <$> try (parseOpLit <* symbol ")"))
  , parseApkRest si ")" False
  ]

parseApkRest :: IntplSrcInfo -> Text -> Bool -> Parser (Expr, IntplSrcInfo)
parseApkRest !si !closeSym !mustApk = do
  mustApk' <- optionalComma >>= \case
    True  -> return True
    False -> return mustApk
  (mustApk'', ss, si') <- parseArgSends si closeSym mustApk' []
  return $ (, si') $ case ss of
    [SendPosArg !singleExpr] | not mustApk'' ->
      if closeSym == ")" then ParenExpr singleExpr else singleExpr
    _ -> ArgsPackExpr $ reverse ss

parseIndexer :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parseIndexer !si = symbol "[" *> parseApkRest si "]" False


-- Notes:
--  * (+)/(-) prefix should have highest precedence below Call/Index
--  * (not) should have a precedence slightly higher than (&&) (||)
--  * guard (|) should have a precedence no smaller than the branch op (->)

parsePrefixExpr :: IntplSrcInfo -> Parser (Expr, IntplSrcInfo)
parsePrefixExpr !si = choice
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
          , keyword "effect"
          , keyword "let"
          , keyword "extends"
          , keyword "perceive"
          , keyword "while"
          , keyword "break"
          , keyword "continue"
          , keyword "fallthrough"
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
  -- remove trailing white spaces of the last src segment
  let sss'' = case sss' of
        SrcSeg src : prev -> SrcSeg (T.stripEnd src) : prev
        _                 -> sss'
  return $ ExprWithSrc x $ reverse sss''

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
parseExprPrec prec !si = lookAhead illegalExprStart >>= \case
  True  -> fail "Illegal expression"
  False -> ((, si) <$> parseExprLit) <|> parseIntplExpr si <|> do
    (x, si') <- choice
      [ parsePrefixExpr si
        -- TODO validate yield must within a generator procedure
      , parseYieldExpr si
      , parseForExpr si
      , parseIfExpr si
      , parseCaseExpr si
      , parsePerformExpr si
      , parseBehaveExpr si
      , parseListExpr si
      , parseDictOrBlock si
      , parseOpAddrOrApkOrParen si
      , parseExportExpr si
      , parseImportExpr si
      , parseNamespaceExpr si
      , parseClassExpr si
      , parseMethodExpr si
      , parseGeneratorExpr si
      , parseInterpreterExpr si
      , parseProducerExpr si
      , parseOpDeclOvrdExpr si
      , (, si) . LitExpr <$> parseLitExpr
      , (, si) . AttrExpr <$> parseAttrAddr
      ]
    parseMoreOps si' x
 where
  parseMoreOps :: IntplSrcInfo -> Expr -> Parser (Expr, IntplSrcInfo)
  parseMoreOps si' expr = choice
    [ parseIndexer si'
      >>= \(idx, si'') -> parseMoreOps si'' $ IndexExpr idx expr
    , parseArgsPacker si'
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
