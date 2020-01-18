
-- | Abstract Syntax Tree of the Edh language
module Language.Edh.AST where

import           Prelude

import           Data.Text                      ( Text )
import qualified Data.Text                     as T

import           Data.Lossless.Decimal          ( Decimal )

import           Text.Megaparsec


type ModuleId = Text

type OpSymbol = Text
type AttrName = Text
data AttrAddressor =
    -- | vanilla form in addressing attributes against
    --   a left hand entity object
    NamedAttr !AttrName
    -- | get the symbol value from current entity,
    --   then use it to address attributes against
    --   a left hand entity object
    | SymbolicAttr !AttrName
  deriving (Eq, Show)


newtype StmtSrc = StmtSrc (SourcePos, Stmt)
instance Eq StmtSrc where
  StmtSrc (x'sp, x'stmt) == StmtSrc (y'sp, y'stmt) =
    x'sp == y'sp && x'stmt == y'stmt
instance Show StmtSrc where
  show (StmtSrc (sp, stmt)) = show stmt ++ "\n@ " ++ sourcePosPretty sp


data Stmt =
      -- | literal `pass` to fill a place where a statement needed,
      -- same as in Python
      VoidStmt
      -- | atomically isolated, mark a code section for transaction bounds
    | AtoIsoStmt !Expr
      -- | similar to `go` in Go, starts goroutine
    | GoStmt !Expr
      -- | not similar to `defer` in Go (in Go `defer` snapshots arg values
      -- and schedules execution on func return), but in Edh `defer`
      -- schedules execution on thread termination
    | DeferStmt !Expr
      -- | import with args (re)pack receiving syntax
    | ImportStmt !ArgsReceiver !Expr
      -- | assignment with args (un/re)pack sending/receiving syntax
    | LetStmt !ArgsReceiver !ArgsSender
      -- | super object declaration for a descendant object
    | ExtendsStmt !Expr
      -- | class (constructor) procedure definition
    | ClassStmt !ProcDecl
      -- | method procedure definition
    | MethodStmt !ProcDecl
      -- | generator procedure definition
    | GeneratorStmt !ProcDecl
      -- | reactor declaration, a reactor procedure is not bound to a name,
      -- it's bound to an event `sink` with the calling thread as context,
      -- when an event fires from that event `sink`, the bound reactor will
      -- get run from the thread where it's declared, after the currernt
      -- transaction finishes, a reactor procedure can `break` to terminate
      -- the thread, or the thread will continue to process next reactor, or
      -- next transactional task normally
      -- the reactor mechanism is somewhat similar to traditional signal
      -- handling mechanism in OS process management
    | ReactorStmt !Expr !ArgsReceiver !StmtSrc
      -- | interpreter declaration, an interpreter procedure is not otherwise
      -- different from a method procedure, except it receives arguments
      -- in expression form rather than values, in addition to the reflective
      -- `callerScope` as first argument
    | InterpreterStmt !ProcDecl
      -- | while loop
    | WhileStmt !Expr !StmtSrc
      -- | break from a while/for loop, or terminate the Edh thread if given
      -- from a reactor
    | BreakStmt
      -- | continue a while/for loop
    | ContinueStmt
      -- | similar to fallthrough in Go
    | FallthroughStmt
      -- | operator declaration
    | OpDeclStmt !OpSymbol !Precedence !ProcDecl
      -- | operator override
    | OpOvrdStmt !OpSymbol !ProcDecl !Precedence
      -- | similar to exception mechanism in JavaScript
    | ThrowStmt !Expr | TryStmt {
        try'trunk :: !StmtSrc
        , try'catches :: ![(Expr, Maybe AttrName, StmtSrc)]
        , try'finally :: !(Maybe StmtSrc)
        }
      -- | early stop from a procedure
    | ReturnStmt !Expr
      -- | expression with precedence
    | ExprStmt !Expr
  deriving (Eq, Show)

data AttrAddr = ThisRef | ThatRef
    | DirectRef !AttrAddressor
    | IndirectRef !Expr !AttrAddressor
  deriving (Eq, Show)

data ArgsReceiver = PackReceiver ![ArgReceiver]
    | SingleReceiver !ArgReceiver
    | WildReceiver
  deriving (Eq)
instance Show ArgsReceiver where
  show (PackReceiver   rs) = "( " ++ unwords ((++ ", ") . show <$> rs) ++ ")"
  show (SingleReceiver r ) = "(" ++ show r ++ ")"
  show WildReceiver        = " * "

data ArgReceiver = RecvRestPosArgs !AttrName
    | RecvRestKwArgs !AttrName
    | RecvRestPkArgs !AttrName
    | RecvArg !AttrName !(Maybe AttrAddr) !(Maybe Expr)
  deriving (Eq)
instance Show ArgReceiver where
  show (RecvRestPosArgs nm) = "*" ++ T.unpack nm
  show (RecvRestKwArgs  nm) = "**" ++ T.unpack nm
  show (RecvRestPkArgs  nm) = "***" ++ T.unpack nm
  show (RecvArg nm _ _    ) = T.unpack nm

type ArgsSender = [ArgSender]
data ArgSender = UnpackPosArgs !Expr
    | UnpackKwArgs !Expr
    | UnpackPkArgs !Expr
    | SendPosArg !Expr
    | SendKwArg !AttrName !Expr
  deriving (Eq, Show)

data ProcDecl = ProcDecl { procedure'name :: AttrName
                        ,  procedure'args :: !ArgsReceiver
                        ,  procedure'body :: !StmtSrc
                        }
  deriving (Show)
instance Eq ProcDecl where
  ProcDecl x'name _ x'body == ProcDecl y'name _ y'body =
    x'name == y'name && x'body == y'body


data Prefix = PrefixPlus | PrefixMinus | Not
    -- | to disregard the match target in context,
    -- for a branch condition
    | Guard
  deriving (Eq, Show)

data Expr = LitExpr !Literal | PrefixExpr !Prefix !Expr
    | IfExpr { if'condition :: !Expr
            , if'consequence :: !StmtSrc
            , if'alternative :: !(Maybe StmtSrc)
            }
    | CaseExpr { case'target :: !Expr , case'branches :: !StmtSrc }

    | DictExpr ![Expr] -- should all be Infix ":"
    | ListExpr ![Expr]
    | TupleExpr ![Expr]
    | ParenExpr !Expr

    -- | the block is made an expression in Edh, instead of a statement
    -- as in a C family language. it evaluates to the value of last expr
    -- within it, in case no `EdhCaseClose` encountered, or can stop
    -- early with the value from a `EdhCaseClose`, typically returned
    -- from the branch `(->)` operator.
    --
    -- this allows multiple statements grouped as a single expression
    -- fitting into subclauses of if-then-else, while, for-from-do,
    -- and try-catch-finally etc. where an expression is expected.
    -- 
    -- this also made possible for a method procedure to explicitly
    -- `return { continue }` to carry a semantic to the magic method
    -- caller that it should try next method, similar to what
    -- `NotImplemented` does in Python.
    | BlockExpr ![StmtSrc]

    | YieldExpr !Expr

    -- | a for-from-do loop is made an expression in Edh, so it can
    -- appear as the right-hand expr of the comprehension (=<) operator.
    | ForExpr !ArgsReceiver !Expr !Expr

    | AttrExpr !AttrAddr
    | IndexExpr { index'value :: !Expr
                , index'target :: !Expr
                }
    | CallExpr !Expr !ArgsSender

    | InfixExpr !OpSymbol !Expr !Expr
  deriving (Eq, Show)


data Literal = NilLiteral
    | DecLiteral !Decimal
    | BoolLiteral !Bool
    | StringLiteral !Text
    | SinkCtor -- sink constructor
    | TypeLiteral !EdhTypeValue
  deriving (Eq, Show)


type Precedence = Int


-- | the type for the value of type of a value,
-- a type name should parse as literals, so here it is.
data EdhTypeValue = TypeType
    -- nil has no type, its type if you really ask, is nil
    | DecimalType
    | BoolType
    | StringType
    | SymbolType
    | ObjectType
    | DictType
    | ListType
    | PairType
    | TupleType
    | ArgsPackType
    | BlockType
    | HostProcType
    | HostOperType
    | HostGenrType
    | ClassType
    | MethodType
    | OperatorType
    | GeneratorType
    | InterpreterType
    | BreakType
    | ContinueType
    | CaseCloseType
    | FallthroughType
    | YieldType
    | ReturnType
    | SinkType
    | ExprType
  deriving (Eq, Ord, Show)
