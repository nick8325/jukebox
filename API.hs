module API where

-- this is not actual code, it is just for writing down ideas

-----------------------------------------------------------------------------
-- Solver

data Solver s
  = Solver
  { state :: s
  , solve :: [Lit] -> IO (Maybe Bool)
  }

getSolver :: (s -> t) -> Solver s -> Solver t
getSolver f (Solver st sv) = Solver (f st) sv

-----------------------------------------------------------------------------
-- SAT

type SAT = Ptr MiniSAT

newSATSolver :: IO (Solver SAT)

-----------------------------------------------------------------------------
-- types

type Lit

neg :: Lit -> Lit
false, true :: Lit

-----------------------------------------------------------------------------
-- methods

-- create
newLit        :: SATSolver s => Solver s          -> IO Lit

-- constrain
addClause     :: SATSolver s => Solver s -> [Lit] -> IO ()

-- after solve
getConflict   :: SATSolver s => Solver s ->       -> IO [Lit]
getModelValue :: SATSolver s => Solver s -> Lit   -> IO Bool

-- top-level
getValue      :: SATSolver s => Solver s -> Lit   -> IO (Maybe Bool)

-----------------------------------------------------------------------------
-- overloading

class SATSolver s where
  getSAT :: s -> SAT

instance SATSolver SAT where
  getSAT s = s

-----------------------------------------------------------------------------
-- EqSAT

data EqSAT =
  EqSat
  { table :: IORef EqTable
  , sat   :: SAT
  }

newEqSATSolver :: Solver SAT -> IO (Solver EqSAT)

-----------------------------------------------------------------------------
-- types

type Elt

-----------------------------------------------------------------------------
-- methods

-- create
newElt      :: EqSATSolver s => Solver s               -> IO Elt
equals      :: EqSATSolver s => Solver s -> Elt -> Elt -> IO Lit

-- after solve
getModelRep :: EqSATSolver s => Solver s -> Elt        -> IO Elt

-- top-level
getRep      :: EqSATSolver s => Solver s -> Elt        -> IO Elt

-----------------------------------------------------------------------------
-- overloading

class SATSolver s => EqSATSolver s where
  getEqSAT :: s -> EqSAT

instance SATSolver EqSAT where
  getSAT s = sat s

instance EqSATSolver EqSAT where
  getEqSAT s = s

-----------------------------------------------------------------------------
-- TermSAT

data TermSAT =
  TermSat
  { table :: IORef TermTable
  , eqSat :: EqSAT
  }

newTermSATSolver :: Solver EqSAT -> IO (Solver TermSAT)

-----------------------------------------------------------------------------
-- types

type Fun

-----------------------------------------------------------------------------
-- methods

-- create
newFun           :: TermSATSolver s => Solver s -> Int          -> IO Fun
apply            :: TermSATSolver s => Solver s -> Fun -> [Elt] -> IO Elt

-- after solve
getModelFunTable :: TermSATSolver s => Solver s -> Fun     -> IO [([Elt],Elt)]

-- top-level
getModelFunTable :: TermSATSolver s => Solver s -> Fun     -> IO [([Elt],Elt)]

-----------------------------------------------------------------------------
-- overloading

class EqSATSolver s => TermSATSolver s where
  getTermSAT :: s -> TermSAT

instance SATSolver TermSAT where
  getSAT s = getSAT (eqSat s)

instance EqSATSolver TermSAT where
  getEqSAT s = eqSat s

instance TermSATSolver TermSAT where
  getTermSAT s = s

-----------------------------------------------------------------------------
-- ConstrSAT

data ConstrSAT =
  ConstrSat
  { table   :: IORef Whatever
  , termSat :: TermSAT
  }

newConstrSATSolver :: Solver TermSAT -> IO (Solver ConstrSAT)

-----------------------------------------------------------------------------
-- methods

-- create
newConstrFun     :: TermSATSolver s => Solver s -> Int     -> IO Fun

-- after solve
getModelConstr   :: TermSATSolver s => Solver s -> Elt     -> IO (Maybe (Fun,[Elt]))

-- top-level
getConstr        :: TermSATSolver s => Solver s -> Elt     -> IO (Maybe (Fun,[Elt]))

-----------------------------------------------------------------------------
-- overloading

class TermSATSolver s => ConstrSATSolver s where
  getConstrSAT :: s -> ConstrSAT

instance SATSolver ConstrSAT where
  getSAT s = getSAT (termSat s)

instance EqSATSolver ConstrSAT where
  getEqSAT s = getEqSAT (termSat s)

instance TermSATSolver ConstrSAT where
  getTermSAT s = termSat s

instance ConstrSATSolver ConstrSAT where
  getTermSAT s = s

-----------------------------------------------------------------------------
-- FuncSAT

data FuncSAT =
  FuncSat
  { table     :: IORef Whatever
  , constrSat :: ConstrSAT
  }

newFuncSATSolver :: Solver ConstrSAT -> IO (Solver FuncSAT)

-----------------------------------------------------------------------------
-- types

data Def
  = CaseDef
    { name      :: Fun
    , args      :: [Var]
    , scrutinee :: Term
    , cases     :: [(Fun,[Var],Term)]
    , deflt     :: Term
    }

directDef :: Fun -> [Var] -> Term -> Def
directDef f xs rhs = CaseDef f xs undefined [] rhs

-----------------------------------------------------------------------------
-- methods

-- create
whnf :: FuncSATSolver s => Solver s -> Elt -> IO Lit

-- constrain
addDef :: FuncSATSolver s => Solver s -> Def -> IO ()

-----------------------------------------------------------------------------
-- FolSAT

data FolSAT =
  FolSAT
  { state   :: IORef Something
  , termSat :: TermSAT
  }

newFolSATSolver :: Solver TermSAT -> IO (Solver FolSAT)

-----------------------------------------------------------------------------
-- types

type Var = String

data Term
  = Fun Fun [Term]
  | Var Var

data EqLit
  = Term :=: Term
  | Term :/=: Term

-----------------------------------------------------------------------------
-- methods

-- constrain
addFolClause :: FolSATSolver s => Solver s -> [EqLit] -> IO ()

-- idea: instead of having clauses represented as [EqLit], why not take
-- Equinox's internal clause datatype (definitions + equalities) as this?

-----------------------------------------------------------------------------
-- overloading

class TermSATSolver s => FolSATSolver s where
  getFolSAT :: s -> FolSAT

instance SATSolver FolSAT where
  getSAT s = getSAT (termSat s)

instance EqSATSolver TermSAT where
  getEqSAT s = getEqSAT (termSat s)

instance TermSATSolver TermSAT where
  getTermSAT s = termSat s

instance FolSATSolver FolSAT where
  getFolSAT s = s


