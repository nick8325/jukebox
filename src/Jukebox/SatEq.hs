module Jukebox.SatEq where

import Jukebox.Sat
import Jukebox.Sat3
import Jukebox.SatMin

import Data.IORef
import Data.Map as M

--------------------------------------------------------------------------------

data SolverEq =
  SolverEq
  { satSolver :: Solver
  , counter   :: IORef Int
  , table     :: IORef (Map (Elt,Elt) Lit3)
  , model     :: IORef (Maybe (Map Elt Elt))
  }

newSolverEq :: Solver -> IO SolverEq
newSolverEq s =
  do ctr <- newIORef 0
     tab <- newIORef M.empty
     mod <- newIORef Nothing
     return SolverEq
       { satSolver = s
       , counter   = ctr
       , table     = tab
       , model     = mod
       }

instance SatSolver SolverEq where
  getSolver = satSolver

class SatSolver s => EqSolver s where
  getSolverEq :: s -> SolverEq

instance EqSolver SolverEq where
  getSolverEq s = s

--------------------------------------------------------------------------------

newtype Elt = Elt Int
  deriving ( Eq, Ord )

instance Show Elt where
  show (Elt k) = "#" ++ show k

newElt :: EqSolver s => s -> IO Elt
newElt s =
  do k <- readIORef (counter (getSolverEq s))
     writeIORef (counter (getSolverEq s)) $! k+1
     return (Elt k)

equal :: EqSolver s => s -> Elt -> Elt -> IO Lit3
equal s x y =
  case x `compare` y of
    GT -> equal s y x
    EQ -> return true3
    LT -> do tab <- readIORef (table (getSolverEq s))
             case M.lookup (x,y) tab of
               Just q ->
                 do return q
       
               Nothing ->
                 do q <- newLit3 s
                    writeIORef (table (getSolverEq s)) (M.insert (x,y) q tab)
                    return q

--------------------------------------------------------------------------------

solveEq :: EqSolver s => s -> [Lit] -> IO Bool
solveEq = undefined

--------------------------------------------------------------------------------

modelRep :: EqSolver s => s -> Elt -> IO (Maybe Elt)
modelRep s x =
  do mmod <- readIORef (model (getSolverEq s))
     return $
       case mmod of
         Just mp -> M.lookup x mp
         Nothing -> Nothing

--------------------------------------------------------------------------------
