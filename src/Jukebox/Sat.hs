module Jukebox.Sat
  ( Solver
  , newSolver
  , deleteSolver
  , Lit, neg
  , false, true
  
  , SatSolver(..)
  , newLit
  , addClause
  , solve
  , conflict
  , modelValue
  , value
  )
 where

--------------------------------------------------------------------------------

import MiniSat
  ( Solver
  , deleteSolver
  , Lit(..)
  , neg
  )

import qualified MiniSat as M

--------------------------------------------------------------------------------

false, true :: Lit
true  = MkLit 0
false = neg true

newSolver :: IO Solver
newSolver =
  do s <- M.newSolver
     x <- M.newLit s
     if x == false || x == true
       then do M.addClause s [true]
               return s
       else do error "failed to initialize false and true!"

--------------------------------------------------------------------------------

class SatSolver s where
  getSolver :: s -> Solver

instance SatSolver Solver where
  getSolver s = s

newLit :: SatSolver s => s -> IO Lit
newLit s = M.newLit (getSolver s)

addClause :: SatSolver s => s -> [Lit] -> IO ()
addClause s xs = M.addClause (getSolver s) xs >> return ()

solve :: SatSolver s => s -> [Lit] -> IO Bool
solve s xs = M.solve (getSolver s) xs

conflict :: SatSolver s => s -> IO [Lit]
conflict s = M.conflict (getSolver s)

modelValue :: SatSolver s => s -> Lit -> IO (Maybe Bool)
modelValue s x = M.modelValue (getSolver s) x

value :: SatSolver s => s -> Lit -> IO (Maybe Bool)
value s x = M.value (getSolver s) x

--------------------------------------------------------------------------------
