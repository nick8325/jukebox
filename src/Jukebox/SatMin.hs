module Jukebox.SatMin where

import Jukebox.Sat

solveLocalMin :: SatSolver s => s -> [Lit] -> [Lit] -> IO Bool
solveLocalMin s as ms =
  do b <- solve s as
     if b then do l <- newLit s -- used as a local assumption for this minimization
                  localMin s as l ms
                  addClause s [neg l]
                  return True
          else do return False

localMin :: SatSolver s => s -> [Lit] -> Lit -> [Lit] -> IO ()
localMin s as l ms =
  do -- find out the current values of the m's
     bs <- sequence [ modelValue s m | m <- ms ]
  
     -- assert that all false m's should stay false
     sequence_ [ addClause s [neg l, neg m] | (m,b) <- ms `zip` bs, b /= Just True ]
     
     -- assert that at least one true m should become false also
     let ms1 = [ m | (m,Just True)  <- ms `zip` bs ]
     addClause s (neg l : [ neg m | m <- ms1 ])
     
     -- is there still a solution?
     b <- solve s (l:as)
     if b then localMin s as l ms1
          else return ()
