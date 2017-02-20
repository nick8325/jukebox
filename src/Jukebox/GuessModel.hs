{-# LANGUAGE GADTs, PatternGuards #-}
module Jukebox.GuessModel where

import Control.Monad
import Jukebox.Name
import Jukebox.Form
import Jukebox.TPTP.Print
import Jukebox.TPTP.ParseSnippet
import Jukebox.Utils

data Universe = Peano | Trees

universe :: Universe -> Type -> NameM ([Function], [Form])
universe Peano = peano
universe Trees = trees

peano i = do
  zero <- newFunction "zero" [] i
  succ <- newFunction "succ" [i] i
  pred <- newFunction "pred" [i] i
  let types = [("$i", i)]
      funs = [("zero", zero),
              ("succ", succ),
              ("pred", pred)]
  
  let prelude =
        map (cnf types funs) [
          "zero != succ(X)",
          "pred(succ(X)) = X"
        ]
  return ([zero, succ], prelude)

trees i = do
  nil <- newFunction "nil" [] i
  bin <- newFunction "bin" [i, i] i
  left <- newFunction "left" [i] i
  right <- newFunction "right" [i] i
  let types = [("$i", i)]
      funs = [("nil", nil),
              ("bin", bin),
              ("left", left),
              ("right", right)]
  
  let prelude =
        map (cnf types funs) [
          "nil != bin(X,Y)",
          "left(bin(X,Y)) = X",
          "right(bin(X,Y)) = Y"
        ]
  return ([nil, bin], prelude)

guessModel :: [String] -> Universe -> Problem Form -> Problem Form
guessModel expansive univ prob = run prob $ \forms -> do
  let i = ind forms
  answerType <- newType "answer"
  answer <- newFunction "$answer" [answerType] O
  let withExpansive f func = f func (base (name func) `elem` expansive) answer
  (constructors, prelude) <- universe univ i
  program <- fmap concat (mapM (withExpansive (function constructors)) (functions forms))
  return (map (Input "adt" (Axiom "axiom") Unknown) prelude ++
          map (Input "program" (Axiom "axiom") Unknown) program ++
          forms)

ind :: Symbolic a => a -> Type
ind x =
  case types' x of
    [ty] -> ty
    [] -> Type (name "$i") Infinite Infinite
    _ -> error "GuessModel: can't deal with many-typed problems"

function :: [Function] -> Function -> Bool -> Function -> NameM [Form]
function constructors f expansive answerP = fmap concat $ do
  argss <- cases constructors (funArgs f)
  forM argss $ \args -> do
    fname <- newFunction ("exhausted_" ++ base (name f) ++ "_case")
               [] (head (funArgs answerP))
    let answer = Literal (Pos (Tru (answerP :@: [fname :@: []])))
    let theRhss = rhss constructors args f expansive answer
    alts <- forM theRhss $ \rhs -> do
      pred <- newFunction (concat (lines (prettyShow rhs))) [] O
      return (Literal (Pos (Tru (pred :@: []))))
    return $
      foldr (\/) false alts:
      [ closeForm (Connective Implies alt rhs)
      | (alt, rhs) <- zip alts theRhss ]

rhss :: [Function] -> [Term] -> Function -> Bool -> Form -> [Form]
rhss constructors args f expansive answer =
  case typ f of
    O ->
      Literal (Pos (Tru (f :@: args))):
      Literal (Neg (Tru (f :@: args))):
      map its (map (f :@:) (recursive args))
    _ | expansive -> map its (usort (unconditional ++ constructor))
      | otherwise -> map its (usort unconditional) ++ [answer]
  where recursive [] = []
        recursive (a:as) = reduce a ++ map (a:) (recursive as)
          where reduce (_f :@: xs) = [ x:as' | x <- xs, as' <- as:recursive as ]
                reduce _ = []
        constructor = [ c :@: xs
                      | c <- constructors,
                        xs <- sequence (replicate (arity c) unconditional) ]
        
        subterm = terms args
        its t = f :@: args .=. t
        unconditional = map (f :@:) (recursive args) ++ subterm

cases :: [Function] -> [Type] -> NameM [[Term]]
cases _constructors [] = return [[]]
cases constructors (ty:tys) = do
  ts <- cases1 constructors ty
  tss <- cases constructors tys
  return (liftM2 (:) ts tss)

cases1 :: [Function] -> Type -> NameM [Term]
cases1 constructors ty = do
  let maxArity = maximum (map arity constructors)
      varNames = take maxArity (cycle ["X", "Y", "Z"])
  vars <- mapM (flip newSymbol ty) varNames
  return [ c :@: take (arity c) (map Var vars)
         | c <- constructors ]
