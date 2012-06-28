{-# LANGUAGE TypeOperators #-}
module GuessModel where

import Control.Monad
import qualified Data.ByteString.Char8 as BS
import Name
import Form
import Clausify hiding (cnf)
import TPTP.Print
import TPTP.ParseSnippet
import Utils
import qualified HighSat as S
import HighSat(Sat1)
import Provers.E
import Control.Monad.Trans

type Universe = ([Function], [Form])

peano, trees :: Type -> NameM Universe

peano i = do
  zero <- newFunction "zero" [] i
  succ <- newFunction "succ" [i] i
  pred <- newFunction "pred" [i] i
  let types = [("$i", i)]
      funs = [("zero", zero),
              ("succ", succ),
              ("pred", pred)]

  prelude <- mapM (cnf types funs) [
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

  prelude <- mapM (cnf types funs) [
    "nil != bin(X,Y)",
    "left(bin(X,Y)) = X",
    "right(bin(X,Y)) = Y"
    ]
  return ([nil, bin], prelude)

ind :: Symbolic a => a -> Type
ind x =
  case types' x of
    [ty] -> ty
    [] -> Type nameI Infinite Infinite
    _ -> error "GuessModel: can't deal with many-typed problems"

type Var = Term ::: Form -- Answer term ::: case
type Choice = Function -> [Var]

guessModel :: EFlags -> (Type -> NameM Universe) -> Problem Form -> IO (Problem Form)
guessModel fl univM prob =
  S.runSat1 (const (return ())) $ do
    choice <- initialise answerPred univ
    loop fl answerPred choice [] univ (fmap (const forms) prob')
  where
    prob' = close prob $ \forms -> do
      let i = ind forms
      answerPred <- newFunction "$answer" [i] O
      univ <- univM i
      return (i, answerPred, univ, forms)
    (i, answerPred, univ, forms) = open prob'

initialise :: Function -> Universe -> Sat1 (Either Var Function) (Bool -> Choice)
initialise = undefined

loop :: EFlags -> Function -> (Bool -> Choice) -> [Function] -> Universe -> Problem Form ->
        Sat1 (Either Var Function) (Problem Form)
loop fl answerPred choice expansive univ prob = do
  let choice' f = choice (f `elem` expansive) f
  mod <- S.model
  let prob' = fmap (encodeModel answerPred (mod . Left) choice' univ) prob
  res <- liftIO (runE fl prob')
  undefined

encodeModel :: Function -> (Var -> Bool) -> Choice -> Universe -> [Input Form] -> [Input Form]
encodeModel answerPred model choice (constructors, prelude) forms =
  map (Input (BS.pack "adt") Axiom) prelude ++
  map (Input (BS.pack "program") Axiom) program ++
  forms
  where
    answer x = Literal (Pos (Tru (answerPred :@: [x])))
    program =
      [ rhs \/ answer lhs
      | func <- functions forms,
        t@(lhs ::: rhs) <- choice func,
        model t ]

rhss :: [Function] -> [Term] -> Function -> Bool -> [Form]
rhss constructors args f expansive =
  case typ f of
    O ->
      Literal (Pos (Tru (f :@: args))):
      Literal (Neg (Tru (f :@: args))):
      map its (map (f :@:) (recursive args))
    _ | expansive -> map its (usort (unconditional ++ constructor))
      | otherwise -> map its (usort unconditional)
  where recursive [] = []
        recursive (a:as) = reduce a ++ map (a:) (recursive as)
          where reduce (f :@: xs) = [ x:as' | x <- xs, as' <- as:recursive as ]
                reduce _ = []
        constructor = [ c :@: xs
                      | c <- constructors,
                        xs <- sequence (replicate (arity c) unconditional) ]

        subterm = terms args
        its t = f :@: args .=. t
        unconditional = map (f :@:) (recursive args) ++ subterm

cases :: [Function] -> [Type] -> NameM [[Term]]
cases constructors [] = return [[]]
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
