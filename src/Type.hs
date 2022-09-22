module Type where

import Data.List
import qualified Data.Map as Map
import Data.Map ((!), Map)

import Prel
import Data
import Deg



offset :: Var -> Tele -> Tele
offset v (Tele rs) = Tele $ map (\(Formula rs) -> Formula $
                                  map (\(Disj is) -> Disj $
                                        map (\(Conj i) -> Conj (if i > v then i-1 else i)) is) rs) rs


infer :: Cube -> Term -> Int -> Type
infer cube (Term (id , Tele [Formula r])) d = Type $ map (\i -> (evalTerm i e0, evalTerm i e1) ) [1..d]
  where
  evalTerm :: Var -> Endpoint -> Term
  evalTerm i (Endpoint e) =
    if e
      then let red = map (Disj . delete (Conj i) . literals ) r in
        if (Disj []) `elem` red
          then getBoundary e1
          else Term (id , offset i $ Tele [Formula red])
      else let red = filter (\(Disj c) -> not (Conj i `elem` c)) r in
        if red == []
          then getBoundary e0
          else Term (id , offset i $ Tele [Formula red])

  getBoundary :: Endpoint -> Term
  getBoundary (Endpoint e) = let def = lookup (id) (map decl (faces cube)) in
    case def of
      Just (Type [(l , r)]) -> if e then r else l
      Nothing -> error $ "Could not find definition of term " ++ id
