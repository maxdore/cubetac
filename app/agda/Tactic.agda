{-# OPTIONS --cubical --allow-unsolved-metas --allow-exec  #-}

module Tactic where

open import Agda.Builtin.Reflection as R
open import Agda.Builtin.String

open import Cubical.Data.List

open import Cubical.Data.Nat.Base
open import Cubical.Reflection.Base as R

open import Prelude

debug! : String -> Term → TC ⊤
debug! id tm = typeError (strErr "[" ∷ strErr id ∷ strErr "]" ∷ termErr tm ∷ [])

debugt! : String -> Telescope → TC ⊤
debugt! id tele = typeError (strErr "[" ∷ strErr id ∷ strErr "]" ∷ zip tele)
  where
  zip : Telescope → List ErrorPart
  zip [] = []
  zip (x ∷ asd) = strErr (fst x) ∷ zip asd

debugd! : List (Name × Term) → TC ⊤
debugd! a = typeError (map (λ (n , t) → termErr t) a)



definition→Context : Definition → List Name
definition→Context (data-type pars cs) = cs
definition→Context _ = []

getDefs : List Name → TC (List (Name × Term))
getDefs [] = returnTC []
getDefs (c ∷ cs) = do
  cty ← getType c
  csty ← getDefs cs
  returnTC ((c , cty) ∷ csty)

-- Retrieve the name of a HIT from a PathP/Path type
getName : Term → Name
-- getName (con p _) = p
getName (def p []) = p
getName (def p (a ∷ (arg ai t) ∷ as)) = getName t
getName (lam _ (abs _ p)) = getName p

postulate
  execTC : (exe : String) (args : List String) (stdIn : String)
    → TC (Σ ℕ (λ _ → Σ String (λ _ → String)))

{-# BUILTIN AGDATCMEXEC execTC #-}
macro
  cubetac : Term → TC ⊤
  cubetac hole = do
    goal ← inferType hole >>= normalise
    -- debug! "GOAL" goal
    -- typeError (strErr (primShowQName (getName goal)) ∷ [])
    test ← getDefinition (getName goal)
    -- typeError (map (λ x → strErr (primShowQName x)) (definition→Context test))
    idef ← getDefs (definition→Context test)
    contextstr ← formatErrorParts (foldr _++_ [] (map (λ (p , ty) → strErr (primShowQName p) ∷ strErr " : " ∷ termErr ty ∷ strErr "\n" ∷ []) idef))
    goalstr ← formatErrorParts (termErr goal ∷ [])
    let problem = primStringAppend contextstr (primStringAppend "---\n" ( goalstr))
    -- typeError (strErr problem ∷ [])
    (exitCode , (stdOut , stdErr)) ← execTC "cubetac" [] problem
    typeError (strErr stdErr ∷ strErr stdOut ∷ [])
    unify goal unknown



















appi : PathP (λ i → Path Interval (seg i) (seg i)) (λ _ → zero) λ _ → one
appi = λ i j → seg i

















-- macro
--   testmacro : Term → TC ⊤
--   testmacro hole = do
--     goal ← inferType hole
--     resI ← quoteTC one
--     resS ← quoteTC "one"
--     -- case goal of λ {}
--     unify hole resI

-- test1 : Interval
-- test1 = {!cubetac!}





-- appj : PathP (λ i → Path Interval zero one) seg seg
-- appj = {!cubetac!}
