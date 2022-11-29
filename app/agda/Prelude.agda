{-# OPTIONS --cubical #-}

module Prelude where

open import Agda.Primitive public
open import Agda.Builtin.Cubical.Path public
open import Agda.Builtin.Cubical.Sub public
  renaming ( inc to inS
           ; primSubOut to outS
           )
open import Agda.Primitive.Cubical renaming (primINeg to ~_; primIMax to _∨_; primIMin to _∧_;
                                             primHComp to hcomp; primTransp to transp; primComp to comp;
                                             itIsOne to 1=1) public




open import Agda.Builtin.Unit public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Maybe public
open import Agda.Builtin.List public
open import Agda.Builtin.Nat public renaming (Nat to ℕ)


ℓ-max = _⊔_
ℓ-suc = lsuc

_[_↦_] : ∀ {ℓ} (A : Set ℓ) (φ : I) (u : Partial φ A) → _
A [ φ ↦ u ] = Sub A φ u

infix 4 _[_↦_]

private
  variable
    ℓ ℓ' ℓ'' : Level
    A : Set ℓ
    B : A → Set ℓ
    x y z w : A

refl : x ≡ x
refl {x = x} _ = x
{-# INLINE refl #-}

sym : x ≡ y → y ≡ x
sym p i = p (~ i)
{-# INLINE sym #-}

cong : (f : (a : A) → B a) (p : x ≡ y) →
       PathP (λ i → B (p i)) (f x) (f y)
cong f p i = f (p i)


-- HERE COULD COME MORE FROM CUBICAL PRELUDE
doubleComp-faces : {x y z w : A } (p : x ≡ y) (r : z ≡ w)
                 → (i : I) (j : I) → Partial (i ∨ ~ i) A
doubleComp-faces p r i j (i = i0) = p (~ j)
doubleComp-faces p r i j (i = i1) = r j

_∙∙_∙∙_ : w ≡ x → x ≡ y → y ≡ z → w ≡ z
p ∙∙ q ∙∙ r = λ i → hcomp (λ j → λ {
                    (i = i0) → p (~ j)
                  ; (i = i1) → r j
                  }) (q i)

-- (p ∙∙ q ∙∙ r) i = hcomp (doubleComp-faces p r i) (q i)


_∙_ : x ≡ y → y ≡ z → x ≡ z
p ∙ q = λ i → hcomp (λ j → λ {
                    (i = i0) → p i0
                  ; (i = i1) → q j
                  }) (p i)

-- p ∙ q = refl ∙∙ p ∙∙ q

hfill : {A : Set ℓ}
        {φ : I}
        (u : ∀ i → Partial φ A)
        (u0 : A [ φ ↦ u i0 ])
        -----------------------
        (i : I) → A
hfill {φ = φ} u u0 i =
  hcomp (λ j → λ { (φ = i1) → u (i ∧ j) 1=1
                 ; (i = i0) → outS u0 })
        (outS u0)


--           p ∙∙ q ∙∙ r
--       _ _ _ _ _ _ _ _ _ _
--       |\               /|
--       | \sym p      r / |
--       |  \_____q_____/  |
--       |  |           |  |
--       |  |           |  |
-- sym p |  |     q     |  | r
--       |  |           |  |
--       |  |___________|  |
--       |  /           \  |
--       | /             \ |
--       |/_______________\|
--               q

doubleCompPath-filler : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
                      → PathP (λ j → p (~ j) ≡ r j) q (p ∙∙ q ∙∙ r)
doubleCompPath-filler p q r = λ i j → hcomp (λ k → λ {
                    (i = i0) → q j
                  -- ; (i = i1) →
                  --       (hfill (λ l → λ {
                  --         (j = i0) → p (~ l)
                  --       ; (j = i1) → r l
                  --       }) (inS (q j)) k)
                  ; (j = i0) → p (~ i ∨ ~ k)
                  ; (j = i1) → r (i ∧ k)
                  }) (q j)

-- doubleCompPath-filler p q r j i = hfill (doubleComp-faces p r i) (inS (q i)) j





compPath-filler : (p : x ≡ y) (q : y ≡ z) → PathP (λ j → x ≡ q j) p (p ∙ q)
-- compPath-filler p q = doubleCompPath-filler refl p q
compPath-filler p q = λ i j → hcomp (λ k → λ {
                    (i = i0) → p j
                  ; (j = i0) → p i0
                  ; (j = i1) → q (i ∧ k)
                  }) (p j)





Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
Path A a b = PathP (λ _ → A) a b

isContr : ∀{ℓ} → Set ℓ → Set ℓ
isContr A = Σ A(λ x → ∀ y → x ≡ y)

isProp : ∀{ℓ} → Set ℓ → Set ℓ
isProp A = (x y : A) → x ≡ y

isSet : ∀{ℓ} → Set ℓ → Set ℓ
isSet A = (x y : A) → isProp (x ≡ y)

isGroupoid : ∀{ℓ} → Set ℓ → Set ℓ
isGroupoid A = ∀ a b → isSet (Path A a b)



_×_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A × B = Σ A (λ _ → B)


-- module _ {ℓ} {A : Set ℓ} where

--   infixr 5 _++_

--   [_] : A → List A
--   [ a ] = a ∷ []

--   _++_ : List A → List A → List A
--   [] ++ ys = ys
--   (x ∷ xs) ++ ys = x ∷ xs ++ ys

--   map : ∀ {ℓ'} {B : Set ℓ'} → (A → B) → List A → List B
--   map f [] = []
--   map f (x ∷ xs) = f x ∷ map f xs

--   module _ {B : Set ℓ} where
--     foldr : (A → B → B) → B → List A → B
--     foldr c n []       = n
--     foldr c n (x ∷ xs) = c x (foldr c n xs)

--     foldl : (A → B → A) → A → List B → A
--     foldl c n []       = n
--     foldl c n (x ∷ xs) = foldl c (c n x) xs

--     concat : List (List A) → List A
--       concat = {!foldr!} -- foldr _++_ []

Square :
  {a₀₀ a₀₁ : A} (a₀₋ : a₀₀ ≡ a₀₁)
  {a₁₀ a₁₁ : A} (a₁₋ : a₁₀ ≡ a₁₁)
  (a₋₀ : a₀₀ ≡ a₁₀) (a₋₁ : a₀₁ ≡ a₁₁)
  → Set _
Square a₀₋ a₁₋ a₋₀ a₋₁ = PathP (λ i → a₋₀ i ≡ a₋₁ i) a₀₋ a₁₋


data Interval : Set where
  zero one : Interval
  seg  : zero ≡ one


Pointed : (ℓ : Level) → Set (ℓ-suc ℓ)
Pointed ℓ = Σ (Set ℓ) λ A → A

Ω : {ℓ : Level} → Pointed ℓ → Pointed ℓ
Ω (_ , a) = ((a ≡ a) , refl)
