Prelude.Sphere.a : Sphere
Prelude.Sphere.surf : PathP (λ i → a ≡ a) (λ z → a) (λ z → a)
---
PathP
(λ i →
PathP
(λ j →
PathP
(λ k →
PathP
(λ l →
                  PathP (λ z → Sphere) (surf (i ∧ j ∧ k ∧ l) (i ∨ j ∨ k ∨ l)) a)
                (λ l → a) (λ l → a))
          (λ l k → a) (λ l k → a))
      (λ l k j → a) (λ l k j → a))
(λ l k j i → a) (λ l k j i → a)
