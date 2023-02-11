zero : Interval
one : Interval
seg : zero ≡ one
---
PathP (λ i → PathP (λ z → Interval) (seg (i ∨ i)) (seg (i ∧ j))) (λ z → zero)
(λ z → one)
