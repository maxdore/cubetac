zero : Interval
one : Interval
seg : zero ≡ one
---
PathP (λ i → PathP (λ z → Interval) (seg i) (seg i)) (λ z → zero)
(λ z → one)
