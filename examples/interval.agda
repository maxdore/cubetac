Prelude.Interval.zero : Interval
Prelude.Interval.one : Interval
Prelude.Interval.seg : zero ≡ one
---
PathP (λ i → PathP (λ z → Interval) zero one) seg seg
