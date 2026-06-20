**Q1**
Let `hI,hP,hA,cI,cP : ℕ∞` denote `height_R I`, `height_R P`, `height_A p`, `coheight_R I`, `coheight_R P`.
`have hrel : hA + cP = cI := WithTop.add_left_cancel hI_ne_top <| by`
`  calc hI + (hA + cP) = (hI + hA) + cP := by rw [add_assoc]`
`    _ = hP + cP := by rw [← hsplit]`
`    _ = n := E_P`
`    _ = hI + cI := E_I.symm`
Then coerce `hrel` to `WithBot ℕ∞` and rewrite by `dim(A⧸p)=cP`, `dim A=cI`.
Cancellation lemma: `WithTop.add_left_cancel (hx : x ≠ ⊤)`; get `hI_ne_top` from `E_I` and finite RHS `(n : ℕ∞) < ⊤`.

**Q2**
Verified names: `Order.height_orderIso`, `Order.coheight_orderIso`, `Order.height_eq_krullDim_Iic`, `Order.coheight_eq_krullDim_Ici`, `Order.krullDim_eq_of_orderIso`.
Your `primeSpectrumQuotientOrderIsoIci` is the right transport tool for `height_A p = height (⟨P,hIP⟩ : Set.Ici I)`.
Likely absent: a packaged quotient split `height_R P = height_R I + height_{R/I} p`.
Exact but probably not directly this: `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`.
Minimal hand-proof via order iso only proves relative-height transport; proving the additive split needs a real upper bound on arbitrary chains below `P`.

**Q3**
`(**)` is not tautological in a general poset.
Order-iso gives only `height_A(p) = height_{Set.Ici I}(P)`, i.e. chains from `I` upward to `P`.
But `height_R(P)` counts all chains below `P`; they need not pass through `I`.
Concatenation gives the easy inequality `height_R(I)+height_A(p) ≤ height_R(P)`.
The reverse inequality is exactly where catenary/equidimensional content enters.
With `E_I` and `E_P`, `(**)` is essentially equivalent to the target after finite cancellation.

**Q4**
Yes: with `[m.IsMaximal]`, no Jacobson/Nullstellensatz is needed.
Use `Ideal.Quotient.field m` to get `Field (A ⧸ m)`, then exact `ringKrullDim_eq_zero_of_field (A ⧸ m)`.
Maximal implies prime via exact `Ideal.IsMaximal.isPrime` / instance `Ideal.IsMaximal.isPrime'`.
Then the headline gives `m.height + 0 = ringKrullDim A`, hence `m.height = ringKrullDim A`.
For localization use exact `IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)`.
`inferInstance` should supply `IsLocalization.AtPrime (Localization.AtPrime m) m`.

Recommendation: use Route Q, not Route N; the riskiest step is the additive height split upper bound, because it is catenary content, not mere quotient-order transport.