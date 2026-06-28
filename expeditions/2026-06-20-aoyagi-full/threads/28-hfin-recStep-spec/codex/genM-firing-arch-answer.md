**Q1.** PASS. The split `r=0 / r=1 / r=2 / r≥3` is exhaustive, and the arithmetic checks for `schurLambda`. `r=2` should use `core_schur2_lt_top`; your subcritical fallback to exponent `3` would require `3 < lam 2 = 2`, false. For `r≥3`, `3 < lam r = 2r−2` holds, including `r=3`, and mid-case `c''=c'−2` lands in `(0, lam(r−1))`.

**Q2.** Confirmed, modulo pivot alignment. In the `j=1` normalized chart, `M11 = [1]`, so `M11⁻¹ = [1]` exactly and there is no determinant/inversion subtlety. Since angular entries satisfy `|R_ab|≤1`, each Schur shift entry is `M21_a * M12_b`, hence bounded by `1`. Use a common IH box radius like `T'' = max 2 T` or `max (1+B) T`; if `T+B` refers to original `S` radius with small `T`, it may not contain `Sc`.

**Q3.** The disjointness pattern generalises. After writing `R = [[1,u],[v,W]]` and splitting `S=(S0,Sbot)`, the top row is `S0 + u*Sbot`, while the residual is `(W-vu)*Sbot`, depending only on `Sbot`. The shear in `S0` makes the Morse variables independent of the residual, up to a translated/enlarged `S0` box with radius bounded by about `r*T`. One caveat: your listed `radial_morse_residual_power_le` assumes `0<w`; you need the same a.e.-zero-residual/null-set wrapper used in corank 3, or derive it from the IH core. I am marking that wrapper as INFERRED, not listed.

**Q4.** Confirmed: dropping the top block loses the required `p/2 = 2` gain. The shortcut would require applying IH at exponent `c'`, hence `c' < lam(r−1) = 2r−4`, which fails on the upper part of the target range `c' < lam r = 2r−2`. It may prove a smaller range, but not the recursion step. The shifted Morse peel is load-bearing.

**Q5.** Top risk 1: generic pivot alignment/cell discharge after flattening and chart choice. Mitigation: prove one INFERRED helper that turns any chart pivot into the `j=1` Schur cell hypotheses, including row/column permutations and `S` row permutation.

Top risk 2: dependent `Fin (r*r)`/`Fin r × Fin r`/`piFinSuccAbove` cast arithmetic around chart cardinality and exponent `r²−1`. Mitigation: isolate the radial chart assembly into small INFERRED lemmas before touching the analytic proof body.

VERDICT: REACHABLE-PLUMBING