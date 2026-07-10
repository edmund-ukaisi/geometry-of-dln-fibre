**Q1**

CORRECT.

Your determination follows from the stated carrier rule: `rowMix` needs support-homogeneity `hsh`, and after starting with `supp ≡ 0`, `radialStep` prepends a fully shared divisor, so the block remains fresh/common-support when Schur elimination fires. Thus an arbitrary Schur matrix such as `A⁻¹B` is legal there because “arbitrary” is only arbitrary inside one support class. A non-fresh arbitrary `rowMix` would violate the carrier invariant and is not a separate target for this peel design. Inference: if later descents split supports, the obligation is to prove the next elimination is again localized to a fresh support block, not to generalize `rowMix`.

Sharpest possible missing point: variable-dependent Schur coefficients/Jacobian bookkeeping, not non-fresh `hsh`.

**Q2**

Pick **hybrid leaning (a)**: reuse `gammaPeelIntegral_schurShearFree_eq` and the FreedPeel inner branches for the actual matrix-box CoV, then use the decorated carrier only to prove the outer descent/exact monomial factorization. A fully carrier-native measure CoV would mostly reprove the risky analytic CoV and still face the same monomial/Jacobian obligation. The Regime-A/B pointwise branches alone do not dodge the binding issue; the dodge, if valid, is the exact pullback identity on the outer decorated parameters. The shared-divisor absorption works because, on a fresh block, every generator has the same monomial factor `m`, Schur `rowMix` stays within that support class, and `blockSplit` makes the loss an exact additive split after pulling out `m²`. Then the CoV Jacobian and radial monomial are integrated directly by Fubini, while the reduced-chain loss appears with exponent `c' - peelCharge/2 < minAdm(redChain t M)/2`; no Hölder exponent `p > 1` is introduced. This is precisely what avoids the binding-cut saturation.

Exact-factoring route: **YES, conditionally as math; UNPROVEN from the banked list alone.**  
The one load-bearing sub-lemma is the fresh-block radial Schur factorization with Jacobian: after `radialStep + rowMix + blockSplit`, the pulled-back decorated loss and measure factor exactly as a monomial radial factor times the reduced decorated loss, with no inequality or Hölder split.

Cheapest discriminating check: take `M = (2,2,1)`, pivot `t=1`, `p ≠ 0`, and set tail entries `q_p = u x`, `q_b = u y`; verify directly that  
`freedSchurLoss = u² * [(p*(x + p⁻¹ B*y))² + (C*(x + p⁻¹ B*y) + Γ*y)²]`  
and that the radial Jacobian gives the expected integrability threshold `c' < 1`.