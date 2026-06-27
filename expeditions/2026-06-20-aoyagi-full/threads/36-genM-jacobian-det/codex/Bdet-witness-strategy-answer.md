**Q1.**  
No: `∃ B : GenBlk M t, VvalGen u M t B hle > 0` alone does not prove a.e.-positivity of `x ↦ VvalGen (x p) M t (DECODER x) hle`. The decoder composition could land entirely inside the zero locus even if the abstract `GenBlk` space has nonzero points. It helps only if you also prove `∃ w, DECODER w = B_witness` or, more practically, prove the witness properties directly for `DECODER w`. For the `MvPolynomial.ae_eval_ne_zero` route, the nonzero evaluation must be at a point in the flat `x`-space. So use the special `B` argument only as a local abstraction layer, then instantiate it with a genuine flat witness `w`.

**Q2.**  
Use scalar-carry, not a full matrix identity. A matrix identity forces you to define a dependent product of `Bmat_s · ... · Bmat_{L-1}` across opaque `Text` widths, then fight associativity/casts; scalar-carry only opens `Matrix.mul_apply` at row `0`, column `0`. The minimal structural condition is: every coupling term vanishes, the live leaf has `(0,0)=1`, and in Lean’s row convention the `0`-th row of each `Bmat s` is `e₀ᵀ` (or `b_s e₀ᵀ` if you want the product form). This is row-0, not column-0, for the recurrence `H_s = B_s * H_{s+1}`.

```lean
-- c := (chainOfMt u M t (DECODER w) hle).toChain
lemma Hmat00_witness
    (hTpos : ∀ s, s ≤ L → 0 < c.Twid s)
    (hWpos : 0 < c.Wwid L)
    (hEzero : ∀ s (hs : s < L), c.E s = 0)
    (hBrow0 : ∀ s (hs : s < L) (j : Fin (c.Twid (s+1))),
      c.B s ⟨0, hTpos s (le_of_lt hs)⟩ j =
        if j = ⟨0, hTpos (s+1) hs⟩ then 1 else 0)
    (hR00 : c.R ⟨0, hTpos L (le_rfl)⟩ ⟨0, hWpos⟩ = 1) :
    c.Hmat 0 (Nat.zero_le L)
      ⟨0, hTpos 0 (Nat.zero_le L)⟩ ⟨0, hWpos⟩ = 1 := by
  -- Induct on d with s + d = L.
  -- Base: `Chain.Hmat_last`, use `hR00`.
  -- Step: rewrite by `Chain.Hmat_succ`; use `hEzero` to drop `E*suffix`;
  -- expand `(B_s * H_{s+1}) 0 0` and `Finset.sum_eq_single 0` using `hBrow0`.
```

**Q3.**  
The product-side route does not really avoid `Hmat`. The banked identity `prod = u • HrGen` already goes through `Hmat`, and proving positivity by direct evaluation of `prod M (chartParamsGen ...)` reopens the length-`L` product over opaque `Wext` widths. It is at least the same cast burden, and usually worse, because `Agen` contains `chainA`, `Cgen`, `Nblk`, and `Wblk` rather than the stripped recurrence `H_s = B_s H_{s+1} + E_s suffix`. Dividing by `u` also introduces an avoidable `u ≠ 0` side condition. So yes: same mathematical difficulty, worse Lean surface.

**Q4.**  
Known in this repo at the v4.29 pin: the reliable zero-set-nullity tool is `MvPolynomial.ae_eval_ne_zero`, from `DLNFibre.Core.MeasureTheory.PolynomialZeroSet`, and it requires a named `MvPolynomial`. Known Mathlib v4.29 analytic API includes one-variable isolated-zero/identity-theorem style lemmas such as `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` and `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`; these are not a finite-dimensional Lebesgue-null zero-set theorem. Inference from local API search: Mathlib v4.29 does not appear to have an off-the-shelf theorem “nonzero real-analytic `f : ℝ^n → ℝ` has null zero set” usable without naming a polynomial. The identity theorem is not enough in several real variables anyway: nonzero analytic functions may vanish on hypersurfaces with accumulation points. So for this build, expect to define a polynomial-valued decoder/`UPolyGen` or equivalent named `MvPolynomial`, prove `eval w UPolyGen = Ufun w`, and use `ae_eval_ne_zero`.

**Recommended Path.**  
Use Q2’s scalar `Hmat00_witness` lemma, instantiate it at a genuine flat witness `w` for the live-leaf decoder, then use that evaluation to prove the named `UPolyGen ≠ 0` and finish Ubound via `MvPolynomial.ae_eval_ne_zero` plus `ae_restrict_of_ae`. The biggest dependent-width risk is not the induction itself; it is making the zero indices `0 : Fin (Text M t s)` and `0 : Fin (Wext M L)` available uniformly, then aligning those same indices through `HrGen`’s final `Matrix.reindex`.