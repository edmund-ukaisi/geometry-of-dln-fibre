**CARRIER**

Use `EuclideanSpace ℝ (Fin C)` for the radial analysis, then transport back to `Fin C → ℝ`.

Names:
- `EuclideanSpace.norm_eq` [confident] or `EuclideanSpace.real_norm_sq_eq` [confident]: prove `∑ i, x i ^ 2 = ‖x‖ ^ 2`.
- `EuclideanSpace.equiv (Fin C) ℝ` `.toHomeomorph.symm` [confident from repo use]: homeomorphism `Fin C → ℝ ≃ₜ EuclideanSpace ℝ (Fin C)`.
- `PiLp.volume_preserving_toLp (Fin C)` [confident from repo use]: `MeasurePreserving` for the Pi-to-`EuclideanSpace` map.
- `MeasurePreserving.integrableOn_comp_preimage` / `MeasurePreserving.integrableOn_image` [confident]: transport `IntegrableOn`.

Do not use the default norm on `Fin C → ℝ`; it is the sup norm. Treat `WithLp.toLp 2`/`EuclideanSpace.equiv` as the bridge.

**LOCAL-vs-GLOBAL**

Ranking:

1. **(a), if available in your v4.29 checkout:** `MeasureTheory.integrableOn_fun_norm_addHaar` [guess for pin — verify]. Public Mathlib docs list the ball-local version:
   `IntegrableOn (fun x => f ‖x‖) (Metric.ball 0 r) μ ↔ IntegrableOn (fun y => y^(finrank ℝ E - 1) • f y) (Set.Ioo 0 r) volume`. This directly avoids cutoff bookkeeping. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/HaarToSphere.html))
2. **(b), safest in this repo:** the repo already has `DLNFibre.DLN.RLCT.radial_ball_iff` [confident local], built by cutoff + `MeasureTheory.integrable_fun_norm_addHaar` [confident] + `intervalIntegral.integrableOn_Ioo_rpow_iff` [confident]. Use/import that if possible.
3. **(c)** direct proof without polar/cutoff is highest friction.

Winner lemma chain if using the repo-proven route:
- `radial_ball_iff` [confident local]:  
  `IntegrableOn (fun x : EuclideanSpace ℝ (Fin (m+1)) => ‖x‖ ^ s) (ball 0 R) volume ↔ -(m+1 : ℝ) < s`.
- Apply with `s = -(2*c)` and `C = m+1`.
- `EuclideanSpace.norm_eq` + `Real.sq_sqrt` + `Real.rpow_natCast` + `Real.rpow_mul` [confident]: rewrite `(∑ i, x i^2)^(-c)` as `‖x‖^(-(2*c))`.
- `PiLp.volume_preserving_toLp` + `MeasurePreserving.integrableOn_comp_preimage`/`integrableOn_image` [confident]: bridge back to `Fin C → ℝ`.
- `mem_nhds_iff`, `Metric.isOpen_iff` or `isOpen_ball.mem_nhds`, `IntegrableOn.mono_set` [confident]: pass between “some neighbourhood” and a small ball.

**SSUP ENDGAME**

Use:
```lean
have hb : (0 : ℝ) < b := ...
show sSup {c : ℝ | 0 ≤ c ∧ c < b} = b
rw [show {c : ℝ | 0 ≤ c ∧ c < b} = Set.Ico 0 b by ext c; rfl]
exact csSup_Ico hb
```

`csSup_Ico` [confident] is exactly `sSup (Set.Ico a b) = b` from `a < b`; no manual `BddAbove` needed. ([leanprover-community.github.io](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/ConditionallyCompleteLattice/Basic.html))

If you go manual: `csSup_eq_of_forall_le_of_forall_lt_exists_gt` [confident], or `csSup_le`/`le_csSup` [confident]; `BddAbove` witness is `⟨b, by rintro x ⟨_, hx⟩; exact le_of_lt hx⟩`.

**TRAPS**

- `Real.rpow` has `0^negative = 0`, not `∞`. Divergence must come from the punctured neighbourhood/radial theorem, not the value at `0`.
- Avoid the `C = 0` corner. From `1 ≤ C`, reduce to `C = m+1`; this also avoids `finrank - 1` Nat-subtraction pain and satisfies `[Nontrivial E]`.
- Transport neighbourhoods through the homeomorphism, not by pretending Pi and Euclidean norms are defeq.
- For the final theorem, exact characterization is fine, but RLCT equality only needs: every `c < C/2` admissible and every admissible `c ≤ C/2`. The boundary nonintegrability is mathematically true but not necessary for `sSup`.