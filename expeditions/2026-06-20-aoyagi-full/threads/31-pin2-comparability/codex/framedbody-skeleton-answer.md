**1. SOUNDNESS FIX**

Confirmed: the cert is under-hypothesized. For bare `Pf Qf J`, the intended `P0, QL` are not guaranteed to be units, the base corner need not normalize to `fromBlocks 1 0 0 0`, and the `P00` invertible germ can fail.

Add/thread the seven frame facts from `deepestPoint_frame_pivot_exists`:

```lean
(hPunit : ∀ s, IsUnit (Pf s))
(hQunit : ∀ s, IsUnit (Qf s))
(hQf0 : Qf firstLayer = 1)
(hPfL : Pf lastLayer = 1)
(hframe :
  ∀ s, (s : ℕ) + 1 ≠ L →
    Pf s * deepestPoint H r B ... s * Qf s = corM ...)
(hQ22unit : IsUnit ((Qf lastLayer).toBlocks₂₂ ...))
(hcorner :
  reindex ... ... (deepestPoint H r B ... lastLayer * Qf lastLayer)
    = Matrix.fromBlocks 1 0 0 0)
```

Load-bearing map:

- `P0`/`QL` units: `hPunit`, `hQunit`, via S2 endpoint/telescope identification.
- `Pi * P0 = 1`, `QL * Qi = 1`, positive Frobenius norms: same unit facts, plus existing nonzero-dimension/rank hypotheses.
- S2 interface/telescope: `hQf0`, `hPfL`, or the derived `hinterface` expected by `endpoint_telescoping`.
- corner normalization: `hframe + hQf0 + hPfL + hcorner`.
- `P00` invertible on a germ: `hcorner` through S3b, then determinant continuity.
- core/Schur comparability: `hQ22unit` is load-bearing for S5c/core absorption, not for the basic `P0` unit issue.

**2. SKELETON SHAPE**

Use local abbreviations, then keep every S-atom quantified over the same block witnesses.

```lean
let w0 := paramsEquivFlat (deepestPoint H r B ...)
let A  := fun w => paramsEquivFlat.symm w
let F  := fun w => framedParams H r hr hL J Pf Qf (split w)

have hS1 :
  ∀ w (s : Fin L), (s : ℕ) + 1 ≠ L →
    F w s = Pf s * A w s * Qf s := by
  sorry

have hS1' :
  ∀ w,
    F w lastLayer = Pf lastLayer * A w lastLayer * Qf lastLayer := by
  sorry

have hS2 :
  ∃ P0 QL,
    (∀ w, prod H (F w) = P0 * prod H (A w) * QL) ∧
    IsUnit P0 ∧ IsUnit QL := by
  sorry

rcases hS2 with ⟨P0, QL, hprodF, hP0unit, hQLunit⟩

let Hconj := fun w P00 P01 P10 P11 =>
  reindex ... ... (P0 * (prod H (A w) - B) * QL)
    = Matrix.fromBlocks (P00 - 1) P01 P10 P11

let Sreg := fun P00 P01 P10 =>
  (∑ i, ∑ j, ((P00 - 1) i j)^2)
  + (∑ i, ∑ j, (P01 i j)^2)
  + (∑ i, ∑ j, (P10 i j)^2)

have hS3b :
  reindex ... ... (P0 * B * QL)
    = Matrix.fromBlocks 1 0 0 0 := by
  sorry

have hS4 :
  ∀ w P00 P01 P10 P11,
    Hconj w P00 P01 P10 P11 →
    (∑ i, (deepestEFull H r hr hL J Pf Qf (split w) i)^2)
      = Sreg P00 P01 P10 := by
  sorry

have hS5a :
  ∃ Udet ∈ 𝓝 w0, ∀ w ∈ Udet,
    ∃ P00 P01 P10 P11 (_ : Invertible P00),
      Hconj w P00 P01 P10 P11 := by
  sorry

have hS5b :
  ∃ t : ℝ, ∃ Uleak ∈ 𝓝 w0, ∀ w ∈ Uleak,
    ∀ P00 P01 P10 P11 (hI : Invertible P00),
      Hconj w P00 P01 P10 P11 →
      letI := hI
      ∑ i, ∑ j, ((P10 * ⅟ P00 * P01) i j)^2
        ≤ t^2 * Sreg P00 P01 P10 := by
  sorry

have hS5c :
  ∃ γ₁ : ℝ, 0 < γ₁ ∧ ∃ γ₂ : ℝ, 0 < γ₂ ∧
  ∃ Ucmp ∈ 𝓝 w0, ∀ w ∈ Ucmp,
    ∀ P00 P01 P10 P11 (hI : Invertible P00),
      Hconj w P00 P01 P10 P11 →
      letI := hI
      (∑ i, ∑ j, ((P11 - P10 * ⅟ P00 * P01) i j)^2
        ≤ γ₂ * deepestCoreF H r (deepestCoreAbsorb ... (split w)).2.1) ∧
      (deepestCoreF H r (deepestCoreAbsorb ... (split w)).2.1
        ≤ γ₁ * ∑ i, ∑ j,
          ((P11 - P10 * ⅟ P00 * P01) i j)^2) := by
  sorry
```

Assembly order: `S1`, `S1'`, combine to all-layer frame equality, `S2`, destruct `P0 QL`, prove `S3b`, then `S4`, `S5a`, `S5b`, `S5c`, then `refine ⟨P0, QL, Pi, Qi, t, γ₁, γ₂, ...⟩`.

Hazards: state `hcorner`/`hQ22unit` using the cert’s final `J`, not raw `Jb`; convert the `Jb.trans (finCongr ...)` once at the caller. Last-layer `lastLayer.succ = Fin.last L` and `pivotJSucc` are likely cast-sensitive. Also insert `letI := hI` before every `⅟ P00`.

**3. FILL ORDER & RISK**

Fillable now / banked assembly:

1. `S2`: endpoint telescope once S1/S1' provide the layer equality.
2. `S3b`: telescope at `w0` plus `hframe`, boundary facts, `hcorner`.
3. `S1`: banked non-last round-trip.
4. `S4`: copy the `deepestEPivot_sq_sum_eq_blocks` pattern for `deepestEFull`.
5. `S5b`: estimate assembly from `leak_frobenius_bound`, `frobenius_mul_le`, comparability atoms.

Medium Lean work, not new math:

6. `S5a`: determinant-open neighborhood and block extraction.
7. `S1'`: new pivot-column decode variant, mechanical but cast/case heavy.

Leave named `sorry` for now:

8. `S5c`: genuinely new germ comparability atom; not just assembly until written.

**4. THE NEIGHBORHOOD U**

Cleanest: make `S5a`, `S5b`, `S5c` each return a set in `𝓝 w0`, then use

```lean
let U := Udet ∩ Uleak ∩ Ucmp
```

and prove `U ∈ 𝓝 w0` by finite-intersection filter facts, lemma names INFERENCE. For `w ∈ U`, project membership into the three neighborhoods and use the same `P00 P01 P10 P11` from `S5a` for `S4/S5b/S5c`.

No conceptual continuity obstruction. Define `P00(w)` as the top-left block of

```lean
reindex ... ... (P0 * prod H (A w) * QL)
```

rather than through `prod (F w)` if possible. Then entries are finite polynomial expressions in `w` after `paramsEquivFlat.symm`; determinant is continuous. The Lean work is proving/using those continuity facts, not geometry.