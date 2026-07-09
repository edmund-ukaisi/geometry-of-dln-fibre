# Red-team: is the ≤-half extraction of an RLCT-cover equality genuinely gate-free?

You are an adversarial reviewer of a Lean 4 / Mathlib formalisation. I need a
decorrelated second opinion on a SOUNDNESS question. Do not be polite; hunt for
the flaw. Answer the two questions explicitly at the end.

## Setup

There is a proven "cover bridge" equality in the repo:

```lean
structure IsRouteMCover {N} (F : (Fin N → ℝ) → ℝ) (U : Set (Fin N → ℝ))
    (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ) : Prop where
  Fmeas : Measurable F
  Uopen : IsOpen U
  Umem  : (0 : Fin N → ℝ) ∈ U
  -- (finiteness field) below-threshold: ∫_U |F|^{-c'} ≤ C(c') · Σᵢ ∫ monomialᵢ
  cover_le : ∀ c' : NNReal, ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∫⁻ x in U, ENNReal.ofReal (|F x| ^ (-(c':ℝ)))
        ≤ C * ∑ i, ∫⁻ y in unitBox (d i), ENNReal.ofReal (monomialIntegrand (d i) (k i) (h i) c' y)
  -- (divergence field) at-or-above some leaf threshold, |F|^{-c'} not integrable on any open Ω∋0
  cover_ge_div : ∀ c' : NNReal, (∃ i, monomialThreshold (d i) (k i) (h i) ≤ (c':ℝ≥0∞)) →
      ∀ Ω, IsOpen Ω → (0:Fin N→ℝ) ∈ Ω →
        ¬ IntegrableOn (fun x => |F x| ^ (-(c':ℝ)) * (fun _ => (1:ℝ)) x) Ω volume

theorem routeM_rlctAtOn_eq_iInf {N} (F) (U) (ι) [Fintype ι] [Nonempty ι] (d k h)
    (hcover : IsRouteMCover F U ι d k h) :
    rlctAtOn F 0 = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
  refine le_antisymm ?_ ?_
  · -- (≤) branch: uses ONLY hcover.cover_ge_div
    apply rlctAtOn_le_of_adm_le F _
    intro c' hadm; by_contra hgt; rw [not_le] at hgt
    obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt hgt
    obtain ⟨Ω, hΩopen, h0Ω, hint⟩ := hadm
    exact hcover.cover_ge_div c' ⟨i, hi.le⟩ Ω hΩopen h0Ω hint
  · -- (≥) branch: uses hcover.cover_le + hcover.Fmeas/Uopen/Umem + Σ finiteness (needs Fintype)
    ...
```

The new module extracts the (≤) branch as a standalone lemma that consumes ONLY the
`cover_ge_div` payload, drops `U`, drops `[Fintype ι]`, keeps `[Nonempty ι]`:

```lean
theorem routeM_rlctAtOn_le_iInf {N} (F : (Fin N → ℝ) → ℝ)
    (ι : Type) [Nonempty ι] (d : ι → ℕ) (k h : (i : ι) → Fin (d i) → ℕ)
    (hge : ∀ c' : NNReal, (∃ i, monomialThreshold (d i) (k i) (h i) ≤ (c':ℝ≥0∞)) →
        ∀ Ω, IsOpen Ω → (0:Fin N→ℝ) ∈ Ω →
          ¬ IntegrableOn (fun x => |F x| ^ (-(c':ℝ)) * (fun _ => (1:ℝ)) x) Ω volume) :
    rlctAtOn F 0 ≤ ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := by
  apply rlctAtOn_le_of_adm_le F _
  intro c' hadm; by_contra hgt; rw [not_le] at hgt
  obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt hgt
  obtain ⟨Ω, hΩopen, h0Ω, hint⟩ := hadm
  exact hge c' ⟨i, hi.le⟩ Ω hΩopen h0Ω hint
```

Then a downstream result `r1_resolution_general_le` (an RLCT upper bound for a DLN
"reduced core" loss) is built by:
1. constructing the divergence payload `hdiv` from an achiever box-divergence theorem
   `routeMCore_box_diverges_achiever_full'` (which requires only `1 ≤ minAdm M`,
   positive widths, deepest-block nonempty — NOT any box-finiteness hypothesis);
2. converting `hdiv` to the `cover_ge_div` shape via a converter
   `routeM_coverGeDiv_of_boxDiverges`;
3. feeding `routeM_rlctAtOn_le_iInf`;
4. transporting and valuing `⨅ monomialThreshold = ofReal(lambdaCore M)`.

The claim is that `r1_resolution_general_le` is `hbox`-free (`hbox` =
`RouteMBoxThresholdFinite M`, a box-FINITENESS analytic gate), whereas the full
equality `r1_resolution_general` needs `hbox` (it feeds the `≥`/finiteness lane
through `cover_le`).

## Questions (answer each explicitly)

**Q3.** Is the `≤` direction genuinely independent of the box-finiteness gate? I.e.,
is it structurally the case that `rlctAtOn F 0 ≤ ⨅ threshold` follows from divergence
ALONE, with finiteness (`cover_le`) needed only for the reverse `≥`? Give the
mathematical reason (what `rlctAtOn` is, and why "the integral diverges for every c'
at-or-above a leaf threshold" forces the local RLCT to be ≤ that threshold infimum),
and confirm there is no hidden place where the upper bound secretly needs finiteness.
Any way the extraction could be vacuously true (e.g. if `rlctAtOn` is defined so the
`≤` always holds, or `⨅` over an empty/degenerate index)?

**Q4.** Is dropping `[Fintype ι]` (keeping `[Nonempty ι]`) sound for the `≤` branch?
The `≥` branch used a finite sum `Σ i : ι`. The `≤` branch uses `exists_lt_of_ciInf_lt`
on `⨅ i : ι, monomialThreshold …` in `ℝ≥0∞`. Does `exists_lt_of_ciInf_lt` need only
`[Nonempty ι]` (conditionally-complete-lattice iInf) and not `[Fintype ι]`? Could
dropping `Fintype` change the MEANING of `⨅ i : ι, …` (e.g. junk value) in a way that
makes the lemma weaker/stronger than the branch it claims to lift? Is the conclusion
still the intended object?

Keep it tight. Flag any INFERENCE vs. FACT distinctions in your own reasoning.
