<task>
Lean 4 + Mathlib v4.29. Design-review the GENERIC `zEG` carving + the `Sc = M22 − Sh(rest)` readback —
the hardest sub-step of a corank-r matrix-integral firing. I have a VALIDATED corank-3 template
(`zσ`/`zE`/`bgShift`/`matOf`/`Δof_eq_zE`); I need the cleanest generic-r shape BEFORE I sink ~150 bespoke
lines. Be concrete + skeptical; flag any genuine design gap (vs surface cast-friction).

## The corank-3 template (VALIDATED, what I generalize)
For r=3, the angular matrix R' (pivot-normalized to (0,0), so R'(0,0)=1, |entries|≤1) has its 8 non-pivot
entries indexed by the ratio vector z : Fin 8 → ℝ. The Schur complement (j=1, M11=[1]) is the 2×2
`Sc = M22 − M21·M12` where M22 = R'-cells {1,2}×{1,2}, M21 = {1,2}×{0} (a col), M12 = {0}×{1,2} (a row).
The corank-3 carving:
- `zσ p : Fin 8 ≃ (Fin 2 × Fin 2) ⊕ Fin 4` — a bijection carving the 8 ratios into the M22-block coords
  (Fin 2 × Fin 2, the inl) ⊕ the "bg" coords (Fin 4 = the 2 M21-entries g0,g1 ++ the 2 M12-entries b0,b1).
- `zE p : (Fin 8 → ℝ) ≃ᵐ ((Fin 2 × Fin 2 → ℝ) × (Fin 4 → ℝ))` :=
    `(MeasurableEquiv.piCongrLeft _ (zσ p)).trans (MeasurableEquiv.sumPiEquivProdPi _)`  (MP for volume).
- `bgShift (v : Fin 4 → ℝ) : Matrix (Fin 2)(Fin 2) ℝ := !![v0·v2, v0·v3; v1·v2, v1·v3]` (the rank-1
  outer product g·bᵀ with g=(v0,v1), b=(v2,v3)).
- `matOf (M : Fin 2 × Fin 2 → ℝ) := fun i k => M (i,k)`.
- `Δof_eq_zE : Sc(z) = matOf((zE z).1) − bgShift((zE z).2)`  (the readback — the de-shift d = raw − g·bᵀ),
  proven entrywise via a per-cell readback `Rmat334norm_eq_zslot : R'(c) = z (zslot c)` for c≠(0,0).
Then the chart consumes it: ∫_z f(Sc(z)) = ∫_{(M22,bg)} f(matOf M22 − bgShift bg), Tonelli the bg-cube
OUTERMOST, per fixed bg the M22↦Sc is a translation (by bgShift bg, |entries|≤1), box-enlarge + the IH-core.

## The generic-r target
After pivot-WLOG, R' : Fin r → Fin r → ℝ, R'(0,0)=1, |entries|≤1. The r²−1 non-pivot ratios carve into:
- M22 = R'-cells {1..r-1}×{1..r-1}  →  (r-1)² coords, indexed by Fin (r-1) × Fin (r-1) (via (a,b)↦(a.succ,b.succ));
- M21 = R'-cells {1..r-1}×{0}  →  (r-1) coords (the g-vector);
- M12 = R'-cells {0}×{1..r-1}  →  (r-1) coords (the b-vector).
So r²−1 = (r-1)² + 2(r-1). The Schur complement Sc = M22 − M21·M12 = M22 − g·bᵀ (M11=[1]), i.e.
`Sc(a,b) = M22(a,b) − g(a)·b(b)`. I want the generic analog:
- `zσG : (non-pivot-cell index) ≃ (Fin (r-1) × Fin (r-1)) ⊕ (Fin (r-1) ⊕ Fin (r-1))`  (M22 ⊕ (g ++ b));
- `zEG : (ratios → ℝ) ≃ᵐ ((Fin(r-1)×Fin(r-1) → ℝ) × ((Fin(r-1) → ℝ) × (Fin(r-1) → ℝ)))` via piCongrLeft+sumPiEquivProdPi;
- `bgShiftG (g b : Fin(r-1) → ℝ) : Matrix := fun a b' => g a * b b'`  (the generic outer product);
- `ScG_eq : Sc(z) = matOfG((zEG z).1) − bgShiftG (g-part) (b-part)`.

## QUESTIONS (answer each ≤7 sentences)
Q1. Is the generic `zσG` index bijection the bulk of the work, and what is the LOWEST-friction way to build
    it at v4.29? Options: (a) carve directly on the cell-subtype `{ij : Fin r × Fin r // ij ≠ pivot}` with
    an explicit `(Fin(r-1)×Fin(r-1)) ⊕ Fin(r-1) ⊕ Fin(r-1) ≃ {non-pivot cells}` built from `Fin.succ` /
    `finSumFinEquiv`; (b) carve on `Fin N` (N=r²-1) via the `piRatioG` off-pivot decoder I already have
    (`piRatioG_apply_snd : (piRatioG y).2 j = y(decoded j)`, decoded ≠ pivot). Which keeps the readback
    `Rmat-cell = ratio-coord` cleanest — (a) the subtype, or (b) the Fin N decoder?
Q2. The readback `ScG_eq : Sc(z) = matOfG(M22-part) − bgShiftG(g)(b)` — corank-3 proves it entrywise via a
    per-cell `R'(c) = z(zslot c)`. Generically, is the cleanest route to prove, for each cell-class
    (M22/M21/M12), a `zσG`-readback `R'(cell) = (zEG z).<part> (carved-index)` and then assemble Sc
    entrywise? Or is there a slicker matrix-level identity? Flag the `Fin.succ`/`Fin.succAbove` cast-friction
    risk in the entrywise readback (the cells {1..r-1} = `Fin.succ '' (Fin (r-1))`).
Q3. The N2b split gives `Sc = M22 − M21·M11⁻¹·M12` with M11 the 1×1 [R'(0,0)] = [1]. Confirm M11⁻¹ = [1]
    EXACTLY (not just det=1) so `Sc = M22 − M21·M12` with NO inversion subtlety, and that `M21·M12` (an
    (r-1)×1 times 1×(r-1)) is exactly the outer product `fun a b => M21(a,0)·M12(0,b) = g(a)·b(b)`. Any
    Mathlib friction in `Matrix.inv` of a 1×1 = identity, or should I avoid `Matrix.inv` and use the N2b
    lemma's EXPLICIT Sc-formula directly (it states Sc = M22 − M21·(M11)⁻¹·M12 as a raw expression)?
Q4. Is there a GENUINE design gap in the generic carving (vs corank-3), or is it pure volume +
    cast-bookkeeping? Specifically: does the per-cell readback or the Sc-entrywise assembly hit anything
    that does NOT generalize from r=3 (e.g. the bgShift outer-product structure, the M22-cell indexing, the
    Tonelli-bg-outermost + per-fixed-bg-translation)? Give a yes/no + the smallest sharp statement of any gap.
Q5. Rank the top 2 Lean-friction risks + a one-line mitigation each.
</task>
<output_contract>
Answer Q1–Q5 in order. For Q1 name (a) or (b). For Q4 give yes/no + (if yes) the sharp gap statement. End
with one line: "GENERIC-zEG: <PURE-VOLUME | GAP-AT-<step>>" and "CARVE-ON: <subtype | finN-decoder>".
</output_contract>
<grounding_rules>
Mark Mathlib lemma names CONFIRMED only if sure at v4.29, else INFERRED. Distinguish a measure-theoretic /
linear-algebra fact you're confident of from a Lean-tactic guess.
</grounding_rules>
