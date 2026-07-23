# §-note: corner-treatment — both (A) global end-factor gauge and (B) triangular-tolerance FEASIBLE

arch-C-4's corner catch: at a CORNER pivot the pivot-ROW compensator `Q₂⁻¹` acts on the network INPUT `x`
(the `d₀` domain = `A₀`'s columns), a GLOBAL object — inexpressible as a per-edge step (branch-(iii) vacuous
at `S=0`). Interior pivots close identically (their row-compensator is internal). Two model-checks on the
existing harness (which already implements (A)'s structure). Script: `verify/corner_treatment.py` (exit 0),
witnesses `(2,2,2,2)`/`(2,3,2)`/`(2,3,2,2)`, corner pivot `(0,0)` at layer 0.

## (A) END-FACTOR TREATMENT — FEASIBLE, equality close RESTORED (all witnesses)
Split: per-edge clears only the pivot COLUMN (`Q₁`, deeper-compensated by `A₁·Q₁⁻¹`), + the pivot-ROW clear
applied ONCE as a GLOBAL input change-of-variables (`Q₂` on `A₀`'s input columns = the `GL_{d₀}` end-factor
gauge on `x`).
- **Equality close RESTORED:** composite (per-edge col-clear + global `Q₂`) `== original · Q₂` identically,
  and `⟨composite⟩ ⊆ ⟨original⟩` (ideal) — TRUE on all three witnesses. Since `Q₂ ∈ GL_{d₀}` on the input,
  `⟨composite⟩ = ⟨original⟩` (the input gauge is ideal-preserving) ⟹ census 0, no bridge, at the corner.
- **Block forms:** per-edge-only the corner block is upper-triangular `[[1, u₀₀₁],[0, e₂]]` (col cleared,
  row kept); AFTER the global input-CoV it is `diag(1, e₂)` (row cleared by the gauge). Exactly the split
  arch-C-4 described.
So the corner's pivot-row freedom is the `GL_{d₀}` END-FACTOR gauge (a single global input CoV), not a
per-edge op — and factoring it out once restores the equality close that the per-edge Q₂⁻¹ could not.

## (B) TRIANGULAR TOLERANCE — boostReady HOLDS on the triangular corner block (all witnesses)
With col-only clearing per-edge (NO row treatment anywhere), the corner block stays upper-triangular
`[[1, u₀₀₁],[0, e₂]]`. On the reuse node, the residual is MULTILINEAR — `deg_u₀₀₁ = 1`, `deg_u₀₁₀ = 1`
(scoped `i≥cleared` recoord), all three witnesses — so `Deg1SupportedOn ed.center` / boostReady HOLDS with
the triangular block. (Confirms arch-C-4's multilinearity probe + the specific center-support property.)

## Verdict for the elder's corner ruling
Both candidate treatments are compute-FEASIBLE:
- **(A)** the global end-factor gauge (`Q₂` on `x`, once) restores the equality close (census 0) — the
  corner row-freedom is the `GL_{d₀}` input gauge, banked machinery.
- **(B)** even with NO row treatment, the triangular corner block is tolerated by boostReady (multilinear,
  center-supported).
So the corner is not a blocker either way. The paper-first choice (does HER corner step spend the input
gauge, treatment A? or carry the triangular block, B?) is the elder's ruling; the compute side confirms
both close. (A) is the cleaner match to her Lemma-2 mechanism if the corner step is read as the end-factor
`GL_{d₀}` gauge; (B) is the fallback that needs no input-side op at all.
