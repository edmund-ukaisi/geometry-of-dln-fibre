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

## RULED (A) — two follow-on rows (`verify/corner_followons.py`, exit 0)
The elder RULED (A) paper-first (her regular end-transforms `P₁/P₂` absorbed globally via Lemma 1; the
corner row = her input-basis gauge; (B)/(C) rejected on fidelity — (B) drops the diagonalization the
`M_{s,k}`/`diag(b)` read-off wants). Two charged follow-ons:

- **(1) REALIZATION CONDITION — PER-CHART input basis (bounded, not a re-open).** The corner pivot-ROW
  clear `Q₂` is PER-BRANCH (it clears the branch pivot's row): `Q₂^α = [[1,−u₀₀₁],[0,1]]` (clears row 0)
  vs `Q₂^β = [[1,−u₀₁₁],[0,1]]` (clears row 1) — DIFFERENT. So ONE fixed global input-CoV closes only its
  own branch; each chart uses ITS OWN `GL_{d₀}` end-factor gauge. VERDICT: per-chart input basis. Bounded —
  the charts are local and computed independently for the RLCT read-off, so a per-chart gauge is
  resolution-normal (a bounded extension of the end-factor, not a re-open). "One-global" would need all
  branches to share a pivot row; they don't.
- **(2) INTERIOR-PIVOT WITNESS — the interior path closes per-edge (no input gauge).** `(2,2,2,2)` is
  all-corner (every pivot at `(cleared,cleared)`), so it validates (A)'s corner path but NOT the interior
  path. At a strictly-interior LAYER-1 (`S=1`) pivot `(1,1)` of a `3×3` `A₁`: the full row+col clear —
  col-clear `Q₁` compensated by `A₂` (deeper), row-clear `Q₂` compensated by `A₀` (SHALLOWER, internal —
  NOT the input) — gives `cleared == uncleared` identically (`⟨cleared⟩=⟨uncleared⟩`, census 0) with the
  block monomialised (pivot row+col zeroed, interior Schur). So the INTERIOR path closes PER-EDGE, both
  compensators internal, no input gauge — distinct from the corner (`S=0`) path which spends the global
  input gauge (A). Confirms the full three-branch shear + row-and-col clear + equality close at an interior
  pivot, the per-fibre path `(2,2,2,2)` did not exercise.

Net: corner RULED (A), realization = per-chart (bounded), interior path closes per-edge. The corner arc is
complete from the compute side; only the authoritative battery on arch-C-4's rendered formulas remains.
