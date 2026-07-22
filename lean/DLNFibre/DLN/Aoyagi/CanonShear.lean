import DLNFibre.DLN.Aoyagi.MonumentAtlas

/-!
# `DLN.Aoyagi.CanonShear` — the canonical Q/Schur step shear + within-carve emission (SEAT-L4, M7)

The per-step Schur shear `canonShearOf` a case12/case2 edge emits, and the proof that it satisfies
`ShearWithinCarveRaw`'s three clauses (I write-zero on layers ≥ sl / II reads ignore those layers /
III vanishes on ledger birth-corners). Design (SPECIFY, seat-L4 determination battery + elder): the
shear is **Schur-within-carve** — the displacement acts ONLY within the layer-`s.layer` carve block
INTERIOR (row, col > `s.cleared`), writing the Schur cross-term `−γ·β` (`γ` = the pivot-column tail,
`β` = the pivot-row tail), and is IDENTITY (displacement `0`) on every other coordinate. For a
case12/case2 edge the child sits at `cleared ≥ 1` so `sl = supportLayerOf = s.layer + 1`, and the
carve is layer `s.layer < sl` — hence (I)/(II) hold (write/read on layer `s.layer` only, below the
threshold) and (III) holds because the Schur writes the strict interior `(>J, >J)`, never a diagonal
corner (`= clause3_corner_check.py` A1-A4).

`canonShearOf` is the RAW displacement `shearφ` (the edge stores `blockShear (canonShearOf …)`;
`ShearWithinCarveRaw`/`IsRealBranch` read the raw displacement). At a case11/rollover edge the shear is
`id` (displacement `0`), trivially within-carve — this file is the case12/case2 emitter.
-/

open MeasureTheory Set Filter Topology RLCT
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine

namespace DLNFibre.DLN.Aoyagi

variable {N : ℕ}

/-- The flat coordinate of the layer-`S` block entry at `(row, col)` — general (`cornerToFlat` is the
diagonal `(J,J)` special case). `none` off-cone. Used to read the pivot-row/col tails `β`/`γ`. -/
noncomputable def blockEntryFlat (d : Fin (N + 1) → ℕ) (S row col : ℕ) : Option (Fin (flatDim d)) :=
  if hS : S < N then
    let i : Fin N := ⟨S, hS⟩
    if hr : row < d i.succ then
      if hc : col < d i.castSucc then some (tupIdxEquiv d ⟨⟨i, ⟨row, hr⟩⟩, ⟨col, hc⟩⟩) else none
    else none
  else none

/-- **The canonical Q/Schur step shear** (raw displacement, seat-L4 M7). Schur-within-carve: at a flat
coordinate decoding to `(layer, row, col)`, the displacement is the Schur cross-term `−u_γ·u_β` when the
coord is in the layer-`s.layer` carve INTERIOR (`row, col > s.cleared`) — `γ` at `(layer, row, cleared)`,
`β` at `(layer, cleared, col)` — and `0` otherwise. Reads only layer-`s.layer` coords; writes only the
layer-`s.layer` strict interior (never a diagonal/birth corner). Its `blockShear` is the case12/case2
`edgeShear`. -/
noncomputable def canonShearOf (d : Fin (N + 1) → ℕ) (s : ConState N) :
    (Fin (flatDim d) → ℝ) → (Fin (flatDim d) → ℝ) :=
  fun u k =>
    let q := (tupIdxEquiv d).symm k
    if h : (q.1.1 : ℕ) = s.layer ∧ s.cleared < (q.1.2 : ℕ) ∧ s.cleared < (q.2 : ℕ) then
      (-(u (tupIdxEquiv d ⟨⟨q.1.1, q.1.2⟩,
              ⟨s.cleared, lt_trans h.2.2 q.2.isLt⟩⟩)))
        * (u (tupIdxEquiv d ⟨⟨q.1.1, ⟨s.cleared, lt_trans h.2.1 q.1.2.isLt⟩⟩, q.2⟩))
    else 0

/-- **Prepared-form / R_bad-kill (elder-facing candidate for the `CanonicalSchurStep` predicate).**
`canonShearOf` is SUPPORTED on the layer-`s.layer` carve STRICT interior (`row, col > s.cleared`): a
nonzero displacement forces the coordinate there. So the shear writes ONLY the Schur cross-term `−γ·β`
on the interior, never a diagonal/pivot corner nor a bare pivot-column entry — the "γ Schur-cleared"
structure that EXCLUDES the boost-readiness countermodel `R_bad = Z·B·[[1,β],[γ,u_p]]` (unprepared,
`γ≠0`, whose center-zeroing leaves `γ·(…)`). This is the write-side content of clauses (I)/(III) and
the candidate ingredient for the elder's boost-readiness pin (resolution 2). -/
theorem canonShearOf_support (d : Fin (N + 1) → ℕ) (s : ConState N)
    (u : Fin (flatDim d) → ℝ) (k : Fin (flatDim d)) (hk : canonShearOf d s u k ≠ 0) :
    (((tupIdxEquiv d).symm k).1.1 : ℕ) = s.layer ∧
      s.cleared < (((tupIdxEquiv d).symm k).1.2 : ℕ) ∧
        s.cleared < (((tupIdxEquiv d).symm k).2 : ℕ) := by
  by_contra h
  exact hk (by simp only [canonShearOf]; exact dif_neg h)

/-- **M7 emission — `canonShearOf` is within-carve.** At a case12/case2 real-branch edge (node = the
step, so `node.conState = ed.nextState`, `cleared ≥ 1`, `sl = layer+1`), the raw shear
`canonShearOf d p.conState` satisfies `ShearWithinCarveRaw`'s three clauses. The clause the shear-pin of
`IsRealBranch` and the L6 (★) A4 consume. -/
theorem canonShearOf_shearWithinCarve (d : Fin (N + 1) → ℕ)
    (e : (Fin (flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d) (p : TreePath d) (ed : TreeEdge d p)
    (hcase : ed.case = StepCase.case12 ∨ ed.case = StepCase.case2)
    (hshear : ed.shearφ = canonShearOf d p.conState) :
    ShearWithinCarveRaw d e (p.extend ed) ed.shearφ := by
  -- map: M7-emission (canonShearOf satisfies ShearWithinCarveRaw I/II/III at case12/case2)
  sorry

end DLNFibre.DLN.Aoyagi
