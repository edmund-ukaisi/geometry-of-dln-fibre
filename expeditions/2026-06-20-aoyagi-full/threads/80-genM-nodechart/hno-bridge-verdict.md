# hNo-bridge verdict — `BoundaryClean M ⟹ NoInteriorBothDrop M`

**Question (controller, precision):** is the clean branch's `hNo : NoInteriorBothDrop M` (a) provable
from `BoundaryClean M`, (b) a confirmed-true dischargeable structural fact, or (c) a real residual that
can fail? **Method:** brute-force (widths 1..4, L≤5, 5456 M, all argmins) + one decorrelated xhigh
Codex (`codex/hno-{prompt,answer}.md`).

## VERDICT: (b)+(a) — `hNo` is TRUE for ALL clean-branch M (NOT a gap), and PROVABLE, but the proof
is **argmin-specific** (needs the minimality of `tStar`), NOT pure admissibility arithmetic.

### Evidence
- **Brute-force:** ZERO clean-branch M (¬InteriorDrop ∧ deepRank=deepRows) violate `NoInteriorBothDrop`
  across 5456 M's, all argmins (`scripts/hno_bridge.py`). So `hNo` is not a soundness gap — it holds
  wherever the clean branch fires.
- **The mechanism (L=2):** the only interior `s` is `s=L−1=1`; the both-drop's second conjunct
  `Text(2)<M[1]` is `deepRank<deepRows`, which clean (`deepRank=deepRows`) makes FALSE. Trivial.
- **The mechanism (L≥3) is NOT trivial — argmin-specific.** Codex's exact counterexample to the
  over-strong "pure admissibility" version (VERIFIED in brute-force): `M=(4,3,1,1)`, `T=(2,1,0)` is
  admissible, weakly decreasing, with `Text(L)=1=M[L−1]` (clean-shaped), but HAS an interior both-drop
  at `s=1` (`Text=[4,4,2,1]`: `2<4` and `2<M[1]=3`). It is NOT the minimizer: `Mval(2,1,0)=3`, whereas
  the actual `tStar=(3,1,0)` has `Mval=1`, `Text=[4,4,3,1]`, no interior both-drop. The block-raise
  `(2,1,0)→(3,1,0)` (raise the unsaturated first coord) strictly lowers `Mval` 3→1.

### The structural invariant (Codex, confirmed)
For a `Mval`-MINIMIZER `tStar` with the deep equality `Text(L)=M[L−1]`, every descent is **saturated**:
at an interior drop `Text(s+1)<Text(s)`, minimality forces `Text(s+1) = bound(s) ≥ M[s]`, so the
second conjunct `Text(s+1)<M[s]` of the both-drop FAILS. Proof (deferred): an unsaturated interior
descent admits a block-raise (`raiseBlock_admissible`) that strictly lowers `Mval`
(`Mval_raiseBlock_lt`, the exit term at the first saturated index has zero cost since it's at its
bound) — contradicting minimality. `¬InteriorDrop` is NOT needed; only `deepRank=deepRows` + minimality.

### Decision (precision-honest)
`hNo` is **NOT silently-assumed-false** — it is a confirmed-true structural fact. The spine carries it
as a dischargeable precondition (option b), with the Lean proof route known (option a: the minimizer
block-raise lemma chain — a moderate, bounded proof, NOT a wall, NOT pure arithmetic). It is NOT a
residual that can fail (option c ruled out). The clean-branch caller establishes `hNo` either by the
deferred block-raise lemma or, until then, as a per-`M` decidable structural input.

**No wall.** The bridge is a bounded argmin-minimality proof, deferred behind the heavier #3 interior
build unless the controller wants it landed now.
