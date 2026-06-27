<task>
Lean/DLN formalisation. I found a gap in the dead-leaf pivot-survival witness; confirm or refute it.

SETUP: chain `Hmat s = B_s·Hmat(s+1) + E_s·suffix(s+1)`, `Hmat L = Rfin_L = 0` (DEAD leaf),
`suffix s = A_s···A_{L-1}`, `A_s = chainA(N_s)(W_s)(C_{s+1})` (kept rows = `C_{s+1} − N_s W_s`, lift rows
= `W_s`), `C_{s+1} = Bmat_{s+1}·chainQ(N_{s+1}) + u·Rmat_{s+1}` (interior), `C_L = u·Rfin_L = 0`.
`E_s = Rmat_s·A_s`. The decoder reads flat coords; the witness sets all `K=I, X=0, N=0, W=0` except a live
`E`/`W` at one chosen interior boundary.

SYMPY FINDINGS (exact):
1. Live `E`/`W` at the DEEPEST interior boundary `s = L−1` ⟹ `Hmat 0` has one nonzero entry = `e·ω`
   (WORKS): (3,3,4) L=2 and (3,3,3,3) L=3 both give `‖Hmat 0‖² = 1` at `e=ω=1`.
2. Live `E`/`W` at a NON-deepest boundary `s < L−1` (identity elsewhere) ⟹ `Hmat 0 = 0` (FAILS):
   (3,3,3,3) with the live block at `s=1` gives `‖Hmat 0‖² = 0`. Reason: at the witness `A_{L−1} = [0 ; W]`
   (its kept rows `= C_L − N·W = 0` since dead leaf `C_L=0` and N=0), and for `s<L−1` the deeper layers'
   `A` are `[Bmat ; 0]` (lift=0), so the suffix product kills the W-column injected at `s`. Only the LAST
   interior boundary `s=L−1` survives because `suffix L = 1` (no further layers).

THE GAP: the witness MUST place the live block at `s = L−1` (the deepest interior). That boundary's residual
block is `r_{L−1} × c_{L−1}` with `r_{L−1} = Text(L−1) − Text(L)` and `c_{L−1} = Wext(L−1) − Text(L)`. For
the achiever path `tach M = Fin.cons (M 0) (tStar M)`: `Text(L) = tStar(last) = 0` (admPred forces the last
exponent 0), so `r_{L−1} = Text(L−1) = tStar(L−2)` and `c_{L−1} = M(L−1)`. The block is ACTIVE
(nonempty rows) iff `tStar(L−2) ≥ 1`. But `tStar(L−2) ≥ 1` is NOT guaranteed — if the Aoyagi minimiser
drops rank to 0 before the last interior boundary, `tStar(L−2) = 0`, the deepest interior is ROW-EMPTY, and
the dead-leaf witness has no live block there. My `exists_active_block` gives SOME active boundary, but (per
finding 2) a non-deepest active boundary does NOT propagate to `Hmat 0`.

QUESTIONS:
Q1. Confirm or refute: the dead-leaf pivot-survival witness genuinely REQUIRES `tStar(L−2) ≥ 1` (the deepest
    interior boundary active), and when `tStar(L−2) = 0` the dead-leaf `Hmat 0 ≡ 0` even though `minAdm ≥ 1`
    (the codim sits at SHALLOWER boundaries the dead-leaf suffix kills). Is my finding-2 reasoning correct?
Q2. If confirmed: does this force the LIVE-LEAF decoder (`Rfin_L ≠ 0`, the certificate's original §2 spec)
    for a UNIFORM ∀M witness? With a live leaf, `C_L = u·Rfin_L ≠ 0`, so `A_{L−1}` kept rows carry `C_L`,
    and the leaf pivot `Rfin_L(0,0)=1` survives the all-kept telescoping path `Hmat_0(0,0)=∏Bmat_k(0,0)·1=1`
    regardless of where the rank drops — robust to `tStar(L−2)=0`. Is the live leaf the right fix, OR is
    there a dead-leaf witness using a SHALLOWER active boundary with a DIFFERENT (non-identity) suffix that
    preserves the injected column (e.g. set the intervening W's to carry the column down)?
Q3. If the live leaf is needed: the leaf-slot accounting. `Rfin_L : Text(L) × Wext(L) = tStar(L-1) × M(L)`.
    But `tStar(L-1) = 0` (last tStar)! So `Text(L) = 0` ⟹ `Rfin_L` has ZERO ROWS ⟹ the leaf is also empty
    for the achiever path `tach`. So even the live leaf `Rfin_L` is row-empty (Text L = 0). Does this mean
    the leaf must be at `Text(L) = tStar(L-1)` which is 0 — i.e. the ENTIRE achiever-path chain has a
    rank-0 leaf, and the pivot must live at the deepest NONEMPTY boundary? Re-derive: for `tach`, where is
    the LAST nonempty `Text`? `Text(k) = tach(k-1)`; the last nonzero is at `k` = (last index with
    `tStar(k-1) ≥ 1`) + 1. The pivot/witness must live THERE. Is the right construction: the chain's
    "effective leaf" is the deepest boundary with `Text ≥ 1`, and the witness/pivot goes there?

OUTPUT CONTRACT:
- Q1: confirm/refute finding-2 + the `tStar(L−2) ≥ 1` requirement, ≤ 6 sentences.
- Q2: dead-leaf-shallower-witness vs live-leaf, the recommendation, ≤ 8 sentences.
- Q3: the leaf-row-empty issue (`Text L = tStar(last) = 0`) + the "effective leaf = deepest Text≥1
  boundary" construction — is THIS the correct uniform witness location? ≤ 8 sentences.
- End: the ONE correct witness construction for uniform ∀M (2≤L), ≤ 4 sentences. Flag INFERENCE.
</task>
