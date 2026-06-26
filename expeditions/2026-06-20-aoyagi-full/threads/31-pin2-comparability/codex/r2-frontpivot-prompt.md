<task>
Decorrelated adjudication for a Lean RLCT formalisation. TWO questions: (A) does a comparability hold
(refute or confirm), and if A fails, (B) is a "front-pivot WLOG" repair sound? Re-derive independently.
</task>

<setting>
Deep linear net, L layers, widths H, target rank-r matrix B (H0×H_L). Loss = ‖∏A_s − B‖²_F. A gauge
chart near a "deepest point" gives local coords. A rank-r block split needs to pick which r columns of
the H_L-output are the "pivot" columns. The chart uses J = B's pivot column set (the r columns making
B's rank-r witness), which for generic B is NOT the front columns {0..r-1}.

Two residual-energy quantities (r=1, H0=1, H_L=2, J:0↦col1, a non-front pivot):
- Sreg = the regular-block energy ∑(P00−1)²+∑P01²+∑P10² of  reindex(rThr_row, pivotThr_J_col)(P0·(∏A−B)·QL)
  — the PIVOT-column reindex (this normalizes B: reindex(..)(P0·B·QL) = fromBlocks 1 0 0 0).
- ∑deepestEFull² = the same blocks of  reindex(rThr_row, pivotThr_J_col)(∏ framedParamsPivot) — but the
  framed reconstruction's LAST layer carries a column permutation colPerm_J, so (proven index identity)
  reindex(rThr,pivotThr J)(colPerm_J M) = reindex(rThr, rThr)(M): deepestEFull is THRESHOLD-effective.

Established (numeric, r=1 J:0↦1, nontrivial QL): ∑deepestEFull² = 17.98 ≠ Sreg = 23.65. Both vanish at
the deepest point w0 (each in its own column convention). The `−1` corner of the residual sits at the
threshold column (col0) for deepestEFull but the pivot column (col1) for Sreg.
</setting>

<questions>
A. Does the COMPARABILITY ∑deepestEFull² ≍ Sreg (∃ c1,c2>0 uniform on a 𝓝 of w0) hold, even though
   the equality fails? Reason: both are sreg(reindex(N)) of products differing by a column permutation
   on the off-diagonal, but the `−1` corner lands on DIFFERENT columns (thr vs pivot). Is there a germ
   path where one block-energy → 0 while the other stays bounded away (refuting one side)? Specifically:
   for a non-front J, the threshold reindex puts the "1" at a column that is NOT B's pivot, so the
   threshold residual sees a `(0−1)²=1` floor where the pivot residual sees `0`. Does this give a
   non-vanishing GAP (deepestEFull bounded below while Sreg → 0, on a germ)? Give the verdict + the path.

B. IF A fails: is the "front-pivot WLOG" repair sound? Claim: rlctAt(dlnLoss H B) = rlctAt(dlnLoss H (B·π))
   where π is a column permutation bringing B's pivots to the front (so J' = {0..r-1} = front, and then
   pivotThr J' = rThr, making deepestEFull and hconj COINCIDE). The realization: the param change
   A_{L-1} ↦ A_{L-1}·π (a fixed linear measure-preserving bijection on the last layer's params), under
   which ∏A ↦ (∏A)·π and ‖∏A − B‖² = ‖(∏A)π − Bπ‖²·(π orthogonal). Confirm:
   (B1) the column permutation π is measure-preserving on the parameter space (A_{L-1} ↦ A_{L-1}π is a
        coordinate permutation, |det|=1) ⇒ rlctAt invariant.
   (B2) ‖∏A − B‖²_F = ‖(∏A − B)π‖²_F (π orthogonal column permutation) = ‖∏(A with last·π) − Bπ‖²_F,
        so dlnLoss H B at A = dlnLoss H (Bπ) at (A with last·π). Confirm the loss identity.
   (B3) After the change, B's pivots ARE front, so the deepest-point chart for (Bπ, front-J) has
        pivotThr = rThr ⇒ deepestEFull = hconj (conjunct b holds). Confirm the chart for (Bπ, front) is
        a valid instance (rank(Bπ)=rank(B)=r; the deepest-point construction applies).
   (B4) does this touch PIN1 (deepestEPivot_regSlice_fderiv, which must stay axiom-clean)? The π only
        permutes B's columns / the last layer's output basis — PIN1 is a derivative fact about the
        reg-slice, basis-permutation-covariant. Reason whether PIN1 is untouched.

C. Is there a MORE CONTAINED sound repair than B that I'm missing (e.g. defining deepestEFull pivot-aware
   without touching PIN1, or a different bridge)? Or is B the right one?
</questions>

<output_contract>
A: VERDICT comparability holds/FAILS + the germ path. B: VERDICT each of B1–B4 sound/not + the loss
identity. C: any more-contained option. End with: "Option A (comparability) is [SOUND/FAILS]; the sound
repair is [B front-pivot WLOG / other], and it [does/does not] touch PIN1."
</output_contract>

<grounding_rules>
Re-derive the column-permutation algebra + the MP/orthogonality. Distinguish the loss-identity (exact)
from the rlct-invariance (needs MP). Flag if π must be absorbed into QL/endpoint frames coherently.
</grounding_rules>
