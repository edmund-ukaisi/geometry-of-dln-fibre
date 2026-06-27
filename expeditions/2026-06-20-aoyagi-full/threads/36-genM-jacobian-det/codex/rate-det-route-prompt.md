<task>
Adjudicate ONE build-ready Lean route among three. Work the architecture yourself; do NOT rubber-stamp.

CONTEXT (a Lean 4 + Mathlib formalisation of a DLN resolution-chart determinant). The SETTLED math:
- A chart phi : R^N -> R^N (N = sum_k M_k M_{k+1}) for resolving a codim-m achiever center (m=minAdm M)
  must carry BOTH: RATE  routeMCore(phi x) = (x_p)^2 * U(x)  AND  DET  |det Dphi(x)| = |x_p|^{m-1}*spectators.
- The RATE is governed by a BANKED abstract telescope `chain_telescope` (RouteMAchieverTelescope): given a
  `Chain` whose data is per-level local identities `C_s * A_s = B_s * C_{s+1} + u*E_s` and terminal `C_n=u*R`,
  it proves `C_0 * suffix_0 = u * Hmat_0` over ARBITRARY nat-width families (backward induction, sorry-free).
  A suffix bridge turns this into `prod M A = u*H`, hence `routeMCore = u^2 * V`. This is BACKWARD/suffix form.
- The banked rate theorem `routeMCore_phiGen u M t B hle (hC0)` holds for ANY block-data `B : GenBlk M t`
  (consumes only B/hle/hC0). The chart is `phiGen u M t B hle = paramsEquivFlat (chartParamsGen u M t B hle)`,
  whose Params-layers ARE the chain layers `A_s` (reindexed). The radial scalar `u` and the block data `B`
  are SEPARATE arguments.
- The current vector chart `phiFlatStructV x := phiGen (x p) M t (genBlkFlatStruct x) hle` has the RATE ∀M
  (banked) but its flat-map Jacobian is IDENTICALLY ZERO: `genBlkFlatStruct` has `Rfin := 0` (leaf C_L=0) and
  the leaf Schur-slot coords feed UNUSED GenBlk(L) slots (dead columns) -> det 0. (Confirmed: not "off by one",
  genuinely rank-deficient.)
- For the DET, the validated template (banked anchors (4,4,2,2),(3,3,4)) is a SEPARATE factor composition:
  phi = Q_linear ∘ pivotBlowupOn(active,p) ∘ (Schur/b=aβ layer-ops), with |active|=m, det |x_p|^{m-1}, and
  the layer-ops carry spectator monomials. The det infra (`composeFold`, `phiTarget_abs_det_of_factored`,
  `radialFactor`) is banked.
- The achiever path active set: |active| = m = minAdm = sum_j r_j c_j (Aoyagi residual blocks). UNIFORM ∀M.
- KEY simplification (banked-feasible): keep CANONICAL FlatIdx order (pack trivial, det 1); put slot selection
  into a DECIDABLE `active : Finset (Fin N)` (a filter on decoded FlatIdx); pivotBlowupOn needs only active.card.
  So NO per-M Equiv `e_M` to build.

THE THREE ROUTES for the genuine-det chart `phi_det` (which must ALSO carry the rate):
- (2b) BRIDGE: prove `phi_det = phiFlatStructV` (or their GenBlk-decodings agree) over opaque widths, then the
  rate transfers from the banked theorem. FAILURE HISTORY: this is the chartIdxEquiv K/X/N/E role-slot ↔ raw
  Params layer-layout funext-s; a `bridgeCLE`/`paramsBlockSplitCLE` engine was built specifically to absorb it
  but the funext "NEVER LANDED" across two tides. Codex earlier called it "permutation archaeology".
- (2a) RE-DERIVE: define `phi_det` directly with a chosen full-rank decoder `B_det(x)`, prove
  `routeMCore(phi_det x) = (x_p)^2 * U` by applying the BANKED `routeMCore_phiGen` to `B_det` (NOT a new forward
  telescope — just instantiate the existing backward-telescope rate theorem at B = B_det, re-checking only hC0).
  Then the DET via the factor composition / phiTarget_abs_det_of_factored. Question: since `routeMCore_phiGen`
  is decoder-agnostic, is 2a simply "supply a full-rank B_det + re-check hC0 + do the det", with NO bridge and
  NO new telescope? What does "reopen dependent-width Schur-block construction" actually cost here — is the
  full-rank B_det harder to build than genBlkFlatStruct was?
- (A-revisited) FIX-IN-PLACE: modify genBlkFlatStruct's decoder (add a fixed-1 pivot residual slot + nonzero
  Rfin to kill the dead slots), keeping its banked rate (re-check hC0), so phiFlatStructV itself becomes
  full-rank with det |x_p|^{m-1}. Question: does a single decoder edit (Rfin nonzero with a fixed-1 entry, +
  the pivot a distinct slot) make the EXISTING phiFlatStructV's flat-map Jacobian full-rank AND keep the rate,
  WITHOUT any bridge — i.e. is the det then a direct Jacobian computation on the one chart?

QUESTIONS:
1. Among 2a / 2b / A-revisited, which ACTUALLY LANDS in Lean with least risk, given (i) the rate theorem is
   decoder-agnostic (any B), (ii) 2b's funext never landed across two tides, (iii) the det needs a full-rank
   chart whose det = |x_p|^{m-1}? Reason about whether 2a and A-revisited even NEED the bridge at all.
2. For the chosen route, what is the CONCRETE construction of the full-rank decoder/chart, and what is the
   exact funext/induction target (to formalisation precision)?
3. Is there a route where the rate is obtained by INSTANTIATING the banked `routeMCore_phiGen` at the same
   `B_det` the det uses — so there is ONE chart, the rate is a banked-theorem application, and the det is a
   direct Jacobian computation, NEVER a `composeFold = phi` bridge?
4. (3,3,3,3) worked check: minAdm=6, unique minimizer T*=(2,1,0) drops rank at ALL 3 boundaries. Sketch how the
   chosen route handles a chart with drops at every boundary (the multi-boundary Schur coupling), and confirm
   |active|=6, det |x_p|^5, rate (x_p)^2.
5. KILL-FLAG: if ALL THREE are persistent Lean walls (no route lands without an open-ended fight), say so
   sharply — that escalates to a strategic call.
</task>

<output_contract>
- Q1: rank 2a/2b/A by what LANDS, with the bridge-needed-or-not analysis per route. FACT vs INFERENCE.
- Q2: the concrete construction + exact funext/induction target for the chosen route.
- Q3: a sharp yes/no on the "instantiate routeMCore_phiGen at B_det, no bridge" route, with why.
- Q4: the (3,3,3,3) sketch (active.card=6, det |x_p|^5, rate).
- Q5: a clear yes/no on whether all three are walls.
</output_contract>

<grounding_rules>
- The banked facts (decoder-agnostic rate theorem; backward telescope; det infra; |active|=minAdm; canonical
  FlatIdx + active Finset) are FACTS. The 2b funext failure across two tides is a FACT — weigh it heavily.
- Do not assume the bridge is needed; check whether 2a/A sidestep it by instantiating the rate theorem at B_det.
- Be decisive — the goal is the route that LANDS in Lean, not the prettiest.
</grounding_rules>
