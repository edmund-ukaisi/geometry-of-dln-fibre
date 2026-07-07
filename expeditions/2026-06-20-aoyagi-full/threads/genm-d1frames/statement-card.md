# Statement card — #120 interior-frame triviality (`genm-d1frames`)

Closes the two INTERIOR-FRAME sorries in `deepest_gauge_construction`'s L≥3 arm
(`DeepestL2Wiring.lean`, formerly `:913`/`:916`): the strict-interior gauge frames of the deepest
point are the identity. Route source: `threads/genm-gauge120/cert.md` (§ Formaliser runway, the
interior-frame gap paragraph — "a `DeepestPivotFrame`-chooser refinement that picks identity interior
frames").

> **Claim.** For a rank-`r` target `B` and the deepest point of the DLN loss, on every strict-interior
> layer (`0 < s`, `s+1 < L`) the per-layer gauge frames chosen by the deepest-point frame family are
> the identity: `P_s = 1` and `Q_s = 1`. (This is because the interior deepest layer is already the
> block-normal corner `diag(I_r, 0)`, so the identity frame carries it to `corM`.)
>
> - **Lean:** `DLNFibre.DLN.RLCT.deepestPoint_frame_interior_eq_one`
>   (`lean/DLNFibre/DLN/RLCT/Validate/DeepestFrame.lean`), threaded through
>   `deepestPoint_frame_pivot_exists` (`DeepestPivotFrame.lean`) and
>   `deepestPoint_frame_pivot_triangular_exists` (`DeepestPivotFrameTriangular.lean`), consumed in
>   `deepest_gauge_construction`'s L≥3 arm (`DeepestL2Wiring.lean`, the `hinterface` sub-derivation).
>   Branch `genm-d1frames`, base `7af83e49` (final SHA pinned by the controller at integration).
> - **Gloss.** `deepestPoint_frame_interior_eq_one`: given `0 < (s:ℕ)` and `(s:ℕ)+1 < L`, both
>   projections of `deepestPoint_frame … s` equal `1` (`.1 = 1 ∧ .2 = 1`). The two producer existentials
>   each gained one conjunct `∀ s, 0 < s → s+1 < L → P s = 1 ∧ Q s = 1`, propagated verbatim. In the
>   consumer, `hinterface`'s two interior branches close by `(hInterior s hspos hs).2` (the `Qf s = 1`
>   branch) and `(hInterior ⟨s+1,_⟩ _ _).1` (the `Pf (s+1) = 1` branch).
> - **Proved.** The interior frames are IDENTITY, unconditionally. The pinning is legitimate: the
>   interior deepest layer equals `corM` (`deepestPoint_isDeep`'s interior clause = `IsDeepLayers`
>   clause 3), so `1 · deepestPoint s · 1 = corM` — the identity is a valid rank-normal-form frame, and
>   the chooser now selects it. All producer existentials are axiom-clean
>   `[propext, Classical.choice, Quot.sound]` (forced `#print axioms`, no `sorryAx`).
> - **Assumed.** None new. The interior conjunct is guarded by `0 < s ∧ s+1 < L`; endpoint frames
>   (`firstLayer`/`lastLayer`) are untouched, so the endpoint-frame decoration (gauge120 "9th catch")
>   is preserved.
> - **Cited.** None.
> - **Deferred.** `hstep2` (`DeepestL2Wiring.lean:1060`, the grouped-`G0` diffeo bridge
>   `rlctAtOn(Sreg+Score) = rlctAtOn(Sreg+coreΦ)`) — the third #120 sorry, a SEPARATE tide, untouched.
>   `deepest_gauge_construction` therefore still carries `sorryAx` solely from `hstep2` (confirmed:
>   `deepest_gauge_construction_L2`, the L<3 arm that never hits `hstep2`, is fully axiom-clean).
> - **Route.** (controller/cert `genm-gauge120`) Refine the frame chooser to select identity interior
>   frames — valid because `deepestPoint`'s interior layers ARE `blockdiag[I_r,0]`. Realised as: add
>   the interior-identity conjunct at the SOURCE (`deepestPoint_frame_exists`, splitting its interior
>   branch to pick `(1,1)` on strict interior) and thread it verbatim through the two downstream
>   producer existentials; no signature change to any consumer beyond one extra destructure binder.
> - **Status.** sorry-free (for the two interior-frame sorries; `hstep2` remains a named, separate
>   deferred gap). Awaiting reviewer fidelity check.

## Files changed (LoC delta ≈ +83 / −21)

- `DeepestFrame.lean` — interior conjunct on `deepestPoint_frame_exists`; interior branch split to
  pick `(1,1)` via the interior corM clause; `_Pf_eq_one` projection shifted `.2.2.2.2 → .2.2.2.2.1`;
  new wrapper `deepestPoint_frame_interior_eq_one`.
- `DeepestPivotFrame.lean` — interior conjunct on `deepestPoint_frame_pivot_exists`; proved via the
  new wrapper (`P s = deepestPoint_frame.1 = 1`; interior `s ≠ lastLayer` so `Qpiv s = frame.2 = 1`).
- `DeepestPivotFrameTriangular.lean` — interior conjunct on `deepestPoint_frame_pivot_triangular_exists`;
  internal `obtain` gains `hInt0` binder; proved (interior `s ≠ firstLayer` so the layer-0 override is
  skipped, `P s = P0 s = 1`, `Q s = Q0 s = 1`).
- `DeepestL2Wiring.lean` — both triangular destructures gain a binder (`_` in the L2 arm,
  `hInterior` in the L≥3 arm); the two `hinterface` interior sorries closed via `hInterior`.

## Audit evidence

- `scripts/lb DLNFibre.DLN.RLCT.Validate.DeepestL2Wiring`: green (2752 jobs).
- `scripts/sorries` on `DeepestL2Wiring.lean`: exactly one tactic sorry (`:1060` = `hstep2`), down
  from three; `:913`/`:916` gone.
- Forced `#print axioms` (fresh `lake env lean`, no stale olean):
  `deepestPoint_frame_exists`, `deepestPoint_frame_interior_eq_one`, `deepestPoint_frame_pivot_exists`,
  `deepestPoint_frame_pivot_triangular_exists`, `deepest_gauge_construction_L2` — all
  `[propext, Classical.choice, Quot.sound]` (NO `sorryAx`). `deepest_gauge_construction` shows
  `sorryAx` solely from the surviving `hstep2`.
