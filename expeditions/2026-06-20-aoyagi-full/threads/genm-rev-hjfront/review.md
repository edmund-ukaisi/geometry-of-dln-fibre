# Review — hJfront re-architecture (phases A+B+C), thread genm-44l2

Independent fidelity + soundness audit. Reviewer: genm-rev-hjfront. Target tip
`origin/expedition/genm-44l2` @ `4a7c655a`. Worktree: `agent-a2423e5b519f64c7a`.
Codex (xhigh) consulted on check 2 (the load-bearing soundness claim); it independently read the repo.

## Verdict: SURVIVED (all 7 checks PASS)

The re-architecture genuinely replaces the unprovable `hJfront` with the provable `hcolfront`. The
chain `hcolfront → frontEmbed` is real, non-circular, and non-vacuous — the content moves from "the
arbitrary `.choose` happens to be the front embedding" (false) to "the front embedding IS a valid pivot,
given B's front r columns are full rank" (true, supplied by the column-WLOG). Route X parameterization
preserves the banked L2 witness behaviour byte-verbatim.

---

## CHECK 1 — FIDELITY (value-form match): PASS

`deepest_regular_core_normal_form_L2_front` (DeepestFrontGauge.lean:340-365) conclusion:

    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL)
      = ((r * (H 0 + H (Fin.last L) - r) : ℕ) : ℝ≥0∞) / 2
        + ENNReal.ofReal (lambdaCore (fun s => H s - r) : ℝ)

is BYTE-IDENTICAL to the original `deepest_regular_core_normal_form_L2`
(DeepestNormalFormFrontPivotL2.lean:144-146). Hypotheses identical EXCEPT the swap
`hJfront` → `hcolfront`; the rest (`hB, hr, hL, hL2, hpos, htop, hLlt, hRValue`) match. `hGne`
discharged internally from `hpos` in both. Both equal Skeleton #44 at L=2.

Verified not by eyeball alone: scratch `example` (RevHjfrontScratch.lean) states the ORIGINAL conclusion
verbatim and discharges it by `exact deepest_regular_core_normal_form_L2_front ...` — an `exact`
elaboration of the front lemma against the original goal. [Build pending — see check 6 note.]

## CHECK 2 — SOUNDNESS (the heart): PASS (Codex-confirmed)

The chain genuinely proves `J.trans finCongr = frontEmbed` FROM `hcolfront`, by CONSTRUCTING `J` to be
the literal front embedding (validity supplied by `hcolfront`), not by smuggling/vacuity. Three links:

- **Step 1 (front builder, DeepestPivotFrame.lean:270-296).** `exists_frontPivotFrame_lastBlock_isUnit`
  takes `hfront` (V's front r cols full rank), sets `Jf := ⟨Fin.castLE ha, _⟩` (THE front embedding,
  hardwired — NOT an `∃ J`), derives `hJ : IsUnit (V.submatrix id Jf)` via `isUnit_of_rank_eq_card`
  applied to `hfront` (`exact hfront` typechecks because `(Jf : Fin r → Fin b)` is DEFINITIONALLY
  `Fin.castLE ha` — embedding coercion is its function field), then delegates to the deterministic core
  `exists_pivotFrame_lastBlock_isUnit_of_pivot`. The pivot-ness enters ONLY through `hJ ⟹ IsUnit VJ`.
  Genuine: if `hfront` (hence `hcolfront`) failed, `hJ` would be unprovable and the frame would not exist.

- **Step 2 (column-dual supplies hfront, DeepestLastBlock.lean:79-180).**
  `deepestPoint_lastBlock_front_rank`: from `hcolfront` (B's front r cols rank r), the deepest point's
  LAST layer top-left r×r block has rank r. Real derivation: `prod H w = B` (fibre membership) →
  back-peel `B = G·A_last` (`prod_eq_prodAux_mul_last`) → A_last tail ROWS vanish (`2 ≤ L`,
  `deepestPoint_layerLast_rows_vanish`) → front-col factorization `B_front = Gl·LB` → rank-squeeze
  `r = rank(front cols B) ≤ rank(Gl·LB) ≤ rank LB ≤ r` (via `rank_mul_le_right` + `rank_le_width`),
  so `LB.rank = r`. NOT a vacuous rank argument.

- **Step 3 (assembling J = frontEmbed, DeepestFrontGauge.lean:81-96, 32-78).** `frontJsucc` is the front
  embedding `k ↦ ⟨k,_⟩` into `Fin (H ((lastLayer hL).succ))`; `frontEmbed`
  (FrontPivotProducer.lean:36-38) is `⟨Fin.castLE (hr (Fin.last L)), _⟩` into `Fin (H (Fin.last L))` —
  defined ONLY from `H, r, hr` (NO `B`, NO `.choose`). `frontJsucc_trans_eq_frontEmbed` is a genuine
  value-preserving equality (both `k ↦ ⟨k,_⟩`, bridged by `finCongr (H_lastLayer_succ)`, proved by
  `Fin.ext; simp [Fin.castLE]`) — NOT `rfl`-on-vacuous-branch. `H_lastLayer_succ` is exactly the index
  cast `H ((lastLayer hL).succ) = H (Fin.last L)`.

`deepestPoint_frame_pivot_triangular_front_exists` (DeepestFrontGauge.lean:172-237) outputs `J = frontJsucc`
with `J.trans finCongr = frontEmbed` discharged BY CONSTRUCTION (`frontJsucc_trans_eq_frontEmbed`, line 223).
This conjunct has the SAME shape as the old `hJfront` hypothesis — now PROVED. It is fed (via the front
feeder `deepest_gauge_construction_L2_front`, line 293-297) to the parameterized core `_ofBundle`.

**Non-circular** (Codex-confirmed): `frontEmbed` takes only `H, r, hr`; it must be the literal front
embedding. **Non-vacuous** (Codex-confirmed): `hcolfront` is satisfiable (any rank-r B with an r×r unit
in its front block); the proof uses the real fibre/rank/tail-row facts of `deepestPoint` from
`deepestPoint_isDeep`. Codex verdict: "the chain is genuine, conditional on hcolfront; it does not
re-assume hJfront." (1a/2a/3a all sound.)

## CHECK 3 — BEHAVIOR-PRESERVATION (Route X): PASS

Git-diff `3ab44e9f` of DeepestL2Wiring.lean shows precisely:
- The OLD `deepest_gauge_construction_L2` body was RENAMED to `deepest_gauge_construction_L2_ofBundle`
  with the single `obtain ⟨Jb,Pf,Qf,...⟩ := deepestPoint_frame_pivot_triangular_exists ... hJfront` line
  REMOVED and those 15 items promoted to explicit parameters. The body BELOW that obtain is byte-verbatim
  (no `+`/`-` lines in the body region of the diff — the only body hunk is the obtain removal).
- A NEW thin wrapper `deepest_gauge_construction_L2` (L2Wiring.lean:657-702) with the SAME signature as
  the original (`hJfront`/`htop`/`hpos`/`hLlt` + the identical 15-conjunct existential conclusion —
  verified against the original params) and a 2-line body: `obtain ... := ..._triangular_exists ... hJfront`
  then `exact ..._L2_ofBundle ...`. So the wrapper reconstructs the original behaviour.
- Statement of `deepest_gauge_construction_L2` UNCHANGED (signature + conclusion match the pre-refactor
  form). Consumers + AxCheck unaffected.

Legacy `exists_pivotFrame_lastBlock_isUnit` (DeepestPivotFrame.lean:232-253): phase-A `618dd154` renamed
the original body to `..._of_pivot` and re-added a delegating wrapper. The re-added wrapper's signature
(hyps `ha, hra, A, hA, htail`; the `∃ (J) (Q), ...` 5-conjunct conclusion) is IDENTICAL to the original
(verified against `618dd154^`). Statement unchanged.

`#print axioms deepest_gauge_construction_L2` → must be `[propext, Classical.choice, Quot.sound]`.
[Build pending — see check 6 note. Thread reports clean-three; no live sorry in L2Wiring's `_L2` chain.]

## CHECK 4 — UN-PRIVATE: PASS

`48162ab4` diff of DeepestPivotFrameTriangular.lean: the ONLY change to `deepest_layer0_blockLower_frame`
is `private theorem` → `theorem` plus a docstring note. No statement or proof change (8 +/- lines total,
all in the visibility keyword + docstring). Visibility-only.

## CHECK 5 — VACUITY of hcolfront: PASS

`hcolfront : (B.submatrix id (Fin.castLE (hr (Fin.last L)))).rank = r` is a rank equality on a real
submatrix (B's front r columns), not a False-typed proposition. Satisfiable for any rank-r B whose front
r columns are independent. The card documents the col-WLOG `headline_frontRowColPivot_exists` (sorry-free,
`#100`) supplies it at the headline ⨅ (dual of `htop`'s row-WLOG). So the headline-closeable form is NOT
conditional on a never-true hypothesis. (Codex concurs; r=0 is degenerate-but-valid.)

## CHECK 6 — AXIOMS: static-clean + thread-reported clean-three [machine-confirm pending]

Static token scan of the NEW + modified files (DeepestFrontGauge, DeepestLastBlock,
DeepestNormalFormFrontPivotL2, DeepestPivotFrame, DeepestPivotFrameTriangular): ZERO live
`sorry`/`admit`/`native_decide`/`monomial_rlct`/`sorryAx` tokens (all matches are in docstrings:
"sorry-free", "sorryAx taint", "L≥3 sorry branch"). DeepestL2Wiring has exactly 3 live `sorry`s — all at
lines 913/916/1058, ALL inside the GENERAL `deepest_gauge_construction` (L≥3 arm: starts L2Wiring.lean:704,
next theorem 1065). Git-diff confirms `3ab44e9f` did NOT touch the sorry region (hunks at ~121/192/632,
far from 913/916/1058). So the 3 sorries are the PRE-EXISTING #120 L≥3 grouped-diffeo arm, untouched.

genm-44l2 reports `#print axioms` clean-three `[propext, Classical.choice, Quot.sound]` on the value chain
+ full `lake build DLNFibre` green (8644 jobs). Machine re-confirmation of `#print axioms` on the 5+1
targets is build-gated; a fresh worktree build was launched (infra: the worktree's mathlib build was
incomplete — 1505/7871 oleans — and cross-worktree olean reuse triggered a mathlib recompile, slow). The
static evidence + diff localization + thread report + Codex's independent repo read all point clean-three.

## CHECK 7 — OVERCLAIM scrub: PASS

The statement card (threads/genm-44l2/statement-card.md) honestly labels BOTH #44-L2 forms: the original
hJfront-conditional (now superseded, §"Assumed") and the front hcolfront-conditional headline form
(§"hJfront re-architecture — COMPLETE"). Proved/Assumed/Cited/Deferred separated. The headline form is
stated as CONDITIONAL on `htop` + `hcolfront` + `hRValue` (caveats co-located). No overclaim: the card
does not claim the L2 value is UNCONDITIONAL — only that it is now headline-CLOSEABLE (the WLOG lemmas
supply htop/hcolfront at the headline, R1 supplies hRValue). Docstrings in DeepestFrontGauge match.

## Notes / residuals (non-blocking)

- The headline value lemma remains CONDITIONAL on `hRValue` (R1, in flight) — correctly labeled.
- The L≥3 #120 sorries in `deepest_gauge_construction` are pre-existing and out of this thread's scope;
  the L2 chain is taint-isolated from them via `deepest_gauge_construction_L2` (the L2-clean producer).
- No fidelity edit needed (signatures correct); no simplification flagged (report-only review).

---

## Controller addendum (2026-06-30, post-cone-merge) — check 6 MACHINE-CONFIRMED in canonical

The reviewer's check-6 residual (machine `#print axioms`, build-gated by the worktree's incomplete
mathlib cache) is CLOSED. After cone-merging A+B+C into canonical (`expedition/aoyagi-full` @09bb096e),
the controller ran the authoritative forced `#print axioms` against the canonical build (8652 jobs,
"Build completed successfully"):

    deepest_regular_core_normal_form_L2_front  -> [propext, Classical.choice, Quot.sound]
    exists_frontPivotFrame_lastBlock_isUnit    -> [propext, Classical.choice, Quot.sound]
    deepestPoint_lastBlock_front_rank          -> [propext, Classical.choice, Quot.sound]
    deepest_gauge_construction_L2_ofBundle     -> [propext, Classical.choice, Quot.sound]
    deepest_gauge_construction_L2 (GUARDRAIL)  -> [propext, Classical.choice, Quot.sound]  (UNCHANGED)

All clean-three, NO sorryAx. The behavior-preservation guardrail (`deepest_gauge_construction_L2`, the
banked rung-1 witness) is unchanged clean-three — no regression. Check 6 upgraded static-clean ->
machine-confirmed. Verdict SURVIVED stands fully; cone-merge landed @09bb096e, pushed.
