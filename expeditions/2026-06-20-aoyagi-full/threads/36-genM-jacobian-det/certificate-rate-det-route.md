# Certificate — the rate↔det route adjudication (build-ready: ROUTE 2a)

**Seat:** pen-and-paper (witness). **Date:** 2026-06-27. Decisive route choice for the genuine-det chart
`φ_det` (which must carry BOTH the rate `(x_p)²·U` and the det `|x_p|^{minAdm−1}·spectators`). Extends
`certificate-decoder-fix.md` (the (C)-fix verdict, det≡0) + `certificate-achiever-path.md` (KC1: `active.card
= minAdm`). The MATH is settled (F1–F4 in thread UPDATE-12); this picks the Lean route that LANDS.

Decorrelated xhigh Codex (independent — converges on 2a): `codex/rate-det-route-{prompt,answer}.md`.
Exact scripts: `scripts/direct_det_222_1.py`, `check_3333.py`.

**VERDICT — ROUTE 2a. NOT a wall. The other two: 2b is a NO-GO (false statement); A-revisited collapses
into 2a.** The decisive move: instantiate the BANKED decoder-agnostic rate `routeMCore_phiGen` at a
full-rank decoder `B_det` — the rate becomes a one-line theorem application (no bridge, no new telescope),
and the det is a coordinate-level factorization of the SAME chart (NOT the `composeFold = phiFlatStructV`
funext that never landed across two tides).

---

## 1. Why 2b is dead, why A collapses into 2a, why 2a lands (the structural reason)

The pivotal banked fact: **`routeMCore_phiGen u M t B hle (hC0)` holds for ANY block data `B : GenBlk M t`**
(`RouteMGenChartId.lean:136` — it consumes only `B`/`hle`/`hC0`, routed through the banked backward
`chain_telescope`). The chart is `phiGen u M t B hle = paramsEquivFlat (chartParamsGen u M t B hle)`, whose
`Params`-layers ARE the chain layers `A_s` (`chartParamsGen` is `reindex (chainOfMt … B).A_s`,
`RouteMGenChartId.lean:36`). The radial scalar `u` and the block data `B` are SEPARATE arguments.

- **2b (bridge `φ_det = phiFlatStructV`) is a NO-GO, not merely hard.** `phiFlatStructV`'s flat Jacobian is
  IDENTICALLY ZERO (decoder-fix cert D1: `Rfin := 0` ⟹ dead leaf slots). The det chart has det generically
  `|x_p|^{minAdm−1} ≠ 0`. So `φ_det = phiFlatStructV` is **FALSE**. The historical funext failure across two
  tides (UPDATE-11/12) was not a tactic gap — it was funext-ing toward a false equation. **Reject.** (The
  banked `bridgeCLE`/`paramsBlockSplitCLE` engine built to absorb it is moot for this purpose.)

- **2a (instantiate the rate at a full-rank `B_det`) lands.** Because the rate theorem is decoder-agnostic,
  the det chart `φ_det x := phiGen (x p) M t (B_det x) hle` gets its rate for FREE: `routeMCore (φ_det x) =
  (x p)² · VvalGen (x p) M t (B_det x) hle`, by a one-line `routeMCore_phiGen` application (re-check only
  `hC0_det`). **No bridge. No new (forward) telescope** — the banked BACKWARD `chain_telescope`
  (`RouteMAchieverTelescope`) already does the `prod = u·H` divisibility for ANY chain, including `B_det`'s.
  (Codex's "forward `P_k = D_k·C_k + u·G_k` invariant" is the forward mirror — NOT needed; the backward
  suffix form is banked and applies.)

- **A-revisited (fix `genBlkFlatStruct` in place) = 2a under another name.** A "single decoder edit" only
  works if the edited decoder is exactly the full-rank `B_det`. So it is 2a. Building a FRESH `B_det` (not
  mutating the gated `genBlkFlatStruct`, which `routeMCore_phiFlatStructV` and other banked results consume)
  is cleaner and lower-risk than patching the legacy decoder in place. **Build `B_det` fresh; leave
  `genBlkFlatStruct` alone.**

**The deep reason 2a beats 2b:** 2b reconciles TWO charts (the rate chart `phiFlatStructV` vs the det chart
`φ_det`) over opaque widths — a two-decoder `chartIdxEquiv ↔ raw-Params` archaeology. 2a uses ONE chart for
both: the rate is a theorem instance at `B_det`, the det is that same chart's own factorization. No
reconciliation. **This is exactly how the banked anchors (4422/334) work** — they prove the rate and det of
ONE chart (`dlnLoss_chartParams* = u²·U` + `chartParams* = pack ∘ T`), never a bridge to a second chart.

---

## 2. The concrete construction (to formalisation precision)

**The chart** (one decoder, both legs):

    φ_det (x : Fin N → ℝ) : Fin N → ℝ := phiGen (x p) M t (B_det x) hle      (N = routeMAmbient M)

where (keeping the CANONICAL FlatIdx order — KC2/F4, NO per-M Equiv `e_M`):

- `p : Fin N` — the pivot, a chosen residual slot (the canonical `Fin` index of one Aoyagi residual entry).
- `active : Finset (Fin N) := Finset.univ.filter (isAoyagiResidualSlot M T* ∘ decodeFlatIdx)` — the `minAdm`
  residual-block coords (the chosen minimizer `T*`'s `r_j × c_j` blocks, KC1). `active.card = minAdm M`,
  `p ∈ active` (decidable; the count via the KC1 `∑_j r_j·c_j = minAdm` identity).
- **`B_det x : GenBlk M t`** — the FULL-RANK decoder (the fix that defeats D1):
  - the pivot active residual entry is the FIXED `1` (a constant, not read from `x`); the radial scalar
    `u = x p` scales it via the chain's `u • Rmat`/`u • Rfin`;
  - the other `minAdm − 1` active residual entries store their `x`-coords (so `chartParamsGen` produces the
    `u · β` blow-up directions);
  - **`Rfin` is NONZERO** with the fixed-`1` pivot residual entry, so the leaf `C_L = u • Rfin L ≠ 0` — the
    dead leaf slots (D1) are LIVE;
  - spectator Schur slots store their `x`-coords through the `b = aβ` layer-op structure (`T_next = u·Γ −
    β·S`, the load-bearing coupling F1, supplied by the Schur frame `Bmat = [K ; X·K]`, `Rmat = rmatPad(E)`).
  - **EVERY flat coord lands in some output entry** (no dead slots) ⟹ full rank.

**The rate leg** (one line, banked):

    theorem route_phi_det (x) : routeMCore M (φ_det x) = (x p)² · U_det x :=
      routeMCore_phiGen (x p) M t (B_det x) hle (hC0_det x)

with the side goal `hC0_det x : (chainOfMt (x p) M t (B_det x) hle).C 0 · suffix 0 = suffix 0` — the
identity boundary `C 0 = 1`, re-checked for `B_det` exactly as `C0_eq_one_gen` (`RouteMFlatStructV.lean:42`)
does for `genBlkFlatStruct` (reads only `Bmat 0 = I`, `Rmat 0 = 0`, `c_0 = 0` — all preserved by `B_det`).

**The det leg** (the coordinate-level factorization of the SAME chart — the genuine remaining build):

    lemma φ_det_eq (x) : φ_det x = (Q_linear M t) (pivotBlowupOn active p (schurOps M t x))

where `Q_linear` is the canonical-FlatIdx linear pack (det 1, measure-preserving), `pivotBlowupOn active p`
is the banked radial factor (det `|x_p|^{active.card − 1} = |x_p|^{minAdm − 1}`), `schurOps` the det-1 /
spectator-monomial layer-ops. Then `|det Dφ_det| = ∏_j |x_j|^{leafH j}` via the banked
`phiTarget_abs_det_of_factored` (`RouteMPhiTargetDet`) + `composeFold_abs_det` + the factor dets.

**THE EXACT funext/induction TARGET** (`φ_det_eq`): prove `chartParamsGen (x p) M t (B_det x) hle s = (the
factored form's layer s)` by **boundary-prefix induction on the layer index s**, unfolding `B_det` +
`Agen`/`Cgen`/`chainA_apply_castAdd`/`chainA_apply_natAdd` (the banked chain-block accessors,
`RouteMChainBlock`). This is a **per-decoder local statement** (one decoder, decoded-`FlatIdx` cases:
pivot / active-nonpivot / spectator), **NOT** the `chartIdxEquiv K/X/N/E ↔ raw Params` two-decoder
reconciliation. The (2,2,1)/(4,4,2,2)/(3,3,4) anchors prove exactly this shape per-case by
`fin_cases`/`ring` (`chartParams4422_eq_pack_pb`, `chartParams334_eq_pack_T334`); the ∀M version is the
same identity made width-parametric (the dependent-`Fin` reassociation kernel, `lean/CLAUDE.md`).

---

## 3. (3,3,3,3) worked check — the case that forced this (drops at ALL 3 boundaries)

`minAdm(3,3,3,3) = 6`, UNIQUE minimizer `T* = (2,1,0)` (`scripts/check_3333.py`, exact). Per-layer Aoyagi
blocks `(r_j, c_j, r_j c_j)`:

    j=0: (3−2, 3−2) = (1,1) → 1     j=1: (2−1, 3−1) = (1,2) → 2     j=2: (1−0, 3−0) = (1,3) → 3
    active.card = 1 + 2 + 3 = 6 = minAdm.  ✓

So: radial `pivotBlowupOn active p`, `|active| = 6` ⟹ det `|x_p|^{6−1} = |x_p|^5` (= `leafH_pivot`).
**Rate `(x_p)²`** holds despite drops at all 3 boundaries: the banked backward `chain_telescope` gives
`prod = u · Hmat_0` for ANY number of drops (one global pivot ⟹ one global `u`; `scripts/check_3333.py`
schematic). The multi-boundary Schur coupling (`T_next = u·Γ − β·S`, F1) is exactly the chain's per-level
local identity `C_k·A_k = B_k·C_{k+1} + u·E_k` — supplied by `B_det`'s Schur frame, consumed by the banked
telescope. So `φ_det` for (3,3,3,3): `active.card = 6`, det `|x_p|^5 · spectators`, rate `(x_p)²·U`. The
spectator monomials (from the j=0,1 Schur/LDU layer-ops) sit on `k=0` axes (threshold-irrelevant).

This is the validate-small the next tide should run FIRST after (2,2,1): (3,3,3,3) exercises the genuine
multi-boundary coupling that (2,2,1) (single drop) and (4,4,2,2) (single deepest drop) do not. (Alternatively
(2,2,2), minAdm=3, T*=(1,0), drops at 2 boundaries — smaller, also genuinely multi-boundary.)

---

## 4. Residual risk / kill-conditions for the formaliser

1. **(The real remaining work) `φ_det_eq` over opaque widths.** The det leg's factorization
   `chartParamsGen(B_det) = Q ∘ pivotBlowupOn ∘ schurOps` is a genuine dependent-width `funext`/boundary
   induction — substantial. BUT it is tractable in a way 2b is NOT: both sides are the SAME chart's
   coordinates (no two-decoder reconciliation), and the per-case anchors (`chartParams*_eq_pack_T*`) are the
   exact template. Risk: the `chainA`/`Cgen` row-index casts at dependent `Text`/`Wext` widths (the
   `hrow` alignment UPDATE-11 flagged as the hardest cast). Mitigation: validate on (2,2,2)/(3,3,3,3) first.

2. **`B_det` full-rank-ness — the D1 guard.** `B_det` must place EVERY flat coord into some output entry
   (the fixed-1 is the ONLY constant; everything else reads `x`). Verify the chart map is full-rank
   (`det ≠ 0` off `{x_p = 0}`) on the validate-small BEFORE the ∀M det — the D1 lesson (the degenerate
   `genBlkFlatStruct` had `Text(L)·M(L)` dead coords). The `Rfin` nonzero + the pivot fixed-1 is what kills
   the dead slots; confirm leaf `C_L ≠ 0`.

3. **Minimizer choice `T*`.** Fix ONE explicit `T*` with `Mval M T* = minAdm M` (KC1: any argmin; det
   invariant across minimizers). The `active` filter + `hcard : active.card = minAdm` depend on it.

4. **`hC0_det`.** Re-check `C 0 = 1` for `B_det` (reads only `Bmat 0 = I`, `Rmat 0 = 0`, `c_0 = 0`; the
   `C0_eq_one_gen` proof transfers — `B_det 0` must be the identity boundary).

**NONE of these is an open-ended design wall.** The route is decided; the work is bounded (the `φ_det_eq`
opaque-width factorization is the heavy-but-tractable piece, with the anchors as templates).

---

## Close

**Firmest result:** ROUTE 2a — `φ_det x := phiGen (x p) M t (B_det x) hle` with a full-rank `B_det`. Rate =
the banked decoder-agnostic `routeMCore_phiGen` instantiated at `B_det` (one line, re-check `hC0_det`); det =
the coordinate-level factorization `φ_det = Q ∘ pivotBlowupOn active p ∘ schurOps` of the SAME chart
(`phiTarget_abs_det_of_factored`). **No `composeFold = phiFlatStructV` bridge** (2b is FALSE — `phiFlatStructV`
det ≡ 0). Triple-confirmed (structural read of the banked machinery / sympy (3,3,3,3) / xhigh Codex
convergence on 2a).

**Most likely to break it:** the `φ_det_eq` dependent-width factorization (#1) — the `chainA` row-cast
alignment at opaque widths; tractable (same-chart funext, anchor templates) but heavy. **Next construction
that settles it:** build `B_det` + prove `φ_det_eq` on (2,2,2)/(3,3,3,3) (genuine multi-boundary) as the
validate-small, then lift the factorization width-parametrically; the rate + the det-infra + the active/pivot
+ the minAdm correspondence are all banked.

**Strategic note for the controller:** this is NOT a wall — 2a is build-ready. The one judgement that
remains operator/controller-level is whether the `φ_det_eq` opaque-width factorization is charged as one
tide or split (validate-small (2,2,2)/(3,3,3,3) → ∀M lift). The route itself is committed.
