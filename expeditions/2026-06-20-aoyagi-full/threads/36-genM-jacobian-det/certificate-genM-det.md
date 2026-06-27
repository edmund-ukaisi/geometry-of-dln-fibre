# Certificate — the ∀M det route (build-ready: ROUTE (i) PARAMETRIC)

**Seat:** pen-and-paper (witness). **Date:** 2026-06-27. The last design question before the R1-lower
atom closes ∀M: how to build the ∀M chart Jacobian `|det Dφ_M| = |x_p|^{minAdm−1} · spectators`. Extends
`certificate-rate-det-route.md` (ROUTE 2a: `φ_det = phiGen(B_det)`, rate banked). This picks the DET-leg
construction.

Decorrelated xhigh Codex (independent, sharp strategic framing — converges on route (i) parametric):
`codex/genM-det-route-{prompt,answer}.md`. Exact scripts: `scripts/check_3333_det.py`.

**VERDICT — ROUTE (i) PARAMETRIC.** Both routes need a bridge; route (i) puts it at the RIGHT level — ONE
width-parametric extensional funext `chartParamsGen(x_p, B_det x) = pack_M (T_M x)` via the BANKED
`chainA_apply_castAdd/natAdd` entry laws and the BANKED parametric factor maps (`schurFrameMap`/`lduCoreMap`,
`{t r c : ℕ}`-parametric). Route (ii) (direct chain-det telescope) is a NO-GO disguise: it needs the SAME
factorization bridge at the harder fderiv level before the det engine can fire. **Not a wall** — route (i)
is a contained bridge with 4 working templates; the only bad part of the anchors (explicit coordinate
tables) is exactly what the parametric lift removes.

---

## 1. The decision: route (i) parametric, NOT route (ii) (the structural reason)

**Both routes ultimately need "the chart equals a product of factors with known dets."** The question is at
which level that obligation lands.

- **Route (ii) — direct chain-det telescope — is a bridge in disguise, and HARDER.** `φ_M` is NONLINEAR (the
  layers `A_k = chainA(N_k, W_k, C_{k+1})` are products/blocks of read coords). Its Jacobian does NOT
  telescope just because the chart was DEFINED by a chain recursion. To telescope `|det Dφ_M| = ∏_s
  (per-layer block det)` you must first prove `fderiv φ_M x = DF_n(…) ∘ … ∘ DF_1(x)` — the DERIVATIVE-level
  version of the SAME factorization bridge, plus product-rule + block-embedding noise, BEFORE the banked det
  monoid-hom (`general_composed_clm_abs_det`, `RouteMAchieverGeneralDet`) can fire. **Strictly more work, and
  untested.** (Codex Q2, my independent read.)

- **Route (i) — factorization `φ = Q_linear ∘ T_M` — relocates the bridge to the cleanest level.** The
  obligation is `chartParamsGen(x_p, B_det x) = pack_M (T_M x)` (the chain's layers EQUAL the explicit
  factored form) — a `Params`-level extensional `funext s; ext i j` over the layer matrices, discharged by
  the BANKED `chainA_apply_castAdd/natAdd` entry laws (already the method of `Agen0/1_222_eq`,
  `RouteM222Det.lean:227,365`). The det then telescopes through the LINEAR composite `T_M` =
  `composeFold [radialFactor, schurFactors, lduFactors, shearFactors]` via the banked
  `general_composed_clm_abs_det`/`composeFold_abs_det`.

**The decisive fact:** the 4 banked anchors (`(2,2,1)`,`(2,2,2)`,`(3,3,4)`,`(3,3,3,3)`) ALL use route (i).
The bad part was the EXPLICIT coordinate tables (`T222_apply = ![x0−x1·x2, x4·x1, …]`, `pack222 = !![w4,w1;…]`,
the `(3,3,3,3)` `K7sub`/`K7tl`/`K7br` LDU block split `7 = 4+3`), NOT the factorization STRATEGY (the factor
order, pivot placement, spectator factors, final det shape are all validated). The ∀M-clean move is to make
`T_M`/`pack_M` width-parametric functions of `(M, t*, the residual blocks r_j×c_j)`, and prove the bridge
ONCE by indexed extensionality. **The parametric factor maps are ALREADY banked** (`RouteMFactorMaps`:
`schurFrameMap {t r c : ℕ}` det `|det K|^{r+c}`, `lduCoreMap {t : ℕ}` det `∏|q_i|^{2(t−1−i)}`) — so the
`(3,3,3,3)` `K7sub` explicit blocks were a per-case INSTANTIATION of `schurFrameMap`/`lduCoreMap`, not a
fundamental obstruction.

---

## 2. The concrete construction (to formalisation precision)

Keep CANONICAL `FlatIdx` order (F4, banked — NO per-M bijection `e_M`). Fix one explicit minimizer `t* = tStar M`
(KC1; `Mval_tStar_eq = minAdm`, banked). Let `rBlock j, cBlock j` be the achiever residual-block sizes
(banked, `sum_rBlock_cBlock_eq_minAdm`).

**The chart** (ROUTE 2a, banked rate): `φ_M x := phiGen (x p) M (tStar M) (B_det M x) hle`.

**The DET-leg factorization** `φ_M = Q_M ∘ T_M`:

- **`Q_M := paramsEquivFlat M ∘ pack_M`** — `pack_M : (Fin N → ℝ) → Params M` the canonical-FlatIdx reshape
  (a coordinate permutation, `|det| = 1`, measure-preserving via `measurePreserving_paramsPack_of_flatIdxEquiv`
  at the canonical `Fintype.equivFin (FlatIdx M)`). Width-parametric (no per-M table; the canonical equiv).

- **`T_M : (Fin N → ℝ) → (Fin N → ℝ)` = `composeFold (radialFactor :: schurLduFactors)`** — a list of
  full-ambient `ChartFactor N` (banked `composeFold`/`ChartFactor` interface):
  - **`radialFactor active p`** (banked, `RouteMRadialFactor`): `active : Finset (Fin N)`, decidable, the
    `minAdm` residual-block coords (filter on decoded `FlatIdx` for the `t*`-residual slots), `p ∈ active`.
    `active.card = minAdm M` (KC1). Det `|x_p|^{active.card − 1} = |x_p|^{minAdm − 1}` (`radialFactor_abs_det`).
  - **per-boundary `schurFactor`/`lduFactor`/`shearFactor`** (banked parametric maps `schurFrameMap {t r c}`,
    `lduCoreMap {t}`, conjugated to full-ambient `ChartFactor N` via the banked CLE engine
    `RouteMRoleCLE`/`cleConjFactor`): det `|det K_j|^{r_j+c_j}` (Schur), `∏|q_i|^{2(t−1−i)}` (LDU), `1` (shear).
    These carry the SPECTATOR monomials on `k=0` axes (threshold-irrelevant).

  The factor list is INDEXED by the boundary `j` (a `List.ofFn`/`List.range` over `Fin L`), each factor the
  parametric map at the boundary's `(t_j, r_j, c_j)` widths. **No explicit per-coordinate vector — the factors
  are the banked parametric maps.**

**The DET telescope** (banked, one `rw`): `|det Dφ_M| = |det Q_M| · |det DT_M| = 1 · ∏_j (factor det) =
∏_j |x_j|^{leafH_M j}` via `general_composed_clm_abs_det` (`RouteMAchieverGeneralDet`) +
`composeFold_abs_det` + the per-factor `_abs_det` lemmas. `leafH_M p = minAdm M − 1` (the radial; the binding
axis), spectators on `k=0` axes.

**THE ONE BRIDGE FUNEXT (the genuine remaining build):**

    lemma chartParamsGen_eq_pack_T_M (x) :
      chartParamsGen (x p) M (tStar M) (B_det M x) hle = pack_M (T_M x)

proved `funext s; ext i j`, reducing each layer `Agen s` to the factored form's layer via the BANKED
`chainA_apply_castAdd` (kept row = `C_{s+1} − N_s·W_s`) / `chainA_apply_natAdd` (lift row = `W_s`) entry laws
— a WIDTH-PARAMETRIC extensional proof over opaque `Text`/`Wext`, NOT the per-case `!![…]`/`fin_cases` tables.
This is the SAME shape as the banked `Agen0/1_222_eq` + `chartParams222_eq_pack_T`, made parametric. (Step-3
`chartParamsGen_eq` has already shown the kept-row law closes uniformly ∀M — that is exactly this funext's core.)

---

## 3. (3,3,3,3) worked check — drops at ALL 3 boundaries (the forcing case)

`minAdm(3,3,3,3) = 6`, unique `t* = (2,1,0)` (`scripts/check_3333_det.py`, exact). Aoyagi residual blocks
`(r_j, c_j, r_j c_j)`:

    j=0: (3−2, 3−2) = (1,1) → 1     j=1: (2−1, 3−1) = (1,2) → 2     j=2: (1−0, 3−0) = (1,3) → 3
    active.card = 1 + 2 + 3 = 6 = minAdm.  ✓

- **Radial** `radialFactor active p`, `active.card = 6` ⟹ det `|x_p|^{6−1} = |x_p|^5` (= `leafH_pivot`).
- **Spectators** (per-boundary Schur/LDU factors): `|u1|^4 · |u4|^2 · |u9|^3` (the banked `RouteM3333Atom`
  values — Schur `|det K_j|^{r_j+c_j}` + LDU on the `k=0` axes; threshold-irrelevant).
- **Total** `|det Dφ_3333| = |u0|^5 · |u1|^4 · |u4|^2 · |u9|^3` — matches the banked anchor EXACTLY.

This is the validate-small to run FIRST for the parametric lift (3 boundaries exercises the multi-boundary
Schur/LDU coupling that the single-drop anchors do not). The (2,2,2) route-2a det (`phi222_abs_det =
|x0|²·|x4|`) is banked as the L=2 template.

---

## 4. Active-set placement (KC2/F4 — CONFIRMED sufficient)

Canonical `FlatIdx` + decidable `active : Finset (Fin N)` with `active.card = minAdm M` and `p ∈ active`
SUFFICES for the radial `|x_p|^{minAdm−1}` (Codex Q4 confirms; `pivotBlowupOnDeriv_det` needs only
`active.card` + `p ∈ active`, banked `radialFactor_abs_det`). The one side-condition: match the banked
`pivotBlowupOn` pivot convention (`p ∈ active`, so det `|x_p|^{active.card − 1}`). **No `e_M` bijection.**

---

## 5. Residual risk / kill-conditions for the formaliser

1. **(The real remaining work) the parametric bridge `chartParamsGen_eq_pack_T_M` over opaque widths.** The
   `funext s; ext i j` reducing `Agen s` to the factored layer via `chainA_apply_castAdd/natAdd`. Tractable
   (step-3 showed the kept-row law uniform; the anchors are the L=2/L=3 templates) but it IS the dependent-`Fin`
   reassociation kernel (`lean/CLAUDE.md`) — the `hrow` row-cast alignment is the hardest step. Validate on
   (3,3,3,3) first.

2. **`T_M` as a parametric `composeFold` of the banked factor maps.** The factor MAPS (`schurFrameMap`,
   `lduCoreMap`) are banked parametric; the open work is the full-ambient conjugation per boundary (the
   `cleConjFactor`/`RouteMRoleCLE` engine, banked) assembled as a `List.ofFn` over `Fin L`, and the order
   (deepest-first / the chain boundary order). RISK: the per-boundary CLE `role` reindex (which FlatIdx slots
   feed boundary `j`'s `SchurInc t_j r_j c_j`) — a decidable slot map, not a bijection. Guard: the factor det
   list must sum (telescope) to the FULL `leafH_M` (spectators included), matched against `composeFold_abs_det`.

3. **`B_det M` full-rank ∀M (the D1 guard).** The decoder must place EVERY flat coord into some output entry
   (fixed-1 pivot residual + nonzero `Rfin`); verify `det ≠ 0` off `{x_p = 0}` on the validate-small. (The
   (2,2,2) `B_det222` is the L=2 template; nonzero `Rfin 2 = !![1, x7]` killed the dead slots.)

4. **`leafH_M` spectator bookkeeping.** `leafH_M p = minAdm − 1` (banked-shape `leafH_pivot`); the spectator
   exponents (per-boundary Schur `r_j+c_j` powers of `det K_j`, LDU `2(t−1−i)`) must be carried so
   `∏|x_j|^{leafH_M j}` matches `composeFold_abs_det`. All on `k=0` axes (threshold-irrelevant, but the det
   product must still account for them — a vanishing spectator power would break the telescope match).

**NONE is an open-ended design wall.** Route (i) parametric is a contained bridge problem; the factor maps,
the det telescope, the active-Finset, the rate, and the minAdm correspondence are all banked.

---

## Close

**Firmest result:** ROUTE (i) PARAMETRIC. `φ_M = Q_M ∘ T_M`, `T_M = composeFold` of the BANKED parametric
factor maps (radial `|x_p|^{minAdm−1}` + per-boundary Schur/LDU/shear spectators), det via the BANKED
`general_composed_clm_abs_det`. The ONE bridge `chartParamsGen = pack_M ∘ T_M` is a width-parametric funext
via `chainA_apply_castAdd/natAdd` — NOT the explicit anchor tables, NOT the route-(ii) fderiv-as-product
disguise. Triple-confirmed (structural read of the 4 anchors + banked engine / sympy (3,3,3,3) / xhigh Codex
convergence).

**Most likely to break it:** the parametric bridge funext's `hrow` row-cast over opaque widths (#1) — the
dependent-`Fin` kernel; tractable (anchor templates, step-3 uniformity) but the heavy piece. **Next
construction that settles it:** the parametric `T_M`/`pack_M` + the bridge funext on (3,3,3,3) (genuine
3-boundary), then the ∀M lift; the factor maps, det telescope, active-Finset, rate are banked.

**Strategic note for the controller:** route (i) parametric is committed; route (ii) is rejected (a harder
bridge in disguise). The one judgement left is the charge split — recommend (3,3,3,3) parametric-bridge
validate-small FIRST (it exercises the multi-boundary Schur/LDU the L=2 anchors do not), then the ∀M
`List.ofFn` lift. The route is decided; the work is bounded.
