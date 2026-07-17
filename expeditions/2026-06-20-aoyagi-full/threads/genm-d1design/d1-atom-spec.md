# d1-atom-spec — PINNING the native d≤1 heart: the front-collapse (two-matrix product) rank-sector atom + architecture

**Seat:** pen-and-paper (design), `genm-d1design`, Lane 1 follow-on. **Date:** 2026-07-17. **NO Lean.**
Pins the ONE genuinely-new native object the `d≤1` arm of `innerCorankDescent_lt_top` funnels to, BEFORE any
formaliser tide (per controller). Delivers: the exact Lean-friendly statement + widths + the reduction to
`hIH`; the architecture call (standalone vs decorated, with the trade-off); every banked piece + every new
sub-lemma; binding-cell EQUALITY witnesses. Verified: my exact-ℕ census (`scripts/d1_*.py`, `minAdmRec`
transcription) + a decorrelated `local-codex-consult` (xhigh, conclusion withheld — `codex/atom-{prompt,answer}.md`).
Supersedes the `d1-build-plan.md` open-vs-transcription pass with the pinned atom + the architecture decision.

---

## ★ ARCHITECTURE VERDICT (LEAD) — OPT-STANDALONE (no new global decorated IH)

**Recommend the STANDALONE route** (aligns with the operator's lean-away-from-decorations): the `d≤1` native
arm closes on the PLAIN `hIH` + banked atoms + ONE new native atom (the **front-collapse rank-sector**), with
NO new global Gram-decorated `RouteMBoxThresholdFinite` IH. The decorated IH is not merely unpreferred — a
**naked Gram-decorated IH is FALSE** (Codex PROVEN, ε-counter below), so it is not even an available option;
the correct structure is a LOCAL per-cut dispatch, not a carried global weight.

- **Wings (`a=0` wide, `b=0` tall) + `d=1 a<u`: STANDALONE** via the front-collapse rank-sector atom
  (§1). The pushforward `(F, A₁) ↦ F·A₁` is resolved by a **joint SOURCE-incidence-sector `(r,s)` atlas**
  (retain the exceptional variables at the source; do NOT push forward to the density `ρ(W)` first — that is
  what leaves a Gram). Per sector the Jacobian is a pure monomial and reduces to PLAIN `hIH(redChain s M)`.
- **`d=1 a≥u` corank-one: the HARDEST arm — a LOCAL measure-level domain-split** (§2), NOT a global
  decoration. The corank `C` couples to the DEEP product `Q̃ₚ` (not a free next-layer), so its rank-drop is a
  deep event, independent of the front Jacobian (Codex 1, PROVEN) — it produces an irreducible pivot Gram
  `det(Q̃ₚQ̃ₚᵀ)^{−a/2}`. Closure needs a **domain-split by `Q̃ₚ`-conditioning** using the TWO banked inner-Γ
  branches: on the ill-conditioned piece the `_inner_bounded_lt_top` branch (pivot energy lower-bounds the
  loss), on the well-conditioned piece the `_inner_peel_lt_top` (gammaAtom) branch + `hIH`. This is genuinely-
  new to build but uses only banked branches; it is the arm least de-risked on paper (flag §2).

**Nothing here is math-open** (as the controller carries it): every arm is mathematically true (the chain IS
box-finite), NATIVE single-factor (P-invertibility forces `rank F = min(M₀,M₁)`, so the `d≥2` product-corank
tubes are EMPTY — 0/5292 achievable strata reach `minAdm` with the naive charge), and buildable. The cost is
concentrated in ONE new atom (§1) + the `d=1 a≥u` local split (§2). NOT a new cite, NOT a new global decoration.

## 1. THE ATOM — `frontCollapseRankSector_lt_top` (the genuinely-new native heart)

**What it is.** The reduction of the pivot-energy term `frobSq(P·Q̃ₚ) = frobSq(F·Q)` (`F = [P|B₁₂]` for a=0 /
`F = [P;C]` for b=0 / the top-`t` rows of the front in general, `t×M₁`; `Q = prod(tailChain M) A'`, `M₁×q`) to
`hIH`, by recombining the front `F` with the first tail layer `A₁` (`M₁×M₂`) into `W = F·A₁` (`t×M₂`),
collapsing `(t, M₁, M₂) → (t, M₂)` = `redChain t M`, resolved by a source-incidence-sector atlas.

**Exact Lean-friendly statement (widths explicit).** `M : Fin (L+1+1+1) → ℕ`, `t = min (M 0) (M 1)`:

    theorem frontCollapseRankSector_lt_top (M : Fin (L+1+1+1) → ℕ)
        (hIH : ∀ M' : Fin (L+1+1) → ℕ, RouteMBoxThresholdFinite M')
        (c' : NNReal) (hc' : (c':ℝ) < (minAdm M : ℝ) / 2) :
        (∫⁻ F in wingFrontBox M,                              -- F : Fin (M 0) → Fin (M 1) → ℝ, leading t×t minor invertible
          ∫⁻ A' in paramsBoxM (tailChain M) 1,
            ENNReal.ofReal ((frobSq ((Matrix.of F) * prod (tailChain M) A')) ^ (-(c':ℝ)))) < ⊤

with `wingFrontBox M := {F | (∀ i j, F i j ∈ Icc (-1) 1) ∧ IsUnit ((leading t×t block of F))}` and
`(of F) * prod (tailChain M) A' = (F·A₁)·Z_deep`, `A₁` the first tail layer, `Z_deep = prod(M₂,…,M_last)`.

**The reduction (to `hIH`).** Cover `F × A₁`-space by the finite **joint incidence sectors `(r,s)`**,
`r ≤ s ≤ t` (`s =` intermediate/source rank, `r = rank(F·A₁)`); each sector reduces to `redChain s M =
(s, M₂,…,M_last)` at charge `N_s = (M₀−s)(M₁−s)`, i.e. exponent `c_s = c' − N_s/2 < ½·minAdm(redChain s M)`
(cut-soundness), closed by `hIH (redChain s M)`. `min_s [N_s + minAdm(redChain s M)] = minAdm M` EXACTLY
(0/5292, `scripts/d1_charge.py`). Covers BOTH wings in one statement (`F` wide `M₀≤M₁` or tall `M₀≥M₁`); the
top sector is `s = t = min(M₀,M₁)` (Codex correction: NOT `(M₀,M₂,…)` for tall — the tall `W=F·A₁` lies in
`{rank ≤ M₁}`, so the target is `redChain s M`, top `s = M₁`).

**Why the SOURCE-incidence sectors, not a pushforward blow-up (Codex 1, load-bearing).** Pushing forward to
`ρ(W)` first and blowing up `{rank W = r}` leaves a residual Gram/density of the PRODUCT `W·Z_deep` — the
pointwise-fold route, UNSOUND. Instead keep the source `(F, A₁)` variables: a sector CoV indexed by the JOINT
rank pair `(r,s)` has a **pure-monomial Jacobian** `|det DΦ| = u(ξ)·∏_j |z_j|^{ν_j−1}` (`0 < c ≤ u(ξ) ≤ C`),
and integrating the exceptional variables LAST gives a plain reduced-chain integral per sector. An atlas
indexed by `r` alone is insufficient (it conflates the source mechanisms). Single-factor NATIVE: `F` full
rank `t` (P-invertible) ⟹ only `A₁`/the tail drops ⟹ the `(r,s)` incidence is single-factor, distinct from
the `d≥2` non-submersive product-corank `C_m = m²−⌊m²/4⌋` (my `scripts/d1_discriminate.py`: the `rank F < t`
tubes are EMPTY here).

**Banked pieces consumed:** plain `hIH`; `minAdm_le_peelCharge_add_redChain` (`RouteMSJDecoratedCharge:52`, the
charge/cut-soundness); the MP front-split `routeMLayerBoxIntegral_front_split`/`eFront` + `paramsEquivFlat`/
`measurableSet_paramsBoxM` (box CoV plumbing); Tonelli/finite-box plumbing.

**NEW sub-lemmas to build (each its own lemma):**
- **(N1)** the finite joint incidence-sector `(r,s)` cover of `wingFrontBox × A₁`-box (`r ≤ s ≤ t`), measurable,
  covering off a null boundary.
- **(N2)** the per-sector measurable determinantal CoV (the incidence blow-up chart).
- **(N3)** the **Jacobian identity** `|det DΦ| = u(ξ)·∏_j |z_j|^{ν_j−1}`, `0 < c ≤ u(ξ) ≤ C` (pure monomial ×
  bounded unit — the KILL-guard: carry `|det J|`, never drop it).
- **(N4)** the **integral-level sector replacement** `I_{r,s}(c') ≤ C_{r,s}·(1 + I_{redChain s M}(c'−N_s/2))`
  (each sector → plain `hIH`, at charge `N_s`).
- **(N5)** null-boundary removal (`{det = 0}` is null) + the finite sector summation (`ENNReal.sum_lt_top`).

**Diamond guard (`lean/CLAUDE.md`):** raw-`Pi` instances for every matrix product/reindex; `generalize` the
composite (e.g. the CoV image) to a fresh atom across the goal + all hyps (round-7 gotcha, `RouteMSJInteriorR1`).
**Trap:** never the per-`P` CoV `z₀↦P·z₀` (`|det P|^{−M₂}` non-integrable) — use the `F·A₁` source pushforward.

**CLASSIFY: EXPENSIVE-TRANSCRIPTION (native, standalone) — a substantial determinantal-resolution build.**
Est. 800–1500 LoC (the sector atlas + CoV + Jacobian + replacement + summation; the measured record runs 2–5×
short — budget the high end). NOT a cite, NOT a decoration.

## 2. THE `d=1 a≥u` LOCAL DOMAIN-SPLIT (the hardest arm — flag)

`d=1`, `b=1` (a≥1), `a ≥ u`. After the corank-one integration the residual carries the **pivot Gram**
`det(Q̃ₚQ̃ₚᵀ)^{−a/2}`, `Q̃ₚ = W'·Z_deep` a deeper PRODUCT (`u×q`). Codex PROVED (ε-counter, `M=(4,3,2)`,
`t=u=a=q=2`, `b=1`, `c'=5/2`, `Q̃ₚ_ε = diag(1,ε)`: front Jacobian a unit, residual loss → positive const,
`det(Q̃ₚ_εQ̃ₚ_εᵀ)^{−a/2} = |ε|^{−2}`, `∫_{−δ}^{δ}|ε|^{−2} = ∞`): the pivot-Gram divisor is INDEPENDENT of the
front Jacobian (no cancellation), an unconditional last-layer `qbox` FAILS (needs `u≤q ∧ a<q−u+1`, and emits
`det(DDᵀ)^{−q/2}` one layer earlier), and a **naked Gram-decorated IH is FALSE** (diverges near a nonzero
rank-`(u−1)` `Q̃ₚ`).

**The closing structure — a LOCAL domain-split (not a global decoration).** Split the outer `A'`-domain by the
conditioning `σ_min(Q̃ₚ)`:
- **`Q̃ₚ` ill-conditioned (near rank-`(u−1)`):** use `freedSchurLoss_inner_bounded_lt_top` (the pivot energy
  lower-bounds `freedSchurLoss`, so the Γ-integrand is bounded on the finite shear box). The pivot Gram is
  never formed here; the reduced loss reduces via the §1 atom.
- **`Q̃ₚ` well-conditioned (`σ_min(Q̃ₚ) ≥ δ`):** use `freedSchurLoss_inner_peel_lt_top` (= `gammaAtom_aniso_shifted_eq`)
  → `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` bounded by `δ^{−au}`, absorbed into a constant; the reduced loss
  `frobSq(P·Q̃ₚ)^{−(c'−au/2)}` reduces via the §1 atom + `hIH`. Charge closes: `c'−au/2 < ½·minAdm(redChain t M)
  − a(u−1)/2 ≤ ½·minAdm(redChain t M)` (from `minAdm M ≤ a + minAdm(redChain t M)` at `b=1`; verified
  `scripts/d1_charge.py`).

Codex's "OPT-DECORATED (the min of the two branches)" IS this split — the `min{vol(C-Box)·w^{−c'},
K·det(Q̃ₚQ̃ₚᵀ)^{−a/2}·w^{−(c'−au/2)}}` is the a.e. domain-split, NOT a carried global weight. **Banked:** both
inner-Γ branches (`RouteMSJFreedPeel`), `gammaAtom_aniso_shifted_eq`, the §1 atom, `hIH`.
**NEW sub-lemma: (N6)** the measurable `σ_min(Q̃ₚ)`-conditioning domain-split + the a.e. two-branch dispatch +
the `δ`-uniform Gram bound on the well-conditioned piece.

**FLAG (controller's ask — the one arm least de-risked on paper):** the interaction of the TWO degeneracies
on the ill-conditioned piece — `σ_min(Q̃ₚ) → 0` AND the pivot energy `w = frobSq(P·Q̃ₚ) → 0` (when `P` is also
ill-conditioned) — is where my paper analysis is thinnest. The bounded-C branch needs `w > 0`; where `w → 0`
the reduction must fall back to the §1 atom on the ill-conditioned sub-piece. I judge this CLOSES (the §1
atom handles `w → 0`; the bounded branch handles the `Q̃ₚ`-drop where `w` is bounded below), so it is
genuinely-new-to-formalise, NOT math-open — but it is the arm to red-team / build first, and the one where an
unforeseen coupling could force a genuine (mild, local) decoration after all.

**CLASSIFY: EXPENSIVE-TRANSCRIPTION (native, local split) — but the least de-risked; build/red-team FIRST.**

## 3. `d=1 a<u` (the clean leaf) — for completeness

Drop the transverse (`≥0`); the Γ+C integral collapses to `|v_{j₀}|^{−a}·scaledRadialEuclid(w, c')`,
`w = frobSq(P·Q̃ₚ)` `C`-free. **Banked:** `scaledRadialEuclid_lt_top`; `corner_block_lintegral_lt_top` on the
JOINT (pivot⊕corank) sphere (`N = a+u`, the "corner sum" — do NOT apply corner-block to `‖Q̃ₚω‖²` alone, it is
degenerate); `freeBilinear_box_lt_top`/`sumSqND_box_lt_top` (the `b=1` `γ⊗z` leaf); then the §1 atom + `hIH`
for `w`. **NEW: (N7)** the ω-uniformization (`ω = Q_b/‖Q_b‖` swept over `S^{q−1}` by the last free layer with
bounded density). **CLASSIFY: EXPENSIVE-TRANSCRIPTION**, but its pivot term still rides §1.

## 4. Binding-cell EQUALITY witnesses (exact — the operator's binding rule)

Every inequality-shaped condition is TIGHT (marginal) at a concrete cell (`scripts/d1_witnesses.py`):
- **§1 sector charge `c_s < ½·minAdm(redChain s M)`:** tight at the binding sector where `N_s + minAdm(redChain s M)
  = minAdm M` (EQUALITY). E.g. `M=(2,2,1,2)@t=1`: `minAdm=2`, `peelCharge+minAdm(redChain)=1+1=2` (EQUALITY).
- **§2 `d=1 a≥u` boundary `a = u`:** the `a<u` drop-transverse route is marginal (`∫_ω ‖Q̃ₚω‖^{−a}` is the
  rank-`u` form RLCT, finite iff `a<u`, LOG at `a=u`). Cell **`M=(2,2,1,2)@t=1`**: `a=1,b=1,u=1` (`a=u`).
- **§2 well-conditioned qbox range `a < q−u+1`:** Codex's ε-cell **`M=(4,3,2)`** (`t=u=a=q=2`, `b=1`): `a=2`,
  `q−u+1=2−2+1=1`, so `a<1` FALSE → the naked-Gram/qbox route DIVERGES (`∫|ε|^{−2}=∞`) → the domain-split
  (bounded branch) is FORCED here. This is the EQUALITY-at-binding-cell witness that OPT-DECORATED-naked is unsound.
- **`b=0` tall qbox (§1 tall sector) marginal `M₂ = a+1`:** `M=(2,1,2,·)`: `a=1, M₂=2=a+1` (marginal; §1's
  `(r,s)` atlas handles it standalone, unlike the crude one-shot qbox which fails here).
- **`a=0` wide fold boundary `A = 2Δ`:** `M=(1,2,3,3)`, `(1,2,3,4)`: `A=1=2Δ` (the fold is marginal AND unsound
  even here — §1 replaces it with the `(r,s)` atlas).

## 5. Architecture trade-off (STANDALONE vs DECORATED — justified)

- **STANDALONE (recommended).** ONE new native atom (§1) + the `d=1 a≥u` local split (§2, using banked
  branches). No new global IH; the plain driver (`decoratedPeelStep_proof` → `routeMBoxThresholdFinite_of_decoratedPeel`)
  is untouched; footprint stays `[cited_aoyagi_product_corank, propext, Classical.choice, Quot.sound]`.
- **DECORATED (rejected).** A global Gram-decorated `RouteMBoxThresholdFinite` IH carrying `det(leadingGram)^{−w}`
  through the recursion. **Rejected on math, not taste:** Codex PROVED a naked Gram-decorated IH is FALSE
  (diverges near a nonzero rank-`(u−1)` leading Gram outside the qbox range, ε-counter §2) — carrying the weight
  unconditionally does not converge. The only sound use of the Gram branch is the LOCAL well-conditioned split
  (§2), which needs no global carrier. So STANDALONE is not just preferred (operator's lean) — it is the sound
  structure; the decorated global IH is unsound.

## Close

- **Firmest.** The `d≤1` native arm funnels to ONE new NATIVE atom — the **front-collapse rank-sector**
  (`frontCollapseRankSector_lt_top`, §1): reduce `frobSq(F·prod(tailChain M) A')` to `hIH(redChain s M)` via a
  joint SOURCE-incidence-sector `(r,s)` atlas (pure-monomial Jacobian, single-factor NATIVE), covering both
  wings; plus the `d=1 a≥u` LOCAL domain-split (§2, two banked inner-Γ branches). Architecture: STANDALONE (no
  new global decorated IH — the naked Gram-decorated IH is FALSE, Codex PROVEN). Charge airtight (0/5292).
- **Most likely to break.** (i) `d=1 a≥u` (§2) — the double degeneracy (`σ_min(Q̃ₚ)→0` ∧ `w→0`); build/red-team
  FIRST. (ii) The `(r,s)` atlas Jacobian identity (N3) being a clean monomial in the tall sector — the tall
  incidence is subtler than the wide (Codex flagged the tall target correction). (iii) If the source-incidence
  CoV secretly reintroduces a product-Gram in some sector, the §1 standalone claim weakens toward §2's split.
- **Next.** Commission the §1 atom build (start with the WIDE `a=0` sectors — the cleanest, `F` surjective —
  then the tall, then wire the `d=1` dressing), with the §2 `a≥u` split red-teamed first. The `(r,s)` atlas +
  Jacobian (N1–N3) is the genuinely-new heart; N4–N5 is the reduction wire; the banked list is complete.
  Recommend surfacing the standalone-vs-decorated call to the operator (STANDALONE, math-forced) before the tide.

Files (absolute): `…/threads/genm-d1design/d1-atom-spec.md` (this); `d1-build-plan.md` (the open-vs-transcription
pass); `codex/atom-{prompt,answer}.md` (decorrelated, OPT-STANDALONE wings + OPT-DECORATED-as-local-split a≥u);
`scripts/d1_{charge,wings,discriminate,witnesses}.py`. Socket: `RouteMSJDecoratedPeelStep.lean` @ origin/genm-integration.
