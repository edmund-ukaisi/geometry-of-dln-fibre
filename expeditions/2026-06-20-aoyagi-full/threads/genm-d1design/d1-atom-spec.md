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
- **`d=1 a≥u` corank-one: the HARDEST arm — RE-PINNED (§2), the §1 atlas on the EXTENDED tail** (d1split
  red-team + corners Codex, decorrelated). **My earlier "absolute-`σ_min` domain-split" was UNSOUND** (d1split
  PROVEN: it routes the radial cone `{Q̃ₚ→0}` to the bounded branch, dropping the corank charge, diverging on a
  positive-length `c'`-window for 1221/1395 `a≥u` cuts). The correct structure: write the corank energy as a
  free-front Wishart `frobSq([C|Γ]·Q̂)`, `[C|Γ]` free `a×(u+1)`, `Q̂=[Q̃ₚ;Q_b]` the extended tail — the **§1
  source-incidence atlas applied to `([C|Γ], Q̂)`, pivot-regularized** by `w=frobSq(P·Q̃ₚ)` (d1split's radial-peel
  `‖PΘ‖²≥σ_min(P)²>0` on the `Q̃ₚ`-sphere is the regularizer). Tracks `(rank Q̃ₚ, rank Q̂)`, monomial Jacobian, →
  plain `hIH`, **no `‖Q_b‖^{−a}` weight**. At `b=1` the corank leaf is the banked `freeBilinear` (`γ⊗Q_b`). So
  `d=1 a≥u` UNIFIES with §1 (same atlas machinery, extended tail + regularizer), not a separate split.

**Nothing here is math-open** (as the controller carries it): every arm is mathematically true (the chain IS
box-finite), NATIVE single-factor (P-invertibility forces `rank F = min(M₀,M₁)`, so the `d≥2` product-corank
tubes are EMPTY — 0/5292 achievable strata reach `minAdm` with the naive charge), and buildable. The cost is
concentrated in ONE atlas mechanism (§1, extended to `Q̂` for `d=1 a≥u`, §2). NOT a new cite, NOT a global
decoration (the naked Gram-decorated IH is FALSE — d1split ε-counter). **Two soundness corrections from the
red-team are folded into §2** (the absolute-`σ_min` split is unsound; the banked `_inner_peel` emits the CORANK
Gram `‖Q_b‖^{−a}`, not the pivot Gram — both my earlier §2 slips).

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

**NEW sub-lemmas to build (each its own lemma).** ★ **BUILD-ONCE boundary (controller's sequencing):** N1–N3
are the SHARED atlas + Jacobian — build them ONCE, reusable by §2 (which instantiates the same atlas on the
extended tail `Q̂` with a free front `[C|Γ]` + the pivot core). N4–N5 are instantiated PER CASE (§1 pure vs §2
regularized). To make N1–N3 reusable, state them for a **general nonneg measurable core** `κ(Y) ≥ 0` in the
loss `(κ(Y) + frobSq(G·Y))^{−c'}`, front `G` free, tail `Y` a product: **§1 = `κ ≡ 0`** (pure); **§2 = `κ(Y) =
frobSq(P·Q̃ₚ)`** the pivot energy (`Q̃ₚ` = top-`u` rows of `Y = Q̂`). The `(r,s)` decomposition + monomial
Jacobian are `κ`-INDEPENDENT (they read only the `G·Y` product structure) — so N1–N3 transfer verbatim; only
N4 (the per-sector reduction / charge) differs (§2's `κ>0` is the radial regularizer that buys the corank
charge at the `{Y→0}` corner, `‖PΘ‖²≥σ_min(P)²>0`).
- **(N1, shared)** the finite joint incidence-sector `(r,s)` cover of `frontBox × Y`-box (`r = rank(G·Y) ≤ s =
  relative-row/intermediate rank ≤ min`), measurable, off a null boundary. [§2: `(rank Q̃ₚ, rank Q̂)`, RELATIVE-row
  incidence — when `q ≤ u`, `Q_b→0` gives no total-rank drop, so track relative rows, not total rank.]
- **(N2, shared)** the per-sector measurable determinantal CoV (the incidence blow-up chart).
- **(N3, shared)** the **Jacobian identity** `|det DΦ| = u(ξ)·∏_j |z_j|^{ν_j−1}`, `0 < c ≤ u(ξ) ≤ C` (pure
  monomial × bounded unit — the KILL-guard: carry `|det J|`, never drop it). `κ`-independent.
- **(N4, per-case)** the **integral-level sector replacement** `I_{r,s}(c') ≤ C_{r,s}·(1 + I_{redChain s M}(c'−N_s/2))`
  (each sector → plain `hIH`, at charge `N_s`). §2 adds the pivot-core regularization at the `{Q̃ₚ→0}` corner.
- **(N5, per-case)** null-boundary removal (`{det = 0}` is null) + the finite sector summation (`ENNReal.sum_lt_top`).

**Diamond guard (`lean/CLAUDE.md`):** raw-`Pi` instances for every matrix product/reindex; `generalize` the
composite (e.g. the CoV image) to a fresh atom across the goal + all hyps (round-7 gotcha, `RouteMSJInteriorR1`).
**Trap:** never the per-`P` CoV `z₀↦P·z₀` (`|det P|^{−M₂}` non-integrable) — use the `F·A₁` source pushforward.

**CLASSIFY: EXPENSIVE-TRANSCRIPTION (native, standalone) — a substantial determinantal-resolution build.**
Est. 800–1500 LoC (the sector atlas + CoV + Jacobian + replacement + summation; the measured record runs 2–5×
short — budget the high end). NOT a cite, NOT a decoration.

## 1bis. The BOUNDED sub-case (`M₂ ≤ b`) CoV — reaches the threshold WITHOUT Cauchy-Binet (lane1shell's question)

lane1shell asked whether the bounded a=0 base (`M₂ ≤ b`, `b = M₁−M₀`) can be closed WITHOUT Cauchy-Binet
(`det(FFᵀ) = Σ_σ (det F_σ)²`, absent from Mathlib v4.29 + the codebase) or coarea (also absent). **YES — via
an orthonormal-complement extension + a single SQUARE CoV. The GS/Gram machinery it needs is already banked
(`det_gram_cons` + `projection_rpow_lintegral_uniform`, assembled as `qbox_lintegral_lt_top`).**

The per-dominant-minor CoV is the trap: it gives `|det F_σ|^{−M₂}` (`∫_{F_σ box} |det F_σ|^{−M₂}` diverges for
`M₂ ≥ 1`, codim`{det=0}=1`) because a single minor wastes F's extra width. The fix uses ALL of F via its Gram,
obtained by a square CoV — NOT the minor sum:

1. **Extend `F` to a square `[F;S]` (`M₁×M₁`).** On the full-row-rank locus (a.e. on `wingFrontBox`, P-block
   invertible), let `S` be an orthonormal basis of `(rowspace F)^⊥` (`(M₁−M₀)×M₁`), via Mathlib `gramSchmidt`
   (measurable in F on the full-rank locus). Then `F Sᵀ = 0` and `S Sᵀ = I`, so the block-Gram is
   block-diagonal: `det([F;S][F;S]ᵀ) = det(FFᵀ)·det(SSᵀ) = det(FFᵀ)`, hence `|det [F;S]| = det(FFᵀ)^{1/2}`.
   **This is the block-Gram-determinant identity — elementary (`FSᵀ=0` ⟹ off-diagonal blocks vanish), NOT
   Cauchy-Binet.**
2. **Single SQUARE CoV per fixed F** (`lintegral_comp_rightMulₚ`, banked, `RouteMSJGammaAtom:74`): transpose to
   `B := A₁ᵀ` (`M₂×M₁`) and right-multiply by `[F;S]ᵀ` (square `M₁×M₁`, `det ≠ 0`). Jacobian
   `|det [F;S]ᵀ|^{M₂} = det(FFᵀ)^{M₂/2}`. The image `([F;S]·A₁) = (F·A₁, S·A₁) = (W, R)`, `R = S·A₁` the slack.
   So `∫_{A₁ box} g(F·A₁) dA₁ = det(FFᵀ)^{−M₂/2} · ∫_W g(W) [∫_R 1_{A₁∈box} dR]`; the inner `R`-slice volume is
   `≤ (2√(M₁M₂))^{(M₁−M₀)M₂} =: C`, **F-INDEPENDENT** (S orthonormal ⟹ the slice is a fixed box's bounded
   projection, no det-of-F factor).
3. **Factor + close.** `∫_F ∫_{A₁} g(F·A₁) ≤ C·[∫_{F ∈ wingFrontBox} det(FFᵀ)^{−M₂/2}]·[∫_{W box'} g(W)]`.
   The first factor is **`qbox_lintegral_lt_top` DIRECTLY** with `(qbox-b, qbox-q, exp) = (M₀, M₁, M₂)`:
   converges iff `M₀ ≤ M₁ ∧ M₂ < M₁−M₀+1`, i.e. **`M₂ ≤ b`** (qbox is already the assembled GS-norm recursion
   `det_gram_cons` + `projection_rpow_lintegral_uniform` — the "GS-normed density" lane1shell asked about is
   banked INSIDE it). The second factor is `∫_{W ∈ [−M₁,M₁] box'} g(W) = M₁^{M₀M₂−2c'}·hIH(redChain M₀ M)` (the
   box'-scaling is a constant via `frobSq` homogeneity, `frobSq_rmatMul_smul`), finite since `c' < ½·minAdm(M)
   ≤ ½·minAdm(redChain M₀ M)` (peelCharge = 0 at a=0).

So the bounded base = `[qbox(M₂≤b)] × [hIH]`, NO Cauchy-Binet, NO coarea, NO minor sum. The Gram is of the FREE
front F (not a product), so `qbox` applies directly. **Consumed banked:** `lintegral_comp_rightMulₚ`,
`qbox_lintegral_lt_top`, `frobSq_rmatMul_smul`, `hIH`; **Mathlib:** `gramSchmidt` / `OrthonormalBasis` of the
row-complement submodule. **NEW (small):** the block-Gram-det identity `|det[F;S]| = det(FFᵀ)^{1/2}` (elementary,
lane1shell landed it via `det_fromBlocks_zero₂₁`), the F-independent slice-volume bound. **Recommend route (a)
over building Cauchy-Binet (c)** — it reuses the banked square-CoV + qbox and skips the ~150–400 LoC Cauchy-Binet
brick AND the minor-chart cover.

**POINTWISE-bound-then-integrate (lane1shell's refinement — removes the measurable-`S(F)` delicacy).** Do NOT
carry `S` as a measurable function of F. For a.e. (full-rank) `F`, the fixed-F bound
`∫_{A₁ box} g(F·A₁) ≤ C·det(FFᵀ)^{−M₂/2}·∫_{W box'} g` holds with an EXISTENTIAL `S` per F — its RHS is
`S`-INDEPENDENT (`C` and `det(FFᵀ)` do not depend on the choice of `S`; different `S` just relabels the
integrated-out slack `R`). Then `F ↦ ∫_{A₁} g(F·A₁)` is measurable (a partial `lintegral` of a jointly
measurable integrand — automatic), so `lintegral_mono` over the F-box gives
`∫_F ∫_{A₁} g(F·A₁) ≤ C·[∫_W g]·∫_F det(FFᵀ)^{−M₂/2}` (the F-independent `C·∫_W g` pulls out; `qbox` closes the
last factor). No measurable selection of `S`; the `{det=0}` null set is harmless (RHS `= +∞` there). This is
strictly cleaner than a measurable-S(F) pushforward and is the intended form.

**Row-complement `S` construction.** `S : (M₁−M₀)×M₁` with `S·Fᵀ = 0 ∧ S·Sᵀ = 1` = an orthonormal basis of
`(rowspace F)^⊥` (a submodule of `ℝ^{M₁}` of `finrank = M₁−M₀`, from rows-independent ⟺ `det(FFᵀ)≠0` +
`Submodule.finrank_add_finrank_orthogonal`). Take Mathlib `OrthonormalBasis (Fin (M₁−M₀))` of that complement,
stack as rows → `S` (orthonormal ⟹ `S·Sᵀ=1`; in the complement ⟹ `S·Fᵀ=0`). The banked `exists_ortho_ext`
(`RouteMSJOrthoExtend`) is COLUMN-oriented (extends orthonormal columns) — reusable only via `gramSchmidt`(F's
rows)→Q(orthonormal rows)→`Qᵀ`(orthonormal cols)→extend→transpose, i.e. more plumbing than the direct
complement-`OrthonormalBasis` route. Use the submodule route.

**LOG sub-case (`M₂ = b+1`):** `qbox` is MARGINAL here (needs `M₂ < b+1` STRICT), so `∫_F det(FFᵀ)^{−M₂/2}`
is log-divergent. Close by a **δ-fold**: run the CoV at `det(FFᵀ)^{−(M₂−δ)/2}` (qbox strict at `M₂−δ < b+1`)
and pay the `δ` from the loss via `one_add_log_inv_le_rpow` — the headroom `c' < ½minAdm(M)` absorbs it (the
same δ-slack as the corank-one tie). **POWER sub-case (`M₂ ≥ b+2`):** the Gram is genuinely non-integrable
(`qbox` fails), so the front DOES NOT separate from the loss — this is where the full `(r,s)` source-incidence
atlas (§1, N1–N5) is required (the loss must control the rank-drop, per Codex 2b), NOT the §1bis CoV.

## 2. THE `d=1 a≥u` ARM — RE-PINNED (d1split red-team + corners Codex; my earlier absolute-σ_min split was UNSOUND)

**⚠ SUPERSEDES the earlier "LOCAL domain-split by absolute `σ_min(Q̃ₚ)`" pin below — it was UNSOUND, and my
corner-(ii) "tall-collapse" resolution was also wrong. Corrected via d1split (`redteam-cert.md`) + my corners
Codex (`codex/corners-{prompt,answer}.md`, decorrelated) + exact-ℕ.** Two soundness corrections landed:
1. **d1split (PROVEN):** dispatching by the ABSOLUTE `σ_min(Q̃ₚ) < δ` is UNSOUND — the radial corner
   `{Q̃ₚ → 0 radially, comparable singular values, Q_b = O(1)}` (positive-measure cone, `σ_min < δ`) is routed
   to the bounded branch, which DISCARDS the corank charge `ab/2` and DIVERGES on `c' ∈ (½minAdm(redChain u M),
   ½minAdm M)` — a window of positive length on **1221/1395** `a≥u` cuts. Binding cell `M=(4,3,2) @ t=2`: true
   `~ε^{5−2c'}` (conv `c'<3`) vs bounded majorant `~ε^{3−2c'}` (conv only `c'<2`); window `c'∈(2,3)`.
2. **Cert correction:** the banked `_inner_peel` emits the **CORANK** Gram `det(Q_bQ_bᵀ)^{−a/2} = ‖Q_b‖^{−a}`
   (`R = Q_b`), NOT the pivot Gram `det(Q̃ₚQ̃ₚᵀ)^{−a/2}` (that is `R = Q̃ₚ`, a different step). My earlier §2
   conflated them.

**The correct structure — ONE joint source-incidence atlas over the EXTENDED tail, pivot-regularized (this
UNIFIES with §1, no separate machinery).** Write the corank energy as a single free-front Wishart:
`frobSq(C·Q̃ₚ + Γ·Q_b) = frobSq([C|Γ]·Q̂)`, `[C|Γ]` a FREE `a×(u+1)` block, `Q̂ = [Q̃ₚ; Q_b]` the extended tail
`((u+1)×q)`. So `freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq([C|Γ]·Q̂)` — the §1 source-incidence atlas applied to
`([C|Γ], Q̂)`, with the pivot term `w = frobSq(P·Q̃ₚ)` as a **regularizer**. The atlas tracks the JOINT ranks
`(rank Q̃ₚ, rank Q̂)` (Codex resolution (b), PROVEN required), monomial Jacobians, each stratum → PLAIN `hIH`,
**no `‖Q_b‖^{−a}` weight** (that artifact only arises from peeling `Γ` alone; the joint `[C|Γ]` atlas avoids it).
- **d1split's radial-peel is the pivot regularizer.** Blow up `ρ = ‖Q̃ₚ‖`, `Q̃ₚ = ρΘ`; on the sphere
  `‖PΘ‖² ≥ σ_min(P)² > 0` (P injective, `Θ ≠ 0`; does NOT need `Θ` full rank — arity-independent, `codex/corners`
  (i)(a) PROVEN). This positive core lets the atlas close the `{Q̃ₚ → 0}` corner KEEPING the corank charge; the
  radial integral reaches the FULL `½minAdm(M)`. Equivalently: dispatch by RELATIVE conditioning
  `σ_min(Q̃ₚ)/‖Q̃ₚ‖`, not absolute (the radial corner has good relative conditioning → the peel side).
- **The corank-one leaf is banked.** At `b=1`, `Γ·Q_b = γ⊗Q_b` (rank-one outer product), so the joint corner is
  `‖P·Q̃ₚ‖² + frobSq(γ⊗Q_b)`-shaped, closed by the banked `freeBilinear_box_lt_top` (`γ⊗z`, `sumSqND_box_lt_top`)
  reaching `½·min(a+1, D+1)`. Codex's (4,3,2) model `‖X‖² + ‖γ‖²‖r‖²` (`X∈ℝ⁴, γ,r∈ℝ²`) has threshold
  `4/2 + min(2,2)/2 = 3 = full ½minAdm(M)` (vs `2` if the bilinear `‖γ‖²‖r‖²` is dropped) — so KEEPING the
  bilinear corank incidence (resolution (b)) reaches the full threshold; dropping it (bounded-Γ, (a)) undershoots.

**CLASSIFY: EXPENSIVE-TRANSCRIPTION (native, standalone) — the §1 atlas machinery extended to `Q̂` + the pivot
regularizer + the banked FreeBilinear leaf. NEEDS the atlas (already the §1 core), NOT a new global decoration
(the naked Gram-decorated IH is FALSE — d1split ε-counter). No `‖Q_b‖^{−a}` artifact.**

### 2-corners — VERIFIED (controller's ask, before the §2 tide)
- **Corner (i) deeper-arity `Q_p` a PRODUCT — ABSORBED-NATIVE (Codex + exact-ℕ agree).** The sphere bound
  `‖PΘ‖²≥σ_min(P)²>0` is arity-independent (P is the `u×u` outer pivot). The pivot term reduces via the §1
  **wide** atom (`F=[P|B₁₂]`, `u×(u+1)`) at the shifted charge `s = c'−a/2 < ½minAdm(redChain u M)` — **but this
  is the §1 atom, NOT plain hIH**: `Q̃ₚ = F·A₁` collapse is a PRODUCT with singular source-rank pushforward, so
  it needs the §1 source-incidence atlas (product-aware, delivers the right product-shell threshold via
  `hIH(redChain u M)`; Codex (i)(b)). Charge closes 0/3276 (cut-soundness, `scripts/d1_corners.py`, arity-general).
  Deep-tail degeneracy (`Q̃ₚ→0` with `Q_p` near its own rank-drop): shell law worse than `ρ^{uq−1}` but cannot
  exceed the reduced-chain threshold — absorbed by `hIH(redChain s M)` once the collapse chart exposes an
  unweighted reduced product (Codex (i)(c)). Cheapest check (Codex): `M=(2,2,1,3)`, `Q̃ₚ=xy`, the product-shell
  threshold `s<½` is exactly what `hIH` gives (not the free `uq/2`). **VERDICT: absorbed by the §1 atom (core),
  no new gap.**
- **Corner (ii) `Q_b → 0` — NEEDS resolution (b), the JOINT atlas (Codex PROVEN; my earlier (a) was WRONG).**
  My earlier "bounded-in-Γ / tall `[P;C]` collapse → `hIH((M₀,M2,…))`" is UNSOUND: `freedSchurLoss ≥
  frobSq([P;C]·Q̃ₚ)` is FALSE (the free `Γ` can cancel `C·Q̃ₚ`, so the integrand exceeds `frobSq([P;C]·Q̃ₚ)^{−c'}`).
  My exact-ℕ `minAdm((M₀,M2,…)) ≥ minAdm(M)` (0/3276) checked that WRONG reduction — it does not validate (ii).
  The correct handling: `{Q_b→0}` is a rank-`(u+1)→u` drop of the extended tail `Q̂`, a native stratum of the
  JOINT `[C|Γ]` atlas — NO `‖Q_b‖^{−a}` weight. The bounded-Γ / pivot-only cap genuinely UNDERSHOOTS: window
  `c'∈(2,3)` for `M=(4,3,2)` (pivot-only chain `(2,3,2)` threshold 2, true 3; Codex (ii)(c) PROVEN). When `q≤u`,
  `Q_b→0` may cause NO total-rank drop — so the atlas must track RELATIVE-row incidence `(rank Q̃ₚ, rank Q̂)`,
  not total rank (Codex (ii)(b)). **VERDICT: the joint atlas (resolution b) is REQUIRED and is the same §1-family
  machinery on `Q̂`; resolution (a) is unsound. No `‖Q_b‖^{−a}` artifact once (b) is used.**

**Net:** the `d=1 a≥u` arm is the §1 source-incidence atlas on the extended tail `Q̂` (pivot-regularized by the
radial-peel), + the banked FreeBilinear leaf at `b=1`. Both corners are absorbed within this one atlas. NOT a
domain-split, NOT a `‖Q_b‖^{−a}` weight, NOT a global decoration. This is the corrected pin.

---
**(HISTORICAL — the UNSOUND earlier pin, kept for the record):** *"LOCAL domain-split by absolute `σ_min(Q̃ₚ)`;
ill→`_inner_bounded`, well→`_inner_peel`."* d1split PROVED the absolute-`σ_min` dispatch routes the radial cone
to the bounded branch (charge `ab/2` dropped) → diverges on `c'∈(½minAdm(redChain u M), ½minAdm M)`. And my
corner-(ii) tall-collapse was not a valid upper bound. Superseded by the joint-atlas pin above.

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
- **§2 the naked-Gram / bounded-branch UNSOUNDNESS witness `M=(4,3,2)@t=2`** (`u=a=q=2, b=1`): the naked-Gram/qbox
  route DIVERGES (`a<q−u+1=1` FALSE, `∫|ε|^{−2}=∞`), AND the bounded-Γ (absolute-`σ_min`) route DIVERGES on the
  window `c'∈(2,3)` (pivot-only chain `(2,3,2)` threshold 2, true `½minAdm=3`). Only the joint `[C|Γ]`-atlas over
  `Q̂` (KEEPING the corank bilinear, `‖X‖²+‖γ‖²‖r‖²` threshold `4/2+min(2,2)/2=3`) reaches the full threshold.
  This is the EQUALITY-at-binding-cell witness that BOTH the naked-Gram IH and the absolute-`σ_min` split are unsound.
- **`b=0` tall qbox (§1 tall sector) marginal `M₂ = a+1`:** `M=(2,1,2,·)`: `a=1, M₂=2=a+1` (marginal; §1's
  `(r,s)` atlas handles it standalone, unlike the crude one-shot qbox which fails here).
- **`a=0` wide fold boundary `A = 2Δ`:** `M=(1,2,3,3)`, `(1,2,3,4)`: `A=1=2Δ` (the fold is marginal AND unsound
  even here — §1 replaces it with the `(r,s)` atlas).

## 5. Architecture trade-off (STANDALONE vs DECORATED — justified)

- **STANDALONE (recommended).** ONE atlas mechanism (§1, extended to `Q̂` for `d=1 a≥u`, §2). No new global IH;
  the plain driver (`decoratedPeelStep_proof` → `routeMBoxThresholdFinite_of_decoratedPeel`) is untouched;
  footprint stays `[cited_aoyagi_product_corank, propext, Classical.choice, Quot.sound]`.
- **DECORATED (rejected).** A global Gram-decorated `RouteMBoxThresholdFinite` IH carrying `det(leadingGram)^{−w}`
  through the recursion. **Rejected on math, not taste:** d1split PROVED a naked Gram-decorated IH is FALSE
  (diverges near a nonzero rank-`(u−1)` leading Gram outside the qbox range, ε-counter `M=(4,3,2)`) — carrying the
  weight unconditionally does not converge. The `d=1 a≥u` arm is closed by the §1 atlas on the extended tail `Q̂`
  (pivot-regularized), which needs no global carrier. So STANDALONE is not just preferred (operator's lean) — it
  is the sound structure; the decorated global IH is unsound.

## Close

- **Firmest.** The `d≤1` native arm funnels to ONE atlas mechanism — the **front-collapse source-incidence
  `(r,s)` atlas** (`frontCollapseRankSector_lt_top`, §1): reduce `frobSq(F·prod(tailChain M) A')` to
  `hIH(redChain s M)` (pure-monomial Jacobian, single-factor NATIVE), covering both wings + `d=1 a<u`; and, for
  `d=1 a≥u` (§2, RE-PINNED after the d1split red-team), the SAME atlas on the EXTENDED tail `Q̂=[Q̃ₚ;Q_b]` with
  the corank block `[C|Γ]` free, pivot-regularized by `w=frobSq(P·Q̃ₚ)` (`‖PΘ‖²≥σ_min(P)²>0` on the sphere), +
  the banked FreeBilinear leaf at `b=1`. Architecture: STANDALONE (no global decoration — the naked Gram IH is
  FALSE, d1split PROVEN). Charge airtight (cut-soundness 0/22932; front rank-sector 0/5292; corner-(i) 0/3276).
  **Two soundness corrections from d1split folded into §2** (absolute-`σ_min` split unsound; `_inner_peel` emits
  the CORANK Gram `‖Q_b‖^{−a}`, not the pivot Gram — the joint `Q̂`-atlas avoids the `‖Q_b‖^{−a}` artifact).
- **Most likely to break.** (i) `d=1 a≥u` (§2) — the joint `[C|Γ]`-atlas over `Q̂` tracking `(rank Q̃ₚ, rank Q̂)`:
  the `Q_b→0` stratum (corner ii, Codex PROVEN needs the joint atlas — bounded-Γ undershoots, window `c'∈(2,3)`
  for `(4,3,2)`) and the pivot-regularizer at `{Q̃ₚ→0}` are the subtle pieces; build/red-team the atlas Jacobian
  FIRST. (ii) The `(r,s)` / joint atlas Jacobian identity (N3) being a clean monomial in the tall / extended-tail
  sectors (subtler than the wide; Codex flagged). (iii) `q≤u`: `Q_b→0` may cause no total-rank drop of `Q̂`, so
  the atlas must track RELATIVE-row incidence, not total rank (Codex ii-b).
- **Next.** Commission the §1 atom build (start WIDE `a=0` sectors — cleanest, `F` surjective — then tall, then
  the `d=1 a≥u` extended-tail `Q̂` atlas). The `(r,s)` atlas + Jacobian (N1–N3) is the genuinely-new heart;
  N4–N5 is the reduction wire; the banked list is complete. Standalone-vs-decorated is math-forced (STANDALONE).

Files (absolute): `…/threads/genm-d1design/d1-atom-spec.md` (this); `d1-build-plan.md` (the open-vs-transcription
pass); `codex/atom-{prompt,answer}.md` (wings STANDALONE) + `codex/corners-{prompt,answer}.md` (the two-corner
red-team: (i) absorbed by §1, (ii) needs the joint atlas); d1split `redteam-cert.md` @ origin/genm-d1split;
`scripts/d1_{charge,wings,discriminate,witnesses,corners}.py`. Socket: `RouteMSJDecoratedPeelStep.lean` @ origin/genm-integration.
