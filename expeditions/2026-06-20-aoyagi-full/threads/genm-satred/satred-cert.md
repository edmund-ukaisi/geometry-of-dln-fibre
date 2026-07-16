# satred — the P/shear CoV for the SATURATED IH-reduction: resolving the det-P→0 hazard

**Seat:** pen-and-paper (design-space adjudication, decorrelated), aoyagi-full, `genm-satred`.
**Date:** 2026-07-16. **NO Lean edits, NO build.** Exact-algebra + RLCT/pushforward-density reasoning;
Monte-Carlo/float **only** to guide (nothing load-bearing rests on a float). Decorrelated
`local-codex-consult` (gpt-5.x xhigh, my conclusion WITHHELD, prompt framed "argue whichever way, is the
threshold the same or does it drop"): `codex/satred-{prompt,answer}.md`, `codex/satred-run.log`. Structure
confirmed with `arch1build` (SJOuter/outerDom/hsQ/Cresid). Scans: `scripts/{density_probe, ratio_diag,
rlct_exponent, detP_fix, correct_b, final_accounting}.py`.

---

## ★ VERDICT

**The det-P→0 hazard is REAL for the naive CoV but RESOLVED — route (iii), realized STRUCTURALLY (not by
loss-growth, not by a `|det P|` Jacobian). NO KILL: the saturated frontChargeBox is finite for
`c' < ½·minAdm M` and reduces to `RouteMBoxThresholdFinite (redChain u M)`. There is NO RLCT drop below the
needed threshold.**

The load-bearing mechanism: at the saturated cut (`a = M₀−u = 0`, `u = M₀ ≤ M₁`, `b = M₁−u`), the corank
width satisfies **`u + b = M₁`**, so the effective leading layer is the **matrix product**

    z̃₀  =  P·z₀ + B₁₂·A_cor  =  [P | B₁₂] · [z₀ ; A_cor]  =  X · Y,

with `X := [P | B₁₂]` the **full `M₀×M₁` first layer** (full row rank `M₀`, because `P` invertible — and the
corank cross-block `B₁₂` keeps `X` full-rank *uniformly, even as `det P → 0`*) and `Y := [z₀ ; A_cor]` the
**full `M₁×M₂` second layer**. The `det P → 0` degeneracy is thus benign: it is compensated by `B₁₂`, not by
any determinant factor. The naive per-P change of variables `z₀ ↦ P·z₀` (Jacobian `|det P|^{−M₂}`,
non-integrable) is simply the **wrong CoV** — it isolates `P` and picks the always-`P` minor, which
degenerates on the null set `{det P = 0}`; the honest object is the product `X·Y`, whose CoV uses whichever
`M₀×M₀` minor of `[P | B₁₂]` is nonsingular.

**One subtlety the build must carry** (refines `arch1build`'s "log integrable" note): the reduction to
`RouteMBoxThresholdFinite (redChain u M)` at the **same** exponent `c'` is **not** always valid. The
pushforward density `ρ(z̃₀)` of the product map `X·Y` carries an RLCT cost
`Δ := ½·(minAdm (redChain u M) − minAdm M) ≥ 0`; the reduction is
`I ≤ K_ε · RouteMLayerBoxIntegral (redChain u M) (c'+Δ+ε) T★`, which closes for `c' < ½·minAdm M`
**because RMBTF(redChain u M) is valid up to `½·minAdm (redChain u M) = ½·minAdm M + Δ`** — the reduced
chain's headroom **exactly matches** the density cost. (The exactness of that match is the beauty-signal
the accounting is right.)

---

## 1. The exact saturated structure (arch1build-confirmed)

At the saturated cut `a = M₀ − u = 0` (so `u = M₀ ≤ M₁`, `b = M₁ − u`), the entire `frontChargeIntegrand`
collapses (`arch1build`, from `RouteMSJIncidenceAssembly:553`, `RouteMSJHeadSplitDom:44`,
`RouteMSJDeeperFlagCore:467`):

- **(S1)** the SECOND `frobSq` vanishes (`x.2 : Fin 0 → Fin u`, 0 rows ⟹ `frobSq_empty_rows`);
- **(S2)** the corank Gram residual `det⁺(…)^{−a/2} = det⁺⁰ = 1`, and `Cresid ((M₀−u)(M₁−u)) c' = Cresid 0 c'
  = 1` (`RadialResidualPower:39`: `Cresid n c' = ∫_{EuclideanSpace ℝ (Fin n)} (‖Q‖²+1)^{−c'}`; at `n=0` the
  space is a point, integrand `= 1`). So **`Cresid(0) = 1`** exactly — bounded, no residual constant.

The surviving integrand is **pure**:

    ∫_{(P,B₁₂) ∈ outerDom u 0 b,  A_cor ∈ box,  z ∈ paramsBoxM(redChain u M) 1}
        frobSq( (P·z₀ + B₁₂·A_cor) · Zdeep )^{−c'}                                          (I)

where (`Q_inl = prod(redChain u M) z`, head-split `= z₀ · Zdeep`, `z₀ = u×M₂` leading layer,
`Zdeep = deeperFlagZdeep = z₁·…·z_L` the shared reduced-chain deep tail; `Q_inr = A_cor · Zdeep`,
`A_cor = b×M₂`, `B₁₂ = x.1.2 = u×b`, `P = x.1.1 = u×u`). **`P` ranges over the FULL `{IsUnit P} ∩ box`
(outerDom, `RouteMSJChartShear:185`) — NOT pinned away from singular.** So **route (i) [chart pins
`|det P|≥δ`] is unavailable.**

The threshold: at `a=0`, `peelCharge M u = a·b = 0`, so `flagShift_lt_carrierThreshold`
(`RouteMSJShellCharge:69`) gives `c' < carrierThreshold(redChain u M) = ½·minAdm(redChain u M)` directly;
and `minAdm M ≤ minAdm(redChain u M)` (saturated `flagCharge_ge`). The **needed** finiteness is for
`c' < ½·minAdm M`.

## 2. The hazard, made precise: the naive CoV DIVERGES

The natural attempt "absorb `P` into the leading reduced layer": `z₀ ↦ w = P·z₀ + B₁₂·A_cor`, affine in `z₀`
at fixed `(P,B₁₂,A_cor)`, linear part left-mult by `P` on a `u×M₂` matrix ⟹ Jacobian `|det P|^{M₂}`, i.e.
`dz₀ = |det P|^{−M₂} dw`. Enlarging the `w`-image `P·box + B₁₂A_cor ⊆ [−T★,T★]^{u×M₂}` to the full box gives

    (I) ≤ [ ∫_{P∈box} |det P|^{−M₂} dP ] · (vol) · RouteMLayerBoxIntegral(redChain u M) c' T★.

But `∫_{box} |det P|^{−M₂} dP = ∞` for `M₂ ≥ 1` (the log-canonical threshold of `det` is `1`, and `M₂ ≥ 1`).
**So the naive "absorb-P + enlarge" bound is vacuous — it diverges.** [Exact `lct(det)=1`; guiding scan
`scripts/density_probe.py`: the single-product density of `P·z₀` blows up like `‖W‖^{−(M₂−1)}` at `W=0`,
the `|det P|^{−M₂}` artifact.] Codex (decorrelated, Q2) reaches the identical read: the `|det P|^{−M₂}` "is
an artifact of enlarging the conditional `W`-domain… its support collapses with precisely the compensating
volume `|det P|^{M₂}`; replacing that collapsing parallelepiped by a fixed box destroys the cancellation."

The naive CoV fails because it always uses `P` (the fixed top-left minor of `[P | B₁₂]`), which vanishes on
`{det P = 0}`. That set is null, but the enlargement is too lossy near it.

## 3. The resolution — route (iii), structural (`u+b = M₁`, full-rank front factor)

Because `b = M₁ − u` (forced by the corank structure: `Q_inr` has `b = M₁−u` rows), we have `u + b = M₁`.
Hence

    z̃₀ = P·z₀ + B₁₂·A_cor = [P | B₁₂] · [z₀ ; A_cor] = X · Y,
    X = [P | B₁₂]  :  M₀ × M₁   (the FULL first layer),
    Y = [z₀ ; A_cor] : M₁ × M₂  (the FULL second layer),

and `z̃₀ · Zdeep = X·Y·z₁·…·z_L = prod(M)(X, Y, z₁, …, z_L)`. So **(I) is exactly
`RouteMLayerBoxIntegral(M)` restricted to the full-measure chart `{P = X's left M₀×M₀ block is invertible}`.**
Consequences:

- **`det P → 0` is benign.** `X = [P | B₁₂]` stays full row rank `M₀` even as `det P → 0`, because the corank
  cross-block `B₁₂` supplements a near-singular `P`. (`P` invertible already suffices: `P`'s `M₀` rows are
  independent, so `[P|B₁₂]`'s rows are.) The map `Y ↦ X·Y` (fixed full-row-rank `X`) is a bounded-density
  **surjection** `M₁M₂ ↠ M₀M₂`. The near-singular-`P` region contributes a **finite, vanishing-as-`δ→0`**
  amount — `scripts/final_accounting.py`: for `M=(1,3,3,3)`, `c'=1.3`, `E[g·𝟙(|det P|<δ)] = 55.9, 29.5,
  13.3, 3.6` for `δ = 0.3,0.1,0.03,0.01` (→0). Codex (Q4): near-singular-`P` mass `∝ δ → 0`.

- **NO RLCT drop.** `λ_H := ` finiteness threshold of (I) `= ½·minAdm M` **exactly** — since (I) is
  `RMBTF(M)|_{chart}` and `RMBTF(M)` has RLCT `½·minAdm M` (Aoyagi). Verified: sublevel-volume slopes
  `scripts/final_accounting.py` (correct `b=M₁−u`) trend to `½·minAdm M` in every case
  `(1,2,3,3)→1.0, (1,3,3,3)→1.5, (2,3,2,2)→1.5, (1,4,4,4)→2.0, (1,2,2,2)→1.0, (2,4,3,3)→2.5`.
  **[Guard against the calibration trap I initially hit: using `b=1` instead of `b=M₁−u` gives the WRONG
  (inserted) chain and a spurious drop `λ_H = ½·minAdm(u,u+1,M₂,…) < ½·minAdm M`. The correct `b=M₁−u` is
  load-bearing.]**

Codex (decorrelated), generic `b`, gives the inserted-chain codim
`m_I = min_{0≤s≤u}[(u−s)(u+b−s) + m₂(s,M₂,M₃)]` and `I(c')<∞ ⟺ c' < m_I/2`; **specialised to `b=M₁−u`
(`u+b=M₁`), the inserted chain is `(M₀,M₁,M₂,M₃)=M`, so `m_I = minAdm M`** — the needed threshold. Codex's
own "strict drop" example `(u,b,M₂,M₃)=(1,1,3,3)` is the chain `(1,2,3,3)` (an inserted width `k=2 ≠ M₁`);
under the true constraint no such drop below `½·minAdm M` occurs.

## 4. The reduction to `RouteMBoxThresholdFinite (redChain u M)` + the density RLCT cost Δ

The reduction target is the IH on the **strictly shorter** chain `redChain u M = (u, M₂, …, M_L)` (arity −1),
whose leading layer is `z̃₀` (`u×M₂ = M₀×M₂`) and whose product is `z̃₀·Zdeep`. Pushing (I) forward along
`X·Y ↦ z̃₀`:

    (I) = ∫_{z̃₀, deep} frobSq(z̃₀·Zdeep)^{−c'} · ρ(z̃₀) d z̃₀ d(deep),

`ρ` = pushforward density of `(X,Y) ↦ X·Y`. **`ρ` is NOT uniformly bounded** — its singularity on
`{rank z̃₀ < min(u,M₂)}` is controlled by `b` (Codex Q3, matching `scripts/{density_probe, correct_b}.py`):

| regime | `ρ` near the rank-drop |
|---|---|
| `b ≥ M₂` | **bounded** |
| `b = M₂ − 1` | `≍ log(1/·)` |
| `b ≤ M₂ − 2` | `≍ dist^{−A}`, `A = max_{1≤j≤min(u,M₂)} j(M₂−b−j) > 0` |

(At `W=0`, `A = ⌊(M₂−b)²/4⌋` for `u ≥ M₂`, truncated at `j=u` for `u<M₂`; scalar check `u=M₂=b=1`:
`ρ = f∗f`, `f(t)=2log(1/|t|)`, `ρ ≤ ‖f‖₂² = 16` bounded, Codex + `ratio_diag`.)

The density's **RLCT cost is exactly** `Δ = ½·(minAdm(redChain u M) − minAdm M) ≥ 0`
(`scripts/final_accounting.py`: `(1,2,3,3)` has `minAdm M = 2`, `minAdm(redChain=(1,3,3)) = 3`, `Δ = ½`,
measured `λ_H → 1.0 = ½·minAdm M ≠ ½·minAdm(redChain) = 1.5`). Hence

    (I) ≤ K_ε · RouteMLayerBoxIntegral(redChain u M) (c' + Δ + ε) T★,

**finite for `c' < ½·minAdm M`**: the exponent `c'+Δ+ε < ½·minAdm M + Δ = ½·minAdm(redChain u M)`, inside
RMBTF(redChain u M)'s validity. The reduced chain's headroom `½·minAdm(redChain) − ½·minAdm M = Δ` exactly
covers the density cost. (`Δ = 0` ⟺ the saturated cut minimises ⟺ `ρ` bounded/log; `Δ > 0` occurs, e.g.
`M=(1,2,3,3)`, where a shallower cut wins and `ρ` is a genuine power.)

## 5. Deliverables

1. **Explicit CoV.** The intended `z₀ ↦ w = P·z₀ + B₁₂·A_cor` **carries** Jacobian `|det P|^{−M₂}` (never
   drop it — tide-D KILL guard), but this per-`P` CoV is the **wrong** decomposition: `|det P|^{−M₂}` is
   non-integrable and is a domain-enlargement artifact (§2). The **correct** object is the matrix product
   `z̃₀ = [P|B₁₂]·[z₀;A_cor]`; its honest measure is the pushforward `ρ(z̃₀)` (§4), NOT `|det P|^{−M₂}·Leb`.
   `prod(redChain u M) z = z₀·Zdeep` transforms to `prod(redChain u M)(z̃₀, z₁,…) = z̃₀·Zdeep`, and
   `RouteMBoxThresholdFinite(redChain u M)` applies at exponent `c'+Δ+ε` (§4).
2. **The `x.1.2·Q_inr = B₁₂·A_cor` cross-term.** It does **NOT** integrate out separately and does **NOT**
   need a shear. It **folds into the reduced structure** as the bottom `b = M₁−u` rows of the full second
   layer `Y = [z₀ ; A_cor]` (`M₁×M₂`); equivalently it is the `B₁₂`-columns of the full first layer
   `X = [P|B₁₂]`. It is **LOAD-BEARING**: `B₁₂` (paired with `A_cor`) is exactly what keeps `X` full row
   rank `M₀` as `det P → 0`, i.e. it *is* the det-P compensation.
3. **The `Cresid(0)` constant.** Bounded, value **exactly `1`** (`Cresid 0 c' = 1`, §1-S2). Also
   `det⁺⁰ = 1` and the second `frobSq` vanishes — no residual factor survives.
4. **Lean-mechanism map.**
   - *Banked to consume:* `RouteMBoxThresholdFinite (redChain u M)` (the IH; note it must be invoked at a
     **bumped exponent `c'+Δ+ε`** and a **rescaled radius `T★`** — a scaling CoV, `frobSq(prod)` is
     degree-`2·arity` homogeneous); `Cresid_zero`, `frobSq_empty_rows` (S1/S2); the block identity
     `of_blockSplitD_symm_eq_fromBlocks` / `hsQ = fromRows`.
   - *New content (the crux):* the **matrix-product density / RLCT-cost lemma** — that pushing
     `∫_{X∈{IsUnit-left-block}∩box, Y∈box} f(X·Y)` forward is dominated by
     `K_ε·∫_{z̃₀∈box_T★} f(z̃₀)·(rank-degeneracy)^{−(2Δ+ε)}`, absorbed into RMBTF at `c'+Δ+ε`. Two Lean routes:
     (a) **`b ≥ M₂` (Δ possibly 0, ρ bounded):** a clean measure-domination `(X·Y)_*Leb ≤ K·Leb_{box}`
     (surjection-of-a-box) ⟹ `(I) ≤ K·RMBTF(redChain u M) T★` at the **same** `c'` — simplest, no headroom;
     (b) **`b < M₂` (ρ power/log-singular):** the ε-headroom fold. The origin `{z̃₀=0}` piece is handled by
     submultiplicativity `frobSq(z̃₀·Zdeep) ≤ ‖z̃₀‖²‖Zdeep‖²` ⟹ `‖z̃₀‖^{−ε} ≤ ‖Zdeep‖^ε·frobSq^{−ε/2}`,
     folding into the exponent; the deeper rank-strata need the stratified bound (Codex Q3) — genuine
     analytic content, NOT free.
   - *Diamond guard:* the matrix CoV / product must use the **raw-`Pi` instances** (`lean/CLAUDE.md`
     `Matrix.module` diamond) for `[P|B₁₂]·[z₀;A_cor]` and the reindex `X·Y ↦ z̃₀`.
   - *Architecture (arch1build-confirmed).* The coupled route **bypasses** `cornerComparator` (that is the
     decorated `rescopefin` route, controller decision A) — so `cornerComparator` neither helps nor is
     needed here, and would not have absorbed `Δ` anyway (at saturation `peelCharge=0`, its exponent is `c'`,
     no `+Δ` shift). The saturated brick's target is `RouteMBoxThresholdFinite (redChain u M)` **directly**,
     which is exactly what the arity-IH `sjStepHyp_of_coupled` supplies (`∀ M' : Fin (L+1+1),
     RouteMBoxThresholdFinite M'`), valid for **all** exponents `< ½·minAdm(redChain u M) = ½·minAdm M + Δ`.
     ⟹ **the `Δ` headroom costs nothing (free from the IH).** `Δ ≥ 0` is **banked**: at the saturated cut
     `peelCharge M u = (M₀−u)(M₁−u) = 0`, and `minAdm_le_peelCharge_add_redChain` (`RouteMSJResolution:204`)
     gives `minAdm M ≤ 0 + minAdm(redChain u M)`. ⟹ **the Δ-carrying DENSITY DOMINATION (§4) is the NEW
     analytic content — the core of the tide-D saturated brick — while the headroom it consumes is free.**
   - *Brick signature (arch1build).* State the saturated boundary brick **taking the arity-IH as an input
     hypothesis** (the IH-threading happens one level up, in `sjStepHyp_of_coupled`):
     `hbdryShell(j=r) : (hIH : RouteMBoxThresholdFinite (redChain (min (M 0) (M 1)) M)) → (density facts) →
     shellSpineIntegrand M (t★+r) κ ε r ⟨r⟩ c' < ⊤`. The boundary `j=r` is genuinely **not IH-free**; bake
     the `(hIH) →` into the signature.
5. **Decorrelated Codex.** Independently confirmed: (i) the reassembly `W = [P B₁₂][z₀;A_cor] = C·D`;
   (ii) `|det P|^{−M₂}` is a domain-enlargement artifact, real divergence (when present) is rank
   degeneration of `[P|B₁₂]`, not the determinant; (iii) exact threshold `c' < m_I/2`, `m_I ≤ minAdm(redChain)`
   with equality when the saturated cut binds — under `b=M₁−u`, `m_I = minAdm M`; (iv) the density orders
   (§4 table); (v) scalar `ρ` bounded (`≤16`). Its only gap: my prompt withheld the constraint `b=M₁−u`, so
   Codex analysed generic `b` and reports drops "in some width regimes" — correct for generic `b`, excluded
   by the true constraint.

## 6. Levels kept apart

- **Quiver/orbit** — untouched; consumed via `minAdm`/`redChain` (`RouteMLayerSplit`).
- **Codim `(C,θ)`** — this cert establishes the **finiteness/(□) analytic realization** of the saturated
  shell, not the codim count. The `Δ = ½(minAdm(redChain) − minAdm M)` is an arithmetic identity of the
  `minAdm` recursion, not an RLCT claim.
- **RLCT cap** — this works at the per-shell **finiteness** level (`RouteMBoxThresholdFinite`), which needs
  only the box integral + IH, NOT the cited `rlct = ½·codim` equality. `λ_H = ½·minAdm M` here is the
  finiteness threshold of the box integral (Aoyagi-consistent), not a re-derivation of the RLCT equality.

## Close

- **Firmest result.** The det-P→0 hazard is resolved (route iii, structural): `u+b=M₁` makes the leading
  layer the product `[P|B₁₂]·[z₀;A_cor]` with full-row-rank front factor; `det P→0` is compensated by the
  corank block `B₁₂`. No RLCT drop — `λ_H = ½·minAdm M` (I is `RMBTF(M)|_{P invertible}`). The reduction to
  `RMBTF(redChain u M)` closes at exponent `c'+Δ+ε`, `Δ = ½(minAdm(redChain u M) − minAdm M)`, absorbed
  exactly by the reduced chain's headroom. `Cresid(0)=1`. No KILL.
- **Most likely to break it.** (i) The `b < M₂` power-density (`Δ>0`, e.g. `(1,2,3,3)`) is genuine analytic
  content — if the build tries `(I) ≤ K·RMBTF(redChain)` at the **same** exponent (bounded density) it will
  FAIL there; the bumped exponent `c'+Δ+ε` is mandatory. (ii) If a build ever reverts to the per-`P` CoV
  `z₀↦Pz₀` and enlarges, it diverges (`|det P|^{−M₂}`). (iii) The `b=M₁−u` (not `b=1`) identity is
  load-bearing; a mis-set `b` gives a spurious drop.
- **Next construction/consult.** *(Resolved with arch1build.)* `cornerComparator` is bypassed (coupled
  route); the `Δ` headroom is free from the arity-IH `sjStepHyp_of_coupled` and `Δ≥0` is banked
  (`minAdm_le_peelCharge_add_redChain`, `RouteMSJResolution:204`); the **Δ-carrying density domination is the
  new tide-D brick content.** Remaining open construction: the cleanest Lean form of the matrix-product
  pushforward-density bound — (a) the `b≥M₂` bounded-density measure-domination (clean, same exponent), and
  (b) the `b<M₂` stratified `ρ ≍ dist^{−A}` bound + exponent-shift into `c'+Δ+ε` (the deeper-rank strata are
  the real work). The brick is stated `(hIH : RMBTF(redChain (min(M₀)(M₁)) M)) → (density facts) →
  shellSpineIntegrand … < ⊤` (arch1build's skeleton isolates it; IH threaded one level up).

Files (absolute):
- `…/threads/genm-satred/satred-cert.md` (this cert)
- `…/threads/genm-satred/codex/satred-{prompt,answer}.md`, `satred-run.log`
- `…/threads/genm-satred/scripts/{density_probe, ratio_diag, rlct_exponent, detP_fix, correct_b,
  final_accounting}.py`
