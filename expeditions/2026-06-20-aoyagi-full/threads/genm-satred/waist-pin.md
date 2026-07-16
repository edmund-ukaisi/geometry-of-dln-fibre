# waist-pin — `deeperFlag_waist`, the SATURATED (a=0) descent route, pinned Lean-precisely

**Seat:** pen-and-paper (design, decorrelated), `genm-satred`. **Date:** 2026-07-16. **NO Lean edits.**
The 3rd descent route (task #156, TO-BUILD). Pins the contract + per-arm proof + banked citations off
`satred-cert.md` (the X·Y coupled recombination), so a formaliser can build it. Verified: exact-ℕ
(`scripts/waist_reach.py`, 10976 a=0 cells, 0 fails on the recursion) + satred's `final_accounting.py` +
decorrelated Codex (satred-cert §5 Codex + `codex/edgereach-answer.md` Q3, both apply — see §6).

---

## ★ VERDICT — the waist reaches ½minAdm(M) via the FRONT-factor rank-sector (dual of the edge)

At the saturated shell `j=r` (deepest cut `u = min(M₀,M₁)`), the corank/C-block VANISHES and the loss
collapses to the pure front factor `frobSq(z̃₀·Z_deep)`, `z̃₀ = X·Y` (`X=[P|B₁₂]` full row rank `u`,
`Y=[z₀;A_cor]`). This is satred's coupled recombination. The waist reaches `½minAdm(M)` via the **front-factor
rank-sector**: stratify `rank(z̃₀)=r`, strata `s = u−r ∈ 0..u` reduce to `redChain s M`, and
**`m_I = min_{0≤s≤u}[(M₀−s)(M₁−s) + minAdm(redChain s M)] = minAdm(M)` EXACTLY** (the minAdm recursion,
`s` = the cuts `t`; verified **0/10976**). So the three routes are ONE principle (the recursion), stratifying
different factors — interior = corank weight (strong-block), edge = corank rank, **waist = front rank**.
**No `(□)` wall; a=0 reaches `½minAdm(M)`.**

## 0. The a=0 boundary — WHERE a=0 lives (controller adjudication)

**a=0 is ALWAYS the saturated top shell — there is NO interior-cell a=0.** Exact-ℕ (0/49392):
`a = M₀−(t+j) = 0  ⟺  (j = r = min(M₀−t,M₁−t)  ∧  M₀≤M₁)` — i.e. `u = t+j = M₀`, the deepest cut. So
"interior-cell a=0 (a generic cell with a=0)" does not occur; every a=0 cell is the saturated top shell,
which is `deeperFlag_waist`'s domain. **⟹ ROUTE (a): add `1 ≤ M₀−(t+j)` to `headSplit_domination` (Brick
D = interior corank a≥1); a=0 routes to `deeperFlag_waist`.**

**Route (b) — Brick D absorbing a=0 via "P-radial-only" — is NOT cleanly sound.** At a=0 the C-block
(`a×u = 0×u`) is EMPTY, so the S-d shear `Γ' = Γ + C·P⁻¹B₁₂` is TRIVIAL (C, Γ both 0-row) — **`B₁₂` is NOT
sheared away.** Hence the leading layer is the recombination `z̃₀ = [P|B₁₂]·[z₀;A_cor] = X·Y` (§1), which
needs the **front-factor X·Y pushforward** (this waist spec), NOT a free-`z` P-radial. The P-radial handles
only the `P`-block (`u×u`); it does not resolve the `B₁₂`-degeneration in `z̃₀`. So a=0's content genuinely
IS `deeperFlag_waist`'s (the front-factor recombination), NOT Brick-D-absorbable. **CORRECTION to
`brickD-pin.md §4-P3`:** its "a=0 provable inline via P-radial-only (supersedes satred's A>2Δ)" was
over-optimistic — it missed that `B₁₂` is unsheared at a=0, so the X·Y recombination is required. Take
route (a); the upstream ripple (the T-peel shell-stratification routes the top shell → waist) is the honest
geometry (a=0 is intrinsically the saturated shell, distinct in route — coupled/direct-RMBTF — from the
interior decorated/cornerComparator route). brickf's Brick D stub takes `a≥1`.

## 1. The saturated structure (a=0; satred §1, arch1build-confirmed)

Take `M₀ ≤ M₁` (the a=0 branch; `M₁ ≤ M₀` is the b=0 MIRROR, §5). Saturated cut `u = M₀`, so `a = M₀−u = 0`,
`b = M₁−u = M₁−M₀`, and `u+b = M₁`. Then (satred S1/S2):
- the second `freedSchurLoss` term `frobSq(C·Q̃ₚ + Γ·Q_b)` VANISHES (`C : Fin 0 → Fin u`, `Γ : Fin 0 → Fin b`,
  0 rows), so `freedSchurLoss = frobSq(P·Q̃ₚ)`;
- `Cresid 0 c' = 1`, `det⁺⁰ = 1` — no residual constant;
- `frobSq(P·Q̃ₚ) = frobSq((P·z₀ + B₁₂·A_cor)·Z_deep) = frobSq(z̃₀·Z_deep)`, `z̃₀ = [P|B₁₂]·[z₀;A_cor] = X·Y`
  (`X` = M₀×M₁ full row rank M₀, `Y` = M₁×M₂), `= prod(redChain u M)` with leading layer `z̃₀`.

So `shellSpineIntegrand M u κ ε r ⟨r,_⟩ c'` (the saturated shell) has integrand `frobSq(z̃₀·Z_deep)^{−c'}`
(no Γ integral — Γ is 0-dim), integrated over `A'∈shell`, `x=(P,B₁₂)∈outerDom u 0 b`. This is satred's `(I)`.

## 2. The pinned contract

    deeperFlag_waist :
      (M : Fin (L+1+1+1) → ℕ) (t : ℕ) (κ : Fin (min (M 0) (M 1)) ↪ Fin (M 1)) {ε} (hε : 0<ε) (c' : ℝ)
      (ht : t ≤ min (M 0) (M 1)) (hsat : t + min (M 0 - t) (M 1 - t) = min (M 0) (M 1))   -- j=r, the top shell
      (ha0 : M 0 - (min (M 0) (M 1)) = 0)   -- the a=0 branch (M₀≤M₁); b=0 mirror symmetric (§5)
      (hnd : ∀ i, 1 ≤ M i)
      (hIH : ∀ M' : Fin (L+1+1) → ℕ, RouteMBoxThresholdFinite M')      -- the arity-IH (sjStepHyp_of_coupled)
      (hdens : <density/frame facts, §4>)
      (hc' : c' < carrierThreshold M)   -- = c' < ½·minAdm M
      → shellSpineIntegrand M (min (M 0) (M 1)) κ ε (min (M 0 - t) (M 1 - t)) ⟨min (M 0 - t) (M 1 - t), _⟩ c'
          < ⊤.

**Target = FINITENESS (`< ⊤`) directly** (satred §5.4 brick signature), via the coupled route → `RMBTF`
(bypassing `cornerComparator`, satred's "decision A" — at a=0 `peelCharge=0`, the comparator would add no
shift). The assembly composes this with the interior/edge shells (arch1build's wiring: the waist shell → this
finiteness; interior/edge → cornerComparator/RMBTF). **No `hpiv`** — the waist is exactly the `hpiv`-FAILS
base case; the coupled X·Y route does not need it (it uses the structural `[P|B₁₂]` full-row-rank + density).

## 3. The proof design — the front-factor rank-sector (TWO arms, satred §4 A vs 2Δ)

`Δ := ½(minAdm(redChain u M) − minAdm M) ≥ 0` (headroom, free from the IH; `≥0` banked
`minAdm_le_peelCharge_add_redChain` at `peelCharge=0`). `A := max_{1≤j≤min(u,M₂)} j(M₂−b−j)` (density order
of the `X·Y` pushforward at the `z̃₀` rank-drop, satred §4 / Codex table). Split (`scripts/waist_reach.py`,
5208 clean / 5768 sector):

**Arm A≤2Δ — clean pointwise density fold** (satred §5.4a; incl. ALL `b ≥ M₂−1`, density bounded/log).
`ρ(z̃₀) ≤ K·frobSq(z̃₀·Z_deep)^{−A/2}` (pointwise at the deep-generic origin) ⟹
`(I) ≤ K_ε · routeMLayerBoxIntegral(redChain u M) (c'+A/2+ε)`, finite via `hIH(redChain u M)` since
`c'+A/2+ε < ½minAdm(redChain u M)` (as `A≤2Δ`). SINGLE chain; the log (at `b=M₂−1`) folds via any `ε>0`.

**Arm A>2Δ — the joint FRONT rank-sector** (satred §5.4b; the `b=0`/small-b regime, e.g. `(2,2,2,2)`,
`(1,1,M₂,·)`). The pointwise fold UNDERSHOOTS (consumes `A/2 > Δ`). Stratify `rank(z̃₀) = r`; stratum
`s = u−r ∈ 0..u` reduces to `redChain s M` (arity−1, via `hIH`) at charge `(M₀−s)(M₁−s)/2`; the residual
deep integral is finite by the IH. The `min` over strata is
**`min_{0≤s≤u}[(M₀−s)(M₁−s) + minAdm(redChain s M)] = minAdm(M)`** (the recursion; `u=M₀`, `s`=the cuts `t`;
verified **0/10976** `scripts/waist_reach.py`; satred Codex Q1 `m_I=minAdm M` at `b=M₁−u`). MULTI-chain
(arity-IH). Coincident-charge strata give a harmless-multiplicity LOG (δ-slack, no threshold shift —
`edgereach` Codex Q3, model-independent). Reaches `c'<½minAdm(M)`.

## 4. Density / frame facts (`hdens`) + banked citations

`hdens`: the `X·Y` pushforward density `ρ(z̃₀)` obeys satred's order table (`b≥M₂`: bounded; `b=M₂−1`: log;
`b≤M₂−2`: `≍dist^{−A}`, `A=max_j j(M₂−b−j)`) — this is the NEW analytic content (the measure-domination /
per-stratum determinantal blow-up). **Banked:** `frobSq_empty_rows`, `Cresid_zero` (S1/S2);
`of_blockSplitD_symm_eq_fromBlocks`/`hsQ = fromRows` (the block identity `z̃₀=X·Y`);
`minAdm_le_peelCharge_add_redChain` (`Δ≥0`, the recursion); the arity-IH `sjStepHyp_of_coupled`
(`∀ M', RMBTF M'`); the shell cover (`offSector_cover_le`); a scaling CoV (`frobSq(prod)` degree-`2·arity`
homogeneous, for the `T★` radius). **NEW to build:** (a) the `A≤2Δ` bounded/log density domination
(surjection-of-a-box, cleanest); (b) the `A>2Δ` per-stratum front-factor determinantal blow-up +
`min`-over-strata `= minAdm(M)` recursion (the real work — the `b=0`/small-b regime). **Diamond guard:**
raw-`Pi` for `X·Y ↦ z̃₀`. **Trap:** the per-`P` CoV `z₀↦P·z₀` (`|det P|^{−M₂}` non-integrable — the
domain-enlargement artifact; use the `X·Y` pushforward, NOT the per-P Jacobian).

## 5. The b=0 MIRROR — a DISTINCT brick (b0mirror-confirmed, NOT a transpose-dual)

**b0mirror's decorrelated verdict: the b=0 mirror needs its OWN waist brick.** The M₀↔M₁ symmetry transfers
only the COUNT (`m_I = minAdm`, 0/8232 both branches; my re-verify 0/10976) — NOT the analytic domination.
No integrand symmetry (transpose reverses the chain; the tall factor lands at the back). **My a=0 `hdens`
(the wide-product density table `A = max_j j(M₂−b−j)`) is a=0-SPECIFIC and WRONG for b=0** — a formaliser
copying the a=0 brick + swapping M₀↔M₁ would carry the wrong domination. The b=0 brick has its OWN `hdens`.

**b=0 structure** (`M₁ ≤ M₀`, saturated cut `u = M₁`, `a = M₀−u = M₀−M₁`, `b = M₁−u = 0`): the CORANK
vanishes (`b=0`, `A_cor`/`Γ`/`Q_b` empty), and the front factor is the **TALL** `[P;C]` (`M₀×M₁`, `P` the
u×u top block, `C` the a×u bottom block). `freedSchurLoss = frobSq([P;C]·Q_p)`, `Q_p = z₀·Z_deep` (`M₁×n`).
This is the DUAL of a=0's wide `[P|B₁₂]·Y`. Reduced chain `redChain M₁ M = (M₁, M₂,…)` (drops M₀) — my
`redChain (u,M)` at `u=M₁` is ALREADY correct (b0mirror confirmed).

**b=0 `hdens` (DISTINCT — the Gram/Wishart facts, largely BANKED):** integrating the tall `[P;C]` gives the
Wishart determinant `∫_{[P;C]∈box} det(PᵀP + CᵀC)^{−M₂/2}` (`= det([P;C]ᵀ[P;C])^{−M₂/2}`, the Gram of the
tall M₀×M₁ factor). This is `RouteMSJQBoxCore.qbox_lintegral_lt_top` with `(qbox-b, qbox-q, α) = (M₁, M₀, M₂)`
(apply to `X = [P;C]ᵀ`, wide M₁×M₀): **converges ⟺ M₂ < M₀−M₁+1 = a+1 ⟺ M₂ ≤ a** (codim `a+1`, verified).
Split (`scripts/`, 10976 b=0 cells): `M₂ ≤ a` (3136) → clean one-shot qbox (BANKED); `M₂ > a` (7840) →
the one-shot qbox diverges → recurse via the reduced-chain IH (the D-cert §3bis per-level pivot-Gram
recursion — the `[P;C]`-Gram folds into `redChain M₁ M`'s recursion, NO new density content). **So b=0 is
CLEANER than a=0** (injective CoV — the tall `[P;C]` is full column rank M₁; the Gram/Wishart is a banked
qbox/gammaAtom-family object; no wide-product pushforward density).

**b=0 contract:** SAME structure as §2, with the mirror hyp `hb0 : M 1 − min (M 0) (M 1) = 0` (replaces
`ha0`), `u = min(M₀,M₁) = M₁`, and `hdens = the Gram/Wishart facts` (replaces the a=0 wide-density `hdens`).
The contract STRUCTURE degenerates correctly at b=0 (the corank blocks are empty); only `ha0`+`hdens` are
a=0-only. **The one open piece:** the `[P;C]`-Gram → qbox dim-matching (which `qbox-b,qbox-q` from the
actual `[P;C]` dims) → the reduced-chain recursive IH — folds into the coherent-unit merge (D-cert §3bis).

**Routing (resolves Brick D's `hjr` b=0-top):** the b=0 top shell (M₁<M₀, `j = M₁−t`) routes to THIS b=0
mirror waist (not the a=0 waist, not Brick D). At `M₀=M₁` both a=0,b=0 hold at `u=M₀=M₁` (self-dual).

## 5bis. So the WAIST = TWO bricks

- **`deeperFlag_waist_a0`** (§1–§4): a=0 (`M₀≤M₁`, `u=M₀`), the WIDE-product pushforward density `ρ(z̃₀)`
  (`hdens` = the wide-density table, the genuinely-new content), front-rank-sector, A vs 2Δ split.
- **`deeperFlag_waist_b0`** (§5): b=0 (`M₁≤M₀`, `u=M₁`), the TALL Gram/Wishart `det(PᵀP+CᵀC)^{−M₂/2}`
  (`hdens` = the Gram/Wishart facts, banked qbox), CLEANER (injective CoV). Its own `hb0`+`hdens`.
Both reach `½minAdm(M)` (the count symmetry, 0/8232). The waist formaliser builds both.

## 6. Decorrelated coverage

Covered without a fresh consult (deliberate — 3 consults already this session): (i) satred-cert §5 Codex
(the `X·Y` reassembly, the `|det P|^{−M₂}` artifact, `m_I ≤ minAdm(redChain)` with equality at the
saturated cut, the density order table, scalar `ρ≤16`); (ii) `edgereach` Codex Q3 (model-independent = the
minAdm recursion): the joint rank-sector reaches EXACTLY, coincident-charge logs are multiplicity — applies
to the front rank-sector verbatim. **Residual for a fresh check: the b=0 mirror (§5)** — satbuild's
"not-transpose" finding is the one thing not yet decorrelated-confirmed.

## Close

- **Firmest.** `deeperFlag_waist` (a=0 saturated) reaches `½minAdm(M)` via the front-factor rank-sector,
  `m_I = minAdm(M)` EXACTLY (0/10976, the recursion). Two arms: A≤2Δ clean pointwise fold (single-chain,
  5208 cells); A>2Δ joint front rank-sector (multi-chain arity-IH, 5768 cells, harmless-multiplicity logs).
  Contract §2 (finiteness `< ⊤` via coupled RMBTF, no hpiv). The `(C,θ)`/`rlct` levels untouched (pure (□)).
- **Most likely to break the BUILD.** (i) The per-`P` CoV (`|det P|^{−M₂}` divergent) — use the `X·Y`
  pushforward. (ii) Treating A>2Δ via the naive pointwise fold (undershoots) — needs the front rank-sector.
  (iii) The b=0 mirror mis-built as the literal transpose (satbuild) — it is the genuine dual (§5). (iv)
  Routing the waist through `cornerComparator` — bypass it (coupled route, `peelCharge=0`).
- **Next.** The formaliser builds `deeperFlag_waist` off §2/§3/§4; I recommend a decorrelated re-check of
  the b=0 mirror (§5) before the build commits to one template. That completes the 3-descent-route design.

Files (absolute): `…/threads/genm-satred/waist-pin.md` (this); `satred-cert.md` (the full X·Y content +
density table + Codex), `brickD-pin.md`/`hBackbone-edge-pin.md` (the sibling routes); `codex/edgereach-answer.md`
(Q3), `codex/satred-answer.md`; `scripts/waist_reach.py` (0/10976 recursion + A-vs-2Δ split).
