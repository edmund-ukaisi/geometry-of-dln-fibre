# arch1probe — Arch-1 soundness (Q-A) + the hlb front-loss construction (Q-B)

**Seat:** pen-and-paper (design-space adjudication, decorrelated), aoyagi-full Stage 2, `genm-arch1probe`.
**Date:** 2026-07-15. **NO Lean edits, NO build.** Exact `ℕ`-recursion arithmetic + RLCT/Morse–Bott exact
algebra; numerics (float rank / σ_min) only to guide + illustrate — nothing load-bearing rests on a float
rank. Decorrelated `local-codex-consult` (gpt-5.x, xhigh; my verdicts WITHHELD, prompt framed "argue
whichever way / is the gate necessary or not"): `codex/arch1-{prompt,answer}.md`, `codex/arch1-run.log`.

**Verified (signatures, not paraphrased) on `origin/genm-deepatlas`:**
`RouteMSJIncidenceAssembly.lean` (`shellSpine_le_coupledBox` :436, `freedSchurLoss_gammaPeel_le` :493,
`shellSpine_le_frontCharge` :610 with `hGae`/`hEtopae`, `frontChargeIntegrand`/`frontLossIntegrand`,
`tailWidth_le_deepTailMin_of_binding` :234, `minAdm_redChain_succ_le` :219, `clsCodim_gate_genL` :723,
`stratum_corner_lt_top` :767), `RouteMSJCorankGeneric.lean` (`hGae_from_deepRank` :68 reducing hGae to
`hZrank`, `corank_gram_posDef_ae` :38), `RouteMSJRadialPolar.lean` (`corner_block_cube_lintegral_lt_top`
:257 — the banked degree-2 radial with `hom`/`hlb`), `RouteMSJTwoBlockRadial.lean`
(`twoBlock_radial_le` :235), `RouteMSJChartShear.lean` (`SJOuter`, `freedSchurLoss` :146),
`RouteMSJIncidenceChart5BigCell.lean` (`chart5_bigcell_cov` :110, `chart5_rank_le_iff_reassembled` :145),
`RouteMSJIncidenceExponent.lean` (`clsCodim` :44, `clsCodim_add_ab_eq` :52), `RouteMSJDeeperFlagShell.lean`
(`offSector_cover_le`, `uniformWenn_proj_le` — the OLD U_s-frame deep-rank mechanism),
`RouteMLayerSplit.lean` (`minAdm`/`minAdmRec` :51/58, `redChain` :40). Consumed the tideDrecon `recon-map.md`,
`genm-seamrlct/seamrlct-cert.md`, `genm-routeverify/routeverify-cert.md`. Scans: `/tmp/deepscan.py`,
`/tmp/mb2.py` (exact `ℕ` recursion; float Morse–Bott illustration).

---

## ★ VERDICTS

**Q-A — Arch-1 is SOUND + complete; the explicit deep-stratum arc (deepgate `C_k` / `RouteMSJDeepGate` /
crstrat `CRrec`/(I) / the `deepRankLE`/`deepCell` atlas) is GENUINELY UNNECESSARY and off-path** — subject to
three named, load-bearing conditions (below). **But the re-scoping's phrasing is imprecise and must be
corrected:** the deep-factor **integrability is NOT closed by `hGae`.** `hGae` (corank Gram `Q_bQ_bᵀ` PosDef
a.e.) only licenses the **pointwise a.e. Γ-peel** (step 2, `freedSchurLoss_gammaPeel_le`). A.e. positivity is
**not** integrability. The deep-factor integrability is closed by the **DESCENT** — the domination onto
`cornerComparator(redChain u M).integral(c'−ab/2)`, whose finiteness is the decorated **IH on the strictly
shorter chain** (threshold reproduced by `minAdm(M) ≤ ab + minAdm(redChain u M)`). Decorrelated Codex reaches
the identical distinction independently ("positivity a.e. does not imply integrability … descent supplies
joint deep-factor integrability … the gate is off-path *provided the comparator domination is a proved
lemma*").

**Q-B — the single-block transverse loss `g` is cleanly degree-2 Morse–Bott (CONSTRUCTED + verified); the
biquadratic `‖Y·W‖²` corner (`ℓ=0` / `h>0`) is the precise boundary where BOTH `hom` and `hlb` fail** and
`stratum_corner_lt_top` is UNSOUND to apply. That corner is degree-2-homogeneous **only after banking one
factor's scale `σ`** — it MUST be routed through `twoBlock_radial_le` (two-radius, sharp `σ`-charge) or the
descent, NOT the single-block radial. Not a kill of Arch-1 (the two-block engine is banked), but a
load-bearing per-stratum ROUTING requirement.

---

## 1. Q-A — the deep-factor mechanism, exactly

### 1.1 What `hGae` is, and what it is NOT

`shellSpine_le_frontCharge` threads `hGae : ∀ᵐ p, (Q_bQ_bᵀ).PosDef`, `Q_b = A_cor·deeperFlagZdeep M u z`.
`hGae_from_deepRank` REDUCES it to a single input `hZrank : ∀ᵐ z, (M₁−u) ≤ rank(deeperFlagZdeep M u z)` — the
deep-factor generic rank. `deeperFlagZdeep` is the product of the deep tail `(M₂,…,M_last)` (an `M₂×n`
matrix); its generic rank is `deepTailMin M = min(M₂,…,M_last)` **[FACT]** (generic rank of a matrix product
= min of the widths). So:

    hGae holds a.e.  ⟺  b := M₁−u ≤ deepTailMin M.      [FACT]

`hGae` licenses ONLY the pointwise a.e. Γ-peel (`coupledBox_le_frontCharge` via `lintegral_mono_ae`). It does
**not** bound the `∫_p` of the corank charge. **The charge is genuinely non-integrable near the deep
rank-drop even where `hGae` holds a.e.** [FACT, Codex-concurred]: for fixed `G = Z Zᵀ` of rank `k`, the
Wishart criterion is `∫_{bounded N} det(N G Nᵀ)^{−a/2} dN < ∞ ⟺ a < k−b+1`; scaling the singular values of
`Z` by `ε` scales the charge by `ε^{−ab}`, and near a limiting `rank G = k₀ < b` a generic `N` gives blow-up
`ε^{−a(b−k₀)}`. So a **null** deep rank-drop locus still creates non-integrable neighbourhoods — closed only
by the descent, not by `hGae`.

### 1.2 Why the descent closes it (no gate) — and the threshold

`deeperFlag_shell_le` produces (routeverify §1, verified) the domination
`shellSpineIntegrand M u κ … ≤ C · (cornerComparator (redChain u M) …).integral(c' − peelCharge M u/2)`,
`C<⊤`, with `adm(redChain u M)(cornerComparator …)` supplied. `redChain u M = (u, M₂,…,M_last)` has **one
fewer layer**, so its comparator is the decorated IH's strictly-smaller instance. The `∫_{A_cor}` of the
charge is finite iff `a+b ≤ M₂` (Wishart) and yields `∝ det(Z_deep Z_deepᵀ)^{−b/2}·(box const)` — a
deep-factor charge on the shorter chain, reabsorbed into the comparator's `decLoss`; the `∫_z` of that IS the
shorter chain's own singular integral = the IH. The threshold reproduces **[FACT]**:

    minAdm(M) ≤ ab + minAdm(redChain u M)  ⟹  q = c'−ab/2 < ½minAdm(M)−ab/2 ≤ carrierThreshold(redChain u M),

so the comparator at exponent `q` is finite by the IH. Exact scan: **0/75 411 cuts fail** the inequality
(widths 1..7, arity 3..5). So the deep degeneration as `Z_deep` approaches its rank-drop strata is controlled
by the **shorter-chain IH**, not by a deep-stratum gate. [Codex Q-A(a) identical.]

### 1.3 The load-bearing conditions (where soundness bites)

**(i) The peel MUST be binding-anchored (`u = t★+j`, `t★ = argmin`).** hGae's `b ≤ deepTailMin` is discharged
by `tailWidth_le_deepTailMin_of_binding` (arithmetic verified: `a·b = (a−1)(b−1)+(a+b−1)` ⟹ at a binding cut
with room, `a★+b★−1 ≤ deepTailMin`, so `b = M₁−(t★+j) ≤ M₁−t★−1 ≤ deepTailMin−1 < deepTailMin` for `j≥1`).
This **requires the binding hypothesis `hbind`** — it holds ONLY at binding-anchored cuts.

  Exact scan (arity 3..6, widths 1..7; 117 404 good chains, `deepTailMin ≤ M₁`):
  - binding-anchored strict-shell cuts `u=t★+j`, `j≥1`, `b>deepTailMin`: **0 violations**.
  - `a+b > M₂` (corank convergence) at the same cuts: **0 violations** (`a+b ≤ deepTailMin−1 ≤ M₂−1`).
  - arbitrary (non-binding) strict-shell cuts `u≥1` with `b>deepTailMin`: **174 100 violations** (e.g.
    `M=(1,3,1)`, `u=1`: `b=2 > deepTailMin=1` — hGae FALSE, `Q_bQ_bᵀ` singular for ALL `A_cor`).

  So the binding anchoring is **not cosmetic — it is what makes hGae true.** The theorem statements are
  self-guarding: `deeperFlag_shell_le`/`deeperFlag_spineToCore` carry `hpiv` (only dischargeable at binding
  cuts) and hGae's discharge needs `hbind`; a non-binding invocation cannot meet the hypotheses. **Guard for
  the build: never invoke the incidence route off the binding-anchored shell cover.** [Codex Q-A(b): "special
  to binding strict shells; an arbitrary cut with `u < M₁−d` has `b>d`, singular for every `A_cor`."]

**(ii) `hZrank` (the deep-factor generic-rank input) is the ONE genuinely-new AG dependency** —
`∀ᵐ z, deepTailMin ≤ rank(deeperFlagZdeep M u z)` (min-minor-of-product generic nonvanishing). It is NOT
built in the assembly (`hGae_from_deepRank` takes it as a hypothesis); it is the **rankgen deliverable**. True
[FACT] (generic product rank = min width), but its Lean discharge is a real residual, not free.

**(iii) The comparator domination is a PROVED lemma, not asserted.** This is brick (A) (the top-level
`frontChargeIntegrand`/`frontLossIntegrand` assembly + gluing), the single largest UNBUILT piece. Codex:
"if that domination is merely asserted, there is a proof gap — but the gap is not a positive-measure failure
of hGae." On `origin/genm-deepatlas` the CURRENT `deeperFlag_shell_le` still routes through the OLD Brick D
(`headSplit_domination`, `sorry`, route-B dead); the Arch-1 direct build replaces it. So the domination is
the thing the tide-D build must SUPPLY.

**Waist quarantine.** `M₂>M₁` / `deepTailMin>M₁` chains are NOT good, are routed to the separate waist branch
(holes c/e, still open), and are NOT the incidence route. Confirmed off-path.

**Net.** The deep-stratum ARC (deepgate/CRrec/deepRankLE — a standalone deep-rank atlas) is genuinely
unnecessary; Arch-1's descent + hGae replaces it, sound on the good branch. The re-scoping's *conclusion*
(no deep gate) is correct; its *reason* ("hGae handles the deep factor") is wrong — **the descent handles the
deep factor; hGae only enables the a.e. Γ-peel.** State it that way in the build.

---

## 2. Q-B — the transverse loss `g`: `hom` + `hlb`

### 2.1 The single-block construction (CLEAN)

The front loss after the charge pull-out is `frontLossIntegrand = ∫_x (E_top + E_tr)^{−q}`, `x=(P,B₁₂,C)`,
`E_top = ‖P·Q_p + B₁₂·Q_b‖²` (polynomial pivot energy, `pivotEnergy_stack_eq`),
`E_tr = ‖C·Q̃_p·Π_⊥‖²`, `Π_⊥ = I − Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b`. `chart5_bigcell_cov` (unit Jacobian) puts the
rank-drop at the transverse Schur origin `{E=0}`; `chart4` handles the pivot fibre. On a `(ℓ,s)` **single**
stratum with the bounded chart spectators (pivot `P` invertible, `R`/`C₀`, deep rows) full-rank, the
transverse loss on the codim-`C = clsCodim` normal block `w` is an exact quadratic form:

    g(w) = ‖Λ · w‖²,   Λ = a fixed (chart-data-dependent) full-column-rank matrix.   [FACT]

- **`hom` — EXACT.** `g(r·w) = ‖Λ(r·w)‖² = r²‖Λw‖² = r²·g(w)` for all `r` (Λ fixed). ✓ (matches the
  `corner_block_cube_lintegral_lt_top`/`stratum_corner_lt_top` signature `∀ r x, g(r•x)=r^2·g x`.)
- **`hlb` — `σ_min(Λ)² > 0`.** `‖w‖=1 ⟹ g(w) = ‖Λw‖² ≥ σ_min(Λ)²`, and `σ_min(Λ)>0 ⟺ Λ` full column rank
  ⟺ the front map is an immersion transverse to the rank-drop locus = **Morse–Bott nondegeneracy**. [FACT]
- **Codex gave `Λ` explicitly** (independent, decorrelated): for the two-factor slice `AZ=0`, `Λ` is the
  block/Kronecker matrix `[[I⊗P,0,0],[I⊗C₀, Rᵀ⊗I,0],[0,0,I⊗P],[0,0,I⊗C₀]]`, full column rank when `P`
  invertible and `R` full row rank — `Λw=0 ⟹ U=V=0` (from `P`) `⟹ XR=0 ⟹ X=0`. Normal-block dim
  `C_nor = ℓq + (p−ℓ)s`.

**Concrete trace (verified numerically, `/tmp/mb2.py`).** Full-DLN Morse–Bott ground truth: at genuine
zero-fibre points on the **binding** stratum, `‖product‖ ≈ 0` and `rank(D mult) = minAdm` exactly:
`(3,3,3)` binding `t=1,2` → `rank(D mult) = 7 = minAdm`; `(2,2,2,2)` → `3 = minAdm`; `(2,2,2)` → `3`. Since at
a zero of `‖mult‖²` the Hessian is `2·(D mult)ᵀ(D mult)`, transverse-Hessian rank `= rank(D mult) = codim`,
so the transverse quadratic is **nondegenerate ⟹ hlb > 0** at generic stratum points. ✓

**The `hlb` caveat (load-bearing).** `a = σ_min(Λ)²` is **chart-data-dependent** and `→ 0` at chart
boundaries (spectator/pivot → singular). Illustrative scan (`u,a,b,n=2,1,1,3` and `1,1,1,2`, 200 bounded
charts): median `σ_min ≈ 0.17–0.42`, min `≈ 0.001–0.012`. So `hlb`'s `a>0` is **uniform per fixed chart
interior** (which is exactly what `stratum_corner_lt_top` needs — `g` and `Λ` are fixed inside one corner),
but the constant degrades to 0 at the boundary. The resulting `a^{−q}` factor is NOT free: it must be
absorbed by the `chart4` pivot fibre integral (`∫(‖H‖²+τ²)^{−q}`, `2q>N`) + the finite-cover gluing over the
chart data. Codex concurs: "one needs the pivot singular values bounded away from zero; on a compact banked
subchart this holds; at a chart boundary change pivot chart or pass to the lower-rank stratum." The boundary
is a **null overlap** (seamrlct §3/§10), covered by the lower-rank chart.

### 2.2 The KILL / boundary — the biquadratic `‖Y·W‖²` corner (`ℓ=0` / `h>0`)

When the front-block chart stratification degenerates a pivot (rank `ℓ=0`, and generally `h=m−ℓ−s>0` with
`p−ℓ>0`, `q−s>0`), the residual is a genuine **biquadratic** in TWO transverse blocks:

    g_corner(Y, W) = ‖D·(Y·W)‖²,   D a fixed injective chart map.    [FACT, Codex Q-B(ii)]

As a **single** radial block this is UNSOUND for `stratum_corner_lt_top`:
- **`hom` FAILS:** `g_corner(rY, rW) = ‖D(rY·rW)‖² = r⁴·g_corner(Y,W)` — degree 4, not `r²`. [FACT, verified]
- **`hlb` FAILS:** take `Y=0, ‖W‖=1` (or vice versa) `⟹ g_corner = 0` — no positive unit-sphere floor.
- The extremal `(ℓ,s)=(0,0)` stratum is the **pure** product loss `‖YW‖²` with no linear normal block at all.

**This is NOT a kill of Arch-1** — it is the exact reason the design carries `twoBlock_radial_le` (banked,
`RouteMSJTwoBlockRadial.lean:235`), which finitely bounds the **two-radius** form `(κ²‖u‖² + σ²‖v‖²)^{−c'}`
(degree-2-homogeneous jointly, but anisotropic: `hlb = min(κ²,σ²) → 0` as the coupling scale `σ→0`) by
`σ^{−α'}·C` with the **sharp** exponent `α'` (gate `2c'−du < α' < dv`). The biquadratic is handled by first
**banking one factor** (fixing `Y`'s surviving singular value as `σ`, so `‖YW‖² ≥ σ²‖W‖²`), reducing to the
two-radius form + a `σ`-charge (Codex: "handled by descent, or by banking one factor with an injective
surviving-frame bound"). **Load-bearing routing requirement for the build:** split the `(ℓ,s)` atlas into
{single-block: `stratum_corner_lt_top`} vs {`ℓ=0`/`h>0` biquadratic: `twoBlock_radial_le` after a
surviving-frame `σ`-bank}. **Feeding `‖YW‖²` into `stratum_corner_lt_top` (both `hom` and `hlb` false) is a
concrete unsoundness the build must avoid.**

**Note (Q-A ↔ Q-B link).** The "surviving-frame `σ`-bank" the biquadratic corner needs is a **front-block**
analogue of Brick F (`exists_headSplitFrame`'s `U_s`), applied to a degenerating FRONT pivot — NOT the deep
factor. It does not resurrect the deep-stratum gate (which stratifies the DEEP rank). But it means Brick F's
"likely droppable" (recon §6D) is **contingent on the `ℓ=0` corner being closed by `twoBlock_radial_le` +
descent without needing a front-pivot floor** — scope this at build start.

### 2.3 No genuine higher-order (odd-cycle) kill in the unit-Jacobian charts

The only way `hlb` could fail with a genuine **higher-order** vanishing (a pure `x²+y⁴` / odd-cycle deficit,
`rlct < codim/2`) is a coordinate artifact of a **radialising, Jacobian-dropping** chart (seamrlct §10, Codex
`bal-answer`). In the atlas's **unit-Jacobian Schur charts** (`chart5_bigcell_cov` Jac ≡ 1;
`corner_block_cube_lintegral_lt_top` carries the honest `r^{N−1}` polar Jacobian) the seam incidence is
balanced and `rlct = codim/2` natively. **Guard (seam-cert §10, restated):** keep the Schur charts atomic
(unit-Jac); never radialise-and-drop `|det J|`. Under that discipline the single-block strata are clean
Morse–Bott (no odd-cycle kill), and the only non-single-block piece is the biquadratic corner of §2.2.

---

## 3. Levels kept apart

- **Quiver/orbit** — untouched; consumed via the recursion `minAdm`/`redChain` (`RouteMLayerSplit`).
- **Codim `(C, θ)`** — `clsCodim` (`ℕ` block count), the gate `minAdm M ≤ clsCodim + ab` (`clsCodim_gate_genL`,
  general-`L`, PROVEN). This cert does not re-prove it; it establishes the analytic realization (`g`
  Morse–Bott, `hlb>0`) that turns the gate into the radial finiteness `∫ r^{C−1−2q}dr<⊤`.
- **RLCT cap** — `rlct = ½·codim` is the cited Aoyagi equality globally; the native lower bound rides the
  unit-Jacobian Schur charts (seamrlct §10). This cert works at the **finiteness/`(□)`** level (the per-shell
  integrability), which needs only the radial + descent, NOT the cited equality.

---

## Close

- **Firmest result.** (Q-A) Arch-1 is sound; the deep-stratum arc is off-path/unnecessary. But the deep-factor
  **integrability is closed by the DESCENT (IH on `redChain u M`), not by `hGae`** — `hGae` only enables the
  a.e. Γ-peel. Three load-bearing conditions: **binding-anchored** cuts (0/117 404 good chains vs 174 100
  non-binding counterexamples), the **`hZrank`** rankgen input, and the comparator domination being a
  **proved** lemma (brick A). (Q-B) single-block `g = ‖Λw‖²` is exact-`hom` + `hlb = σ_min(Λ)²>0` on the
  compact chart interior (Morse–Bott, `rank D mult = minAdm` verified); the biquadratic `‖YW‖²` corner
  (`ℓ=0`/`h>0`) is degree-4 with no floor and MUST route through `twoBlock_radial_le`, not
  `stratum_corner_lt_top`.
- **Most likely to break it.** (Q-A) if a build ever peels off the binding cut, hGae fails on positive measure
  (174 100 witnesses) — the descent + hZrank + binding must all be wired together; and the comparator
  domination (brick A) is the unbuilt piece where a real gap could hide. (Q-B) mis-routing the `ℓ=0`
  biquadratic corner into the single-block radial (both `hom` and `hlb` false) is a concrete unsoundness; and
  the `a=σ_min² → 0` chart-boundary factor must be absorbed by chart4 + gluing, not dropped.
- **Next construction/consult that would settle the open part.** (i) Pin the top-level comparator domination
  lemma `∫_p[charge·frontLoss] ≤ K·cornerComparator(redChain u M).integral(c'−ab/2)` — the reassembly of the
  `A_cor`-charge + deep factor into the shorter-chain comparator (this is the brick that actually closes
  Q-A). (ii) Enumerate the `(ℓ,s)` atlas with the single-block vs biquadratic split explicit, and confirm the
  `ℓ=0` corner is closed by `twoBlock_radial_le` + descent WITHOUT a front-pivot surviving-frame (settles
  Brick-F droppability). (iii) bltj's `(ℓ,s)`-completeness (`min over strata = 2·T1`, the `b<j` regime) is a
  residual coverage caveat noted in `RouteMSJIncidenceExponent` — decorrelated-closed per routeverify but not
  yet Lean-proven.

Files (absolute):
- `…/expeditions/2026-06-20-aoyagi-full/threads/genm-arch1probe/arch1-cert.md` (this cert)
- `…/expeditions/2026-06-20-aoyagi-full/threads/genm-arch1probe/codex/arch1-{prompt,answer}.md`, `arch1-run.log`
- scans: `/tmp/deepscan.py` (exact `ℕ` recursion), `/tmp/mb2.py` (Morse–Bott + `σ_min` illustration)
