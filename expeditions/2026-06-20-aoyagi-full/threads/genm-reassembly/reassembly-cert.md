# reassembly — the CHARGE→COMPARATOR reassembly (Arch-1 step 6): PINNED for arity-3 (L=0); a genuine DEEP-GRAM RESIDUAL for general L≥1

**Seat:** pen-and-paper (adjudication, decorrelated), aoyagi-full Stage 2, `genm-reassembly`.
**Date:** 2026-07-15. **NO Lean edits, NO build.** Exact algebra (coarea Jacobian of a linear surjection,
Wishart / determinantal-variety lct, matrix-product RLCT) + numerics as GUIDE/confirmation only. Decorrelated
`local-codex-consult` (gpt-5.6, xhigh, my conclusion WITHHELD; prompt framed "argue whichever way"):
`codex/reassembly-{prompt,answer}.md` — **returned; INDEPENDENTLY CONCURS on all three questions (§5)** and
contributed a cleaner scaling obstruction (`Z = tZ₀`) that upgrades my one soft caveat to rigorous (§3.2).

**Consumed / verified (signatures, not paraphrased):**
`RouteMSJDecorated.lean` (`SJDecoration.integral` :139, `decLoss` :128, `carrierThreshold` :64,
`radialAttach_decLoss` :262), `RouteMSJCornerComparator.lean` (`cornerComparator` :50,
`cornerComparator_decLoss` :110 = `commonDivisor²·frobSq(prod M')`), `RouteMLayerSplit.lean`
(`redChain` :40, `minAdm`/`minAdmRec` :51/58), and on `origin/genm-deepatlas`:
`RouteMSJIncidenceAssembly.lean` (`coupledBoxIntegrand` :417, `freedSchurLoss_gammaPeel_le` :493,
`frontChargeIntegrand` :553, `frontLossIntegrand` :645, `frontCharge_factor` :668,
`shellSpine_le_frontCharge` :610, `deeperFlagZdeep`, `Q_b = A_cor·deeperFlagZdeep`),
`RouteMSJIncidenceExponent.lean` (`clsCodim` :45 — **Fin 3 / L=0 only**, `clsCodim_add_ab_eq` :51,
`minAdm_arity3` :68, `clsCodim_gate` :82), `RouteMSJTwoBlockRadial.lean` (`twoBlock_radial_le`).
Cross-read: `genm-arch1probe/arch1-cert.md` §1.1/§1.2/§2.2, `genm-routeverify/routeverify-cert.md` §1/§5/§6,
`genm-incidencepp/incidence-cert.md` §3/§3b/§4, `genm-bltj/mixdegen-cert.md` §3.
Scans (exact ℕ recursion + exact-RLCT criteria; MC guide/confirmation): `/tmp/minadm.py`,
`/tmp/deepresid.py`, `/tmp/witness_summary.py`, `/tmp/confirm_witness.py`.

---

## ★ ERRATUM (2026-07-16) — Verdict B's "`∫ frontChargeIntegrand = +∞`" is RETRACTED

**`∫_p frontChargeIntegrand` is FINITE for L≥1.** genm-diagbfix refuted my +∞ self-audit and is CORRECT; I
concede on the specific point. My divergence step `∫frontCharge ≥ (inf L)·∫det⁺(ZZᵀ)^{−b/2} = +∞` was a
**direction error**: it needs `inf L > 0`, but `inf L = 0` — provable from my OWN scaling identity
`I(tZ)=|t|^{−ab}I(Z)`, which forces the pushforward-box fibre factor `L(tZ) = |t|^{b(k−a)}L(Z) → 0` (since
`bk > ab` at binding cuts). The residual `det⁺(ZZᵀ)^{−b/2}` is a non-integrable **UPPER** bound (vacuous:
`∫f ≤ K·(+∞)` says nothing); the shrinking pushforward box `Ω_Z` collapses like `det⁺(ZZᵀ)^{+b/2}` and
exactly cancels the pole. **Confirmed by exact/careful numerics (`/tmp/concede_check.py`,
`/tmp/global_check.py`):** the honest inner charge `J(Z) = ∫_{A_cor∈box} det(Q_bQ_bᵀ)^{−a/2}` stays `Θ(1)`
(`≈24.3`) as the deep smallest singular value `s_k→0` while the residual blows up (`→2083`); and the global
charge integral for `(4,4,4,4)@u=3` CONVERGES (truncated ∫ stabilises at `≈1.06e6`; small-ball exponent of
`‖A_cor A₂‖²` `≈1.78 ≫ a/2=0.5`).

**What this changes:** Verdict B's headline ("+∞ / the charge chain is dead / KILL-condition triggered") is
WRONG — the charge chain (`shellSpine → frontCharge_factor → stratum_corner`) is FINITE and **reusable**, a
bonus asset, not dead. **What SURVIVES (diagbfix concurs):** (i) the deep-Gram residual is a real coarea
upper-bound prefactor; (ii) the **scaling obstruction** `Z=tZ₀ ⟹ G/cornerComparator = |t|^{−ab} → ∞` REFUTES
the per-slice **descent onto the flat `cornerComparator`** (route α) — that domination IS unsound for L≥1;
(iii) **option 2** (deep-Gram-decorated comparator) is DEAD; (iv) arch1probe's "reabsorb into decLoss" is
FALSE; (v) the **deep-stratum gate (3a)** is load-bearing for L≥1. The correct diagnosis (diagbfix): the L≥1
sound route is the **direct joint stratified atlas** — front gate [banked] + deep-stratum gate `C_k` [banked,
`RouteMSJDeepGate`, sorry-free] — self-contained per cut, NOT a descent onto `cornerComparator`, and NOT
because the object diverges. Verdict A (arity-3) is UNAFFECTED. Read §3.2/§3.3 below through this erratum.

---

## ★ VERDICTS

**A. Arity-3 (L=0): the reassembly is CLEAN and PINNED — no deep factor, no residual.** For `M : Fin 3`
(`M = (M₀,M₁,M₂)`), `deeperFlagZdeep = I_{M₂}` (empty deep-tail product, `n = M₂`), so `Q_b = A_cor` is a FREE
`b×M₂` matrix. The `A_cor`-charge, coupled with the front loss, reassembles onto `cornerComparator`
**exactly** via the incidence charts (incidence-cert, exhaustively verified L=0: 332/332 in-scope cuts). The
exact Lean-ready RHS + the per-stratum exponent gate are in §3.1. **arch1build step (6) for arity-3 can
proceed on this identity** (one correction to the brief's RHS exponent, §1). Q1 answer (§2): the
`A_cor`-Wishart is a finite box constant iff `a+b ≤ M₂` (lct of the `b×M₂` Gram det is `(M₂−b+1)/2`); **no
deep-factor power** (`Z=I`).

**B. General L≥1 — ⚠ PARTIALLY RETRACTED (see ERRATUM at top).** The "+∞ / genuine gap / KILL-condition"
headline is WRONG: `∫frontChargeIntegrand` is FINITE (diagbfix, conceded). What survives is narrower and still
useful: the descent **onto the flat `cornerComparator`** (route α) is unsound for L≥1 (the scaling obstruction),
so the sound L≥1 route is the direct joint stratified atlas + deep-stratum gate (3a) — NOT a `Fin 3 → Fin(L+…)`
lift of the L=0 descent. The text below documents the (correct) coarea residual + (correct) scaling obstruction;
its inference "therefore the object is +∞" is the retracted over-read. — The `A_cor`-measure carries a coarea
Jacobian `det⁺(Z_deep Z_deepᵀ)^{−b/2}` (`det⁺` =
product of nonzero eigenvalues) because `Q_b = A_cor·Z_deep` only sees `row(Z_deep)`; the `cornerComparator`
(flat deep measure, loss `frobSq(prod M') = ‖A'₀ Z_deep‖²`) carries no matching weight, and nothing in `G`
cancels it. This residual is **non-integrable over the deep params** for good-branch binding cuts with
`b > |M₂−M₃|` (L=1) — **including uniform-width `(d,d,d,d)`** (`t★=d−2, u=d−1, a=b=1`) **and `(3,4,5,4)@u=2`**,
all of which satisfy the L=0 scope `a+b ≤ M₂` (so the current scope does NOT catch them). **This is exactly the
route-B failure mode the controller warned against: an asserted reassembly identity that is false for general
L.** In fact (§3.3) the intermediate `∫ frontChargeIntegrand` is itself **`+∞`** for these cuts (the
a-fortiori shell-drop feeds the Morse charge form over the deep rank-drop), so `∫ frontChargeIntegrand ≤
K·cornerComparator.integral` is `+∞ ≤ finite` — and **no comparator redesign rescues it** (a dominating
comparator would carry the same `−b/2` weight and be `+∞` too). arch1probe §1.2's "`det(Z_deep Z_deepᵀ)^{−b/2}
… reabsorbed into the comparator's decLoss" is NOT valid — `det⁺(Z_deep Z_deepᵀ)^{−b/2}` is a distinct
deep-factor charge, not the comparator's loss. **Q1 power confirmed** (`−b/2`, pseudo-det), but it is a
divergent RESIDUAL, not a reabsorption. **KILL-condition #3 is triggered for L≥1.** The fix is to keep the
deep rank-drop OUT of the charge form (deep-stratum gate / undecorated descent, §3.3), NOT a comparator reshape.

**C. σ-bank (3'): DROPPABLE for L=0 — the ℓ=0 biquadratic corner closes via `twoBlock_radial_le` +
intrinsic polar, NO external front-pivot frame.** The two-radius form arises from polar-in-`W` (σ = ‖W‖ is
the intrinsic incidence-coordinate radius) + the `H̃`-fibre (the κ-stable block); the outer `W`-radial absorbs
the σ-charge under a non-empty α'-gate (§4). Parallels Brick F droppable (routeverify §5D). **CAVEAT:** for
L≥1 the corner's `W = Q_p·N` couples the deep factor, so it inherits the Verdict-B residual — droppability is
clean only for L=0.

---

## 1. The exact comparator RHS (Lean-derived) — and a correction to the brief

`cornerComparator (redChain u M) ![1] ![jc₀]` with `d=1`, `k = ![1]`, `jc₀ = minAdm(redChain u M) − 1`. From
`SJDecoration.integral` (:139) and `cornerComparator_decLoss` (:110, `decLoss v z = commonDivisor(supp)² ·
frobSq(prod M' z)`, and `commonDivisor(≡![1]) v = |v₀|¹`):

    cornerComparator(redChain u M) ![1] ![minAdm(M')−1] .integral(q)
      = ∫_{z' ∈ Params(M')} ∫_{v₀∈[0,1]}  |v₀|^{(minAdm(M')−1)}  ·  ( |v₀|² · frobSq(prod M' z') )^{−q}
      = ∫_{z'} ∫_{v₀}  |v₀|^{ minAdm(M') − 1 − 2q }  ·  frobSq(prod M' z')^{−q},          M' := redChain u M.

> **⚠ Brief correction.** The dispatch wrote the monomial weight as `|v₀|^{2(minAdm−1)−2q}`. The exact Lean
> object gives **`|v₀|^{(minAdm(M')−1) − 2q}`** — the Jacobian exponent is `jc₀ = minAdm(M')−1` (single, not
> doubled); the factor `|v₀|²` lives in `decLoss`, not in the monomial. This is load-bearing: the radial
> `∫₀¹ v₀^{minAdm(M')−1−2q} dv₀` converges iff `q < minAdm(M')/2 = carrierThreshold(M')` — the clean IH
> threshold. The doubled exponent would give the wrong threshold `minAdm(M')−½`. Use the single form.

`frobSq(prod M' z')` is the honest reduced-chain loss: `prod M' = A'₀·Z_deep` (`A'₀` the `u×M₂` reduced first
layer, `Z_deep = deeperFlagZdeep`), so `frobSq(prod M' z') = ‖A'₀ Z_deep‖²_F = ‖Q_p‖²_F`. **The comparator
integrates the deep params with FLAT Lebesgue** (`Z := Params M'`, `mZ := inferInstance`, `dom :=
paramsBoxM M' 1`) — no deep-Gram weight. This flat-measure fact is the crux of Verdict B.

---

## 2. Q1 — the `A_cor`-Wishart integral, exactly

Isolated (charge alone, front loss set aside): `I(Z) = ∫_{A_cor∈box} det((A_cor Z)(A_cor Z)ᵀ)^{−a/2} dA_cor`,
`A_cor : b×M₂`, `Z := Z_deep : M₂×n`, rank `k = min(M₂,…,M_last) = deepTailMin`.

Factor `Z = S·Ẑ`, `Ẑ ∈ ℝ^{k×n}` orthonormal rows spanning `row(Z)`, `S = Z Ẑᵀ ∈ ℝ^{M₂×k}` (rank `k`);
`Sᵀ S = det⁺(ZZᵀ)`-carrier, `Q_b = A_cor Z = (A_cor S)Ẑ`. Since the charge is `det(Q_bQ_bᵀ)^{−a/2} =
det((A_cor S)(A_cor S)ᵀ)^{−a/2}` (Ẑ orthonormal), and `A_cor S` ranges over `ℝ^{b×k}` (surjection, `S` full
col rank), the coarea Jacobian of `A_cor ↦ Â := A_cor S` is `det(SᵀS)^{b/2} = det⁺(ZZᵀ)^{b/2}` (√det of the
row map, `b` rows). Hence **[FACT, coarea + determinantal lct]**:

    I(Z) = det⁺(Z Zᵀ)^{−b/2} · (box const) · ∫_{Â∈ℝ^{b×k}, box} det(ÂÂᵀ)^{−a/2} dÂ,
    the Â-integral finite ⟺ a/2 < (k−b+1)/2 ⟺ a+b ≤ k = deepTailMin.

- **Power: `−b/2`** on the deep Gram (arch1probe §1.2's power is CORRECT). But note the OBJECT: for `M₂ > k`
  (deep rank-deficient as an `M₂×M₂` Gram) the FULL `det(ZZᵀ) = 0`; the correct factor is the **pseudo-det**
  `det⁺(ZZᵀ) = det(SᵀS)` (product of the `k` nonzero eigenvalues), never the full det.
- **Criterion: `a+b ≤ deepTailMin`** is the tight fixed-`Z` criterion; `a+b ≤ M₂` (arch1probe/incidence-cert)
  is the LOOSER statement (`deepTailMin ≤ M₂`). At binding cuts arch1probe (i) gives `a+b ≤ deepTailMin−1`, so
  both hold with room.
- **L=0 special case:** `Z = I_{M₂}`, `k = M₂`, `det⁺ = 1` — **no deep-factor power**, `I` a box constant iff
  `a+b ≤ M₂`. This is why the arity-3 route is clean.
- **Precision caveat (decorrelated Codex §5):** for a FIXED box, `I(Z) ≠ C·det⁺(ZZᵀ)^{−b/2}` exactly — the
  residual `∫_{Â} det(ÂÂᵀ)^{−a/2} ρ_{Ω,Z}(Â) dÂ` still depends on `Z`'s singular subspaces + the transformed
  box (fibre volume `ρ`). The `det⁺(ZZᵀ)^{−b/2}` is the exact COAREA prefactor; the scaling identity
  `I(tZ) = |t|^{−ab} I(Z)` vs `det⁺(tZ)^{−b/2} = |t|^{−bk} det⁺(Z)^{−b/2}` shows the fibre integral supplies
  `t^{b(k−a)}` — so "(box const)" is not literally `Z`-constant, but the deep-Gram SINGULARITY is exactly
  `det⁺(ZZᵀ)^{−b/2}`, which is what drives Verdict B.

---

## 3. Q2 — the reassembly: CLEAN for L=0, RESIDUAL for L≥1

### 3.1 L=0 (arity 3) — CLEAN, the exact step-(6) spec for arch1build

`M=(M₀,M₁,M₂)`, cut `u`, `a=M₀−u`, `b=M₁−u`, `q=c'−ab/2`, `Q_b=A_cor` (free `b×M₂`), `Q_p=A'₀` (free `u×M₂`,
`= prod(redChain u M)` since `redChain u M = (u,M₂)`, a 2-width leaf, `minAdm = u·M₂`, `jc₀ = uM₂−1`):

    ∫_{(A'₀,A_cor)∈ box} frontChargeIntegrand M u c'
      ≤  K · cornerComparator (u,M₂) ![1] ![uM₂−1] .integral(q)
      =  K · ∫_{A'₀∈box} ∫_{v₀∈[0,1]}  |v₀|^{ uM₂ − 1 − 2q } · ‖A'₀‖_F^{−2q}  dv₀ dA'₀,    K ~ 1/(T1−c').

**Mechanism (incidence-cert §3/§3b/§4, exhaustively verified L=0), Lean-ready pieces:**
1. `A_cor` `b`-minor chart `Q_b = D[I|X]`, `D∈GL_b`, `X∈ℝ^{b×d}`, `d = M₂−b`; Jac `|det D|^{d} dD dX`;
   charge `det(Q_bQ_bᵀ)^{−a/2} = |det D|^{−a} · det(I+XXᵀ)^{−a/2}` (latter a UNIT `≥1`).
2. `Q_p`-shear `W = Q_p·N` (`N=(−X;I_d)`, Jac 1) — the incidence coordinate; front `B`-shear `H = PU+BD`
   (Jac `|det D|^{−u}`) + `H̃`-completion (unimodular). **Net `|det D|` power `= M₂−b−a−u`, integrable near
   `det D=0` ⟺ `a+b ≤ M₂`** (the ONLY scope for L=0).
3. `H̃`-fibre `∫_{H̃}(‖H̃‖²+τ²)^{−q} ≍ τ^{ub−2q}`, `τ=‖YW‖`, `Y=(P;C)∈ℝ^{M₀×u}`; determinantal big-cells of
   `W` (rank ℓ) and `Y` (rank s) give the radial `∫₀^δ r^{C_{ℓ,s}−1−2q} dr`.
4. `C_{ℓ,s} = u·b + M₀·ℓ + (M₀−s)(u−ℓ−s) + s(d−ℓ)`; the exact `ℓ`-independent identity (incidence-cert §3)
   `C_{ℓ,s} = (M₀−s)(M₁−s)+s·M₂ − ab`, so **`min_{ℓ,s} C_{ℓ,s} = minAdm(M) − ab`** (`clsCodim_gate`,
   `minAdm_arity3`, PROVEN Fin 3) ⟹ `min C_{ℓ,s}/2 = T1_q ≤ uM₂/2 = carrierThreshold((u,M₂))` (the descent
   gate `minAdm(M) ≤ ab + uM₂`, `minAdm_le_ab_add_uM2`). Per-stratum ratio to the comparator finite, summed
   `K = ΣK_{ℓ,s} < ⊤`, per-exponent.

No deep factor ⟹ no residual; the RHS loss `‖A'₀‖²` IS `frobSq(prod(redChain u M))` exactly. **PINNED.**

### 3.2 L≥1 — the DEEP-GRAM RESIDUAL (the gap)

For `M : Fin(L+1+1+1)`, `L≥1`, `Z_deep = A₂⋯A_last ≠ I`. Both `Q_p = A'₀ Z_deep` and `Q_b = A_cor Z_deep` lie
in `row(Z_deep)`, and every load-bearing object (charge, `E_top`, `E_tr = ‖C Q_p(I−Π_b)‖²`, `Π_b`) is a
function of `Q_p, Q_b` only. Reduce `G` to `row(Z_deep)` coordinates (`Ẑ`, `S` as in §2):

    A_cor ↦ Q̂_b = A_cor S   (dA_cor = det⁺(ZZᵀ)^{−b/2} dQ̂_b · fibre),
    A'₀   ↦ Q̂_p = A'₀ S     (dA'₀  = det⁺(ZZᵀ)^{−u/2} dQ̂_p · fibre),

loss/charge become the LEAF integral on `(u,k)` (`k=deepTailMin`), with the SAME `frobSq(prod M') = ‖A'₀
Z_deep‖² = ‖Q̂_p‖²`. Bounding the leaf integral by the leaf comparator, the `−u/2` factor (from `A'₀`) is
matched on BOTH sides and cancels; the `−b/2` factor (from `A_cor`) has **nothing to cancel it in the
comparator** (the comparator has no `A_cor`). **[FACT — coarea, rigorous]:**

    ∫_{(z,A_cor)} frontChargeIntegrand  ≤  K · ∫_{deep params}  det⁺(Z_deep Z_deepᵀ)^{−b/2}
                                              · [ ∫_{A'₀} (|v₀|²‖A'₀ Z_deep‖²)^{−q} dA'₀ ]  d(deep),
    vs.  cornerComparator.integral(q) = ∫_{deep} [ ∫_{A'₀} (|v₀|²‖A'₀ Z_deep‖²)^{−q} ] d(deep).

**The uncompensated residual `det⁺(Z_deep Z_deepᵀ)^{−b/2}` is a deep-Gram charge the comparator does not
carry.** It is a FIXED-exponent (`b/2`, `q`-independent) weight against the FLAT deep measure. It blows up on
the deep rank-drop `{rank Z_deep < k}` (where `‖A'₀ Z_deep‖²` is generically `O(1)`, so the comparator's loss
gives no compensation).

> **⚠ RETRACTED INFERENCE (see ERRATUM).** The residual-integrability computation below is CORRECT as a fact
> about the **upper-bound prefactor `det⁺(ZZᵀ)^{−b/2}` alone**, but it does NOT bound the honest object: the
> object also carries the pushforward-box fibre factor `L(Z) → 0` (like `det⁺^{+b/2}`), which cancels the
> pole. So "non-integrable residual" ≠ "divergent object" — the object is FINITE (`/tmp/concede_check.py`,
> `/tmp/global_check.py`). The table lists where the *majorant* diverges (a failed bound), NOT where the
> object diverges (nowhere). Kept for the record; the divergence conclusion is withdrawn.

**Integrability of the residual over the deep params (L=1 single layer `Z=A₂`, `M₂×M₃`) [FACT about the
majorant, exact]:** `RLCT(det⁺(A₂A₂ᵀ)) = (|M₂−M₃|+1)/2`, so `det⁺(A₂A₂ᵀ)^{−b/2}`
integrable ⟺ `b/2 < (|M₂−M₃|+1)/2` ⟺ **`b ≤ |M₂−M₃|`**.

**Good-branch binding strict-shell cuts where the MAJORANT is NON-integrable (`b > |M₂−M₃|`)** — 9 in the
small search `M₀,M₁≤5` (these are where the naive coarea UPPER bound fails, NOT where the object diverges):

| M | t★ | u | a | b | `\|M₂−M₃\|` | residual | signature (`/tmp/confirm_witness.py`) |
|---|---|---|---|---|---|---|---|
| (4,4,4,4) | 2 | 3 | 1 | 1 | 0 | `\|det A₂\|^{−1}` | **log-divergent** (uniform width) |
| (5,5,5,5) | 3 | 4 | 1 | 1 | 0 | `\|det A₂\|^{−1}` | **log-divergent** (uniform width) |
| (3,4,5,4) | 1 | 2 | 1 | 2 | 1 | `det(A₂ᵀA₂)^{−1}` | divergent |
| (3,4,4,5) | 1 | 2 | 1 | 2 | 1 | `det(A₂A₂ᵀ)^{−1}` | divergent |
| (4,5,5,5),(4,5,5,6),(4,5,6,5),(3,5,5,6),(3,5,6,5) | … | | 1 | 2/3 | 0/1 | | divergent |

Contrast: `(3,3,4,3)@u=2` (`b=1 ≤ |4−3|=1`, boundary) and `(4,5,6,4)@u=3` (`b=2 < |6−4|=2`... at `b/2=1 <
1.5`, integrable) have the residual INTEGRABLE (`/tmp/confirm_witness.py`: truncated ∫ stable).

**The scaling obstruction (rigorous, no `L(Z)` needed) [FACT, decorrelated Codex-derived §5].** On the ray
`Z = t·Z₀` (`t→0`, a direction that lies in the deep-param box):

    G_{tZ₀} = |t|^{−ab−2q} · G_{Z₀},     cornerComparator_{tZ₀} = |t|^{−2q} · cornerComparator_{Z₀},

so the per-`Z` slice ratio `G/cornerComparator = |t|^{−ab} → ∞` as `t→0` whenever `ab > 0`. **Hence NO
`Z`-uniform (integrand-level / per-deep-slice) domination `G ≤ K·cornerComparator` can hold near the deep
origin** — the constructive descent (the form a Lean proof needs: bound the integrand, then integrate) is
refuted directly, for EVERY L≥1 cut with `ab>0`, without appealing to `L(Z)`'s asymptotics. **This part
SURVIVES** — the scaling obstruction is a valid refutation of the per-slice descent onto the flat comparator.

> **⚠ RETRACTED (see ERRATUM).** I previously wrote here that "the INTEGRATED domination fails additionally
> … `∫ frontChargeIntegrand` itself diverges … `+∞ ≤ finite`." That is WRONG. `∫ frontChargeIntegrand` is
> FINITE (diagbfix, conceded; `/tmp/concede_check.py`, `/tmp/global_check.py`). The scaling obstruction only
> refutes the **per-slice/integrand-level** domination onto the flat `cornerComparator` (route α), not the
> finiteness of the object. The correct L≥1 route is the DIRECT joint stratified atlas + deep-stratum gate
> (3a), which does NOT descend onto `cornerComparator`.

**The object IS finite (diagbfix, conceded).** `∫frontChargeIntegrand` is finite for all `c' < carrierThreshold`
— the deep rank-drop is NOT a pole (the pushforward-box fibre `L(Z)→0` cancels the residual majorant; `J(Z)=Θ(1)`
at the codim-1 drop, global ∫ converges, §ERRATUM). So the Γ-peel charge form is NOT "too lossy"; the honest
reason the descent-onto-`cornerComparator` fails is the scaling obstruction (per-slice ratio `|t|^{−ab}→∞`), a
statement about the DOMINATION shape, not the object's finiteness.

**This corrects arch1probe Q-A (and diagbfix concurs).** Its conclusion "the deep-stratum arc is off-path; the
descent handles the deep factor" rests on §1.2's invalid "reabsorption" — refuted by the scaling obstruction
(the per-slice descent onto `cornerComparator` is unsound). So the **deep-stratum arc is reopened / load-bearing
for L≥1** — but as the sound ROUTE (the direct joint per-stratum gate `C_k` on the finite object), NOT because
the object diverges (it does not) and NOT requiring a separate lower-arity descent over the deep strata
(`frontChargeIntegrand` is already finite over them; diagbfix VERDICT 2). arch1probe's L=0 verdicts and its
`hGae`/`hZrank`/binding conditions stand; only its general-L "descent handles the deep factor" claim fails.

### 3.3 What the fix must supply (CORRECTED per ERRATUM — the object is finite; the descent shape is the issue)

> **⚠ RETRACTED.** This section previously argued "the charge form `∫ frontChargeIntegrand` is itself `+∞`"
> via `∫ ≥ (inf L)·∫det⁺^{−b/2} = +∞`. That is WRONG: `inf L = 0` (the pushforward box collapses like
> `det⁺^{+b/2}`; §ERRATUM, `/tmp/concede_check.py`), so the lower bound is `0·∞`, invalid — and the object is
> FINITE (`/tmp/global_check.py`). diagbfix refuted this and is correct; I concede.

**The corrected picture.** `∫ frontChargeIntegrand` is FINITE for all L≥1 good cuts. So the charge chain
(`shellSpine → frontCharge_factor → stratum_corner`) is a **reusable asset**, not dead. What genuinely fails
for L≥1 is only the **per-slice descent onto the flat `cornerComparator`** (route α), refuted by the scaling
obstruction (§3.2) — a statement about the DOMINATION shape, not the object. So:

1. **Scope step (6) to arity-3 (L=0) now** — clean, buildable (§3.1) — and treat general L as a genuinely-open
   brick (= routeverify Brick B), NOT a mechanical `Fin 3 → Fin(L+…)` lift. (Recommended: unblocks
   arch1build immediately without an unsound general-L claim.)
2. **Option 2 (deep-Gram-decorated comparator) is DEAD** — but for the RIGHT reason (diagbfix VERDICT 5). Not
   because any intermediate is `+∞` (it is finite), but because decorating `cornerComparator` to match a
   SPURIOUS residual (the vacuous majorant) introduces an unnecessary deep-Gram-weighted IH that does not
   close. Drop it.
3. **The sound L≥1 route is the DIRECT joint stratified atlas — front gate [banked] + deep-stratum gate `C_k`
   (3a)** — NOT a descent onto `cornerComparator`. diagbfix (adjudicated winner): `frontChargeIntegrand` is
   ALREADY finite over every deep stratum `{rank Z_deep = ρ−k}` (the corank charge is inert at the binding
   stratum), so (3a) is a JOINT per-stratum RLCT gate `C_k = min(uρ, u(ρ−k)+κ_k−γ_{ρ−k}) ≥ minAdm(M)−ab =
   2T1_q` — the banked, sorry-free `deepGate_branch` (`RouteMSJDeepGate`), each stratum radial-finite via the
   same `corner_block_cube_lintegral_lt_top` engine as `stratum_corner_lt_top`. It needs NO separate
   lower-arity descent over the deep rank-drops (my earlier (3a) framing was heavier than needed). **(3b)**
   (undecorated descent) is viable ONLY as the full Aoyagi §5 `(S,J)` recursion, NOT as a "drop the Γ-peel"
   shortcut — the charge `det(Q_bQ_bᵀ)^{−a/2}` is the EXACT Gaussian integral of the peeled corank block,
   intrinsic to any front peel (diagbfix §4).

The **deep-stratum arc is load-bearing for L≥1** (arch1probe's "off-path" is un-reversed) — but the correct
consequence is the JOINT gate (3a) on the finite object, not a wall and not a comparator reshape. Any general-L
build must NOT assert the descent `∫ frontChargeIntegrand ≤ K·cornerComparator.integral` (unsound per the
scaling obstruction) — but it MAY use `∫ frontChargeIntegrand < ⊤` directly (it is finite) as the reusable
front-charge asset feeding the joint atlas.

---

## 4. Q3 (3') — the σ-bank / ℓ=0 biquadratic corner: DROPPABLE (L=0)

The ℓ=0 corner front loss (after the `H̃`-fibre) is `∫_{H̃,Y,W}(‖H̃‖² + ‖Y·W‖²)^{−q}`, `Y=(P;C)∈ℝ^{M₀×u}`,
`W∈ℝ^{u×d}` (`d=M₂−b`). **Verdict (a): the σ-bank is DROPPABLE — no externally-supplied front-pivot
orthonormal frame / Loewner floor is needed.** [FACT for L=0]

**Mechanism (intrinsic, sharpened by decorrelated Codex §5).** The one subtlety: the σ-scaled block is NOT
all of `Y` — it is the **leading left-singular direction** of `W`. Let `σ = ‖W‖_F`, `τ₁` = top singular value
of `W`, `p = min(u, d)`; then `τ₁² ≥ σ²/p`, and with `e₁(W)` the (intrinsic) leading left singular vector,

    ‖Y·W‖²_F = tr(Y W Wᵀ Yᵀ) ≥ τ₁²‖Y e₁‖² ≥ (σ²/p)·‖Y e₁‖².

The orthogonal split `Y ↦ (Y e₁ ∈ ℝ^{M₀}, Y_⊥)` has Jacobian 1 and `Y_⊥` contributes only bounded volume.
Feed `twoBlock_radial_le` with the **`H̃`-block as the κ-stable block** (`d_u = ub`, `κ=1`) and the **leading
`Y e₁`-slice as the σ-scaled block** (`d_v = M₀`, the row-dim of `Y` — NOT `d_v = M₀·u = dim Y`), `σ = ‖W‖`:

    ∫_{H̃, Ye₁}( ‖H̃‖² + σ²‖Ye₁‖² )^{−q}  ≤  C · σ^{−α'},   C σ-independent,   max(0, 2q − ub) < α' < M₀,

then the **outer `W`-radial** (`∫₀^B σ^{dW−1} · σ^{−α'} dσ`, `dW = u·d`) absorbs it, finite ⟺ `α' < dW`.
Composite gate `max(0, 2q − ub) < α' < min(M₀, u·d)` — non-empty ⟺ `2q < ub + min(M₀, u·d)`, which holds in
the operative range `q < T1_q` (matches the `C_{ℓ,s}` min at `(ℓ,s)=(0,·)`; corner `(2,2,3)` gives two radial
`∫r^{2−2q}dr`, `C_{0,0}=3`). The σ is the **intrinsic incidence-coordinate radius `‖W‖`**, an integration
variable — NOT a banked external frame; `twoBlock_radial_le`'s `C` is σ-independent, so no frame field is
threaded. **Using `d_v = dim Y = M₀·u` instead of the leading slice `M₀` WOULD require an external Loewner
floor `W Wᵀ ⪰ σ²·I_u` — that is the failure mode to avoid.** The `Y`-rank degeneration (`σ_min(Y)→0`) is the
`s`-index determinantal big-cell (intrinsic), not a floor. Parallels **Brick F droppable** (routeverify §5D).

**CAVEAT (L≥1).** For `L≥1`, `W = Q_p·N` with `Q_p = A'₀ Z_deep` couples the deep factor, so the corner's
`σ = ‖W‖` polar and the `Y`-block sit under the same deep-Gram residual as §3.2. So (a) "droppable" is clean
for L=0; for L≥1 the ℓ=0 corner inherits the Verdict-B residual and is not independently closable.

---

## 5. Decorrelated Codex (conclusion WITHHELD; prompt "argue whichever way")

`codex/reassembly-{prompt,answer}.md` (gpt-5.6, xhigh, no repo access, my verdicts withheld). Independent,
CONCURS on all three, and sharpened two points:
- **Q1 [FACT].** Coarea prefactor is `pdet(ZZᵀ)^{−b/2}` (my `det⁺`); full det must not be used when `M₂>k`;
  criterion `b≤k, a<k−b+1`; **and** a fixed-box `I(Z)` is not a determinant-only function of `Z` (the fibre
  volume matters) — the scaling identity `I(tZ)=|t|^{−ab}I(Z)` proves it. (Folded into §2.)
- **Q2 [FACT + INFERENCE].** "After row-space coarea + a `Z`-uniform leaf estimate, an uncompensated
  `Δ_k(Z)^{−b/2}` remains" — verbatim my §3.2. Option (ii): integrable iff `b < |m−n|+1` (single free layer),
  and for a **width-`k` bottleneck `Z=LR`**, `Δ_k(LR) = det(LᵀL)·det(RRᵀ)`, so **square `k×k` factors give
  threshold `b<1` — every `b≥1` fails**. "The supplied IH does NOT constructively prove `G<∞` for a genuine
  deep product … a separate weighted local-zeta estimate would be needed." **NB (ERRATUM):** Codex was
  careful here — "the IH does not CONSTRUCTIVELY prove `G<∞`" is TRUE and does NOT say `G=+∞`; my §3.3 over-read
  it into "+∞", which diagbfix refuted (`G` is finite). Codex contributed the scaling obstruction `Z=tZ₀`
  (slice ratio `|t|^{−ab}→∞`, §3.2) — that refutes the per-slice DESCENT, which is the surviving content.
- **Q3 [FACT].** Frame DROPPABLE, provided `d_v` is the **leading-singular slice** `Ye₁` (`d_v = M₀`), not all
  of `Y` (that would need a Loewner floor); gate `max(0, 2q−ub) < α' < min(M₀, u·d)`. (Folded into §4.)

No point of divergence between my exact-algebra derivation and the decorrelated consult.

---

## 6. Levels kept apart

- **Quiver/orbit** — untouched; consumed via `minAdm`/`redChain` (`RouteMLayerSplit`).
- **Codim `(C,θ)`** — `clsCodim`/`clsCodim_gate` are the `ℕ` block-count gate, **Fin 3 (L=0) ONLY** (verified).
  The general-`L` gate against `minAdm(redChain u M)` is unbuilt (routeverify Brick B); §3.2 shows it is NOT a
  ring-identity lift — the deep factor changes the analysis.
- **RLCT cap / finiteness** — this cert works at the per-shell FINITENESS/(□) level (the descent domination),
  not the cited Aoyagi `rlct = ½·codim` equality. The finiteness threshold `T1_q = (minAdm(M)−ab)/2` and the
  gate `minAdm(M) ≤ ab + minAdm(M')` are exact (0/75 411, banked); the gap is the CONSTRUCTIVE realisation for
  L≥1, not the arithmetic.

---

## Close

- **Firmest result.** Arity-3 (L=0) reassembly is CLEAN and PINNED — the exact identity + per-stratum gate in
  §3.1, with the brief's monomial exponent corrected to `|v₀|^{minAdm(M')−1−2q}` (single, not doubled).
  **arch1build step (6) can proceed for arity-3.** For general **L≥1** (CORRECTED per ERRATUM, diagbfix
  conceded): `∫ frontChargeIntegrand` is **FINITE** (my "+∞" was a direction error — `inf L = 0`, the vacuous
  majorant); the charge chain is a **reusable asset**. What genuinely fails is only the per-slice **descent
  onto the flat `cornerComparator`** (scaling obstruction `|t|^{−ab}→∞`, SURVIVES) — so L≥1 is not a
  `Fin 3→Fin(L+…)` descent-lift; the sound route is the direct joint stratified atlas + **deep-stratum gate
  `C_k`** (3a, banked sorry-free `RouteMSJDeepGate`). σ-bank (3') is DROPPABLE for L=0.
- **Most likely to break it.** (a) Arity-3 (Verdict A) is unaffected — proceed. (b) The SURVIVING L≥1 content
  (scaling obstruction refutes route-α descent; option 2 dead; deep-stratum arc load-bearing) is solid and
  diagbfix-concurred. The RETRACTED content (the "+∞" object-divergence) is fully conceded — the residual
  `det⁺^{−b/2}` is a vacuous non-integrable UPPER bound, not a divergence proof (`/tmp/concede_check.py`:
  `J(Z)=Θ(1)` at rank-drop; `/tmp/global_check.py`: global ∫ converges). Lesson banked: a non-integrable
  MAJORANT never proves an integral diverges — I should have computed the honest `J(Z)` (bounded) from the
  start, not the residual alone.
- **Next construction/consult.** (i) Ship arity-3 step (6) (§3.1). (ii) L≥1: build the direct joint stratified
  atlas + deep-stratum gate `C_k` (diagbfix's adjudicated (3a)); confirm `C_k ≥ 2T1_q` on the finite object
  per stratum (banked `deepGate_branch`, `minAdm3_add_chargeExp_le`). (iii) If a pen-and-paper adjudication of
  (3a) `C_k` vs the front-gate composition is wanted, I can take it.

**Files (absolute):**
- `/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/genm-reassembly/reassembly-cert.md` (this cert)
- `…/genm-reassembly/codex/reassembly-{prompt,answer}.md` (decorrelated consult)
- scans (in the thread dir): `minadm.py`, `witness_summary.py`, `confirm_witness.py` (majorant — the vacuous
  bound), and the CONCESSION checks `concede_check.py` (`J(Z)=Θ(1)` at rank-drop), `global_check.py` (global ∫
  converges) — the decisive refutation of the retracted "+∞".
