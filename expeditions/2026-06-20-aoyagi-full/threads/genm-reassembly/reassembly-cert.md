# reassembly — the CHARGE→COMPARATOR reassembly (Arch-1 step 6): PINNED for arity-3 (L=0); a genuine DEEP-GRAM RESIDUAL for general L≥1

**Seat:** pen-and-paper (adjudication, decorrelated), aoyagi-full Stage 2, `genm-reassembly`.
**Date:** 2026-07-15. **NO Lean edits, NO build.** Exact algebra (coarea Jacobian of a linear surjection,
Wishart / determinantal-variety lct, matrix-product RLCT) + numerics as GUIDE/confirmation only. Decorrelated
`local-codex-consult` (gpt-5.6, my conclusion WITHHELD; prompt framed "argue whichever way"):
`codex/reassembly-{prompt,answer}.md` (pending at write time — folded in when it returns; the finding below
does not rest on it).

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

## ★ VERDICTS

**A. Arity-3 (L=0): the reassembly is CLEAN and PINNED — no deep factor, no residual.** For `M : Fin 3`
(`M = (M₀,M₁,M₂)`), `deeperFlagZdeep = I_{M₂}` (empty deep-tail product, `n = M₂`), so `Q_b = A_cor` is a FREE
`b×M₂` matrix. The `A_cor`-charge, coupled with the front loss, reassembles onto `cornerComparator`
**exactly** via the incidence charts (incidence-cert, exhaustively verified L=0: 332/332 in-scope cuts). The
exact Lean-ready RHS + the per-stratum exponent gate are in §3.1. **arch1build step (6) for arity-3 can
proceed on this identity** (one correction to the brief's RHS exponent, §1). Q1 answer (§2): the
`A_cor`-Wishart is a finite box constant iff `a+b ≤ M₂` (lct of the `b×M₂` Gram det is `(M₂−b+1)/2`); **no
deep-factor power** (`Z=I`).

**B. General L≥1: the charge-form reassembly has an UNCOMPENSATED deep-Gram residual
`det⁺(Z_deep Z_deepᵀ)^{−b/2}` that does NOT land on `cornerComparator` — a genuine gap, NOT a mechanical
lift of the L=0 gate.** The `A_cor`-measure carries a coarea Jacobian `det⁺(Z_deep Z_deepᵀ)^{−b/2}` (`det⁺` =
product of nonzero eigenvalues) because `Q_b = A_cor·Z_deep` only sees `row(Z_deep)`; the `cornerComparator`
(flat deep measure, loss `frobSq(prod M') = ‖A'₀ Z_deep‖²`) carries no matching weight, and nothing in `G`
cancels it. This residual is **non-integrable over the deep params** for good-branch binding cuts with
`b > |M₂−M₃|` (L=1) — **including uniform-width `(d,d,d,d)`** (`t★=d−2, u=d−1, a=b=1`) **and `(3,4,5,4)@u=2`**,
all of which satisfy the L=0 scope `a+b ≤ M₂` (so the current scope does NOT catch them). **This is exactly the
route-B failure mode the controller warned against: an asserted reassembly identity that is false for general
L.** arch1probe §1.2's "`det(Z_deep Z_deepᵀ)^{−b/2} … reabsorbed into the comparator's decLoss" is NOT valid
— `det⁺(Z_deep Z_deepᵀ)^{−b/2}` is a distinct deep-factor charge, not the comparator's loss. **Q1 power
confirmed** (`−b/2`, pseudo-det), but it is a RESIDUAL, not a reabsorption. **KILL-condition #3 is triggered
for L≥1.**

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

**Integrability of the residual over the deep params (L=1 single layer `Z=A₂`, `M₂×M₃`) [FACT, exact +
confirmed `/tmp/confirm_witness.py`]:** `RLCT(det⁺(A₂A₂ᵀ)) = (|M₂−M₃|+1)/2`, so `det⁺(A₂A₂ᵀ)^{−b/2}`
integrable ⟺ `b/2 < (|M₂−M₃|+1)/2` ⟺ **`b ≤ |M₂−M₃|`**.

**Good-branch binding strict-shell cuts where the residual is NON-integrable (`b > |M₂−M₃|`)** — 9 in the
small search `M₀,M₁≤5`, all satisfying `a+b ≤ M₂` (so the L=0 scope does NOT exclude them):

| M | t★ | u | a | b | `\|M₂−M₃\|` | residual | signature (`/tmp/confirm_witness.py`) |
|---|---|---|---|---|---|---|---|
| (4,4,4,4) | 2 | 3 | 1 | 1 | 0 | `\|det A₂\|^{−1}` | **log-divergent** (uniform width) |
| (5,5,5,5) | 3 | 4 | 1 | 1 | 0 | `\|det A₂\|^{−1}` | **log-divergent** (uniform width) |
| (3,4,5,4) | 1 | 2 | 1 | 2 | 1 | `det(A₂ᵀA₂)^{−1}` | divergent |
| (3,4,4,5) | 1 | 2 | 1 | 2 | 1 | `det(A₂A₂ᵀ)^{−1}` | divergent |
| (4,5,5,5),(4,5,5,6),(4,5,6,5),(3,5,5,6),(3,5,6,5) | … | | 1 | 2/3 | 0/1 | | divergent |

Contrast: `(3,3,4,3)@u=2` (`b=1 ≤ |4−3|=1`, boundary) and `(4,5,6,4)@u=3` (`b=2 < |6−4|=2`... at `b/2=1 <
1.5`, integrable) have the residual INTEGRABLE (`/tmp/confirm_witness.py`: truncated ∫ stable).

**Consequence.** The inner leaf integral `L(Z)` stays bounded-below-positive (or itself blows up) as
`Z_deep → rank-drop`, so `G` (the charge-form integrand of `frontChargeIntegrand`, integrated) genuinely
**diverges** for these cuts — for `(4,4,4,4)@u=3` it diverges for *every* `q ≥ 0`. Meanwhile the comparator is
finite (`q < uM₂/2`). So **`∫ frontChargeIntegrand ≤ K · cornerComparator.integral(q)` is FALSE for these
L≥1 cuts** (∞ ≤ finite). The reassembly does NOT close.

**Why the TRUE object is still finite (no contradiction with Aoyagi/bltj).** The undecorated shell integral
`∫_{shell,A',T} frobSq(T·hsQ)^{−c'} = ∫ frobSq(prod M)^{−c'}|_shell ≤ off-shell`, RLCT `= ½minAdm(M) = T1`
(arity-agnostic, bltj §3) — finite for `c'<T1`, general L. But that bound is the **circular** off-shell route
(same chain `M`; assumes the answer). The Γ-peel **charge form** `frontChargeIntegrand` is a Morse
OVER-estimate (`freedSchurLoss_gammaPeel_le` is `≤`); near the deep rank-drop the over-estimate blows up
(the residual) even though the true object is finite. **So the charge form is too lossy for general L, and the
non-circular descent onto `cornerComparator` (which the recursion NEEDS) does not hold.**

**This corrects arch1probe Q-A.** Its conclusion "the deep-stratum arc is off-path; the descent handles the
deep factor" rests on §1.2's invalid "reabsorption". The residual `det⁺(Z_deep Z_deepᵀ)^{−b/2}` is precisely a
deep-rank-drop charge, and controlling it is exactly what a deep-stratum handling would do — so the deep-strata
question is **reopened** for L≥1, not off-path. (arch1probe's L=0 verdicts and its `hGae`/`hZrank`/binding
conditions stand; only the general-L "descent handles the deep factor" claim fails.)

### 3.3 What the fix must supply (for the controller / arch1build)

The constructive descent onto `cornerComparator` as DEFINED (flat deep measure, loss `‖A'₀ Z_deep‖²`) is
sound **only for L=0**. For L≥1 one of:
1. **Scope step (6) to arity-3 (L=0) now** — clean, buildable (§3.1) — and treat general L as a genuinely-open
   brick (= routeverify Brick B), NOT a mechanical `Fin 3 → Fin(L+…)` lift. (Recommended: unblocks
   arch1build immediately without an unsound general-L claim.)
2. **Give the comparator a deep decoration** carrying `det⁺(Z_deep Z_deepᵀ)^{+b/2}` on the deep params (a new
   `SJDecoration` slot), so the residual is exactly matched. Its own finiteness/IH must then be re-established
   (the deep-Gram-weighted RLCT), which is new content — and my numerics say the weighted RLCT drops below
   `T1_q` for uniform width, so the weight must be IN the comparator (not "hoped absorbed").
3. **Handle the deep rank-drop before the descent** (a deep-stratum gate — the deepgate/CRrec arc arch1probe
   dismissed), absorbing `det⁺(Z_deep Z_deepᵀ)^{−b/2}` against the deep-rank-drop codimension. This is the
   `hZrank`-adjacent AG content, now load-bearing for L≥1.

Any general-L build must NOT assert `∫ frontChargeIntegrand ≤ K·cornerComparator.integral` without one of
these — that is the false coupling identity (route-B mode).

---

## 4. Q3 (3') — the σ-bank / ℓ=0 biquadratic corner: DROPPABLE (L=0)

The ℓ=0 corner front loss (after the `H̃`-fibre) is `∫_{H̃,Y,W}(‖H̃‖² + ‖Y·W‖²)^{−q}`, `Y=(P;C)∈ℝ^{M₀×u}`,
`W∈ℝ^{u×d}` (`d=M₂−b`). **Verdict (a): the σ-bank is DROPPABLE — no externally-supplied front-pivot
orthonormal frame / Loewner floor is needed.** [FACT for L=0]

**Mechanism (intrinsic).** Polar-in-`W`: `W = σ·Ŵ`, `σ = ‖W‖`, `Ŵ∈S^{dW−1}`, `dW = u·d`. Then `‖YW‖² =
σ²‖YŴ‖²`. Feed `twoBlock_radial_le` with the **`H̃`-block as the κ-stable block** (`d_u = ub`, `κ=1`) and the
**`Y`-projection as the σ-scaled block** (`d_v = active Y-directions`, `σ = ‖W‖`):

    ∫_{H̃, Y}( 1·‖H̃‖² + σ²‖YŴ‖² )^{−q}  ≤  C · σ^{−α'},   C σ-independent,   max(0, 2q − ub) < α' < d_v,

then the **outer `W`-radial** (`∫₀^B σ^{dW−1} · σ^{−α'} dσ`, from the `dW`-dim polar measure) absorbs it,
finite ⟺ `α' < dW`. Composite gate: `max(0, 2q−ub) < α' < min(d_v, dW)` — non-empty exactly in the operative
range `q < T1_q` (the `C_{ℓ,s}` min at `(ℓ,s)=(0,·)`, incidence-cert §3b: corner `(2,2,3)` gives two radial
`∫r^{2−2q}dr`, `C_{0,0}=3`). The σ here is the **intrinsic incidence-coordinate radius `‖W‖`**, an
integration variable — NOT a banked external frame; `twoBlock_radial_le`'s `C` is σ-independent, so no frame
field is threaded. The `Y`-rank degeneration (`κ_eff = σ_min(Y)→0`) is the `s`-index determinantal big-cell
(intrinsic), not a floor. This parallels **Brick F droppable** (routeverify §5D): the coupled incidence route
keeps everything in intrinsic chart coordinates and needs no Loewner floor.

**CAVEAT (L≥1).** For `L≥1`, `W = Q_p·N` with `Q_p = A'₀ Z_deep` couples the deep factor, so the corner's
`σ = ‖W‖` polar and the `Y`-block sit under the same deep-Gram residual as §3.2. So (a) "droppable" is clean
for L=0; for L≥1 the ℓ=0 corner inherits the Verdict-B residual and is not independently closable.

---

## 5. Levels kept apart

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
  **arch1build step (6) can proceed for arity-3.** For general **L≥1** the charge-form reassembly carries an
  **uncompensated deep-Gram residual `det⁺(Z_deep Z_deepᵀ)^{−b/2}`** (coarea Jacobian of the `A_cor`-measure),
  non-integrable over the deep params for good-branch cuts with `b > |M₂−M₃|` — witnessed by **uniform-width
  `(d,d,d,d)`** and `(3,4,5,4)@u=2`, all inside the L=0 scope `a+b ≤ M₂`. `∫ frontChargeIntegrand ≤
  K·cornerComparator.integral` is FALSE there; it must NOT be asserted (route-B mode). σ-bank (3') is
  DROPPABLE for L=0 (intrinsic `‖W‖`-polar + `twoBlock_radial_le`, no external frame), deep-caveated for L≥1.
- **Most likely to break it.** (a) If the arch1build target is arity-3 ONLY, Verdict B is a scope flag, not a
  blocker — proceed. (b) My last non-rigorous step is that `L(Z)` (the inner leaf integral) does not vanish
  fast enough on the deep rank-drop to kill the residual; I argued it stays `O(1)` or blows up (never
  suppresses), so `G` diverges — but a Codex/hardener check of `L(Z)`'s deep-rank-drop asymptotics would fully
  seal "the domination is FALSE" vs merely "the natural bound is too lossy". The residual's PRESENCE and
  non-integrability are rigorous regardless (coarea + exact RLCT + `/tmp/confirm_witness.py`).
- **Next construction/consult.** (i) Confirm arch1build's step-(6) target is arity-3 (if so, ship §3.1).
  (ii) For general L, pick a fix (§3.3): the deep-decorated comparator (option 2) is the cleanest — pin the
  deep-Gram-weighted RLCT `RLCT(det⁺(Z_deep Z_deepᵀ)^{−b/2}·‖A'₀Z_deep‖^{−2q})` and whether it stays `≥ T1_q`
  (my numerics say NO for uniform width). (iii) Decorrelated Codex on `L(Z)` asymptotics to upgrade (b).

**Files (absolute):**
- `/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/genm-reassembly/reassembly-cert.md` (this cert)
- `…/genm-reassembly/codex/reassembly-{prompt,answer}.md` (decorrelated consult)
- scans: `/tmp/minadm.py`, `/tmp/deepresid.py`, `/tmp/witness_summary.py`, `/tmp/confirm_witness.py`
