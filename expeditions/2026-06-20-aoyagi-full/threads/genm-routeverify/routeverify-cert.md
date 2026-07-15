# routeverify — capstone-route gate: route B broken (type error) / incidence route SOUND + gives the DESCENT

**Seat:** pen-and-paper (adjudication: obstruction on route B, witness on the incidence route), aoyagi-full
Stage 2, `genm-routeverify`. **Date:** 2026-07-15. **NO Lean edits, NO build.** Verified statements via
`git show` on `origin/genm-sj5-brickdcont` (Brick D + charts), `origin/genm-sj5-good`,
`origin/genm-sj5-waist`, `origin/genm-sj5-holesbe` (the dispatch). Exact algebra + a decorrelated
`local-codex-consult` (gpt-5.1-codex-max, xhigh, my conclusions WITHHELD): `codex/routeverify-{prompt,answer}.md`.
Exact numerics (guide + certificate): `/tmp/descent_check.py`, `/tmp/scope2.py`.

**Consumed / cross-read (verified, not paraphrased):** `genm-routefork/routefork-cert.md`,
`genm-incidencepp/incidence-cert.md` §3/§3b, `genm-bltj/mixdegen-cert.md`,
`genm-couplingfin/coupling-verdict-cert.md`, `genm-t2adjud/t2-bridge-adjudication-cert.md`; the Lean:
`RouteMSJHeadSplitDom.lean` (`hsQ` L38, `pivotShell` L62, `headSplit_pivotDom` L82), `RouteMSJPivotBlowup.lean`
(`pivotBlock_radial_blowup` L154), `RouteMSJDeeperFlagCore.lean` (`shell_corankOffSector_le_unif` L259,
`deeperFlag_shell_core_le` L368, `shellSpineIntegrand` L444, `tailMinWidth` L458, `headSplit_domination`
stub L508, `deeperFlag_spineToCore` L677, `deeperFlag_shell_le` L752), `RouteMLayerSplit.lean` (`minAdm`,
`minAdmRec` L58, `redChain` L40), `RouteMSJDecorated.lean` (`carrierThreshold` L64),
`RouteMSJDecoratedCharge.lean` (`peelCharge` L45), `RouteMSJIncidence{Chart,Chart4Polar,Exponent,Gluing}.lean`
(the charts), `RouteMSJDecoratedStep.lean` + `RouteMSJGoodConnector.lean` (the dispatch).

---

## ★ VERDICTS (definitive)

1. **CHECK 1 — NO driver gap; the routing is PROVEN.** The good/waist dispatch keys on the **sound Nat key
   `M 1 < deepTailMin M`** (waist) vs `deepTailMin M ≤ M 1` (good), NOT on the buggy per-cut hpiv. On GOOD
   chains the per-cut hpiv `minAdm (redChain u M) ≤ u·tailMinWidth M` holds at **every** cut `u`, PROVEN
   sorry-free (`minAdm_redChain_le_deepTailMin` ∀u, unconditional; plus `tailMinWidth M = deepTailMin M` on
   good). Every hpiv-failing cut lives on a chain with `deepTailMin M > M 1`, which the dispatch routes to
   the **separate waist branch** (holes (c)/(e)) — so the hpiv-gated head-split is only ever invoked where
   hpiv provably holds. Exhaustive: **0/64 918 good-chain cuts fail hpiv**. The operator's flagged chains
   `(2,2,3)`, `(3,3,7)`, `(3,3,4,4)` are all WAIST (correctly quarantined); routefork's refuter `(3,3,3)` is
   GOOD with hpiv marginal (`6 ≤ 6`). **Caveat:** the dispatch *structure* is sorry-free, but the waist holes
   (c)/(e) are themselves still `sorry` — the M₂>M₁ chains are correctly quarantined, not yet discharged.

2. **CHECK 2 — route B is a GENUINE TYPE ERROR, not bridgeable.** `pivotBlock_radial_blowup` applied to the
   front block `W=[P|B₁₂]` with `Q = hsQ` (the FULL stack `[Q_p ; A_cor·Z]`) produces the pivot energy
   `r²·frobSq(P̂·hsQ) = r²·‖P̂_p·Q_p + P̂_b·(A_cor·Z)‖²_F` — **affine in `A_cor`**. `shell_corankOffSector_le_unif`
   requires a scalar `w` **constant** across the `(A_cor,Γ)` integration. There is **NO `A_cor`-free positive
   lower bound** on the pivot energy: for `Q_p ∝ Z` (which it is — `Q_p, Q_b` both live in `row(Z_deep)`)
   the cancellation `P̂_b·A_cor·Z = −P̂_p·Q_p` is reachable inside the box, driving the energy to `0`. So the
   compose (blow-up → constant-`w` corank lemma) does not type-check at the interface; the "drop `B₁₂·Q_b`"
   the Lean docstring names is exactly this missing lower bound. This is the coupled estimate the incidence
   machinery was built for. Decorrelated Codex + couplingfin both concur (details §2).

3. **CHECK 3 — the INCIDENCE route is SOUND, gives the genuine DESCENT (non-circular), and is COMPLETE on
   the good branch (in scope, which is auto-satisfied there).** (a) it resolves the `A_cor`-coupling jointly
   (det-Gram coupled, no `sup` pull-out); (b) it covers ALL strict shells `1≤j<r` on good chains — the scope
   `a+b≤M₂` holds at **every** nondegenerate strict-shell good cut (0 fails, arity-3 and deeper), the
   uniform-width DLN `(d,…,d)` is GOOD hence covered, and the `b<j` strata are indexed (bltj); (c) it gives
   the **descent** `shellSpineIntegrand ≤ C·(cornerComparator (redChain u M)).integral(c'−peelCharge/2)` onto
   the **strictly shorter chain** `redChain u M`, NOT the circular `B(M)` self-bound — the threshold
   reproduces because `minAdm(M) ≤ ab + minAdm(redChain u M)` is the recursion's "min ≤ term" (0/75 411
   fails; Codex concurs). (d) hpiv is derived on good, `hcT` is the peel regime `c'<carrierThreshold M`,
   `hfloor`/Brick F may be reducible for the incidence route (§5). **This is NOT the bigger flag: the
   incidence route does not have the no-descent gap.** The genuine remaining bricks are the top-level
   assembly + the general-`L` exponent gate + Lean coverage (§6).

---

## 1. The Lean architecture, verified (what feeds what)

`deeperFlag_shell_le` (DeeperFlagCore:752, general `L`) is a REAL theorem giving the descent

    shellSpineIntegrand M (t+j) κ ε (min(M₀−t)(M₁−t)) ⟨j⟩ c'
      ≤ C · (cornerComparator (redChain (t+j) M) k jc).integral (c' − peelCharge M (t+j) / 2)

with `k=![1]`, `jc=![minAdm(redChain u M)−1]`, and `adm (redChain u M) (cornerComparator …)` also supplied
(so the decorated IH closes the comparator). It is proven by `deeperFlag_spineToCore` (S1-good) ∘
`deeperFlag_shell_core_le` (L1). Its two open dependencies:

- **L1 `deeperFlag_shell_core_le` (DeeperFlagCore:368) — PROVEN, sorry-free.** Core → comparator, valid
  because its LHS `deeperFlagCoreIntegrand` carries the **DECOUPLED** pivot `decLoss v z = |v₀|²·frobSq(Q_p)`
  (`A_cor`-FREE), so `shell_corankOffSector_le_unif` applies pointwise with `w = decLoss` a genuine constant.
- **S1-good `deeperFlag_spineToCore` (DeeperFlagCore:677)** obtains `⟨Zf,U_sf⟩` from `exists_headSplitFrame`
  (**Brick F, sorry**) and the domination from `headSplit_domination` (**Brick D, sorry**), the crux
  `shellSpineIntegrand ≤ C_hle · deeperFlagCoreIntegrand` (spine → the DECOUPLED core).

So the whole descent rests on filling `headSplit_domination` (Brick D). Its intended fill is route B, via
`headSplit_pivotDom` (HeadSplitDom:82), whose own docstring names the crux as "the coupled pivot→`decLoss`
domination (dropping the `B₁₂·Q_b` cross-coupling) … the `B₁₂·Q_b` cross-term drop is **non-pointwise**".
That drop is the type error (CHECK 2). (routefork already killed the *other* route-B fill,
`headSplit_domination_impl` via the FALSE `shellSpine_le_hsQ_box`, VERDICT 1.)

---

## 2. CHECK 2 — the coupling type error (exact)

**The objects.** `hsQ = fromRows(Q_p, Q_b)`, `Q_p = prod(redChain u M) z` (`u×n`), `Q_b = A_cor·Zf z`
(`b×n`), both rows landing in `row(Z_deep)`. `pivotBlock_radial_blowup` (PivotBlowup:154) is the exact CoV

    ∫_W ofReal(φ(frobSq(W·Q))) = ∫_ω ∫_{r>0} ofReal(r^{u·M₁−1})·ofReal(φ(r²·frobSq(matReshape ω · Q))).

Route B (routefork §5 step 2, and the `headSplit_pivotDom` docstring) applies this with `W=[P|B₁₂]`
(`u×M₁`) and **`Q = hsQ`** (the full stack). The exposed pivot energy is therefore

    E(P̂, A_cor) = frobSq(P̂·hsQ) = ‖P̂_p·Q_p + P̂_b·(A_cor·Z)‖²_F,   P̂=matReshape ω = [P̂_p | P̂_b].

This is **affine in `A_cor`** (the `P̂_b·A_cor·Z` term). `shell_corankOffSector_le_unif` (DeeperFlagCore:259)
consumes a **scalar `w : ℝ`, `hw : 0<w`**, constant across `∫_{A_cor∈matBox}∫_Γ`, and returns
`≤ Cunif·w^{−(c'−ab/2)}` with `Cunif` free of `A_cor`. Feeding `w := E(P̂,A_cor)` is not an instance of the
lemma — `w` is not a constant.

**No `A_cor`-free lower bound (the obstruction).** For the compose to work one would need
`E(P̂,A_cor) ≥ w₀ > 0` uniformly over the box, `w₀` free of `A_cor`. It does not exist. Minimal exact witness
(`u=b=1`, `Z=Iₙ` so `Q_b=A_cor` a row, `P̂=(α,β)`, `α²+β²=1`): `E=‖α·Q_p + β·A_cor‖²`; choosing
`A_cor = −(α/β)·Q_p` gives `E=0`, and `A_cor∈matBox` once `|α/β|·‖Q_p‖_∞ ≤ 1` (e.g. `α` small). More
generally `inf_{A_cor} E = ‖α Q_p‖² − α²(Q_p·Z)²/‖Z‖² = 0` whenever `Q_p` is colinear with `row(Z)` — which
it always is (`Q_p = z₀·Z_deep ∈ row(Z_deep)`). So the "pivot energy" the blow-up produces is not bounded
below on the box; the compose fails, in either order (integrating `A_cor` first leaves the same coupled
`frobSq(W_p·Q_p + W_b·A_cor·Z)` inside the `−c'` power).

**The rank-drop / shell reconciliation (why this is NOT contradicted by couplingfin).** At the `A_cor`
achieving `E=0`, `Q_b = A_cor·Z ∝ Q_p`, so `hsQ=[Q_p;Q_b]` drops rank ⟹ `σ_min(hsQ)=0`, i.e. the cancellation
sits exactly on the **rank-drop locus** the shell `{σ_min(hsQ)≥ε}` excludes. couplingfin's "BOUNDED" verdict
is precisely this: **on the shell** the coupled pivot threshold is restored to `uρ/2`; and couplingfin §1
already states "S3's fixed-scalar-`w` lemma does not apply pointwise-in-`w`". But `shell_corankOffSector_le_unif`
integrates over the **FULL `matBox`**, and routefork §5's corrected bridge explicitly drops to the full box —
so the excluded corner is back IN the domain, and no shell floor rescues a lemma whose integration domain is
unrestricted. Route B tries to have it both ways (drop the shell to reach the full box, yet keep the pivot
bounded below as if on the shell); it cannot. **This is exactly the coupled residual the incidence machinery
was built for** (couplingfin's "uniform-in-`A_cor` reorganization", incidencepp's joint resolution).

**Decorrelated Codex (conclusions withheld) CONCURS.** Q1 [FACT]: `E=‖P̂_p Q_p+P̂_b A_cor Z‖²_F`, affine in
`A_cor`; explicit `inf_a E = ‖αq‖²−α²(q·Z)²/‖Z‖²`, `=0` for `q∝Z` (identical witness); "Step (ii) is
invalid — the lemma assumes a fixed scalar `w` independent of `A_cor`, but the pivot energy … can vanish."
Q2 [FACT/INFERENCE]: the `E=0` locus is rank-deficient `hsQ`; "shell restriction would help but is not
permitted by the lemma's domain, so the interface remains invalid."

---

## 3. CHECK 3(c) — the DESCENT is genuine and non-circular (the decisive question)

The recursion (`minAdmRec`, RouteMLayerSplit:58, `= minAdm`):

    minAdm(M) = min_{t ≤ min(M₀,M₁)} [ (M₀−t)(M₁−t) + minAdm(redChain t M) ],   redChain t M = (t,M₂,…,M_last).

`redChain u M` has **one fewer layer** (`Fin (L+1+1)` vs `Fin (L+1+1+1)`), so the comparator on it is a
strictly smaller instance — the decorated IH's descent target. The peeled corner charge is
`peelCharge M u = (M₀−u)(M₁−u) = ab`.

**Threshold reproduction (exact, immediate from the recursion).** For any cut `u ≤ min(M₀,M₁)`, "the min is
≤ the `t=u` term":

    minAdm(M) ≤ ab + minAdm(redChain u M)   ⟹   ½minAdm(M) − ab/2 ≤ ½minAdm(redChain u M) = carrierThreshold(redChain u M).

Hence for `c' < carrierThreshold(M) = ½minAdm(M)`:

    c' − peelCharge/2  <  ½minAdm(M) − ab/2  ≤  carrierThreshold(redChain u M),

so the reduced comparator's integral at exponent `c'−ab/2` is **finite by the IH on the shorter chain**.
Numerically **0/75 411 cuts fail** `minAdm(M) ≤ ab + minAdm(redChain u M)` (widths 1..7, arity 3..5);
**23 405 achieve equality** (the binding cuts, where the descent is TIGHT and reproduces `T1` exactly).
Decorrelated Codex Q3 reaches the identical inequality and verdict: "a genuine descent to a shorter chain
(one fewer layer), not circular."

**Why this is NOT the circularity trap.** The circular "subset route" bounds
`shellSpineIntegrand ≤ ∫_{full matBox over all A_cor}(…)`, whose RLCT is `B(M)=½minAdm(M)` on the **same**
chain `M`; feeding that back into the mountain (which needs each shell integrand finite below `B(M)`) assumes
the answer. The descent instead lands on `cornerComparator(redChain u M).integral(c'−ab/2)` on the
**shorter** chain — the IH is a strictly smaller instance, the recursion terminates on arity, and `B(M)` is
*produced* by the min over cuts, not assumed. `deeperFlag_shell_le` already encodes this descent
structurally (§1). The incidence route (incidencepp §1) lands on the SAME target
`K·cornerComparator.integral(c'−ab/2)` directly.

---

## 4. CHECK 3(a,b) — coupling + coverage on the good branch

**(a) coupling.** The incidence route keeps the `(z,A_cor,front)` integration JOINT: the corank-Gram
`det(Q_bQ_bᵀ)^{−a/2}` rides *inside* the incidence tube (incidencepp §4, "no `sup_{A_cor}` pull-out"), so
it never needs the constant-`w` corank lemma that route B misuses. The chart algebra (RouteMSJIncidenceChart:
`det_chartGram`, `transverseSchurGram`, `pushThrough`, `chartProjComplement`) and the `H̃`-fibre
(`chart4_Htilde_fibre_lt_top`) are the coupled resolution. This is the object couplingfin proved BOUNDED and
incidencepp proved TRUE (per-exponent `K ∼ 1/(T1−c')`, in scope).

**(b) coverage.** On GOOD chains, at strict shells `1≤j<r`, nondegenerate `M₀,M₁≥2`: the incidence scope
`a+b ≤ M₂` holds at **every** cut — **0 fails**, arity-3 (183 cuts) and deeper `L≥1` (3 649 cuts). So the
incidence route's scope is automatically discharged on the good branch. Boundary cases: `j=0` (shell-0) is
the SOUND `headSplit_pivotDom`/`pivotPeel_domination` base (routefork VERDICT 2), no corank blow-up; `j=r`
(saturated) is the separate saturated shell. The `b<j` upper-half strata (routefork/operator's live worry)
are indexed by `ℓ=rank W` (`rank hsQ = b+ℓ`) and do NOT undershoot (bltj, outcome (b), decorrelated).
Uniform-width `(d,…,d)`: `deepTailMin=d=M₁` ⟹ GOOD, hpiv marginal, covered.

**M₂>M₁ / `deepTailMin>M₁` is a SEPARATE branch**, not the incidence route: the dispatch sends it to the
waist holes (c) SVD-qPeel+reorientation / (e) `M₁=1` reversal-free. So the incidence route does **not** cover
those cuts — and it is not asked to; the dispatch quarantines them soundly (CHECK 1). This is the honest
scope boundary, identical to couplingfin's `M₂>M₁` "wall" and incidencepp's `a+b≤M₂` scope.

---

## 5. CHECK 3(d) + the architecture correction

The incidence route lands `shellSpineIntegrand ≤ K·cornerComparator(redChain u M).integral(c'−ab/2)`
**directly** (spine → comparator, integrating Γ inside the charts). This is `deeperFlag_shell_le`'s
conclusion — but it does **not** pass through `deeperFlagCoreIntegrand` (the DECOUPLED core, `A_cor`-free
`decLoss`, Γ NOT integrated). The core is the object `shell_corankOffSector_le_unif`/L1 were built for, and
it is only reachable if the pivot is decoupled from `A_cor` — which is exactly route B's type error. So the
incidence route is **architecturally incompatible with the `headSplit_domination` + L1 decomposition**; it
must prove `deeperFlag_shell_le` directly, replacing `deeperFlag_spineToCore`. (`headSplit_domination`'s
*statement* — spine ≤ `C·decoupled-core` — is plausibly true, since core and coupled spine share the RLCT
`R_core = ½(ab+minAdm(redChain u M))` at each cut; but its intended proof is dead, and it is the wrong
intermediate. Bypass it — do not spend a tide trying to fill it.)

- **hpiv:** derived on the good branch at every cut (§CHECK 1) — feed `minAdm_redChain_le_deepTailMin`.
- **hcT `c' < carrierThreshold M`:** the operative peel regime (below it the spine is finite; above,
  everything is `⊤` and the bound is vacuous). Keep it; do NOT drop it (dropping it is what let the false
  `shellSpine_le_hsQ_box` be stated on `c'∈[7/2,9/2)`, routefork).
- **hc' `ab/2 < c'`:** the freed-corner regime (incidencepp `ab/2 < c' < T1`). Matches.
- **hfloor / Brick F (`exists_headSplitFrame`):** the piecewise `m`-frame + Loewner floor was introduced for
  `shell_corankOffSector_le_unif`'s `Z Zᵀ ⪰ ε'²·U_sU_sᵀ`. The incidence route keeps det-Gram coupled and
  works on the already-shell-restricted `shellSpineIntegrand` (the outer `singularShell` on `A'`), so it may
  NOT need `shell_corankOffSector_le_unif` or the `U_sf` frame at all. **Scope this at build start** — if the
  incidence charts subsume the corank charge, Brick F drops off the good-branch path (a simplification).

---

## 6. The VERIFIED capstone spec (good branch)

**Route: prove `deeperFlag_shell_le` (strict shells `1≤j<r`) DIRECTLY via the incidence machinery.** Bypass
`headSplit_domination` (route B, dead) and `deeperFlagCoreIntegrand`/L1. Exact reduction chain:

1. **Row-split + shell → core** (BANKED plumbing): `hsSplit`/`measurePreserving_hsSplit`, `prod_headSplit`
   exposing `Q_b = A_cor·Z_deep`; Ky-Fan `shell ⊆ good` so `Zf z = Z_deep z` on the shell image.
2. **IsUnit-`P` freed-corner shear + Γ-integration → coupled corank charge** `det(Q_bQ_bᵀ)^{−a/2}`, exponent
   shift `c' → q = c'−ab/2`. Kept COUPLED (incidence tube indicator part of the chart) — NOT
   `shell_corankOffSector_le_unif`.
3. **Joint incidence charts** (BANKED, sorry-free algebra): `Q_b = D·[I|X]` minor chart
   (`det_chartGram`, `transverseSchurGram`), `Q_p`-shear `W = Q_p·N`, front `B`-shear `H=PU+BD` +
   `H̃`-completion (`chartProjComplement`), the `H̃`-fibre (`chart4_Htilde_fibre_lt_top`), the determinantal
   big-cell of `W` (`{rank W=ℓ}` strata).
4. **Per-stratum exponent gate** (BANKED for arity-3): `clsCodim_gate` — `minAdm M ≤ C_{ℓ,s}+ab` — via the
   `ring` identity `clsCodim_add_ab_eq` + `Finset.inf'_le` on `minAdm_arity3`. Gives each stratum's radial
   integral `∫r^{C_{ℓ,s}−1−2q}dr` finite below `T1`, per-stratum ratio to the comparator finite.
5. **Finite-cover gluing** (BANKED skeleton `lintegral_lt_top_of_finite_cover`) + sum over the finite
   `(b-minor × ℓ-minor × s-minor)` atlas ⟹ `shellSpineIntegrand ≤ K·cornerComparator.integral(c'−ab/2)`,
   `K = ΣK_{ℓ,s} < ⊤`, per-exponent (`∼1/(T1−c')`).

**GENUINE REMAINING BRICKS (the tide's real spec — genuine analysis, not mechanical):**
- **(A) Top-level assembly.** Wire the (grep-confirmed **orphaned**) charts into the theorem
  `shellSpineIntegrand ≤ K·cornerComparator(redChain u M).integral(c'−ab/2)` — the finite determinantal
  atlas, per-chart `lintegral_image_eq_lintegral_abs_det_fderiv_mul` CoVs (Jacobians `|det D|^{n−b−a−u}`,
  `det(I+XXᵀ)^{−a/2}` a unit, big-cell `|det|≡1`), null-overlap gluing, per-stratum ratio summed. This is
  the single largest piece; incidencepp §3b certifies every chart map + Jacobian is explicit.
- **(B) General-`L` exponent gate.** `clsCodim`/`clsCodim_gate` are **arity-3 (`Fin 3`, L=0) only**. Extend
  to the deep-factor `Z_deep` (`M₂×n`, `n=M_last`) so the gate is against `minAdm(redChain u M)` (the full
  reduced chain), not the arity-3 `minAdm`. incidencepp §3 gives the general `C_{ℓ,s}` parametrized by
  `n`; the Lean formula and gate must be lifted off `Fin 3`.
- **(C) Coverage / index-completeness in Lean.** The `(ℓ,s)` enumeration is exhaustive (every point in some
  chart, incl. `b<j`); pen-and-paper confirmed (bltj + incidencepp §3b), but the finite-atlas cover + null
  overlaps is Lean labour. The per-stratum gate (A/B) is banked; "min over strata `= 2·T1`" coverage is not
  yet Lean-proven (the `RouteMSJIncidenceExponent` docstring flags this; bltj discharged the math).
- **(D) Brick F scoping** (§5): determine whether the incidence route needs `exists_headSplitFrame`/`hfloor`
  at all; likely reducible.
- **(E) `j=0` shell-0 base** (`headSplit_pivotDom` on the pivotShell) and **`j=r` saturated shell** — sound
  base cases, kept as-is; only `1≤j<r` needs the incidence route.

**Do NOT:** fill `shellSpine_le_hsQ_box` (FALSE, routefork), fill `headSplit_domination` via route B (type
error, §2), or drop `hcT`/the shell/the `a+b≤M₂` scope.

**The WAIST branch** (`deepTailMin M > M 1`, incl. every operator-flagged `(2,2,3)/(3,3,7)/(3,3,4,4)`) is a
distinct, still-open build (holes (c)/(e)); the dispatch quarantines it soundly. Full coverage of the
capstone needs it too, but it is **not** the incidence route.

---

## 7. Most likely thing to break these verdicts / residual

- **CHECK 2:** would be wrong only if some hidden hypothesis forced `P̂_b=0` (no `B₁₂` block) or an
  `A_cor`-free floor on every use. Checked: `hsQ` genuinely stacks the corank rows; `Q_p∈row(Z_deep)` always;
  the cancellation is in-box. Codex + couplingfin (independent) reach the same `inf=0`. Stands.
- **CHECK 3(c):** the descent inequality is the recursion's "min ≤ term" — unconditional; 0/75 411. Stands.
- **CHECK 3(b) coverage:** the residual is (C) — Lean index-completeness of the `(ℓ,s)` atlas; the *math* is
  bltj-closed (decorrelated), the *formalisation* of exhaustiveness is genuine labour. If bltj's coverage
  had a gap at a non-`b<j` cut it would inherit here — outside my scope, but bltj's subset-monotonicity
  argument is chain-shape-agnostic.
- **General-`L` (B):** the arity-3 gate is proven; the deep-chain lift is unverified in Lean. The per-cut
  head-split reduces to a single deep-factor `Z_deep` (`M₂×n`), so the incidence charts are structurally
  `L`-uniform, but the exponent bookkeeping against `minAdm(redChain u M)` must be re-derived off `Fin 3`.
  **Next construction:** pin the general-`L` `C_{ℓ,s}`↔`minAdm(redChain u M)` identity (the `L≥1` analogue of
  `clsCodim_add_ab_eq`) before the tide, so the gate is a `ring`+`inf'_le`, not a case sweep.

## Close

- **Firmest result.** Route B (`pivotBlock_radial_blowup` → `shell_corankOffSector_le_unif` with constant
  `w`) is a **genuine type error** — the blow-up's pivot energy `frobSq(P̂·hsQ)` is `A_cor`-coupled with no
  `A_cor`-free lower bound over the box (in-box cancellation on the rank-drop locus; exact witness §2,
  Codex + couplingfin concurring). The **incidence route is sound + complete on the good branch + gives the
  genuine descent** to the shorter chain `redChain u M` (threshold reproduced by `minAdm(M) ≤ ab +
  minAdm(redChain u M)`, non-circular). The driver **provably** routes hpiv-failing (M₂>M₁) cuts to the
  waist branch (0/64 918 good-chain hpiv failures; sound `deepTailMin` key). NOT the bigger flag — the
  incidence route has the descent.
- **Most likely to break it.** The general-`L` exponent-gate lift (B) is the least-verified piece; and the
  Lean coverage/atlas (C) is genuine labour (the math is bltj-closed).
- **Next.** (i) Scope Brick F out of the incidence path (§5(D)); (ii) pin the general-`L` `C_{ℓ,s}` ↔
  `minAdm(redChain u M)` gate identity (§7); then (iii) build the top-level assembly (A) as the capstone
  tide, targeting `deeperFlag_shell_le` directly.

Files (absolute):
- `…/expeditions/2026-06-20-aoyagi-full/threads/genm-routeverify/routeverify-cert.md` (this cert)
- `…/expeditions/2026-06-20-aoyagi-full/threads/genm-routeverify/codex/routeverify-{prompt,answer}.md`, `run.log`
