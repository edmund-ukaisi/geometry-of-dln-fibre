# Addendum — the REAL non-separated object at the edge: BOTH parts CONVERGE (LATE-16 rescue confirmed)

**Seat:** pen-and-paper (obstruction-leaning, decorrelated), `genm-corneradj`, follow-on. **Date:** 2026-07-16.
**NO Lean, NO build.** Exact algebra (codim / transverse order / RLCT-exponent budget) + numerics (guide) +
a decorrelated `local-codex-consult` (`codex/coupled-{prompt,answer}.md`, xhigh, conclusion WITHHELD).
Extends `corner-cert.md`. The separated object was settled there (front charge `Ch(S)` finite ⟺ `a+b≤ρ`;
coupled *separable* `I` = +∞ at edge). This addendum handles the REAL **non-separated** object the build
actually needs, where `A_cor` is TIED to the loss.

---

## ★ VERDICT — BOTH parts CONVERGE. `(□)` is NOT threatened at the edge.

1. **Part (1) [interior deep-locus]: CONVERGES.** In a valid core (`a+b ≤ ρ`), `∫_S Ch(S)` converges near the
   rank-drop locus `{rank S = a+b−1}` where `Ch(S)→∞`. Mechanism: `Ch(S)` blows up only **logarithmically**
   (`Ch(S) ~ C·ln(1/σ_{a+b}(S))`) as `S` approaches the locus, while the `S`-measure vanishes at least
   linearly (codim ≥ 1); `∫₀ ln(1/τ)dτ < ∞`. couplerad's E-recursion claim (S-measure pays the `Ch` blowup)
   CONFIRMED. The two blow-up directions are **coupled, not independent**: `σ→0` (the `S` full-rank parameter
   `τ`) supplies the transverse direction that tames `A_cor·u→0` off the stratum; on the measure-zero stratum
   `τ=0` the `A_cor·u` direction is unpaid (`Ch=∞`, log) but the transverse `S`-measure absorbs the residual
   log. couplerad's per-stratum LP `γ ≤ measure` holds with `γ=0` (log ≤ codim-1).

2. **Part (2) [the edge, REAL coupled object]: CONVERGES for `c' < ½·minAdm(M)`** — verified at BOTH the
   non-binding edge `(5,5,3,3)@u=3` (slack: threshold 5.5 > target 4.5) AND the **tight binding edge**
   `(3,3,3)@t=1` (threshold **exactly** ½·minAdm = 3.5, marginal at the endpoint = correct binding RLCT).
   Tonelli fails here (`A_cor` sits INSIDE the loss), so the LATE-16 rescue genuinely applies — the front
   charge `+∞` is an artifact of the separation upper bound (`≤`) that drops the regularizers.

3. **Build consequence.** The front-charge factoring route (`shellSpine_le_frontCharge_binding`, an `≤`
   upper bound) is VACUOUS at `a+b=ρ+1` (RHS = +∞), so schurrec's charged core must carry the **rankgen
   scope `a+b ≤ ρ`** for that route — resolving its "rankgen scope OPEN" note (the exact form is `a+b ≤ ρ`,
   `ρ = tailMinWidth`, NOT `a+b ≤ ρ−1`). At the edge (`a+b=ρ+1`) the piece is finite via the **direct
   coupled bound** (the loss-sum `decLoss + frobSq(corank)` regularizes; the joint `{Γ=0}` component gives
   the `ab/2` reduction), NOT via the front-charge factoring. The edge is NOT a `(□)` wall.

Decorrelated **Codex CONCURS** on the coupled mechanism (κ=6, β=c'−3 generic; the regularizers named). §5.

---

## 1. The REAL object (extracted from Lean), and why it is not the separated `I`

`shellSpineIntegrand` (`RouteMSJDeeperFlagCore.lean:444`) integrates `freedSchurLoss^{−c'}`, and
`freedSchurLoss` (`RouteMSJChartShear.lean:146`) is a **SUM**:

    freedSchurLoss = frobSq(P·Q̃ₚ)               [pivot energy, Γ-free — after P-radial blow-up = decLoss ≥ 0]
                   + frobSq(C·Q̃ₚ + Γ·Q_b)        [corank energy], with Q_b = A_cor·Zf.

So the honest per-`(z,v)` inner integrand is `(decLoss + frobSq(Ccross + Γ·A_cor·Zf))^{−c'}` — `A_cor`
appears **inside** the loss (tied to `Γ` and `Zf`), added to `decLoss`. The binding
`shellSpine_le_frontCharge_binding` (schurrec wt, `RouteMSJShellFrontChargeBinding.lean:34`) is a
**`≤`** (confirmed): it pulls out `det((A_cor Zf)(A_cor Zf)ᵀ)^{−a/2}` (the front charge) as an UPPER bound
by doing the `Γ`-integral first and over-estimating. That upper bound is `+∞` at the edge, but the honest
LHS need not be. Tonelli does NOT apply to the honest object (unlike the separated `I` of `corner-cert.md`):
`A_cor` and the loss share the variable, so the LATE-16 rescue can recur.

**Chain arithmetic** (`minAdm` recursion, `scripts/minadm.py`): `minAdm(5,5,3,3)=9` (½=4.5). The edge cut
`u=3` (`a=b=2, ρ=3, a+b=ρ+1`) is **NON-binding** (peel+minAdm(redChain)=4+7=11 ≠ 9); binding cuts are
`u=4` (`a=b=1`, interior) and `u=5` (trivial). But the edge DOES occur at binding cuts for other chains —
`scan.py`: **205** edge-at-binding cuts among chains of length 3–4, widths ≤ 6; the smallest and tightest is
**`(3,3,3)@t=1`** (`a=b=2, ρ=3`, binding `ab+minAdm(1,3)=4+3=7=minAdm`, ½=3.5). This is the genuine stress
case (no slack), and it is the one that must be checked hardest.

## 2. Part (1) — interior deep-locus: `∫_S Ch(S)` converges (log blow-up vs linear measure)

Model `a=b=2, ρ=4→3`, `S = diag(1,0.9,0.8,τ)`, `τ = σ₄ → 0` (approach rank `a+b−1=3`). Exact transverse
model: near the locus the Gram determinant `det((A_cor S)(A_cor S)ᵀ) ≈ |z_a|² + τ²·y²` with `z_a ∈ ℝ^a`
(the on-stratum transverse) and `y` the `A_cor`-component along `S`'s small singular direction, weighted by
`τ²`. The `A_cor`-integral gives (for every `a≥1`)

    Ch(S) ~ C·ln(1/τ)     (LOGARITHMIC blow-up; the s^{-1} tail of ∫₀^{1/c}(s²+1)^{-a/2}s^{a-1}ds).

`scripts/fast1.py`: `Ch(S)/ln(1/τ)` ≈ constant (~1300–1700, MC noise) over `τ ∈ [2⁻²,2⁻¹²]` — confirms LOG;
the per-octave integral bands `Ch(τ)·τ·ln2` decay geometrically (`416→295→…→1.8`), so `∫₀ Ch(τ)dτ` CONVERGES.
The `A_cor·u→0` direction (unpaid on the exact stratum, where `Ch=∞`) is paid **jointly**: `τ>0` restores the
transverse dimension; the residual log is absorbed by `∫dτ` (`∫₀ ln(1/τ)dτ = [τln(1/τ)+τ]₀ < ∞`).

## 3. Part (2) — the edge, honest coupled object: reduction `ab/2` from the `{Γ=0}` component

Per `(z,v)`, `H(w) := ∫_{A_cor∈box}∫_{Γ∈box}(w + frobSq(Ccross + Γ·A_cor·Zf))^{−c'}`, `w=decLoss≥0`,
`Zf` 3×3 rank 3, `Ccross` 2×3. `H(w) < ∞` for every `w>0` (integrand `≤ w^{−c'}`, bounded boxes). The
`w→0` scaling `H(w) ~ w^{−β}` decides convergence of the full object `∫_z∫_v(v-mon)·H(w(z,v))`, which is
finite iff `β < ½·minAdm(redChain u M)` (the reduced-comparator threshold in the exponent).

**Generic `Ccross` (full rank 2):** the exact-fit locus `N = {Ccross + Γ·A_cor·Zf = 0}` has codim
`κ = ab + ν = 4 + 2 = 6` in the 10-dim `(Γ,A_cor)` space (Φ:(Γ,A_cor)↦Γ·A_cor·Zf is a submersion at `N`
where `Γ,A_cor` are full rank; the `ν=2` is the codim of `{rows Ccross ∈ rowspace(A_cor Zf)}`). So
`β = c'−κ/2 = c'−3` — reduction 3 (Γ-reduction `ab/2=2` + A_cor-sublocus `ν/2=1`), PROVIDED `N` meets the
boxes. `det((A_cor Zf)(A_cor Zf)ᵀ)` is bounded away from 0 on `N` (there `A_cor Zf` has full row rank `b`),
so no residual front-charge singularity. If `N` misses the boxes (the boxes fix a scale; generic O(1)
`Ccross` needs `Γ = −Ccross·(A_cor Zf)⁺` outside `[−1,1]`), then `β=0` (`H` bounded). Numerics (`fast.py`):
`Ccross`-scale 1.0 → `β<0`; 0.1 → `β≈0.14` — both `< 3.5`, converge.

**Worst case `Ccross=0` (the C→0 region, no cross-regularization):** `H(w)=∫∫(w+frobSq(Γ·A_cor·Zf))^{−c'}`.
The zero-locus `{Γ·A_cor·Zf=0}={Γ·A_cor=0}` has its lowest-codim component `{Γ=0}` of codim **`ab=4`**, so
the `Γ`-integral gives reduction `ab/2=2` **directly** — WITHOUT the intermediate `∫_{A_cor}det(G)^{−a/2}=Ch`
that diverges. The `A_cor` rank-drop (the front-charge locus) is a higher-codim sub-singularity WITHIN
`{Γ=0}` and contributes only a **log correction**:

    H(w) ~ w^{−(c'−ab/2)}·ln(1/w) = w^{−(c'−2)}·ln(1/w).

`scripts/tight.py` confirms it: the plain slope sits just above `c'−2` (`1.32/1.81/2.30` vs `1.0/1.5/2.0`,
the ≈0.3 excess = the log), and `H(w)·w^{c'−2}` grows **linearly in `ln(1/w)`**.

**Consequence at the tight binding edge `(3,3,3)@t=1`** (`ρ=3`, redChain `(1,3)`, `½minAdm(1,3)=1.5`,
target `½minAdm(3,3,3)=3.5`): full object `~ ∫_z∫_v(v-mon)·w^{−(c'−2)}·ln(1/w)`, finite iff `c'−2 < 1.5`
⟺ **`c' < 3.5 = ½minAdm(M)`**, marginal (log) at the endpoint. That is EXACTLY the correct binding RLCT:
`λ = ½minAdm(M)`, finite below, divergent at. The reduction `ab/2 = 2` is achieved by the `{Γ=0}` component;
the front-charge log-divergence bumps only the **pole ORDER / RLCT multiplicity** `m` at the endpoint (order
1 → 2), NOT the threshold value `λ`. `(□)` (the value `λ=½·codim`) is intact.

**Non-binding edge `(5,5,3,3)@u=3`:** redChain `(3,3,3)`, `½minAdm=3.5`; reduction `ab/2=2` gives threshold
`3.5+2=5.5 > 4.5` — converges with margin 1.0. (Consistent with the cut over-covering.)

## 4. The mechanism, named (the LATE-16 rescue, precisely)

The separated front charge does the `Γ`-integral first → `det((A_cor Zf)(A_cor Zf)ᵀ)^{−a/2}`, then
`∫_{A_cor}(·) = Ch = +∞` (order of integration manufactures the divergence). The honest coupled object sees
the **joint** zero-locus `{Γ=0}` (codim `ab`) and gets the `ab/2` reduction directly; the `A_cor` rank-drop
is a higher-codim sub-locus that contributes a harmless `ln(1/w)`. Two independent regularizers keep the base
bounded below off the joint locus: (i) `w = decLoss > 0` (pivot energy, pointwise cutoff), and (ii) the
cross-term `Ccross` (full-rank + bounded `Γ` excludes ill-conditioned `A_cor·Zf` from the low-loss region,
supplying `ν=2` extra `A_cor`-codim). The front charge drops BOTH by over-estimating; that is why it is only
an `≤` upper bound and why it goes vacuous exactly at `a+b=ρ+1`.

## 5. Decorrelated Codex (conclusion WITHHELD; `codex/coupled-answer.md`, xhigh) — CONCURS

- **[exact]** `H(w)<∞` for `w>0`; `κ=6`, `β=c'−3` for generic `Ccross` when `N` meets the boxes; the split
  `ab/2 + ν/2 = 2+1 = 3`; `det((A_cor Zf)(A_cor Zf)ᵀ)` bounded away from 0 **on `N`** (though not on all of
  the sublocus `S`). **[feasibility caveat, independently raised]** "this power law requires `N` to meet the
  cubes cleanly … if `N=∅`, compactness gives a positive minimum loss and `H(w)→H(0)<∞`, so `β=0`."
- **[exact, Q-B]** "The coupled integral is finite for every `w>0`, despite `Ch=+∞`." Regularizers named:
  `w>0` pointwise cutoff; the row-space residual gives the `A_cor`-codim `ν=2`; full-rank `Ccross` + bounded
  `Γ` exclude ill-conditioned `B`. Reduction `c'−β = 3 > ab/2 = 2`.

(Codex analysed the generic-`Ccross` regime; my `Ccross=0` worst-case analysis — reduction `ab/2=2` + log
via the `{Γ=0}` component — is the tight-binding case Codex did not separately treat, and is what fixes the
threshold at exactly `½minAdm(M)` at binding cuts.)

## Close

- **Firmest result.** REAL non-separated object: BOTH parts CONVERGE. Part (1): `∫_S Ch(S)` converges near
  the rank-drop (log blow-up `~ln(1/σ_{a+b})` vs codim-≥1 `S`-measure). Part (2): the honest coupled
  `shellSpineIntegrand` is finite for `c' < ½minAdm(M)` at both the non-binding edge `(5,5,3,3)@u=3`
  (margin) and the tight binding edge `(3,3,3)@t=1` (exact, marginal at endpoint) — via the `{Γ=0}`
  component's `ab/2` reduction; the front-charge log-divergence is only a pole-order/multiplicity bump, not a
  threshold shift. `(□)` (the RLCT VALUE `λ=½minAdm`) is intact. Codex concurs.
- **Most likely to break it.** (i) The reduced-comparator threshold `½minAdm(redChain u M)` "in the exponent"
  is taken from the induction hypothesis / couplerad's ledger — if the `v`-monomial `jc` shifts it, the exact
  endpoint arithmetic moves (the qualitative rescue stands: reduction `ab/2` at binding, `> ab/2` off-binding).
  (ii) The `Ccross=0` worst-case reduction is `ab/2` with a log; if some binding edge cut had the reduced
  comparator ALSO at its endpoint simultaneously in a non-transverse way, the multiplicity could stack — worth
  a spot-check on one more binding-edge chain (`(3,3,4)@t=1`, `(3,4,4)@t=1` from the scan). The RLCT VALUE is
  unaffected regardless.
- **Next (for schurrec / the tide).** State `ChargedRectSchurCore` finiteness with the front-charge route
  scoped to `a+b ≤ ρ` (the rankgen hypothesis = `a+b ≤ tailMinWidth`, discharged at binding cuts where
  `a+b ≤ ρ`), and route the edge `a+b=ρ+1` cuts through the DIRECT coupled bound (loss-sum `{Γ=0}` codim
  `ab`), not the front-charge factoring. The multiplicity bump at edge cuts means: claim the RLCT VALUE
  `½minAdm`, do NOT claim a specific multiplicity `m` unless separately computed.
