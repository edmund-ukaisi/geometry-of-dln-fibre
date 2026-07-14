# The partial-shell transverse-Schur incidence estimate — VERDICT: **PROVEN (true in scope), via the JOINT (z,A_cor,front) incidence-rank resolution.** Pointwise-in-z is FALSE; scope `a+b ≤ M₂` required.

**Seat:** pen-and-paper (witness, decorrelated), aoyagi-full, `genm-incidencepp`. **Date:** 2026-07-14.
**NO Lean, NO git, NO build.** Exact algebra (incidence blow-up, corank-Gram Wishart threshold, joint
normal-crossing codimensions) + numerics as guide only (`inc_corner.py`, `inc_ratio.py`,
`inc_pointwise_check.py`, `inc_integrated.py`). Decorrelated `local-codex-consult` (xhigh, my conclusion
WITHHELD; prompt framed "argue whichever way"): `codex/incidence-{prompt,answer}.md`.

**Consumed / read:** `genm-brickd-design/reconciliation-T1.md` (T1 wins, off-shell = B(M), shell = descent),
`genm-shelljhunt/codex/shellj-answer.md` (λ_j = ½min_{s≤R_j}C(s) ≥ T1), `genm-couplingfin/coupling-verdict-cert.md`
(shell load-bearing for the pivot, keep w coupled), `genm-thresholdhunt/threshold-verdict-cert.md`
(off-shell RLCT = ½minAdm(M) = T1), `RouteMSJDeeperFlagShell.lean` (`uniformWenn_proj_le`, `offSector_cover_le`),
`RouteMSJCornerComparator.lean` (`cornerComparator_decLoss = commonDivisor²·frobSq(prod M')`),
`RouteMSJLedger.lean` (`commonDivisor`/`genMonomial`).

---

## ★ VERDICT — the incidence estimate is TRUE (finite per-exponent `K_{j,c'}` for `ab/2 < c' < T1`), **in scope `a+b ≤ M₂`**, via the joint incidence-rank resolution. TWO load-bearing corrections to the presumed route:

1. **The POINTWISE-in-`z` bound is FALSE** (decorrelated Codex Q3 + confirmed here). `G(z) ≤ K·(δ²‖Qp‖²)^{−q}`
   fails: at a rank-dropping `Qp` (one singular value `→ δ`) the front integral grows like `δ^{5−2q}` (for the
   `(3,3,5)@u=2` witness), which blows up for `q > 5/2`, while `‖Qp‖²_F ≍ 1` stays bounded. The estimate is a
   genuinely **INTEGRATED** domination — the `z`-integration participates: the `Qp` rank-stratum codimension
   absorbs the front-integral rank-drop blow-up. A builder attacking this per-`z` will hit a false wall.
2. **Scope `a+b ≤ M₂` is REQUIRED** (= the object's `hcvg: a+b ≤ m` ∧ `hmM: m ≤ M₂`). Without it the
   corank-Gram `∫_{A_cor} det(Qb Qbᵀ)^{−a/2}` DIVERGES (Codex Q4 witness `(3,3,3)@u=1, a=b=2`, `a+b=4>3=M₂`:
   `∫(x²+y²)^{−1}dx dy = ∞` on a rank-1-`Qb` chart, uniform-lower-bounded inner integral, RHS finite). That
   witness is **out of scope** (violates `a+b≤M₂`); Codex agrees it is excluded under the binding-cut scope.

Inside the scope, the LHS resolves to finitely many normal-crossing strata with codimensions `C_{ℓ,s}`, and
`min_{ℓ,s} C_{ℓ,s}/2 = T1_q := T1 − ab/2 ≤ uM₂/2 = ` comparator threshold — so both sides converge for
`c' < T1` and the domination closes per-stratum with per-exponent `K ~ 1/(T1−c')`. **The shell is NOT needed
for the finiteness** (off-shell is already finite to T1, binding at `s = t★`); it is needed for the **descent**
(non-circularity), exactly as reconciliation-T1 said.

---

## 1. The object (L=0 leaf), precisely

`Qp = prod(redChain u M) z` (`u×M₂`, fn of `z`); `Qb = A_cor` (`b×M₂`); `hsQ = (Qp ; Qb)` (`(u+b)×M₂`);
`Πb =` proj onto `row(Qb)`; `q = c' − ab/2`, `ab/2 < c' < T1 = ½·minAdm(M)`. The target (after the banked
row-split + `IsUnit P` shear + `Γ=D`-integration producing `det(Qb Qbᵀ)^{−a/2}` and the exponent shift
`c' → q`):

    G := ∫_z ∫_{A_cor∈S_j(z)} det(Qb Qbᵀ)^{−a/2} · [ ∫_{P,B,C} ( ‖[P|B]·hsQ‖²_F + ‖C·Qp·(I−Πb)‖²_F )^{−q} ]
       ≤  K_{j,c'} · ∫_z ( commonDivisor(z)²·‖Qp(z)‖²_F )^{−q}   =  K_{j,c'} · cornerComparator.integral(q).

`E_top := ‖[P|B]·hsQ‖² = ‖P·Qp + B·Qb‖²` (pivot rows, weight `w`); `E_tr := ‖C·Qp·(I−Πb)‖²` (transverse
Schur, `a` rows). Both are load-bearing: dropping either makes the front integral DIVERGE (its threshold is
`(u·rank hsQ + a·rank(Qp(I−Πb)))/2`, marginal at the corner) — no term can be discarded.

## 2. The binding corner `M=(2,2,3)`, `u=1`, `a=b=1` — EXACT, AIRTIGHT (RLCT = T1, per-exponent K)

`Qp = e₁ = (1,0,0)`; `Qb = A_cor = (1,t₂,t₃)`, `t=(t₂,t₃)→0` (incidence: `row(Qp)→row(Qb)`). Exact:
`det(Qb Qbᵀ)=1+|t|² ≍ 1`; `‖Qp(I−Πb)‖² = |t|²/(1+|t|²) ≍ |t|²`. Front block scalars `p,β,γ`:
`E_top=(p+β)²+β²|t|²`, `E_tr = γ²|t|²/(1+|t|²)`.

**Blow-up.** Set `ξ = p+β` (unimodular), `s=|t|`, polar in the `(β,γ)`- and `t`-planes. Fibre estimate
`∫_{-1}^1 (ξ²+A²)^{−q}dξ ≍ A^{1−2q}` (`q>½`) with `A = s·ρ`, `ρ²=β²+γ²`, gives the joint monomial density

    ρ^{2−2q} · s^{2−2q} dρ ds   ( × analytic units ),   and the two decisive radial integrals are
    ∫₀^δ ρ^{3−2c'} dρ · ∫₀^δ s^{3−2c'} ds        (q = c'−½).

Both converge ⟺ `3−2c' > −1 ⟺ c' < 2 = T1`. So `RLCT_{c'} = 2 = T1` **exactly**; the value is finite for
every fixed `c'<T1` and blows up like a double pole `∼ 1/(T1−c')²` as `c'↑T1` — **per-exponent K, K→∞ at
T1⁻**, precisely the requirement. `commonDivisor²·‖Qp‖² ≍ 1` here, so `R = G/RHS` is finite. Confirmed
numerically: `inc_corner.py` (front slope `≈ 1−2q`, radial slope `≈ 3−2c'`); `inc_integrated.py`
(`K·(T1_q−q) ≈ 100` constant, `q → T1_q⁻`). Codex Q1 concurs verbatim (`RLCT_q = 3/2, RLCT_{c'} = 2 = T1`).

The corner shows the shell does **not exclude** the incidence corner — finiteness below T1 holds by the
blow-up, not by exclusion — exactly the brief's flag.

## 3. The general moving-subspace incidence resolution (charts, Jacobians, joint exponents)

On a `b×b` minor chart of `Qb` (`n:=M₂`, `d:=n−b`, `Qb` full row rank generically):

    Qb = D·[ I_b | X ],   Qp = [ U | U X + W ],   D∈GL_b, X∈ℝ^{b×d}, U∈ℝ^{u×b}, W∈ℝ^{u×d}.

Then `Qb·N = 0`, `Qp·N = W` for `N = (−X ; I_d)`, and the **transverse Schur is monomialised by `W`**:

    ‖Qp(I−Πb)‖²_F = tr( W (I_d + XᵀX)^{−1} Wᵀ ) ≍ ‖W‖²_F.

**Incidence strata:** `𝓘_h = { dim(row Qp ∩ row Qb) ≥ h } = { rank W ≤ u−h }`, `codim 𝓘_h = h(n−b−u+h)`.
Total vanishing `‖Qp(I−Πb)‖=0` needs `row Qp ⊆ row Qb` (only forced when `u=1`; for `u>1` "meeting" is a
partial-incidence stratum). **The pivot weight decouples by a det-1 output shear** `H = PU + BD`:
`E_top+E_tr ≍ ‖H‖²_F + ‖Y·W‖²_F` with `Y = (P;C) ∈ ℝ^{M₀×u}`.

**Jacobian bookkeeping (EXACT, Codex Q2).** `dQb = |det D|^d dD dX`, `det(Qb Qbᵀ)^{−a/2} = |det D|^{−a}
det(I+XXᵀ)^{−a/2}`, `dB = |det D|^{−u} dH`. Joint determinant power **`|det D|^{ n−b−a−u }`**. On the rank-`ℓ`
chart of `W` (`h=u−ℓ`) and the rank-`s` chart of the `Y`-block, the normal codimension is

    C_{ℓ,s} = u·b + M₀·ℓ + (M₀−s)(u−ℓ−s) + s(d−ℓ),      radial chart  ∫₀^δ r^{ C_{ℓ,s} − 1 − 2q } dr.

**Verified EXHAUSTIVELY (`inc_sweep.py`, exact-integer, all arity-3 chains widths 2..8):** over **all 332
in-scope binding cuts** (`a+b≤M₂`, `1≤j<r`, `u=t★+j`), `min_{ℓ,s} C_{ℓ,s}/2 = T1_q` with **0 failures**, and
`T1_q ≤ uM₂/2` with **0 violations**. The minimiser sits at `ℓ=0, s = ` an **argmin cut `t★` of `minAdm(M)`**
(the resolution finds the cheapest argmin; when `minAdm` has two argmins it may pick the one other than the
`t★` the cut was built around — 56/332). So the **off-shell** LHS is finite to **exactly T1**, binding at an
argmin cut (= reconciliation-T1 / thresholdhunt "binding at `r=t★`", independently re-derived here from the
joint charts).
The **shell-restricted** LHS excludes `s>R_j`, so its threshold `λ_j ≥ T1` (shellj) — even more room. Either
way finite for `c'<T1`.

## 4. Why the domination closes with finite per-exponent K (the INTEGRATED, per-stratum mechanism)

Not pointwise-in-`z`. On each joint stratum the LHS is a monomial integral `∫ r^{C_{ℓ,s}−1−2q} dr`, finite for
`q < C_{ℓ,s}/2` (⊇ `q<T1_q`); the comparator, resolved on the SAME `z`-stratum, is a monomial with exponent
governed by its own RLCT `uM₂/2 ≥ T1_q`. Because **`min C_{ℓ,s}/2 = T1_q ≤ uM₂/2`**, every stratum's ratio
`K_{ℓ,s} = (LHS monomial integral)/(comparator monomial integral)` is a finite explicit rational (`→∞` only as
`q→T1_q`). E.g. the rank-drop stratum of `(3,3,5)@u=2`: LHS `∫ r^{8−2q}dr`, comparator `∫ r^{3}dr`,
`K = 4/(9−2q) < ∞` for `q<9/2 ⊇ q<T1_q=4`. Summing the finitely many strata gives `K_{j,c'} = Σ K_{ℓ,s} < ⊤`,
per-exponent, `∼ 1/(T1−c')` (corner: double pole). **The pointwise route fails because the LHS binding
stratum (`s=t★`, a joint B-rank locus) is a DIFFERENT locus than the comparator's (`Qp→0`)** — they only
reconcile after integration, never chart-wise.

**The det-Gram stays coupled (Codex Q2).** `sup_{Qb} det(Qb Qbᵀ)^{−a/2} = ∞`; it must ride inside the incidence
tube (the shrinking indicator `𝟙{|H−(PU)_i|≲τ_i}` is part of the monomialisation — removing it changes the
exponents). The corank-Gram integrability threshold is exactly `a < n−b+1 ⟺ a+b ≤ M₂` (Wishart smallest-SV:
`∫ τ^{ n−b−a } dτ`), the scope hypothesis of §Verdict-2.

## 5. Numerics (GUIDE only; exact algebra above is load-bearing)

- `inc_corner.py`: corner front slope `≈ 1−2q`, radial `≈ 3−2c'` (MC-noisy near T1, as expected).
- `inc_ratio.py`: pointwise `R(z)` bounded **at `q=1.5`** — but this is BELOW the `5/2` trigger; misleading.
- `inc_pointwise_check.py`: **at `q=2.8` the front integral GROWS `189→1517` as `δ→0`** while `‖Qp‖²≍1` —
  pointwise ratio unbounded (confirms Codex Q3; corrects the `inc_ratio.py` false comfort).
- `inc_integrated.py`: (a) `min C_{ℓ,s}/2 = T1_q` exact, 7 cases; (b) integrated corner `K·(T1_q−q)≈100`.
- `inc_sweep.py`: **332/332 in-scope binding cuts (widths 2..8): `min C_{ℓ,s}/2 = T1_q` (0 fail),
  `T1_q ≤ uM₂/2` (0 violations)** — the central exponent claim, exhaustive.

## 6. Decorrelated Codex (conclusion WITHHELD; prompt "argue whichever way")

`codex/incidence-{prompt,answer}.md` (xhigh). Independent, CONTRIBUTED the two corrections:
- **Q1 [FACT]** corner `RLCT_{c'}=2=T1`, double-log at T1 (identical to §2).
- **Q2 [FACT]** the incidence charts, `‖Qp(I−Πb)‖²≍‖W‖²`, `codim 𝓘_h = h(n−b−u+h)`, joint det power
  `|det D|^{n−b−a−u}`, `C_{ℓ,s}` (§3); det-Gram not pull-out-able; corank threshold `a+b≤M₂`.
- **Q3 [FACT]** pointwise-in-`z` FALSE (`(3,3,5)@u=2`, `δ^{5−2q}`); integrable only after `z`-integration.
- **Q4 [FACT]** out-of-scope det-Gram divergence `(3,3,3)@u=1,a=b=2` (`a+b=4>3`); **explicitly notes** the
  binding-cut scope `M₂≥M₀+M₁−1 ⟹ a<M₂−b+1` excludes it and "the `(2,2,3)` corner is consistent with a true
  integrated estimate." No in-scope counterexample.

## The exact lemma the tide needs (INTEGRATED form, per-exponent, scoped)

**`deeperFlag_shell_le` / the incidence estimate:** for a binding cut `u=t★+j`, `1≤j<r`, `a=M₀−u`, `b=M₁−u`,
under **`a+b ≤ M₂`** (`hcvg`∧`hmM`) and `ab/2 < c' < carrierThreshold M = T1`, there is `K_{j,c'} < ⊤` with
`G ≤ K_{j,c'}·cornerComparator.integral(c'−ab/2)`. **Load-bearing (do NOT drop):**
- **INTEGRATED, not pointwise** — resolve `(z, A_cor, front)` jointly (§3 charts); the `Qp` rank-stratum
  codimension absorbs the front rank-drop blow-up. A per-`z` bound is FALSE (§Verdict-1).
- **Scope `a+b ≤ M₂`** (§Verdict-2) — else the corank-Gram diverges.
- **det-Gram coupled** (§4) — no `sup_{A_cor}` pull-out; the incidence tube indicator is part of the chart.
- **per-exponent `K_{j,c'}`** (`∼1/(T1−c')`), never endpoint-uniform.
The RHS finiteness for `c'<T1` is the outer IH on `redChain u M` (a fortiori: `q = c'−ab/2 < T1−ab/2 ≤ uM₂/2`).

**Lean-friendly pieces:** the `b×b`-minor chart `Qb=D[I|X]`, the shear `H=PU+BD`, the `|det D|^{n−b−a−u}`
Jacobian, the `C_{ℓ,s}` monomial exponents (§3), feeding banked `uniformWenn_proj_le` (corank on the shell),
`offSector_cover_le` (shell cover), `detGram_lintegral_box_lt_top` (corank integrability, needs `a+b≤M₂`),
`cornerComparator.integral` (RHS). This is a genuine (not trivial) resolution, but the charts + exponents are
explicit and verified.

## Close

- **Firmest result.** The incidence estimate is **TRUE** (finite per-exponent `K ∼ 1/(T1−c')`) for
  `ab/2<c'<T1` **in scope `a+b≤M₂`**, via the joint incidence-rank resolution. Corner `(2,2,3)` airtight
  (`RLCT=T1`, blow-up explicit). Joint exponents `C_{ℓ,s}` give `min/2 = T1_q` **exhaustively (332/332
  in-scope binding cuts, widths 2..8; `T1_q ≤ uM₂/2` always)**, binding at an argmin cut `t★`. NOT a wall —
  no in-scope counterexample; the hard configs are absorbed by the `z`-integration.
- **The two corrections (decorrelated Codex + confirmed).** (i) The **pointwise-in-`z`** shortcut is FALSE
  (rank-drop `Qp` ⟹ `δ^{5−2q}` blow-up, `q>5/2`); the domination is INTEGRATED. (ii) **`a+b≤M₂`** is required
  (corank-Gram). Both were latent risks in the presumed route (which leaned on a per-`(z,A_cor)` corank peel).
- **Most likely to break the BUILD (not the math).** A tide that (a) bounds per-`z` (false), or (b) drops the
  `a+b≤M₂` scope, or (c) pulls the det-Gram out uniformly, will thrash on never-landed content. Thread the
  scope, keep the resolution joint, keep det-Gram coupled.
- **Next.** Formalise the joint resolution: `Qb=D[I|X]` minor chart → shear `H=PU+BD` → the `C_{ℓ,s}` monomial
  strata → per-stratum ratio to `cornerComparator.integral`, summed. The exhaustive `min C_{ℓ,s}/2 = T1_q`
  check (332/332, `inc_sweep.py`) is DONE — the exponent arithmetic is the reusable Lean-side certificate for
  "off-shell LHS finite to exactly T1"; the remaining labour is the chart maps + Jacobians + the per-stratum
  ratio, all explicit above. Deeper decorrelated-confirmation of the general per-stratum ratio `K_{ℓ,s}<⊤`
  (beyond the corner + rank-drop stratum worked here) would fully close the constructive-`K` claim.
