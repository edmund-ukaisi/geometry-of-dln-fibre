# Off-sector arity recursion — INDEPENDENT obstruction hunt (decorrelated adversary)

**Seat:** pen-and-paper, `obstruction` direction. **Date:** 2026-07-12. **NO Lean, NO repo edits** (only
this file). **Charge (controller):** attack the exhaustiveness / well-foundedness of `genm-sj5-cover`'s §7
"airtight" off-sector arity recursion (`joint-corner-cert.md` §6–§7). Do NOT trust the cert; hunt it.

**Discipline.** Exact algebra only (sympy; Newton polygon on the charpoly of `ZZᵀ` for exact
parameter-order of `σ_min`; exact `lct`/integral thresholds). Monte-Carlo NOT used to certify. Decorrelated
`local-codex-consult` fired with the conclusion WITHHELD, framed neutrally ("derive what the structure
forces"): `/tmp/offsector-hunt/codex-{prompt,answer}.md`. Instrument self-validated against 5 known cases
before use (`diag(t,1)→1`, `diag(t²,1)→2`, `diag(t³,1,1)→3`, transverse rank-1 perturbation `→1`, `a·b→2`).

---

## ★ VERDICT

**GAP FOUND — the §7 exhaustiveness is NOT the airtight PROOF it claims.** Two independent lines (my exact
algebra + a decorrelated Codex + a *sibling banked thread the cert does not cite*) converge:

1. **Well-foundedness clause (C) is CONFLATED / false as written.** It invokes Eckart–Young ("a single
   matrix has `σ_{ρ+1}² ≍ dist²`, `m=1` always") to conclude the base has vanishing-order 1. Eckart–Young
   is a **matrix-space distance** equality that holds for **every** matrix — products included — so it
   cannot distinguish single matrices from products and cannot establish the **parameter-order** the
   integral actually needs. The real hypothesis is uniform transversality / metric regularity (owed piece
   A) — and that is strictly stronger than immersion (a **tangency** counterexample below has order 2
   despite an affine, immersive parametrization).

2. **The corank-≥2 shared-divisor binders break both "bottoms out at width-2" and "charges ADD."** The
   sibling R1 thread (`theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex` L607–656) has **PROVED** that
   a threshold-only / naive-corner charge account is insufficient at corank ≥ 2 (the exact obstruction
   `⟨δx,δy⟩` `lct=½` vs `⟨δ₁x,δ₂y⟩` `lct=1`, *identical widths/multiplicities*), and that it **binds at a
   genuine DLN branch** `(3,3,4)` whose minimiser is a corank-2 coupled block **not reachable by corank-≤1
   peels**. §7's "peel to a width-2 single matrix (Eckart–Young `m=1`), bad loci charge ADD (Q1)" is exactly
   the mechanism that thread refuted; it needs Aoyagi's **coupled `diag(b)` / symbolic-divisor-support**
   recursion, which §7 does not name.

**Scope of the gap (important, and fair to the cert):** this is a gap in the §7 **PROOF / well-foundedness
argument**, *not* a refutation of the finiteness `□` at `½·minAdm`. The **value** `½·minAdm` is separately
defended (the QIP min-identity `min_q ½(M₀ρ+min(M₀q,D_q)) = ½minAdm` + Aoyagi + the R1 coupled recursion):
the collapse branches are either non-binding (higher `Mval`) or resolve *correctly* to `½minAdm`. The one
residual `□`-risk I could not close (nor construct a counterexample for) is the **general-width QIP
no-collapse**, which is verified only on dmcheck's finite sweep (7 chains), not proved — the cert itself
admits "general width MUST check it."

`GAP FOUND: well-foundedness/exhaustiveness proof (C) — Eckart–Young (matrix-distance) does not give the
parameter-order it is used for, and the corank-≥2 shared-divisor binders (proven load-bearing by the
sibling R1 thread) defeat both the width-2 bottoming-out and "charges ADD"; the ½·minAdm VALUE survives
(QIP+Aoyagi) but §7 is not an airtight PROOF and must route through the coupled diag(b)/symbolic-support
recursion, not the naive corner.`

---

## Attack (3) — the MISSED STRATUM / dichotomy (C) is false [the sharpest]

**FACT.** Eckart–Young: `σ_{ρ+1}(M) = dist(M, {rank ≤ ρ})` in **matrix** (operator-norm) space — an exact
equality for **every** `M`, product or not. So `σ = dist` ("`m=1`" in matrix distance) is trivially true
even for `Z=a·b`; it does **not** distinguish single matrices from products, and cannot be the reason a
single matrix is order-1.

**FACT.** The order the integral needs is the **parameter-order** of `σ_min(M(θ))` as `θ→` bad locus. A
single matrix (no product) can have parameter-order > 1 (exact, my instrument):

| single matrix `M(t)` | parametrization | `σ_min` param-order |
|---|---|---|
| `diag(t², 1)` | monomial chart | **2** |
| `[[1,t],[t,0]]` | **affine & immersive** (`dM/dt = [[0,1],[1,0]] ≠ 0`) | **2** (tangent to `{det=0}`) |
| `[u²]` (= `a·b` blown up `a=u,b=uv`, `v≠0`) | blow-up chart | **2** |
| `diag(1,0) + t·E` (generic `E`) | free entries, **transverse** | 1 |

The tangency case is decisive: `λ_min(MMᵀ) = t⁴ + O(t⁵)` **exactly**, so `σ_min = t²`. Affine immersion is
**not** enough for order 1 — the slice is tangent to the rank-drop locus. Order 1 requires a **metric
error bound** `dist(M(θ),D) ≍ dist(θ, M⁻¹D)`, i.e. uniform transversality (= owed piece A), which
Eckart–Young does not supply. **[Codex #1/#2 independently derived exactly this, incl. the `[[1,t],[t,0]]`
example, before I saw its answer.]**

**JUDGEMENT.** So "(C): `m>1` is a PRODUCT-ONLY phenomenon; the base (single matrix) is `m=1` everywhere by
Eckart–Young" is **false as stated**. It is a category error (matrix-distance order vs parameter-map order).
The bad loci `(C)` wants to confine to products are, precisely, **same-corank critical loci of the
parameter→matrix map** (Codex's original Q2 catch, `codex/offsector-answer.md` #2), and these arise for
single matrices reached through composed blow-up charts. The recursion survives **only if** owed-A supplies
*uniform transversality on every good tube*, including inherited charts — not inferable from "one factor."

## Attack (1) — persistence / termination vs closure

**FACT (termination holds).** Peeling one factor strictly drops the crossing order (instrument: `k`-factor
scalar product along `a_i=t` has order `k`; peel → `k−1`; `2×2·2×2` coincidental rank-1 → order 2, one
factor alone → 1). Arity strictly decreases and is bounded below by 2, so the **indexing recursion
terminates**. No infinite regress. This much of §7-(C) is sound.

**FACT (closure ≠ termination — the "charges ADD" is a units-sector value only).** The scalar chain
`Z = a₂···a_L` has `σ_min² = (∏a_i)²`; the integral **factorizes**, `∫_{[0,1]^{L-1}} (∏a_i)^{-2c} = ∏∫a_i^{-2c}`,
finite iff `c < ½` for **every** `L`. So `lct = ½ = ½·minAdm` (minAdm = 1), **not** the `(L−1)/2` a naive
"charges ADD to `½Σ`-dims" gives. In the nested blow-up `a₂=u, a_i=u·τ_i`: the outer `u` binds at `c<½`
(**not** `(L−1)/2`) and **each** `τ_i→0` *also* binds at `c<½` — because `τ_i→0` is a **genuine singular
direction** (a deeper factor vanishing), not a unit. The true threshold is the **MIN** over all binding
directions. `nested3.py`'s "`½Σ`-dims = `½minAdm`" is only the outer-radial binding under the *units*
assumption; it is a correct **local** value on the units sector and **false** as a global identity
(`L=3` scalar chain: `½Σ = 1 ≠ ½ = ½minAdm`). The cert flags the units caveat, so this is not a hidden
error — but it means the recursion's correctness rests entirely on the off-units recursion recovering the
**MIN**, i.e. **analytic closure**, which arity-boundedness does **not** deliver (Codex #3, `offsector-answer.md` #3).

**FACT / the load-bearing failure mode (corank ≥ 2, shared divisor).** The off-units recursion's closure
can **COLLAPSE** below the naive sum via a **shared exceptional-divisor variable** — exact, independently
re-derived from the sibling R1 thread:

- SHARED `K = d²(x²+y²) = (dx)²+(dy)²`: polar `→ (∫d^{-2c})(∫r^{1-2c})`, binds at `c<½` → **`lct = ½` (MIN/collapse)**.
- UNSHARED `K = (d₁x)²+(d₂y)²`: disjoint-variable summands, each normal-crossing `lct=½`, disjoint sum → **`lct = 1` (ADD)**.

Identical widths and per-row multiplicities, **different** `lct`. Whether a corner ADDs (`½Σ`) or collapses
(MIN) depends on **which divisor variables are shared** — data a "charges-ADD" / threshold-only corner does
**not** carry. This is the R1 thread's proven obstruction (`aoyagi-2023-worked.tex` L616, "two independent
computations agree"), and it **BINDS** at a genuine DLN branch:

- `(3,3,4)`: `Mval(t₁) = (3−t₁)²+4t₁ = {0:9, 1:8, 2:9, 3:12}`; minimiser `t₁=1`, `Mval=8`, `RLCT=4=½·minAdm`,
  layer-1 corank `(2,2)`. The corank-≤1 (clean) branches `t₁∈{0,3}` give `9,12 > 8` — so **no corank-≤1 peel
  reaches the minimiser**. A threshold-only account gives `3` (wrong); the coupled `diag(b)` resolution gives
  `4` (correct, CERTIFIED in `verify-r1-diagb-334.md`).

**JUDGEMENT.** §7's "the bad locus IS the intersection rays ⟹ Q1 (charges ADD)" + "(C) bottoms out at
width-2" **misses** these corank-≥2 coupled binders: they are neither width-2 single matrices nor `m=1`,
and their charge is not the naive corner sum but a sharing-dependent value. The sound route is Aoyagi's
coupled `diag(b)` / symbolic-support recursion (the R1 thread's decided route), not the arity-to-width-2 +
naive-corner-ADD of §7. The value `½minAdm` is not thereby refuted (the collapse branches are non-binding
or resolve to `½minAdm`), but §7 does **not** prove it.

## Attack (2) — finite subcover / uniform constants

**FACT.** The corner `τ`-integral `I(ε) = ∫₀¹ τ^{b-1}(ε + τ²U₁)^{-c'} dτ` with units `U₀=ε→0` scales
(sub `τ=√ε·s`) as `I(ε) ~ C·ε^{b/2 − c'}` with `C = ∫₀^∞ s^{b-1}(1+s²)^{-c'}ds`; at the anchor region
`b=3, c'=7/2` this is `I(ε) ~ (2/15)·ε^{-2} → +∞`. So the **per-chart constant diverges without bound as the
units approach the rank-drop**.

**JUDGEMENT.** Uniformity is **not** free: it holds **only** on a gated region `{U₀ ≥ const}`, and the
`{U₀ < const}` complement **cannot** be absorbed with a uniform constant — it must recurse (this vindicates
the cert's gate-and-recurse, but shows "finite subcover with uniform constants" is *contingent*, not
established). The finiteness then reduces to (i) compactness giving finitely many **gated** charts
[plausible] AND (ii) the gated recursion closing with the correct MIN [= attack 1's residual, owed E].
Codex #1 (`offsector-answer.md`) already flagged: "finitely many coranks do not by themselves provide
finitely many uniform tube charts." Confirmed.

---

## What survives / most likely to break / next

- **Firmest (obstruction + scope).** §7's exhaustiveness is not an airtight PROOF: (C) conflates
  Eckart–Young matrix-distance with parameter-order (exact + Codex + tangency counterexample); "bottoms out
  at width-2, charges ADD" misses the corank-≥2 shared-divisor binders that the sibling R1 thread PROVED
  load-bearing and binding at `(3,3,4)`. The `½minAdm` **value** survives (QIP min-identity + Aoyagi +
  coupled `diag(b)` recursion).
- **Most likely to break the VALUE (the residual `□`-risk I could not close).** The **general-width QIP
  no-collapse** — dmcheck verified it on 7 chains (a sweep, not a proof); a width whose *binding* branch has
  a shared-divisor collapse driving `lct < ½minAdm` would falsify `□`. I could not construct one (it needs
  the full DLN QIP geometry, outside this hunt's exact-algebra reach), but the shared-divisor mechanism
  (F4) is the exact place such a width would hide. This is the single highest-value next check.
- **Next construction/consult that would settle the open part.** (a) Re-derive the `genm-sj5` off-sector
  bad-locus estimate as an instance of the R1 `diag(b)` / symbolic-support recursion (reconcile §7's Q1
  corner with the R1 thread's proven-necessary sharing data) — this either closes the gap or exposes where
  the two threads' resolutions disagree. (b) Push the shared-divisor collapse (F4) through the general-width
  QIP: for each corank-`q` binding cell, check the *binding-branch* `lct` against `½minAdm` symbolically
  (not by sweep), specifically hunting a shared deep factor `C^{(s)}` (the R1 thread's optional-refinement
  case, not yet exercised at a binding witness).

---

## Reproducible scripts (exact; kept under `/tmp/offsector-hunt/`)

Instrument = exact parameter-order of `σ_min` via the Newton polygon of the charpoly of `ZZᵀ`
(no floats). Self-validated against 5 known cases. Load-bearing excerpts:

    # instrument.py  — exact t-order of sigma_min via Newton polygon of charpoly(ZZ^T)
    def sigma_min_sq_order(Z):
        M = sp.expand(Z * Z.T); n = M.shape[0]; lam = sp.symbols('lam')
        poly = sp.Poly(sp.expand((lam*sp.eye(n) - M).det()), lam)
        coeffs = [poly.coeff_monomial(lam**i) for i in range(n+1)]     # low->high in lam
        orders = root_orders_via_newton(coeffs)      # root order = -slope of lower hull of (i, ord_t c_i)
        return max(orders), sp.Rational(max(orders), 2)   # (order of lambda_min, order of sigma_min)

    # attack 3 — single matrices with parameter-order > 1 (dichotomy (C) is false)
    sigma_min_sq_order(sp.diag(t**2, 1))        # -> order 2   (monomial chart, single matrix)
    sigma_min_sq_order(sp.Matrix([[1,t],[t,0]]))# -> order 2   (AFFINE + IMMERSIVE, tangent; lam_min=t^4+O(t^5))
    sigma_min_sq_order(sp.diag(1,0)+t*E)        # -> order 1   (free entries, TRANSVERSE)

    # attack 1 — scalar chain lct = 1/2 for all L (MIN), not (L-1)/2:
    #   int_[0,1]^{L-1} (prod a_i)^{-2c} = prod int a_i^{-2c}  finite <=> c < 1/2   (each factor)

    # attack 1/3 core — shared vs unshared divisor (the collapse):
    #   K = d^2(x^2+y^2): polar -> (int d^{-2c})(int r^{1-2c})  binds c<1/2  -> lct = 1/2  (COLLAPSE)
    #   K = (d1 x)^2 + (d2 y)^2: disjoint sum of two normal-crossings (each 1/2) -> lct = 1  (ADD)

    # attack 2 — per-chart constant blows up as units eps->0:
    #   I(eps)=int_0^1 tau^{b-1}(eps+tau^2)^{-c'} dtau ~ eps^{b/2-c'} * int_0^oo s^{b-1}(1+s^2)^{-c'} ds
    #   b=3, c'=7/2:  I(eps) ~ (2/15) eps^{-2} -> +infinity

Full runnable scripts: `/tmp/offsector-hunt/{instrument,attacks,attacks2,attacks3}.py`. Decorrelated
consult (conclusion withheld, neutral framing): `/tmp/offsector-hunt/codex-{prompt,answer}.md` — Codex
returned independently "ORDER-CLAIM (C) AS WRITTEN: false — conflates matrix-space distance with
parameter-space contact order" and "WELL-FOUNDED: no — closure requires uniform stratified metric
regularity in terminal charts and valuation-wise integrability inequalities preserving the threshold."
