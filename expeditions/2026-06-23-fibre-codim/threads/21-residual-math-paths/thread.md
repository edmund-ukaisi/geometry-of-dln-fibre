# thread 21 — residual math paths (explore-scout recon)

**Type:** explore-thread scout. **Read-only recon** — map terrain and rank the candidate
*mathematical* routes to the single certified-true residual the expedition reduced Lemma 4.6's geometry
to. NO Lean source, NO commits to the package.

**The residual (precisely):** prove (Lean 4 / Mathlib v4.29, `DLNFibre.Core`) the geometric content of
LR Lemma 4.6 — any ONE of: (i) `fibreGenIdeal d E` is **radical** (`N≥1`, `E = diag(I_r,0)`); (ii) the
fibre `mult⁻¹(E) ∩ chart` is **smooth** of the right dim; (iii) the deep **flat trivialization**
`Σ̄^r ≅ base × fibre`; (iv) directly `codim_{Σ̄^r}(fibre) = δ := r(d₀+d_N−r)`.

**Avoid** re-proposing the circular trivialization route (building the product iso `e` needs the
radicality it would establish — thread 20 wall-analysis).

---

## COMPUTE — the submersion / Jacobian on the anchor `(2,2,2), r=1`

Setup: `mult(A) = A₂A₁`, both 2×2 (8 coords). Differential `d(mult)(X₁,X₂) = X₂A₁ + A₂X₁`, a linear
map `T_A Rep = k⁸ → Mat₂ₓ₂ = k⁴`. The fibre is `mult⁻¹(E)`, `E = diag(1,0)`. I compute the rank of the
4×8 Jacobian at fibre points, stratified by `(rank A₁, rank A₂)`.

| stratum (rk A₁, rk A₂) | rank(d mult) | ker dim = local fibre dim |
|---|---|---|
| (1,2) | **4** | 4 |
| (2,1) | **4** | 4 |
| (1,1) — both rank-1 | **3** | **5** |

(Computed exactly in sympy; the (1,1) stratum swept over all 36 integer rank-1 pairs with `A₂A₁=E` —
rank is uniformly 3. r=2 full-rank sanity: fibre over `I` = GL₂, rank(d mult)=4 everywhere, smooth, dim 4. ✓)

**Reading.**
- On the GENERIC part of the fibre (one factor full rank) the Jacobian has rank **4 = dim Mat** —
  `mult` is a submersion **onto all of Mat**, not merely onto `Σ̄^r`. There the fibre is **smooth of
  dim 4**, codim 4 in Rep = `C + δ = 1 + 3`. ✓
- On the DEEP `(1,1)` stratum (both factors rank-1) the Jacobian rank **drops to 3**; the tangent
  space jumps to dim 5. The `(1,1)` stratum is the locus `{ca+db=1}` in the 4 free params — **dim 3**,
  i.e. **codim 1 inside each 4-dim component**. It is the locus where the **two components meet**
  (thread 16: 2 comps, each dim 4, reduced/reducible). So the fibre is **singular** (as a reduced
  variety) along `(1,1)`, and `mult` is **NOT a submersion at every point of the fibre**.

**Two decisive consequences for the submersion route.**

1. **`mult` is a submersion onto Mat (rank 4) generically, NOT onto `Σ̄^r` (rank 3).** The LR/paper
   phrasing "submersion onto the rank-r locus" is the SMALLER rank-3 image. The actual generic
   differential hits ALL of Mat — a different and stronger statement. The fibre codim it yields is
   `8 − 4 = 4 = C + δ` *directly* (no `C`/`δ` split). But this only holds on the dense open; it is NOT
   a clean "submersion onto `Σ̄^r`" tangent statement.

2. **The smooth-locus is dense but the fibre IS singular.** `E = diag(1,0)` is rank-1, OUTSIDE the
   dense open `{rank-2 targets}` over which `mult` is a smooth/flat submersion. Generic-smoothness OF
   THE MAP does NOT transfer to the fibre over `E`. The fibre over `E` is the genuine singular object;
   the singular locus (the `(1,1)` stratum, the component-crossing) has codim 1 in the fibre.

**Net for route 1 (submersion).** "Smooth ⟹ reduced + right codim" needs care: the fibre over `E` is
NOT smooth (it is singular along `(1,1)`). What IS true: the fibre is smooth on a DENSE OPEN, hence
**generically reduced**, and being a level set its **top-dimensional components have the right codim**
(4). To get "the fibre is REDUCED" (the residual content) from "generically reduced" one needs **no
embedded primes** — i.e. an `(S₁)` / unmixedness condition, which is exactly the type-A rank-locus CM
input, NOT a consequence of the generic submersion alone.

## Pivot-chart clarification (important)

The LR pivot chart `U` is `{top-left r×r block of the TARGET invertible}` — a chart on the **base**
`Mat^{rk=r}`. On the fibre, `mult A = E` always, so `(mult A)₀₀ = 1 ≠ 0`: the ENTIRE fibre lies in
`U`. So restricting to the pivot chart does **NOT** remove the singular `(1,1)` stratum — the fibre
over `E` is the same singular object on the chart. The chart trivializes `Σ̄^r` over its rank base; it
does not smooth the fibre. This is why the route reduces to "fibre/`F_E` reduced", not to "fibre smooth".

---

## The radical-insensitivity pivot (the decisive structural fact)

`codimRepCanonical Z = Ideal.height (vanishingIdeal (canonicalCoord '' Z))` (`OrbitCodim:134`). The
`vanishingIdeal` is **radical by construction**, so:

> `codimRepCanonical(fibre) = height(vanishingIdeal(fibre)) = height(radical(fibreGenIdeal))
>   = height(fibreGenIdeal)`

The codim is **radical-insensitive**. It reads the **reduced** variety `mult⁻¹(E)` as a set; whether
`fibreGenIdeal` is radical (the residual the trivialization chased) is **irrelevant to the codim
number**. The catenary bridge `height_vanishingIdeal_add_varietyDim_eq_card` (`NullstellensatzCodim:147`,
needs `IsPrime` ⟹ per component) gives `codim = card − varietyDim`, and `varietyDim` is
`ringKrullDim (MvPol ⧸ vanishingIdeal)` — the dimension of the **reduced** variety.

**So the residual for the CODIM is: `varietyDim(mult⁻¹(E)) = card − (C + δ)` (min/max over top
components) — a purely set-/reduced-variety dimension fact.** This is what Codex (decorrelated, xhigh)
independently converged on: "radicality is unnecessary for the codimension statement." This is
**weaker** than the scheme-radicality residual and dodges flatness/`F_E`-reduced entirely.

Confirmed by both me and Codex: the radicality residual is a **red herring for the codim claim**. (It
remains the genuine content for a scheme-theoretic Lemma 4.6, but the RLCT payoff needs only the codim.)

## The dimension route — where the wall actually sits (honest)

Target `varietyDim(fibre) = card − (C+δ)` splits into two inequalities. NOT symmetric:

- **LOWER bound on dim** (`varietyDim ≥ card−C−δ` ⟺ `codim ≤ C+δ`): EXHIBIT a `(card−C−δ)`-dim
  subfamily of the fibre. Geometrically easy (the explicit Schur/gauge section parametrizes a
  `(card−C−δ)`-dim family). In Lean: a dominant map from affine `(card−C−δ)`-space, or a
  transcendence-degree / `varietyDim`-monotone argument. MED.
- **UPPER bound on dim** (`varietyDim ≤ card−C−δ` ⟺ `codim ≥ C+δ`): the **HARD half**. Fibre-dimension
  upper-**semicontinuity** gives `dim(special fibre) ≥ dim(generic fibre)` — the **WRONG** direction.
  An upper bound needs **equidimensionality** of `mult|Σ̄^r` over its rank base — exactly the
  trivialization/flatness content. **NOT dodged by going to dimensions.**

### The refinement that DOES dodge flatness: a REDUCED/set-level product variety iso

`varietyDim` reads the reduced structure. A **set-level (reduced) variety isomorphism**
`Σ̄^r ∩ U ≅ base × fibre(E)` (NOT a scheme iso — no cut-ideal radicality, no flatness) gives, via
`dim(X×Y) = dim X + dim Y`:

> `varietyDim(Σ̄^r) = δ + varietyDim(fibre(E))` ⟹ `varietyDim(fibre) = (card−C) − δ`
> ⟹ `codim(fibre) = C + δ`.

The set-level trivialization is exactly the thread-16-certified LEH transport — **TRUE as a set map**,
and it is reduced/set-level, so it needs neither the flatness nor the cut-ideal radicality that
walled `e`. The remaining Lean gaps:
1. The set-level (or reduced-ring) product iso `Σ̄^r ∩ U ≃ base × F_E^red` — the gauge/section, now at
   the level of REDUCED coordinate rings (`Sred ≃ R ⊗ F_E^red`, where `F_E^red = F_E / nilradical`).
   *Subtlety:* if we use `F_E^red` (the reduced fibre) the descent is automatic and we never assert
   `F_E` reduced — but constructing the iso to `R ⊗ F_E^red` still needs identifying `Sred`'s relevant
   quotient, which is close to the same content. **This is the rung to scope carefully — it may still
   be the wall, just at reduced level.**
2. **`dim(X × Y) = dim X + dim Y` for affine varieties** — Mathlib v4.29 has `MvPolynomial.ringKrullDim`
   (Noetherian) but NO tensor/product Krull-dim additivity (grep-confirmed; G07 recon agrees). Would be
   built — but the engine's `affine_domain_height_add_ringKrullDim_quotient_eq` (equidim, NO flatness,
   per irreducible component) is a near-substitute IF the product structure is exhibited as an integral
   extension. The product additivity could route through Noether normalization of the product (the
   engine's own `exists_integral_inj_algHom_of_quotient` pattern), not tensor-additivity.

### Honest verdict on the dimension route

It **genuinely dodges the scheme-radicality/flatness wall** (the codim is radical-insensitive — a real,
decorrelated-confirmed simplification). But the **upper bound** still needs a product-dimension-additivity
that comes from a trivialization; the trivialization is now only required at the **reduced/set level**,
which is *easier* than the scheme iso `e` but is **not obviously free**. Whether the reduced-level
product iso escapes the circularity that killed `e` is the **one question to resolve before committing**
(the circularity for `e` was: forward map well-defined ⟺ `sigmaIdeal ≤ ker φ` ⟺ radicality. At the
reduced level the target is `R ⊗ F_E^red`, where the analogous condition `sigmaIdeal ≤ ker φ_red` may
hold *because* `R ⊗ F_E^red` is reduced by construction — this is the crack to probe).

## Route 2 — type-A rank-locus reducedness (direct)

Prove `Z_r = {rank(mult A) ≤ r}` (= `Σ̄^r`, a type-A quiver rank locus) reduced directly. Known TRUE
(Buch–Fulton / Kinser–Rajchgot: reduced, normal, CM, rational singularities). Cleanest classical
arguments: (i) Gröbner / standard-monomial (straightening law) degeneration to a reduced monomial ideal;
(ii) CM + generically-reduced ⟹ reduced (Serre `(R₀)+(S₁)`).

**Lean v4.29 feasibility: very low.** No determinantal Gröbner / straightening-law library, no
standard-monomial basis, essentially no CM/depth/Serre-condition API. From scratch = research-grade,
many modules. Codex concurs ("very high difficulty"). AND: even with `Z_r` reduced, transferring
reducedness to the FIBRE is a *separate* descent that routes through the same flat trivialization —
so it does not even dodge the wall. **Note:** `Σ̄^r`'s codim (`= C`) is ALREADY landed (Brick A,
`SigmaCodim`) without its reducedness — the engine got `C` via the orbit/Voigt route, not via a
determinantal-ideal reducedness. So route 2 is both hard AND not on the critical path for the codim.

## Route 3 — other routes

- **(a) Homogeneous space / orbit ⟹ smooth.** `mult⁻¹(E)` is NOT a single orbit (G07 recon: the inner
  group does not act transitively; stabiliser dim jumps on the `(1,1)` stratum — confirmed by my
  Jacobian-rank drop). The fibre is reducible + singular, so it is not globally homogeneous. **DEAD**
  as a smoothness route. (A dense open of each component IS smooth, but that is just generic
  smoothness, already covered under route 1.)
- **(b) Complete intersection / regular sequence.** `mult⁻¹(0) = Σ̄^0` is NOT a CI (`codim 3 ≠
  d_N·d_0 = 4`, landed). The `(1,1)` singular stratum confirms the fibre is not a smooth CI. The `δ`
  cut equations are NOT a regular sequence in general. **DEAD** (and was independently killed thread 14
  as the "`d_N·d_0` shortcut confound").
- **(c) Stratified dimension count.** Stratify `mult⁻¹(E)` by intermediate rank-patterns; `dim(fibre) =
  max over strata`. This is a genuinely DIFFERENT and possibly-clean route to the dimension UPPER bound
  WITHOUT a trivialization: each rank-pattern stratum has an explicit dimension formula (the engine
  carries rank-pattern combinatorics — `rankPattern`, Gabriel, Kostant), and the fibre is their finite
  union, so `dim = max`. *If* the per-stratum dims are computable from the landed combinatorics + a
  per-stratum dimension lemma, this could give the upper bound directly. **Worth probing** — it reuses
  the engine's strongest landed asset (the rank-pattern/orbit combinatorics) rather than building new
  AG. Risk: each stratum's dimension still needs a dimension formula (the orbit-dimension machinery is
  landed for `Σ̄^r` but the FIBRE strata are orbit-intersections, a new count). MED-HIGH; the most
  engine-aligned of the genuinely-new routes.
