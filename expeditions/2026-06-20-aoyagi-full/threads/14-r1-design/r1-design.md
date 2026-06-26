# R1 design — the resolution (`resolution_charts`), the mountain

- **Seat:** `pp` (pen-and-paper), thread 14. **Read-only on repo; /tmp scratch; no Lean.**
- **Status:** design complete; chart-construction correctness adjudicated (self-cert on small cases +
  decorrelated Codex, which CORRECTED an over-clean claim — see §3/§6). Ready to formalise once
  `paramsEquivFlat` (fm-2, #15) lands.
- **Builds on:** thread-03 (the stratification `codim S(t) = Mval(t)`, proven general-L 3 ways; the
  per-case chart blueprints).

## R1 statement (Skeleton.lean, specialised to `dlnLoss`)

```
theorem resolution_charts (H) (B) (wstar) :
  ∃ (ι) (Fintype ι) (d : ι → ℕ) (k h : (i:ι) → Fin (d i) → ℕ),
    rlctAt H (dlnLoss H B) wstar = ⨅ i : ι, monomialThreshold (d i) (k i) (h i)
```
`monomialThreshold d k h = sSup { c' ≥ 0 : ∫_{[0,1]^d} (∏|uⱼ|^{hⱼ})·(∏|uⱼ|^{2kⱼ})^{−c'} < ∞ }`.
The whole deliverable is a **VALUE-MATCH**: a finite chart-exponent family `(ι, d, k, h)` whose
monomial thresholds reconstruct `rlctAt`. It does NOT require reproducing Aoyagi's bookkeeping (§0),
but — corrected by Codex — the **chart construction itself** is most tractably Aoyagi's recursion
(§2), while the **value** is pinned cleanly by the stratification + a cited codim/2 theorem (§3).

---

## §0. Two separable things: the VALUE (clean) and the CHART ATLAS (Aoyagi's recursion)

The mistake to avoid (the prior expedition's failure mode, brief's "awkward middle") is reproducing
Aoyagi's exponent engine as the *content*. The fix is to separate:

- **The VALUE** `rlctAt = ½·min_t Mval(t)` — pinned by the stratification (`codim S(t) = Mval(t)`,
  proven) + the RLCT-of-zero-fibre `= codim/2` (§3). Clean, general, no chart enumeration.
- **The CHART ATLAS** (`ι, φᵢ, k, h`) — the explicit normal-crossing family the statement names.
  Codex (§6) corrects my first instinct: a literal smooth-center normal-crossing atlas organised
  "one blow-up per prefix-stratum `S(t)`" is **NOT correct as stated** (the prefix ranks `t_j` are
  too coarse; the centers are determinantal hence singular). The tractable explicit atlas is
  **Aoyagi's iterated affine-coordinate blow-ups** (§2) — coordinate-subspace blow-ups + explicit
  substitutions + integer exponent bookkeeping. The cleaner flag/quiver resolution exists but is a
  far heavier Lean target (§2).

**So R1 = [VALUE pinned by §3] feeding [the monomial thresholds of Aoyagi's affine atlas §2].** The
atlas supplies the `(ι,d,k,h)`; the value-match (that their `⨅` equals `rlctAt`) rides on §3.

**Toric/Newton route ruled out** (`/tmp/r1_toric.py`, Codex §2): `F = ‖∏C‖²` is Newton-degenerate
— Codex's explicit torus zero `A=[[1,1],[1,1]], B=[[1,1],[-1,-1]]` (all entries ≠0, `AB=0`, so `F`
and all derivatives vanish there) kills Kouchnirenko nondegeneracy. Not toric.

---

## §1. The geometry: nested-rank strata (the VALUE substrate)

`{F=0} = {∏C = 0}` is the finite union of nested-rank strata
`S(t) = { C : rank(C¹···Cʲ) = tⱼ ∀j }`, `t` weakly-decreasing, `t_L = 0`. Proven (thread-03,
general-L, 3 ways):
> `codim S(t) = (M¹−t₁)(M²−t₁) + Σ_{j=2}^L (t_{j−1}−tⱼ)(M^{j+1}−tⱼ) = Mval(t)`, and each `S(t)` is
> **smooth** (the strata, not their closures; the closure `S(t)⁻` is determinantal hence singular).

`codim{∏C=0} = min_t codim S(t) = min_t Mval(t)` (the zero-fibre is the union; its codim is the min
over its smooth strata).

**Codex refinement (§6):** the strata that index a literal *chart atlas* are finer than the prefix
ranks `t_j` — they are the **full type-A rank pattern** `r_{ab} = rank(C^a···C^b)` over all intervals
`a ≤ b` (the quiver-orbit strata). The prefix `S(t)` partition is right for **codim-minimisation**
(the VALUE), too coarse for the **atlas**. This is exactly why the value/atlas split (§0) is the
right architecture: minimise on the coarse strata, build the atlas with Aoyagi's affine charts.

---

## §2. The explicit chart atlas (a) — Aoyagi's iterated affine blow-ups (Lean-tractable)

**What `ι` is.** `ι` = the **branches** of Aoyagi's recursion (2023 pp.15–21): at each step, a choice
of **pivot** (which regular entry survives) = an affine chart of one smooth-center blow-up. The center
each step is `{d_ij = 0, u_{s,k} = 0}` (Case 1) or `{d_ij = 0}` (Case 2) — in the chart a **smooth
coordinate subspace** (single rank-drop pivot, never the singular determinantal variety). Branches are
finite ⟹ `ι` `Fintype`. Charts vastly outnumber strata (24 vs 3 for (2,2,2)) — by design, they
refine strata via the full rank-pattern + the affine-minor (pivot) choices.

**The chart maps `φᵢ` (explicit, symbolically verified).** Compositions of "pivot `= u`; off-pivot
`= u·(new var)`; Schur-residual `= u·(residual) + (next-block)`". Worked cases (thread-03 + Codex §1,
all `F∘φ`, `|det Dφ|` verified in sympy):

- **(1,1,1)** `F = c₁²c₂²` — ALREADY normal-crossing, `ι = {*}` (identity), `d=2`, `k=(1,1)`,
  `h=(0,0)`, ratios `(½,½)`, min `½ = λ`. *(validate-small-first: needs only `paramsEquivFlat` + the
  box monomial threshold — both in hand.)*
- **(2,1,2)** `F = (a₁²+a₂²)(b₁²+b₂²)` — 4 product charts, each `F = x²z²(1+y²)(1+w²)`,
  `|det Dφ|=|xz|`, `(k,h)=(1,1)` on `x,z`, ratios `(1,1)`, min `1 = λ`, θ=2.
- **(2,2,2)** `F = ‖AB‖²` — 24 charts. Codex §1 gives a clean 3-blow-up smooth sequence
  (`Z_A={A=0}` codim4 → strict-transform `Z_B={B=0}` codim4 → strict-transform incidence
  `{rkA≤1,rkB≤1,AB=0}` codim3) with the explicit incidence chart `A=α[[1,a],[b,ab+δ]]`,
  `B=[[u−ar,v−as],[r,s]]` ⟹ `AB=α[[u,v],[bu+δr,bv+δs]]`, blow up `(δ,u,v)`, δ-chart `δ=ρ,u=ρξ,v=ρη`
  ⟹ `F = α²ρ²·[ξ²+η²+(bξ+r)²+(bη+s)²]` (positive unit), Jacobian `|ρ|²` ⟹ `(k,h)=(1,2)`, ratio
  `3/2`. min over charts `= 3/2 = λ`, θ=1. *(Independent of and matching my thread-03 `x²s²` chart.)*

**The per-chart `(k,h)` in general (the divisor exponents) — CORRECTED (`/tmp/r1_binding_check.py`).**
Each exceptional divisor `u` resolves a smooth center along which `F` (sum of squares) vanishes to
order **exactly 2** (`/tmp/r1_order2_check.py`: each `(∏C)_ij` is linear in the vanishing block,
squared ⟹ `u²`), so **`k = 1` for every divisor**; a smooth codim-`c` blow-up gives Jacobian
`u^{c−1}`, so **`h = c−1`**, ratio `c/2`. The chart's `(k_i,h_i)` are these per its crossing divisors;
non-exceptional coords have `k=h=0`.

**The binding divisor sees the FULL stratum codim in ONE blow-up** (this corrects an earlier
"telescoping divisor-by-divisor sum" framing, which was WRONG — `/tmp/r1_telescope_L3.py`). On the
branch resolving `S(t)`, after the regular pivot split exposes the **residual block** (whose vanishing
IS the stratum `S(t)`), a **single** blow-up of that residual-block-zero center — of codimension
exactly `codim S(t) = Mval(t)` — gives the **binding divisor** `(k,h) = (1, Mval(t)−1)`, ratio
`½·Mval(t)`. Verified on (2,2,2): the minimizing chart has TWO divisors — `α` (A-origin, codim-4)
`(1,3)`→ratio 2, and `ρ` (the residual `{δ=u=v=0}`, codim-**3** in one step = Mval(t=1)) `(1,2)`→ratio
**3/2** = λ. The binding divisor is `ρ`; its `h=2 = Mval−1`, NOT `min(1,2)` of the rank-drop steps.
The `Mval = 1+2` *sum-formula* is the codim **arithmetic** (rank-drop bookkeeping, thread-03);
geometrically it is realized as ONE codim-`Mval` binding center per branch — not a chain of small
divisors. So: **each branch's binding divisor ratio = ½·Mval(t) for its terminal stratum `t`; min over
branches = ½·min_t Mval(t) = λ.**

---

## §3. The assembly (c) + R1↔min-Mval (d) — the VALUE-LEVEL bridge (Codex-corrected)

**The clean general argument (value-level, NOT chart-bijection — Codex §3):**
1. each `S(t)` is **smooth** with `codim = Mval(t)` (thread-03, proven);
2. `{∏C=0} = ⋃_t S(t)` ⟹ `codim{∏C=0} = min_t Mval(t)`;
3. **`rlctAt(‖∏C‖²) = codim{∏C=0} / 2`** — the RLCT-of-the-zero-fibre `= codim/2`. This is the
   **Lehalleur–Rimányi `codim/2` theorem** (Codex cites arXiv:2411.19920 — the *companion paper to
   this expedition*); for the homogeneous core it gives `λ = ½ min_t Mval(t)` directly;
4. therefore **every** valid log-resolution — including Aoyagi's affine atlas — satisfies
   `min over charts min_j (h+1)/(2k) = ½ min_t Mval(t)`.

**This is the R1 value-match.** The `⨅` over charts realises the `min` (admissible-`c` are down-sets;
the joint integral over the cover is finite iff every chart-piece is — partition of unity; S1.1 §4).

**The R1↔Adm match (d), correctly stated** (final form, supersedes design-spec §9.3 AND my own first
draft): NOT a chart↔`T` bijection (charts outnumber `T`-vectors), and NOT even "each minimizing chart
↔ one prefix-stratum" (Codex §3: **too strong** — charts refine strata by the full rank-pattern +
affine-minor choices). The match is purely the **VALUE**: `min over charts of the ratios =
½ min_t Mval(t)`, with `Mval(t) = codim S(t)` the geometric input. The divisor-ratio mechanism (§2,
`k=1`, `h=Mval(t)−1` at the per-branch **binding** divisor, ratio `½·Mval(t)`) is the *per-branch*
realisation; the *clean* proof of the value is steps 1–4 above (the codim/2 theorem), which avoids
the atlas entirely.

**TWO PROOF ROUTES for the value-match, both valid:**
- **(R3a) Cited codim/2** (cleaner, lighter): use the Lehalleur–Rimányi `rlct = codim/2` as an input
  (it is a *separate* result — but note the expedition's one-citation policy is S2; adding codim/2
  as a second citation would need operator sign-off). Then R1's value = `½·codim{∏C=0}` and the chart
  atlas only needs to EXIST (some log-resolution) for the `⨅`-form, not to be computed.
- **(R3b) Self-contained via the atlas** (the brief's prove-all-but-S2 route): build Aoyagi's affine
  atlas (§2), read off `(k,h)`, prove `min_chart ratios = ½ min_t Mval` by the divisor-ratio
  binding-divisor ratio (`½·Mval(t)` per branch) + `codim S(t) = Mval`. No codim/2 citation; uses only S1.1 + S2. **This is the route
  consistent with the one-citation policy** — recommended unless the operator admits codim/2.

---

## §4. Cover (b) + interfaces

**Cover:** the pivot branches exhaust the rank-pattern stratification of `{∏C=0}` near `wstar`
(each step's charts cover the blown-up locus minus the next center; iterate over branches). Off
`{F=0}` the integrand is locally bounded (threshold-irrelevant).
**Consumes S1.1** (`paramsEquivFlat` + weighted-threshold transport): per-chart `rlctAt(F) =
θ(F∘φᵢ, |det Dφᵢ|·bump)` + the finite-cover `⨅`. The mandatory Jacobian weight `|det Dφᵢ|` is the
`u^{c−1}` factor, already in `h`.
**Consumes S2** (the one axiom): `monomialThreshold d k h = min_j (h_j+1)/(2k_j)`.
**Hands A1** the value `⨅ = ½ min_t Mval(t)`; **hands A2/θ** the minimizing-divisor-type multiplicity
`= a(ℓ−a)+1` (NOT chart count, NOT `|argmin Adm|` — thread-03 θ-seam).

---

## §5. Hypotheses beyond `hB : B.rank = r` (flag) — NONE hidden (Codex §4 confirms)

After L2/Theorem-3, `B` is gone; the core is `‖∏C‖²` with `M⁽ˢ⁾ = H⁽ˢ⁾ − r`. R1 on the core needs
only: char 0 / ℝ (automatic); **positive integer widths** (the strata are nonempty & smooth for all
admissible `t` — thread-03 verified L=2,3,4); the rank condition `r = rank B ≤ min_s M⁽ˢ⁾` (well-
specified, fed by `hB`). **No genericity, no width inequality.** Codex §4 also notes the Frobenius
norm may be replaced by ANY positive-definite quadratic form on the output without changing the RLCT
(consistent with the Σ_X-elimination, S1.4a). Clean — no hidden hypothesis.

The one geometric fact R1's Lean proof must establish per step: **each pivot-vanishing center is
smooth in its chart** (a single-rank-drop coordinate subspace, not the singular determinantal
variety). Verified explicitly on the small cases; the general statement is the "variety-of-complexes /
Aoyagi affine" smoothness, the R1 construction obligation.

---

## §6. Decorrelated Codex consult (verdict — folded in above)

Fired at xhigh (own web research, incl. arXiv:2411.19920 = Lehalleur–Rimányi, and the determinantal-
resolution literature). Verdict + the two corrections it forced, both adopted:
1. **CORRECTED my over-clean §3:** "one smooth-center blow-up per prefix-stratum `S(t)`" is NOT a
   literal normal-crossing atlas — determinantal centers are singular; the smooth resolution
   (Vainsencher complete-collineations / Reineke tautological-flag) is a *sequence* refined by the
   **full rank-pattern** `r_{ab}`, not prefix ranks. The prefix `S(t)` is right for the VALUE
   (codim-min), too coarse for the ATLAS. ⟹ value/atlas split (§0).
2. **Lean-tractability reversal:** Codex now judges **Aoyagi's recursive affine blow-ups the MOST
   tractable explicit atlas** (coordinate-subspace blow-ups + substitutions + integer bookkeeping),
   vs the conceptually-clean flag resolution which needs determinantal-resolution + flag-bundle +
   strict-transform + SNC machinery (a much larger formalisation). So §2 recommends Aoyagi's atlas
   for the atlas, §3(R3b) for the value.
CORROBORATED: the value `λ = ½ min_t Mval = codim/2`; `codim S(t) = Mval(t)`; no hidden hypotheses;
the (2,2,2) incidence chart `(k,h)=(1,2)`→3/2 (matches my thread-03 `x²s²`); toric route dead.
I judged its algebra: the incidence-chart computation (`AB=α[[u,v],[bu+δr,bv+δs]]`, δ-chart
`F=α²ρ²·unit`, Jacobian `ρ²`) is correct and matches my independent (2,2,2) resolution.

---

## §7. Recommended R1 Lean architecture (ready to formalise)

**Decision: build the atlas with Aoyagi's affine charts (§2); prove the value-match self-contained
(R3b, one-citation-policy-clean).** Concretely:

1. **(1,1,1) first** [validate-small-first]: `ι = Unit`, identity chart, `(k,h)=((1,1),(0,0))`. Needs
   only `paramsEquivFlat` + the box monomial threshold (both in hand) — the gate. Closes #12.
2. **The divisor-ratio lemma** (§2): a smooth codim-`c` center (the residual-block-zero locus =
   `S(t)` in the chart, `c = codim S(t) = Mval(t)` at the binding divisor) ⟹ `F∘φ = u²·unit`
   (`k=1`, order-2 vanishing of a sum-of-squares) + `|det Dφ| = u^{c−1}·pos` (smooth-blow-up
   Jacobian, `h=c−1`), ratio `c/2`. The reusable per-divisor core; the binding divisor of each branch
   realises `½·Mval(t)` (NOT a sum of single-rank-drop steps — `/tmp/r1_telescope_L3.py`).
3. **`codim S(t) = Mval(t)`** (A1/R1 shared, thread-03 proof): telescoping determinantal codim.
4. **Atlas + assembly:** Aoyagi affine branches give `(ι,d,k,h)`; `min_chart ratios = ½ min_t Mval`
   by the per-branch binding-divisor ratios (`½·Mval(t)`) + step 3; the `⨅`-form via S1.1 transport + S2.
5. **Cover** (§4): pivot branches exhaust the stratification.

**Scope flag for the operator:** R3a (cite Lehalleur–Rimányi `codim/2`) would collapse R1's value to
one line, but adds a SECOND citation beyond S2 — needs sign-off. R3b (self-contained, recommended)
keeps one-citation but requires the atlas + telescoping proof. Either way the small-case ladder
(1,1,1 → 2,1,2 → 2,2,2) is the validation path, every step symbolically verified.

**Hardest remaining piece** (honest): the general-L Aoyagi-atlas *construction* in Lean (the
recursive pivot blow-ups with the smooth-center + `(k,h)` bookkeeping). This is THE mountain; steps
1–3 are tractable and reusable, step 4's general-L atlas is the heavy lift. The small cases are
closed-form and give the validation gate; the general atlas is the open construction.

## §8. The general-L binding-divisor route REUSES L1 (cost-reducing, verified)

A finding that shrinks the step-4 heavy lift (`/tmp/r1_residual_codim.py`, L=3 (2,2,2,2) verified):
the **value-match needs only the MINIMIZING branch's binding divisor**, not the full atlas. And that
binding divisor is produced by **iterated L1 (block elimination) down to the deepest block** — the
machinery `fm` is *already* building for L1 / `deepestPoint_exists`. Concretely:

> For a minimizing stratum `t`, the iterated pivot split (= L1 applied layer-by-layer, peeling the
> regular rank-`tⱼ` blocks) exposes a **residual block** of exactly `Mval(t)` coordinates whose
> simultaneous vanishing is `S(t)`. That residual-block-zero locus is a **smooth coordinate subspace
> of codim `Mval(t)`** (it's `codim S(t) = Mval(t)`, thread-03, realized as coordinates post-split).
> ONE blow-up of it → binding divisor `(k,h) = (1, Mval(t)−1)`, ratio `½·Mval(t)`. (2,2,2): the
> `{δ=u=v=0}` residual, 3 coords, codim 3 = Mval(t=1) — exactly the verified chart.)

> **NOT over-determined — the residual is a REGULAR SEQUENCE of length `Mval(t)`** (the controller's
> flagged worry, adjudicated — me + decorrelated Codex agree). Verified: `/tmp/residual_check2.py`,
> `/tmp/residual_sweep.py` (sweep L=2,3,4, all admissible strata, product-map diff-rank = Mval
> EXACTLY, zero mismatches). The full interval rank-pattern `r_{ab}` (a≥2) adds NO equations: a prefix
> stratum `S(t)` cuts only the prefix ranks; inner intervals MAY be constrained but only as
> **consequences** (e.g. on `S(t=(1,0,0))` of (2,2,2,2), `rank C² ≤ 1` is forced by `C¹C²=0 ∧ rank C¹=1`
> — derived, NOT an independent generator). (This drops an earlier wrong "inner intervals stay generic"
> sub-claim of mine — they need not be generic; what holds is codim = Mval exactly.)
>
> **The residual is NESTED Schur-blocks `R_1,…,R_L`, not a single matrix (Codex refinement, adopted).**
> The pivot split gives, per layer, `R_j = D_j − C_j A_j⁻¹ B_j` (Schur complement of the chosen
> `t_j×t_j` pivot `A_j` in the active `t_{j−1}×M^{j+1}` block), of size `(t_{j−1}−t_j)×(M^{j+1}−t_j)`;
> for `j=1` it's `(M¹−t₁)×(M²−t₁)`. Then `S(t)∩chart = {R_1=…=R_L=0}` (+ open `det A_j ≠ 0`), and the
> total scalar count is `Σ |R_j| = (M¹−t₁)(M²−t₁) + Σ_{j≥2}(t_{j−1}−t_j)(M^{j+1}−t_j) = Mval(t)`. The
> `R_j` entries are JOINTLY coordinate functions ⟹ their joint zero-locus IS a single smooth
> codim-`Mval(t)` coordinate subspace — so the "single smooth center" picture holds, but the center is
> the CONCATENATION of all `R_j`, not one final-product residual. (CAUTION, Codex: a *final-product*
> residual alone would cut the COARSER product-zero locus = union over rank profiles — the naive
> `{∏=0}`, not `S(t)`. Must use all the `R_j`.) Codex's explicit L=3 (1,1,0) chart: `{s=u=v=0}`, 3
> residual coords, binding divisor `(k,h)=(1,2)`, ratio 3/2 — matches my thread-03/binding-check.
>
> **Generic-point caveat (Codex):** the binding divisor `(1, Mval−1)` ratio `½Mval` holds at a GENERIC
> point of the minimizing stratum (where the product map has full normal rank `Mval`, so `F = u²·unit`).
> At nongeneric points a suffix factor can vanish and `F/u²` may not be a unit — more blow-ups there,
> but those do not invalidate the generic binding divisor, which is what the value-match consumes.

So R3b's step 4 is NOT "build the whole 24-chart atlas + bookkeeping" — it is:
1. iterated L1 to the deepest residual block (REUSES fm's L1);
2. the residual block is a codim-`Mval(t)` coordinate subspace (codim S(t) = Mval, thread-03);
3. blow it up → binding divisor, divisor-ratio lemma (§2) → ratio `½·Mval(t)`;
4. this is the binding (min) ratio; S1.1's `min`-over-cover + the lower bound (no chart beats the
   minimal-codim stratum) close `rlctAt = ½·min_t Mval(t)`.

The full atlas (all branches, all charts) is needed for the *complete* normal-crossing statement, but
**the value-match — which is what the headline consumes — needs only the minimizing branch's binding
divisor**, built from L1 + one blow-up + the divisor-ratio lemma. This is materially lighter than the
general Aoyagi recursion and is the recommended R3b execution order. (The lower bound "every chart's
ratio ≥ ½ min codim" still needs the cover/exhaustiveness argument §4 — that part does range over
branches, but as an *inequality* over strata, not a per-chart exponent computation.)
