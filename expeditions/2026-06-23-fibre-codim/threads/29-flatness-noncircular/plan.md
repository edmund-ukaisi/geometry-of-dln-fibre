# Thread 29 — non-circular flatness route to `dim Σ^r = δ + dim F` (pen-and-paper plan)

*Seat: `pen-and-paper`. Decisive question (operator, build COMMITTED): is there a **non-circular**
route to `dim Σ^r = δ + dim F` (≡ discharging `hSweep` = `cited_bundle_shift`)? Exact algebra
(Singular, two anchors) + decorrelated xhigh Codex + Lean-API reachability against the landed engine.
No Lean writes.*

## VERDICT (one line)

**(A-qualified) A non-circular route to the dimension identity EXISTS** — the **generic-flatness +
homogeneity-transport** route (Codex's "sidestep", which I independently converged on). It dodges
WALL 1 (the reducedness-forcing scheme iso `e`) and WALL 2 (product-trdeg). **BUT** its load-bearing
input — **generic flatness / generic freeness** — is **ABSENT from Mathlib v4.29** and is itself a
from-scratch build; and the alternative "prove `schurToSred` flat at `E` then going-down" route is
**genuinely blocked**: the chart fibre is non-equidimensional at `E`, so flatness-at-`E` is a real
extra statement that re-enters product-decomposition territory (≈ WALL 1). So the operator's
committed build is **viable but its true cost is dominated by a generic-freeness sub-library**, not by
the height-additivity closer the engine already carries. **This is closer to (B)'s "true cost is a
deeper build" than to a clean ~8–12-module (A).**

Two decorrelated xhigh Codex consults + exact Singular primary-decomposition on `(2,2,2)r1` and
`(3,3,3)r1` concur on the obstruction and the winning route.

---

## 1. The decisive exact-algebra finding (ground truth, both anchors)

The brief's hope was: *dimension is radical-insensitive, so a flatness/going-down route may dodge the
R2-3b-4 reducedness circularity.* That hope is **correct for the dimension value but does not make
`schurToSred` flat-at-`E` non-circularly**, because of one hard structural fact, computed exactly:

### 1.1 The chart fibre over `E` is NON-EQUIDIMENSIONAL — and `E` IS in the chart

`E = diag(I_r,0)` has the top-left `r×r` minor `= 1` invertible, so **`E` lies in the pivot chart**
and the chart fibre over `E` is the *full* fibre `F = mult⁻¹(E)`. On `(3,3,3) r=1` (`card=18, C=3,
δ=5`):
- **`Σ̄^r` (rank-`≤1` product locus) is REDUCIBLE**: 3 components, dims **15, 14, 14** (top = `card−C
  = 15`). Singular `minAssGTZ`.
- **`F = mult⁻¹(E)` has 3 components, dims 10, 9, 9** (top = `card−C−δ = 10`). The dim-10 component =
  *both* `3×3` factors rank-`≤2` (`detA1, detA2 ∈ ideal`); the two dim-9 = *endpoint-invertible*
  branches (`A1∈GL_3` or `A2∈GL_3`, other factor rank `≤1`).
- **ALL THREE `F`-components have `mult = E` exactly** (product rank exactly `1`), so all three **meet
  the exact-rank chart** `{pivot invertible}`. The chart does NOT trim away the dim-9 components.

So the chart fibre is genuinely non-equidimensional (10, 9, 9). The uniform shift `+δ=+5` holds *per
component* (`15−10=14−9=14−9=5`), but the fibre is not equidimensional.

### 1.2 What this kills, and what survives

- **Miracle / local flatness (route A): CIRCULAR.** EGA-IV-6.1.5 / Stacks `00R4` needs the local
  equality `dim S = dim R + dim(S/m_E S)` — i.e. `(card−C) = δ + dim F` — which **IS the target**.
  Feeding it is circular. (CM, route A2, *is* true — see 1.3 — but the dimension-equality hypothesis
  is still the target, so CM alone does not close it.)
- **Regular sequence / relative CI (route B): FAILS.** On `(2,2,2)r1` the fibre ideal `(mult(Ã)−E)`
  is codim 4 with 4 generators but its minimal free resolution is **NOT Koszul** (Betti
  `1,?,6,8,3`, `pd=4`), so the 4 entries are **not a regular sequence**; on `(3,3,3)r1` there are
  `d_N·d_0=9` endpoint equations but the top component has codim `8` — excess generators, syzygies.
  No relative CI.
- **Flatness-at-`E` via "free resolution / explicit presentation" (brief's (i)): re-enters WALL 1.**
  `schurToSred` IS in fact flat on the chart (1.3), but any *proof* of flatness-at-`E` that exhibits
  the structure (the product decomposition `S ≅ R ⊗ (F_E)_red` Codex names) **forces `F_E` reduced**
  — the exact R2-3b-4 circularity. Height being radical-insensitive removes the *need* for
  reducedness downstream, but it does **not** remove it from the *flatness proof at `E`* — flatness
  at the closed point is the product-trivialization statement in disguise.

### 1.3 The flat family is real (so the dimension IS right) — but flatness-at-`E` is not the lever

Every chart fibre has **identical Hilbert data**: `(dim, mult)` `= (4, 8)` on all four tested
`(2,2,2)r1` chart points, and `= (10, 60)` on all three tested `(3,3,3)r1` chart points (`E` +
generics). By `GL_{d_N}×GL_{d_0}`-homogeneity (engine `codimRepCanonical_fibre_eq_of_rank_eq`, G1) all
rank-`r` fibres are **literally isomorphic**, so the family is flat — `schurToSred` IS flat on the
chart. **But** "flat on the chart" as a *theorem* is the product trivialization (WALL 1); what is
cheap and non-circular is only the *isomorphism of fibres* (homogeneity), which gives constant fibre
**structure/dimension**, not flatness-as-an-`R`-module-property proved at `E`. `O(Σ̄^r)` is also
**Cohen–Macaulay** (`pd = codim = 3` on `(3,3,3)r1`, Auslander–Buchsbaum ⟹ `depth = dim`; Hochster–
Eagon / Kinser–Rajchgot for the quiver locus) — but as Codex notes, importing the *right* quiver-locus
CM theorem is a serious result, not a small lemma, and it still leaves the circular dimension-equality.

---

## 2. The non-circular route that DOES exist (generic flatness + homogeneity transport)

Both Codex and my computation land here. It proves the **dimension value** without ever proving
flatness at `E`:

> **(GF-H)** `mult|_{Σ^r} : Σ^r → Mat^{=r}` (or the reduced chart map `R → S`). By **generic
> flatness** (Grothendieck; Stacks `052B`/`051R`) there is a dense open `V ⊆ Mat^{=r}` over which the
> map is flat; for a closed `k`-point `y ∈ V`, the flat-fibre dimension formula gives
> `dim(fibre over y) = dim Σ^r − dim Mat^{=r} = (card−C) − δ`. **Homogeneity** (`Mat^{=r} = H·E`, all
> rank-`r` fibres `H`-isomorphic — engine G1) transports this dimension to the closed point `E`:
> `dim F = dim(fibre over y) = (card−C) − δ`, i.e. **`codim F = C + δ`**.

- **Dodges WALL 1:** uses only *isomorphism* of fibres (the `H`-action, LANDED), never the
  reduced-product scheme iso `e`. No reducedness of `F_E` is asserted or needed.
- **Dodges WALL 2:** no product-trdeg; the dimension comes from generic flatness on a *single*
  morphism + a per-point dimension formula, not from `trdeg(O(H)⊗O(F))`.
- **Closes the closed-vs-generic gap WITHOUT flatness-at-`E`:** the generic point need not be `E`;
  homogeneity moves a *good* (flat-locus) closed point to `E`. Codex's one caution: transport via a
  **closed `k`-point in the flat-locus open**, NOT a literal `F_E ≅ F_{k(Y)}` (the generic fibre lives
  over `k(Y)`).

### Why this is *not* a clean win (the honest cost)

The load-bearing inputs are **Mathlib-absent at v4.29** (grep-verified):
- **Generic flatness / generic freeness** (a finite module over a Noetherian domain is free on a dense
  open): **ABSENT.** `Mathlib.RingTheory.Spectrum.Prime.FreeLocus` has only `isOpen_freeLocus`
  (free-locus open) + `freeLocus_eq_univ` (finite+flat ⟹ free everywhere) + `rankAtStalk`
  locally-constant — the *substrate*, but **not** the generic-freeness theorem (no proof that the free
  locus is *dense*/nonempty for a finite torsion-free module over a domain). That theorem is the
  from-scratch piece.
- **The flat-fibre dimension formula** `dim X_y = dim X − dim Y` for a finite-type affine morphism on
  the flat locus: **ABSENT** as a packaged lemma (the engine has the single-orbit `dim = trdeg`
  pullback and the affine-domain catenary, but not a relative/morphism fibre-dimension theorem — this
  is exactly thread-28's "Mathlib-absent" finding restated).
- **Engine is fully ring-level** (no `AlgebraicGeometry`/`Spec` import in `Core`; `mult` is set-level
  on `Tuple d`). So "generic flatness of a morphism" must be reconstructed at the ring level
  (`localization at a single element of the base makes the module free`), then bridged to the engine's
  `varietyDim`/`vanishingIdeal` codim — a non-trivial new layer.

---

## 3. Decomposition / true cost (what the operator's committed build actually is)

The `+δ` does NOT decompose into a clean ~8–12-module build that reuses the going-down closer cheaply,
because the going-down closer needs flatness-at-`E` (blocked) and the dimension route needs
generic-freeness (absent). The honest module map of the **(GF-H) route**:

1. **[reuse, LANDED]** `dim Σ̄^r = card − C` (`SigmaCodim` + catenary); `dim Mat^{≤r} = δ`
   (`DeterminantalStratumDim` thermometer + `ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta`);
   homogeneity `codimRepCanonical_fibre_eq_of_rank_eq` (G1); the gauge (`EndpointNormalization`);
   `Sred`/`schurToSred` (`DeepChartRing`); the comorphism (`MultComorphism`); `FibreCodim` lower
   bound; `RouteCAssembly` arithmetic (consumes the value once obtained).
2. **[NEW, the dominant cost — generic freeness sub-library]** Ring-level generic freeness: for a
   finite module `M` over a Noetherian **domain** `R`, there is `0 ≠ f ∈ R` with `M_f` free over
   `R_f`. (Classical Grothendieck/Bourbaki; Mathlib has only `isOpen_freeLocus`/`rankAtStalk`, not
   density.) **~3–5 modules** (the induction on a filtration / the "shrink the base" argument).
3. **[NEW]** The flat-fibre dimension formula on the flat locus, bridged to the engine's
   `varietyDim`/Krull-dim: `dim(R_f-fibre) = dim S − dim R` for the chart map — via the LANDED
   going-down height-additivity `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
   (`FlatQuasiFiniteHeight`) applied **on the flat locus** `R_f` (where `Module.Flat ⟹
   Algebra.HasGoingDown` via `HasGoingDown.of_flat`, present at v4.29). **~2–3 modules** (the
   localization-height bookkeeping the brief's part (i) imagined, now legitimately on the flat open).
4. **[NEW]** Homogeneity transport of the dimension value from the flat-locus closed point to `E`
   (the `H`-action carries `varietyDim` of fibres; reuse G1's machinery). **~1–2 modules**.
5. **[NEW, MED]** Reducibility / per-component min: `codim F = min over components = δ` — the dim-9
   components have codim `> δ`, the dim-10 gives `= δ`; via Brick A `minimalPrimes_sigmaIdeal_eq`.
   **~1–2 modules**.
6. **[thin]** G4 DLN wiring: discharge `BundleShiftInterface.cited_bundle_shift`.

**Total ≈ 8–12 modules** — *matching* the prior estimate in raw count, but with the **risk relocated**
from "build the flat trivialization `e`" (circular) to "build generic freeness + the relative
fibre-dimension formula" (Mathlib-absent but **non-circular** and standard mathematics). The
generic-freeness sub-library (rung 2) is the new wall and is genuinely sub-expedition-scale; it is
*not* a quiver-specific obstruction (it's a general commutative-algebra theorem Mathlib lacks), which
is both good (reusable, no circularity) and bad (a real from-scratch build).

---

## 4. Direct answer to the brief's two parts

- **(i) Is `schurToSred` provably flat DIRECTLY (free res / explicit presentation / `Sred`
  presentation) WITHOUT `e` and WITHOUT product-trdeg?** **NO, not non-circularly at `E`.** It *is*
  flat on the chart (the family is flat — uniform fibre Hilbert data, fibres `H`-isomorphic), but every
  *proof* of flatness **at the closed point `E`** exhibits the product decomposition `S ≅ R ⊗
  (F_E)_red`, which **forces `F_E` reduced** = the R2-3b-4 circularity (WALL 1). Miracle flatness needs
  the target dimension equality (circular); the relation ideal is not a regular sequence (route B
  fails); the explicit `Sred` presentation does not by itself yield flatness without the trivialization.
  The closed-fibre subtlety the brief flagged is exactly the break: **`E` is in the chart, the chart
  fibre over `E` is the full non-equidimensional `F`**, so going-down-at-`E` cannot be fed a
  relative-height-0 uniformly.

- **(ii) Any OTHER non-circular route?** **YES — generic flatness + homogeneity transport (GF-H,
  §2).** It computes the dimension on a *generic* flat-locus closed point and transports to `E` by the
  `H`-action, entirely sidestepping flatness-at-`E`, the going-down-at-`E`, the scheme iso `e`, and
  product-trdeg. It is the cleanest non-circular route. Its cost is dominated by **building generic
  freeness** (Mathlib-absent) + the relative fibre-dimension formula (§3 rungs 2–3).

**The smallest from-scratch Mathlib-side theorem** (so the operator knows (b)'s true cost): **ring-level
generic freeness** — *a finitely generated module over a Noetherian integral domain is free after
inverting a single nonzero element* (equivalently: the free locus of a f.g. module over a domain is a
dense open). With it, the LANDED going-down/affine-domain engine + homogeneity close the rest. Without
it, the `+δ` cannot be reached non-circularly. (The `HasGoingDown.of_flat` + height-additivity closer
the brief hoped to lean on is present and correct — but it only applies *after* flatness is in hand,
which on the flat locus comes from generic freeness, and at `E` is circular.)

---

## 5. Kill-conditions / what is most likely to break it

- **Sharpest break (Codex + my computation concur):** the **non-equidimensional closed chart fibre**.
  Because `E` lies in the chart, the chart fibre over `E` *is* the full `F` (dims 10,9,9 on
  `(3,3,3)r1`), so any route through equidimensional fibres, a regular sequence, miracle flatness, or
  going-down-at-`E` with uniform relative height is refuted by `(3,3,3)r1`. Only the
  *generic*-point + homogeneity-transport route survives.
- **Next risk:** the generic-freeness build (rung 2) is the wall-within. If it proves harder than
  ~3–5 modules at v4.29 (it is a genuine Grothendieck-flavoured theorem, not a one-liner), the (b)
  cost balloons. The engine's ring-level (no `Spec`/scheme) substrate means it must be done at the
  module-over-domain level, then bridged to `varietyDim` — adds friction.
- **Scope (engine-standing):** `[IsAlgClosed k] [CharZero k]`, `N ≥ 1`, `r ≤ min_i d_i`. The
  homogeneity needs `N ≥ 1` (for `N=0` `mult` is constant). Char 0 for the engine dimension chain.

## 6. Reproduction (this thread)

- `flatness_probe.sing` — the decisive `(3,3,3)r1` script: `Σ̄^r` comps (15,14,14), `pd=codim=3`
  (CM), `F`-comps (10,9,9) all meeting the exact-rank chart, uniform fibre `(dim,mult)=(10,60)`.
- Inline `(2,2,2)r1`: `dim Σ̄^r=7`, `detP = detA1·detA2` (reducible), fibre `(dim,mult)=(4,8)`
  uniform across 4 chart points, fibre ideal `pd=4` not Koszul (route B dead).
- `codex/noncirc-flatness-{prompt,answer}.md` — decorrelated xhigh Codex; converges: generic-flatness
  + homogeneity is the clean non-circular route; miracle/regular-seq circular/failing; flatness-at-`E`
  a genuine extra statement; generic freeness is the missing standard (likely from-scratch) piece.
