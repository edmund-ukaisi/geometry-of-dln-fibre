# Thread 01 — Mathlib recon for the Voigt discharge

**Scout, 2026-06-18.** READ-ONLY recon. Maps Mathlib v4.29 coverage for the four AG/CA pillars of
the tangent-space+smoothness route, returns a dependency-ordered build ladder with size reads, pins
the field hypotheses, confirms `orbitRankLocus` status and the route at the Lean level, and
reconciles a decorrelated Codex consult.

Pin verified: `lean-toolchain = leanprover/lean4:v4.29.0`, `lakefile.toml rev = v4.29.0`.
Mathlib root: `lean/.lake/packages/mathlib/Mathlib/`.

---

## TL;DR for the controller

- **Route is correct** at the Lean level against our actual defs (tangent + smoothness), with one
  structural caveat: our `codimRep` is point-set commutative algebra (`Ideal.height` of
  `MvPolynomial.vanishingIdeal` of points in `kⁿ`), while every dimension/irreducibility theorem in
  Mathlib lives on `PrimeSpectrum`. The route therefore has an *extra* mandatory layer: a
  point-space ↔ `PrimeSpectrum` bridge via the Nullstellensatz, which **forces `[IsAlgClosed k]`**.
- **The single largest absent piece is the height–dimension formula** (`height I = n − dim V(I)`,
  i.e. catenary / `dim = trdeg` for finite-type `k`-algebras). `IsCatenary` does **not exist** in
  Mathlib (0 hits). This is a sizeable sub-library, not a tide. Both my analysis and Codex converge
  here.
- **Cleanest field hypothesis: `[Field k] [IsAlgClosed k]`.** No char-0 needed. `IsAlgClosed ⇒
  PerfectField` (instance) covers generic smoothness; `IsAlgClosed` covers the Nullstellensatz
  point-space bridge. Compatible with the Core engine being network-free (an `[IsAlgClosed k]`
  hypothesis on the Core lemma is acceptable; DLN instantiates over its own field, expected ℝ/ℂ —
  flag in §Field).
- **`orbitRankLocus` is the rank locus (`≤`), NOT defined as the orbit closure.** The identification
  `orbitRankLocus = Ō_M` (Thm 3.8) is currently Cited and is part of the zero-cited target. Proving
  it needs a topology on `Tuple d = kⁿ` (absent) + the degeneration-order direction.
- **One pleasant surprise:** `RingEquiv.height_comap` / `height_map` now exist (`@[simp]`), so the
  linear-coordinate-invariance lever the `OrbitCodim` docstring flagged as absent at v4.29 is
  PRESENT. The docstring is out of date on this single point.

---

## The target, pinned (exact defs)

From `Core/OrbitCodim.lean`:

- `orbitRankLocus M : Set (Tuple d) := {A | ∀ i j (h : i ≤ j), rankPattern d A i j h ≤ rankPattern d M i j h}`
  — the **rank locus** (pointwise `≤` on the interval-subproduct ranks). A `≤` condition, not `=`.
- `codimRep coord Z := Ideal.height (MvPolynomial.vanishingIdeal (σ := RepCoord d) (k := k) (K := k) (coord '' Z))`
  — `Ideal.height : ℕ∞` of the vanishing ideal of `coord '' Z ⊆ (RepCoord d → k)` in
  `MvPolynomial (RepCoord d) k`. `RepCoord d = Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)`
  (one variable per matrix entry).
- `canonicalCoord d : Tuple d ≃ (RepCoord d → k)` — the entry flattening, `A ↦ ⟨i,r,c⟩ ↦ A i r c`.
  `hVoigt` is to be discharged at this coordinatisation.
- `hVoigt : codimRep (canonicalCoord d) (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞)`.

Algebra side (`Core/OrbitLinearCodim.lean`, PROVED):
`orbitLinearCodim M = finrank C¹ − finrank (range δ_M) = finrank (deformationExt1 M M) = dim Ext¹(M,M)`.
`δ_M = deformationδ M M : cochain0 → cochain1` (`Core/DeformationExt.lean`); `im δ_M` = tangent to
the orbit at `M`.

`G_d` action (`Core/BaseChange.lean`): `BaseChangeGroup d = ∀ v, (Matrix (Fin (d v)) (Fin (d v)) k)ˣ`,
`(P • A)_i = P_{i.succ} · A_i · P_{i.castSucc}⁻¹`. `MulAction` instance present;
`rankPattern_smul` PROVED (rank pattern is a `G_d`-invariant).

Complete invariant (`Core/Orbit.lean`, PROVED): `rankPattern_eq_iff_orbit` — `rankPattern A =
rankPattern B ↔ ∃ P, P • A = B`. So the **orbit** of `M` is exactly `{A | rankPattern A =
rankPattern M}` (equality), already Lean-proved. The closure is the `≤` locus (Cited).

---

## Pillar coverage map (exact decls; PRESENT vs ABSENT)

### P1 — Krull dimension / height in polynomial rings

**PRESENT** (verified in source):
- `ringKrullDim`, `Ideal.height`, `Ideal.primeHeight`, `Ideal.height_eq_primeHeight`
  (`RingTheory/Ideal/Height.lean`, `RingTheory/KrullDimension/Basic.lean`).
- `MvPolynomial.ringKrullDim_of_isNoetherianRing` : `ringKrullDim (MvPolynomial ι R) = ringKrullDim
  R + Nat.card ι` (Finite ι). With `ringKrullDim_eq_zero_of_field` (`KrullDimension/Field.lean`)
  ⇒ **`ringKrullDim (MvPolynomial (RepCoord d) k) = Nat.card (RepCoord d) = dim Rep`. FREE.**
- `RingEquiv.height_comap` / `RingEquiv.height_map` (`@[simp]`, `Ideal/Height.lean:277,289`) —
  height invariant under a ring iso. **The linear-coordinate-invariance lever; PRESENT** (the
  `OrbitCodim` docstring's "Mathlib v4.29 has no transport lemma for `Ideal.height` under a
  RingEquiv" is out of date).
- `Ideal.height_le_ringKrullDim_of_ne_top`, `Ideal.primeHeight_le_ringKrullDim`,
  `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`, `IsLocalization.AtPrime.ringKrullDim_eq_height`.
- **Krull's height theorem (Höhensatz)**: `Ideal.height_le_spanRank_toENat`,
  `Ideal.height_le_spanFinrank`, `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` (Haupt-
  idealsatz) — `Ideal/KrullsHeightTheorem.lean`. Gives the **`height ≤ #gens`** direction for free.
- `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` (`Spectrum/Prime/Topology.lean:1286`).
- `Order.coheight`, `krullDim_eq_iSup_height_add_coheight_of_nonempty`, `coheight_eq_krullDim_Ici`
  (`Order/KrullDimension.lean`) — order-level only.
- `NoetherNormalization.lean`, transcendence-basis machinery (`AlgebraicIndependent/*`) — building
  blocks toward dimension theory, **not assembled** into a dim theorem.

**ABSENT** (verified, 0 hits):
- **`IsCatenary` / catenary — does not exist** (`grep -ri catenary` over all of Mathlib = 0).
- **No `height p + coheight p = ringKrullDim R`** for a *fixed* prime (only the sup over all primes
  — that sup is not the dimension formula; equality for each prime IS the catenary content).
- **No `height I = n − dim V(I)`** / `height p + ringKrullDim (R ⧸ p) = ringKrullDim R`.
- **No `ringKrullDim = trdeg`** for finite-type domains over a field. No `IsEquidimensional`.

➤ **P1 verdict: the `≤` direction (height ≤ codim) is reachable from the Höhensatz; the equality
(the dimension formula) is the biggest single gap — a sub-library (Noether normalization →
`dim = trdeg` → catenary for finite-type `k`-algebras).**

### P2 — Zariski tangent space + regularity

**PRESENT**:
- `IsRegularLocalRing` (class, `RegularLocalRing/Defs.lean`): `(maximalIdeal R).spanFinrank =
  ringKrullDim R`.
- `IsRegularLocalRing.iff_finrank_cotangentSpace`: **regular ⇔ `finrank (ResidueField R)
  (CotangentSpace R) = ringKrullDim R`** — the local "embedding dim = Krull dim" bridge. PRESENT.
- `IsLocalRing.CotangentSpace R := (maximalIdeal R).Cotangent`,
  `spanFinrank_maximalIdeal_eq_finrank_cotangentSpace` (`Ideal/Cotangent.lean`,
  `Algebra/Module/SpanRankOperations.lean`), `FiniteDimensional` instance for Noetherian `R`.
- `KaehlerDifferential` (`Ω[A⁄R]`), `Ideal.cotangentEquivIdeal`, `Ideal.cotangentToQuotientSquare`.

**ABSENT** (verified):
- **`IsRegularLocalRing` is used nowhere outside its own Defs file** (`grep` over all of Mathlib).
  No theorem connects it to smoothness, to a geometric point, or to a variety.
- **No `Smooth`/`IsSmoothAt ⇒ IsRegularLocalRing`** bridge.
- **No packaged Zariski tangent space of an affine variety at a `k`-point** (`Module.tangentSpace`
  is the Kähler/relative cotangent dual, not the geometric tangent to a zero locus). No
  "linearized equations = tangent space" lemma. No `Tᵤ V(I) = ker (Jacobian)`.
- No instance `IsRegularLocalRing (localization of MvPolynomial at a maximal ideal)`.

➤ **P2 verdict: the local-algebra characterization (regular ⇔ cotangent finrank = dim) is PRESENT
and clean; the geometric bridges (smooth point ⇒ regular; tangent = ker Jacobian = `im δ⁰`) are
entirely ABSENT and must be built.**

### P3 — Smoothness / generic smoothness

**PRESENT**:
- `Algebra.FormallySmooth`, `Algebra.Smooth`, `Algebra.smooth_iff`; `RingHom.Smooth`;
  `Algebra.IsSmoothAt p := FormallySmooth R (Localization.AtPrime p)` (`Smooth/Locus.lean`).
- `Algebra.smoothLocus`, `Algebra.isOpen_smoothLocus`, `Algebra.smoothLocus_eq_univ_iff`,
  `Algebra.IsSmoothAt.exists_notMem_smooth`.
- `Smooth ⇒ Module.Flat` (`Smooth.flat`, `Smooth/Flat.lean`).
- **Scheme smoothness**: `AlgebraicGeometry.Smooth`, `Scheme.Hom.smoothLocus` (an `X.Opens`),
  `Scheme.Hom.smoothLocus_eq_top_iff`, `Scheme.Hom.mem_smoothLocus`.
- **Generic smoothness over a perfect field** (scheme level):
  `Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField`,
  `Scheme.Hom.dense_smoothLocus_of_perfectField` (`Morphisms/Smooth.lean:363`) — needs
  `[PerfectField K] [IsReduced X]`.
- **Group-scheme smoothness** (homogeneity ⇒ smooth-everywhere principle):
  `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed` (`AlgebraicGeometry/Group/Smooth.lean`,
  copyright 2026) — a reduced, locally-finite-type **group scheme** over `[IsAlgClosed K]` is smooth.

**ABSENT**:
- **No regular-locus API** (smooth locus ≠ regular locus is not bridged).
- **No algebraic-group / orbit / stabilizer / orbit-dimension API.** No `LinearAlgebraicGroup`.
  `GL_n` exists only as `Matrix.GeneralLinearGroup` (a type + group), **not as a scheme / group
  object**. To even invoke `smooth_of_grpObj_of_isAlgClosed` we'd have to build `G_d` and its action
  as schemes — the entire algebraic-group layer is missing.
- Applying generic smoothness to our concrete `orbitRankLocus` still needs the affine ↔ scheme
  bridge (our locus is a point set in `kⁿ`, not a `Scheme`).

➤ **P3 verdict: scheme-level smoothness + generic smoothness + group-scheme smoothness are PRESENT
(needs `PerfectField`/`IsAlgClosed`), a meaningfully better state than the 2026-06-17 recon recorded
("a Mathlib desert"). But they are scheme-level and unusable without (a) the affine↔scheme bridge
and (b) modelling `G_d`/the orbit map as schemes — both absent.**

### P4 — Irreducibility & the variety side

**PRESENT**:
- **Concrete (point-space) Nullstellensatz** (`RingTheory/Nullstellensatz.lean`, already imported by
  `OrbitCodim`): `MvPolynomial.vanishingIdeal`, `MvPolynomial.zeroLocus`,
  `vanishingIdeal_zeroLocus_eq_radical`, `IsPrime.vanishingIdeal_zeroLocus`,
  `isMaximal_iff_eq_vanishingIdeal_singleton` (all need `[IsAlgClosed K] [Finite σ]`),
  `pointToPoint : (σ → K) → PrimeSpectrum (MvPolynomial σ k)`,
  `vanishingIdeal_pointToPoint` (links point-space vanishingIdeal to `PrimeSpectrum.vanishingIdeal`).
- **`PrimeSpectrum` topology / prime ↔ irreducible**: `PrimeSpectrum.isIrreducible_zeroLocus_iff`,
  `isIrreducible_iff_vanishingIdeal_isPrime`, `zeroLocus_vanishingIdeal_eq_closure`,
  `vanishingIdeal_closure`, `minimalPrimes.equivIrreducibleComponents`
  (`Spectrum/Prime/Topology.lean`).
- **Abstract topology**: `IsIrreducible.image` (image of irreducible under continuous map is
  irreducible), `IsPreirreducible.image`, `IsIrreducible.closure`, `isIrreducible_iff_closure`
  (`Topology/Irreducible.lean`, `Topology/Sober.lean`).
- `AlgebraicGeometry.AffineSpace` (`𝔸(n; S)`, a `Scheme`), `AffineSpace.SpecIso`.

**ABSENT**:
- **No classical Zariski topology on the point space `kⁿ = (σ → k)`.** All Mathlib irreducibility
  lives on `PrimeSpectrum`, not on the point set our `codimRep` operates on. Bridging needs
  `pointToPoint` + the Nullstellensatz ⇒ `[IsAlgClosed k]`.
- **No `GL_n` (or product of `GL`) as an irreducible variety/scheme.** No decl.
- **No orbit-map / orbit-closure / group-action variety API.**
- No determinantal / rank-locus ideal-height API.

➤ **P4 verdict: prime↔irreducible and image/closure-of-irreducible are PRESENT but on
`PrimeSpectrum`; the Nullstellensatz point-space bridge is PRESENT but `[IsAlgClosed k]`-gated;
`GL`/orbit/variety irreducibility is ABSENT.**

---

## Field hypotheses — verdict

**Cleanest set: `[Field k] [IsAlgClosed k]`.** Step-by-step forcing:

- **Nullstellensatz point-space bridge** (`codimRep` is point-set; all dimension/irreducibility
  theory is on `PrimeSpectrum`): `vanishingIdeal_zeroLocus_eq_radical` etc. require `[IsAlgClosed
  K] [Finite σ]`. `RepCoord d` is `Finite` (instance already in `OrbitCodim`). ⇒ forces `IsAlgClosed`.
- **Generic smoothness** (`dense_smoothLocus_of_perfectField`): needs `[PerfectField k]`. Covered by
  `PerfectField` from `[IsAlgClosed k]`. ⇒ no separate hypothesis.
- **Group-scheme smooth-everywhere** (`smooth_of_grpObj_of_isAlgClosed`): needs `[IsAlgClosed K]`.
- **Smooth ⇒ regular**: mathematically does not need algebraic closedness, but the bridge is absent
  and must be built; building it over `[IsAlgClosed k]` is fine.
- **char 0: NOT needed** under `IsAlgClosed` (generic smoothness via perfect field, not char-0).

**Compatibility.** `codimRep` / `hVoigt` / `orbitRankLocus` are currently over a general `[Field k]`.
Adding `[IsAlgClosed k]` to the *Voigt lemma* is a hypothesis, not a cited interface — allowed by the
closing criterion. The engine is network-free, so an `[IsAlgClosed k]` hypothesis on the Core lemma
is acceptable.

**One flag for the controller.** The DLN application's natural field is ℝ (square-Frobenius loss) or
ℂ. ℝ is **not** algebraically closed. Discharge over `[IsAlgClosed k]` gives the codim over `k̄ = ℂ`;
the real codim equals the complex codim for these loci (cut out by the same rational equations,
ranks/Ext computed combinatorially the same), but **that real-vs-complex codim equality is a separate
small fact** the DLN-side instantiation must address. It does not block the Core discharge.
Recommendation: discharge the Core lemma over `[IsAlgClosed k]`; handle ℝ-vs-`k̄` on the DLN side.

---

## `orbitRankLocus` status

`orbitRankLocus M` is **defined as the rank locus** (`{A | rankPattern A ≤ rankPattern M}`, pointwise
`≤`), **not** the orbit closure. `orbitRankLocus = Ō_M` is Lehalleur–Rimányi Thm 3.8 (degeneration
order, equioriented type A), currently **Cited** in the `OrbitCodim` docstring.

Already PROVED that bears on it:
- `rankPattern_eq_iff_orbit` (`Core/Orbit.lean`): the **orbit** `O_M = {A | rankPattern A =
  rankPattern M}` (equality). Complete invariant, done.
- `rankPattern_smul`: rank pattern is a `G_d`-invariant.

Proving `orbitRankLocus = Ō_M` (zero-cited) takes **two non-trivial pieces**:
1. **A topology on `Tuple d = kⁿ`** to define `Ō_M = closure(O_M)`. Mathlib has none on the point
   space (only `PrimeSpectrum`). Routes through the same point-space↔`PrimeSpectrum` Nullstellensatz
   bridge (⇒ `[IsAlgClosed k]`), defining `Ō_M` as the Zariski closure of the point set `O_M`.
2. **The degeneration-order theorem.** `O_M ⊆ orbitRankLocus` is the easy half (rank-drop is a closed
   condition — minors vanish). The reverse `orbitRankLocus ⊆ Ō_M` is the substantive content.

**Scoping note:** the *route as written* does not need the set equality explicitly **if** we instead
(a) prove `Ō_M` (closure of the proved orbit `O_M`) is irreducible, (b) compute `height
(vanishingIdeal Ō_M)`, (c) show `vanishingIdeal (orbitRankLocus M) = vanishingIdeal Ō_M` (same
radical ideal). Step (c) IS Thm 3.8 at the ideal level — unavoidable, because `codimRep` is the
height of the vanishing ideal of `orbitRankLocus`. So **Thm 3.8 (at the radical-ideal / closed-set
level) is in scope for the zero-cited target.**

---

## Route confirmation (tangent + smoothness, at the Lean level)

The brief's four-step chain is the right and (with one addition) complete one. Mapped to our defs:

1. **`Ō_M` irreducible** = closure of the image of `G_d` (irreducible) under `P ↦ P • M`. Lean:
   `IsIrreducible.image` + `IsIrreducible.closure` present **but on a topological space**; must first
   install the Zariski topology on `kⁿ` (via `pointToPoint`) AND prove `G_d = ∏ GL` irreducible
   (absent). Needs the GL/orbit-geometry build.
2. **`M` smooth point, `T_M Ō_M = im δ⁰`.** Homogeneity (smooth locus dense + `G`-stable ⇒ smooth
   everywhere): Mathlib has the *principle* via `smooth_of_grpObj_of_isAlgClosed` /
   `dense_smoothLocus_of_perfectField`, but only for **schemes/group-schemes**; using them needs
   `G_d`/orbit/action as scheme objects (absent). The concrete `T_M Ō_M = im δ⁰` (= ker Jacobian =
   image of orbit-map differential) needs the affine-tangent API (absent). **Most hidden build.**
3. **smooth ⇒ local dim = tangent dim.** `IsRegularLocalRing.iff_finrank_cotangentSpace` gives
   `regular ⇔ cotangent finrank = ringKrullDim` (PRESENT). Missing: **smooth point ⇒
   `IsRegularLocalRing`** (absent) + identifying `finrank CotangentSpace` with `dim im δ⁰` (absent).
4. **`height (I(Ō_M)) = dim Rep − dim Ō_M`.** The **dimension formula** — `IsCatenary` absent; the
   biggest gap. The Höhensatz gives only `≤`.

**Addition the brief omits:** a **point-space ↔ `PrimeSpectrum` bridge** (Layer 0). Our `codimRep` is
`Ideal.height (vanishingIdeal (points))`; everything in steps 1–4 lives on `PrimeSpectrum`. The glue
is `pointToPoint` + `vanishingIdeal_pointToPoint` + Nullstellensatz (radical ↔ closed) ⇒
`[IsAlgClosed k]`. Without it the height in `codimRep` is not connected to any geometry.

**Subtlety (tangent of closure vs orbit):** step 2 computes the tangent of the **closure** `Ō_M` at
`M`. Because `O_M` is open in `Ō_M` (orbits of an algebraic group action are open in their closure —
a fact to build), `T_M Ō_M = T_M O_M = im δ⁰`. The "orbit open in closure" step is a named sub-fact
(absent in Mathlib). Without it, `T_M Ō_M ⊇ im δ⁰` is the wrong inequality direction.

**Cleaner alternatives considered (rejected for Lean):**
- *Orbit–stabilizer* (`dim O = dim G − dim Stab`): needs stabilizer group schemes + orbit dimension.
  Not cleaner.
- *Determinantal / rank-locus ideal height*: 2026-06-17 rankloc-probe + Codex established the rank
  locus is **not a complete intersection** (codim 3 with 6 generators on (2,2,2); `{BA=0}` reducible,
  codim 3 not 4; no regular sequence cuts it), so the cheap Eagon–Northcott/regular-sequence height
  is unavailable; it needs Schubert/quiver-determinantal CA + the same catenary theory. Relocates the
  ocean, does not shrink it.
- *Fibre-dimension*: needs fibre-dimension theorems (absent).

Tangent+smoothness remains the best reusable Lean route. Its irreducible cost is the **dimension
formula** (ladder step 5).

---

## Build ladder (dependency order, with size reads)

Sizes: **tide** = one focused PR/module; **module** = a substantial file/family; **sub-library** =
multi-file, multi-tide effort.

0. **Point-space ↔ PrimeSpectrum / Zariski-closure bridge.** *(module)* Define the Zariski closure of
   a point set in `kⁿ` (via `vanishingIdeal`/`zeroLocus` round trip, Nullstellensatz); relate
   `Ideal.height (vanishingIdeal S)` to `PrimeSpectrum` height of the corresponding closed set; port
   `IsIrreducible`/closure to the point space. Forces `[IsAlgClosed k]`. PRESENT bricks:
   `pointToPoint`, `vanishingIdeal_pointToPoint`, `vanishingIdeal_zeroLocus_eq_radical`,
   `RingEquiv.height_comap`.

1. **`G_d = ∏ GL` and the orbit map as geometry.** *(module → sizeable module)* Model `GL_{d_v}` as
   the principal open `D(det)` in affine matrix space; product = product of principal opens. Prove
   **irreducible** (+ reduced, finite type). Define the orbit morphism `P ↦ P • M`, prove its image's
   closure is irreducible. Absent today: no `GL` scheme, no product-of-GL irreducibility.

2. **Concrete affine Zariski tangent space + linearization.** *(sizeable module)* Define the tangent
   space of `V(I) ⊆ kⁿ` at a `k`-point as `ker (Jacobian)`; tangent functoriality for polynomial
   maps; **identify the orbit-map differential at `M` with our `δ⁰ = deformationδ M M`** (the
   differential of `P ↦ P·M·P⁻¹` is `φ ↦ φ·M − M·φ` = our `δ`). Identify `dim tangent = finrank (im
   δ⁰)`. Absent today entirely.

3. **Smooth point on the orbit (homogeneity).** *(module → sizeable module)* Either (a) wrap the
   orbit as a reduced, finite-type **group-scheme-homogeneous** space + `smooth_of_grpObj_of_isAlgClosed`
   / `dense_smoothLocus_of_perfectField` + `G`-stability of the smooth locus, or (b) prove
   smooth-everywhere directly from a dense smooth point transported by the transitive `G_d` action.
   Also prove **orbit open in its closure**. Bricks present (scheme generic smoothness); scheme-
   modelling of `G_d`/orbit is the cost.

4. **Smooth point ⇒ `IsRegularLocalRing` ⇒ tangent dim = local Krull dim.** *(module)* Build the
   missing `smooth/regular point ⇒ IsRegularLocalRing (local ring at the point)`, then
   `IsRegularLocalRing.iff_finrank_cotangentSpace` (PRESENT) + identify `finrank CotangentSpace` with
   the geometric tangent dim from step 2.

5. **★ The height–dimension formula (catenary / `dim = trdeg`).** *(sub-library — the largest piece)*
   Build, for `MvPolynomial (Fin n) k` / finite-type domains over `[Field k]`: `height p +
   ringKrullDim (R ⧸ p) = ringKrullDim R`, ideally via `dim = trdeg` (Noether normalization, a brick
   in `NoetherNormalization.lean`) + catenary. Derive the tailored form: *for prime `I ≤ k[x₁..xₙ]`,
   a smooth `k`-point of `V(I)` with tangent dim `t` ⇒ `I.height = n − t`*. **`IsCatenary` does not
   exist — greenfield.** Höhensatz (PRESENT) gives only `height ≤ #gens`.

6. **Thm 3.8 at the radical-ideal level.** *(module)* `vanishingIdeal (orbitRankLocus M) =
   vanishingIdeal Ō_M` (same closed set / radical ideal) — so `codimRep (orbitRankLocus M) = height
   (I(Ō_M))`. Easy half (semicontinuity: rank-drop is closed) + degeneration-order half. Needs step
   0's closure + the rank-condition ideals.

7. **Final Voigt assembly.** *(tide)* Glue: `codimRep (orbitRankLocus M) = height I(Ō_M)` (step 6)
   `= dim Rep − dim Ō_M` (step 5) `= dim Rep − dim T_M Ō_M` (steps 3,4) `= finrank C¹ − finrank (im
   δ⁰)` (step 2) `= orbitLinearCodim M` (PROVED). Discharges `hVoigt`.

### The 3–5 biggest must-build pieces (size)
1. **Height–dimension formula / catenary** (step 5) — **sub-library**. The irreducible ocean; both my
   analysis and Codex flag it as *the* risk. `IsCatenary` 0% present.
2. **Concrete affine Zariski tangent space + `T_M = ker Jac = im δ⁰`** (step 2) — sizeable module.
   Entirely absent; load-bearing for the whole tangent route.
3. **`GL`/`G_d`/orbit-map geometry + irreducibility** (step 1) — sizeable module. No `GL` scheme, no
   product-of-GL irreducibility, no orbit API.
4. **Smooth point ⇒ regular local ring** (step 4) + **orbit open/smooth-everywhere** (step 3) —
   module each. Local-algebra target (`iff_finrank_cotangentSpace`) present; geometric feed-ins absent.
5. **Point-space ↔ PrimeSpectrum bridge** (step 0) — module. Bricks present, assembly absent; gates
   everything and forces `[IsAlgClosed k]`.

---

## Codex reconciliation (decorrelated, xhigh; `codex/voigt-route-{prompt,answer}.md`)

Withheld my view first; fired the consult before finishing my own map. Codex independently
reproduced **every** pillar verdict (P1 catenary/dim-formula absent; P2 `iff_finrank_cotangentSpace`
present + smooth⇒regular absent; P3 scheme generic smoothness present, regular-locus absent; P4
Nullstellensatz/PrimeSpectrum present, GL/orbit/variety-tangent absent), the **`[Field k]
[IsAlgClosed k]`** verdict with the same "no char-0 needed" reasoning, and the **height–dimension
formula as the single biggest risk** ("the part most likely to turn this from a theorem into a
commutative-algebra sublibrary"). Its build ladder matches mine (it adds the explicit "model `GL_n`
as `D(det)`" tactic and names `AlgebraicGeometry.AffineSpace` as a possible scheme host).

Codex added value: (i) the tailored target lemma "smooth `k`-point of `V(I)` with tangent dim `t` ⇒
`I.height = n − t`" as the cleanest form to aim step 5 at; (ii) explicitly listing "orbit locally
closed / open-in-closure" as a named must-build (I had it as a route subtlety).

No disagreement to reconcile. One inference of Codex's I down-weight to "observation, verify in
build": that the determinantal route "may be cleaner on paper for type A" — the 2026-06-17
rankloc-probe already showed it is *not* cleaner in Lean, and Codex itself concludes it becomes a
separate large sub-library. Tangent+smoothness stands.

---

## Reflection (which claim advances / which breaks / next computation)

- **Most likely to advance:** the recognition that the route has a mandatory **Layer 0
  point-space↔PrimeSpectrum bridge** that forces `[IsAlgClosed k]`. Pinning it lets the controller
  layer the build correctly (a prerequisite the brief's 4-step chain omitted) and fixes the field
  hypothesis before any tide.
- **Most likely to break / the real risk:** the **dimension formula (step 5)**. Kill-condition for
  "step 5 is a bounded sub-library": if assembling `dim = trdeg` from Mathlib's `NoetherNormalization`
  + transcendence-basis bricks itself needs a chain of absent integral-extension dimension lemmas
  (going-up/going-down, `dim ≤ dim` under integral extension), the sub-library is multi-expedition,
  not one.
- **Next computation that would clarify:** trace the standard `ringKrullDim (finite-type domain /k) =
  trdeg` proof and check each link against Mathlib (what stands between `NoetherNormalization.lean` +
  `AlgebraicIndependent/*` and the dim theorem). That single trace sizes step 5, which sizes the
  expedition. A `pen-and-paper`/focused-scout seat on "the `dim = trdeg` gap in Mathlib v4.29" is the
  highest-value next move.
