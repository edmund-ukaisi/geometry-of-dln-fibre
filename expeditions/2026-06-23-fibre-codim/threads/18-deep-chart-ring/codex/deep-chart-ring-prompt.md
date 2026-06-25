<task>
Lean 4 + Mathlib v4.29 formalisation. I am building the DEEP chart ring `Sred` for the
rank-`≤ r` locus of the multiplication map of a deep linear network, over a GENERAL dimension
vector `d : Fin (N+1) → ℕ`, and the localized base→total `k`-algebra map that gives it a
`SchurLoc`-algebra structure. The engine's localized determinantal presentation is currently
`N = 1` ONLY. I need a decorrelated design review of the cleanest assembly, and the API to pin.

CONTEXT — the existing N=1 machinery (all LANDED, sorry-free):
- `RepCoord d := Σ i : Fin N, Fin (d i.succ) × Fin (d i.castSucc)`  (one coord per matrix entry).
- `multPoly d : Fin (d (last N)) → Fin (d 0) → MvPolynomial (RepCoord d) k` — the generic product
  entries; `multComap d : MvPolynomial (Fin (d last) × Fin (d 0)) k →ₐ[k] MvPolynomial (RepCoord d) k`
  is `aeval (fun rc ↦ multPoly d rc.1 rc.2)`, the comorphism of `mult`.
- `sigmaIdeal d r : Ideal (MvPolynomial (RepCoord d) k)` = vanishingIdeal of `Σ̄^r` (the closed
  rank-≤r product locus); RADICAL, prime only at N=1 (where the locus is a single orbit closure).
- `dStratum q p := ![q, p] : Fin 2 → ℕ` (single matrix); `dStratum q p (last 1) = p`, `dStratum q p 0 = q`
  both by `rfl`.
- N=1 base presentation (over `dStratum q p`):
  - `detPivotPoly q p r hp hq : MvPolynomial (RepCoord (dStratum q p)) k` = det of the top-left r×r
    submatrix of `Matrix.of (multPoly (dStratum q p))`.
  - `Iad q p r hp hq := (sigmaIdeal (dStratum q p) r).map (algebraMap _ (Localization.Away detPivotPoly))`.
  - `SchurLoc q p r := Localization.Away (detSchurS q p r)` (a domain; `R` in the trivialization).
  - `basePresentationEquiv [IsAlgClosed k] [CharZero k] q p r hp hq :`
    `(Localization.Away (detPivotPoly q p r hp hq) ⧸ Iad q p r hp hq) ≃ₐ[k] SchurLoc q p r`.
- The downstream consumer (R2-3a, LANDED, conditional on a hypothesis `e`):
  `fibreGenIdeal_isRadical_of_trivialization (d) (B) (R S : Type u) [Nontrivial R] ...`
  `(e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) : (fibreGenIdeal d B).IsRadical`.
  So my deep `S = Sred`, my `R = SchurLoc (d 0) (d last) r`. R2-3b-3/-4 (LATER tides) build `e`;
  THIS tide builds only `Sred`, the instances, the type bridges, and the localized base→total map.

WHAT I HAVE ALREADY VERIFIED LOCALLY (elaborates clean, v4.29):
1. The deep defs:
   `ΔPdeep d r (hp : r ≤ d (last N)) (hq : r ≤ d 0) := det of submatrix (Fin.castLE) of Matrix.of (multPoly d)`.
   `IadDeep d r hp hq := (sigmaIdeal d r).map (algebraMap _ (Localization.Away (ΔPdeep d r hp hq)))`.
   `Sred d r hp hq := Localization.Away (ΔPdeep d r hp hq) ⧸ IadDeep d r hp hq`.
   `CommRing`, `Algebra k`, `IsLocalization.Away (ΔPdeep)` all infer; `Algebra k Sred` infers.
2. The type bridge `RepCoord (dStratum q p) ≃ Fin p × Fin q` is `Equiv.uniqueSigma (fun i : Fin 1 ↦ ...)`
   (Sigma over the `Unique` base `Fin 1`; `default = 0` makes `β default = Fin p × Fin q` defeq).
   Hence `MvPolynomial.renameEquiv k (that equiv) : MvPolynomial (RepCoord (dStratum q p)) k ≃ₐ[k]
   MvPolynomial (Fin p × Fin q) k`. CLEAN.
3. `IsLocalization.Away.mapₐ (f : A →ₐ[R] B) (a : A) [Away a Aₚ] [Away (f a) Bₚ] : Aₚ →ₐ[R] Bₚ` EXISTS.
   `Ideal.quotientMapₐ (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) : A ⧸ I →ₐ[R₁] B ⧸ J` EXISTS.
4. For N=1, `multPoly (dStratum q p) r c = X ⟨0, r, c⟩` (the single generic matrix entry) is provable.

THE OPEN DESIGN QUESTION (what I want reviewed):
The base→total map should be a `k`-algebra map `SchurLoc (d 0) (d last) r → Sred d r hp hq`. My plan:
  (a) `basePresentationEquiv.symm : SchurLoc q p r → (Localization.Away detPivotPoly ⧸ Iad)` (q=d 0, p=d last).
  (b) a localized quotient map `(Localization.Away detPivotPoly ⧸ Iad) → Sred d r hp hq` built from
      `multComap d` (after the rename bridge), via `Away.mapₐ` then `quotientMapₐ`.
The crux of (b): I must (i) show `multComap d` (precomposed with `renameEquiv` to land in the right
domain) sends `detPivotPoly`'s polynomial to `ΔPdeep d` (so `Away.mapₐ` applies — needs `f a` to be the
localization element of the codomain), and (ii) show the comap-image of `sigmaIdeal (dStratum q p) r`
lands in `sigmaIdeal d r` (so `quotientMapₐ` applies: `Iad ≤ IadDeep.comap (the localized map)`).
For (ii), Codex's prior wall note said: prove `multComap` maps the BASE `sigmaIdeal` into the DEEP
`sigmaIdeal`, and AVOID the circular `sigmaIdeal ≤ fibreGenIdeal`.
</task>

<output_contract>
Five sections, terse:

1. ROUTE VERDICT — is plan (a)+(b) the cleanest base→total map, or is there a shorter assembly
   (e.g. a single `IsLocalization.Away.mapₐ` from the base localization, skipping the rename, by
   choosing the localization element directly)? Give the recommended morphism chain explicitly as a
   composite of named Mathlib/engine constructions.

2. THE `detPivotPoly ↦ ΔPdeep` TRANSPORT — the precise statement I must prove for `Away.mapₐ` to
   typecheck (what `f a = (localization element)` equality, and over which ring map `f`). Is the
   right `f` `multComap d ∘ renameEquiv`, or should I instead define a direct
   `MvPolynomial (RepCoord (dStratum q p)) k →ₐ[k] MvPolynomial (RepCoord d) k` and prove it carries
   the pivot det to `ΔPdeep`? Name the determinant-commutes-with-aeval lemma (`AlgHom.map_det` /
   `RingHom.map_det` / `map_det`) and how the submatrix indices line up.

3. THE `sigmaIdeal → sigmaIdeal` DIRECTION — concretely, is
   `(sigmaIdeal (dStratum q p) r).map (multComap d ∘ rename) ≤ sigmaIdeal d r` provable WITHOUT
   circularity, and what is the mechanism? (My read: `sigmaIdeal` is a `vanishingIdeal`; pulling
   back along the comorphism = pushing forward the locus; a base point in `Σ̄^r_{(q,p)}` lifts to a
   total point whose product has rank ≤ r. State the cleanest Lean route — `vanishingIdeal` membership
   chase, or `Ideal.map_le_iff_le_comap` + `mem_vanishingIdeal`.) Flag if this is actually HARD and
   should be deferred to R2-3b-4 with the base map left at the `IsScalarTower`-structure level only.

4. THE `IsScalarTower`/instance ladder around `SchurLoc` — list the instances I must establish so
   that `Sred` becomes a `SchurLoc q p r`-algebra (the `R`-algebra structure R2-3a's `e` needs,
   `R = SchurLoc`). Is `Algebra.compHom` / `RingHom.toAlgebra` from the base→total `k`-algebra map the
   right way, and does it conflict with the existing `Algebra k Sred`?

5. R2-3b-3 PRE-STAGE — for the endpoint-normalization `aeval` substitution AlgEquiv on the
   UNQUOTIENTED `MvPolynomial (RepCoord d) R` over an arbitrary coeff ring `R` (NOT
   `baseChangeAlgEquiv`, which carries `[Infinite k]`): give the exact `AlgEquiv.ofAlgHom` skeleton
   (the two `aeval` directions + the two `AlgHom.ext` round-trips on generators) as `example`-block
   contracts I should pin now. Keep it to the shape, not a full proof.
</output_contract>

<grounding_rules>
This is Mathlib v4.29 (Lean 4.29.0). Do NOT trust recalled lemma signatures — for any lemma you
name, flag it as "verify exists" unless it is in the list I gave above (which I confirmed locally).
Distinguish (a) what you are confident is in Mathlib v4.29 from (b) plausible-but-unverified names.
If a step is genuinely a Mathlib-API wall (no clean path), SAY SO — I would rather defer it than grind.
</grounding_rules>
