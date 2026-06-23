# Codex consult — chart-flatness construction for the DLN fibre-codimension (route M-goingdown)

You are a decorrelated second model red-teaming a Lean-formalisation design decision. Be concrete and
adversarial. We need a GO/NO-GO on whether a specific *flatness* fact is (a) true and (b) reachable in
Lean 4 + Mathlib v4.29, on the SIMPLEST nontrivial case, before we commit ~6-9 modules.

## The setup (paper: Lehalleur–Rimányi 2024, geometry of fibres of DLN multiplication map)

Dimension vector `d = (2,2,2)`, `N=2`. `Rep_d = Mat_{2x2}(k) × Mat_{2x2}(k)` — tuples `(A1, A2)`.
The multiplication map `mult : Rep_d → Mat_{2x2}(k)`, `(A1,A2) ↦ A2·A1`.
Target rank `r = 1`; `E = diag(1,0)`. We want the geometric identity
`codim(fibre over B) = cCodim(d,r) + r(d_0 + d_N - r)` for `B` of rank `r`.

The paper's proof: `mult` restricted to the exact-rank-`r` stratum `Σ^r` is a Zariski-locally-trivial
fibre bundle over `Mat^{rk=r}` (the rank-exactly-`r` locus), GL×GL-equivariant; so
`dim Σ^r = dim Mat^{rk=r} + dim(fibre)`. On the **pivot chart** `U` (top-left r×r block of the
product invertible), the Schur-complement section `D = C A^{-1} B` trivializes:
`mult^{-1}(U) ∩ Σ^r ≅ U × mult^{-1}(E)`.

## The engine we have (all sorry-free, Lean v4.29)

- `mult` defined over any CommRing. Coordinate rings as `MvPolynomial`:
  - base (target) ring `R_base = MvPolynomial (Fin 2 × Fin 2) k` = `k[b_{rc}]` (the 4 entries of B);
  - total ring `R_tot = MvPolynomial (RepCoord d) k` = `k[A1,A2]` (8 entries).
  - comorphism `multComap : R_base →ₐ[k] R_tot`, `X (r,c) ↦ multPoly d r c = (A2·A1)_{rc}` (a degree-2
    polynomial in the 8 A-variables). This is GLOBAL (no rank restriction baked in).
- We have the LANDED going-down height-additivity:
  `Ideal.height P = Ideal.height p + height(P mod p·R_tot)` when `R_tot` is flat over `R_base`
  through an algebra map, both Noetherian (`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`),
  and `Module.Flat ⟹ Algebra.HasGoingDown` is an instance.
- `IsLocalization.flat`, `Localization.Away.mapₐ (f) (a) : Localization.Away a →ₐ Localization.Away (f a)`.

## Route M-goingdown (the one we are gating)

Localize `multComap` at the pivot minor: base away from `Δ_B := b_{00}` (or `det` of top-left rxr),
total away from `multComap(Δ_B) = (A2·A1)_{00}`. Get
`φ_loc : R_base[1/Δ_B] →ₐ[k] R_tot[1/multComap Δ_B]`.
**Claim to gate:** `R_tot[1/(A2A1)_{00}]` is FLAT (ideally FREE, via the Schur section) over
`R_base[1/b_{00}]` through `φ_loc`. Then HasGoingDown + the landed lemma give the height shift.

## The questions — be precise and adversarial

1. **Is the flatness even TRUE as stated?** Sharp worry: `R_base` is the FULL `Mat_{2x2}` coordinate
   ring (dim 4), but `mult` (product of two general 2×2) is generically rank 2 = surjective onto a
   dense open of `Mat_{2x2}`, so `multComap` is INJECTIVE and `R_tot` has dim 8 = 4 + 4 over a dim-4
   base — fibre dim 4. BUT the geometry the paper needs is the EXACT-RANK-1 stratum `Σ^1` mapping to
   `Mat^{rk=1}` (dim 3), fibre dim 4, total dim 7. These are DIFFERENT maps. Which ring does
   route M-goingdown actually need to be flat over which? The global `multComap` (R_base = full
   Mat_{2x2}) — is THAT flat on the pivot chart? Or do we need the comorphism of the RESTRICTED map
   `Σ^1 → Mat^{rk=1}`, whose coordinate rings are QUOTIENTS by determinantal ideals (rank ≤ 1)?
2. If we need the restricted map: the base becomes `R_base ⧸ (2×2 minors)` (the rank-≤1 ideal) and the
   total becomes `R_tot ⧸ (fibre-rank ideal)`. Is the localized restricted comorphism flat/free? Is the
   Schur section a genuine AlgEquiv `(R_tot/I)[1/Δ] ≃ (MvPolynomial fibreVars (R_base/J)[1/Δ])`? Spell
   out what's actually free over what.
3. **Reachability at v4.29:** which is the showstopper — constructing the localized determinantal
   quotient algebra map, or PROVING freeness/flatness? Is there a route to `Module.Flat` that does NOT
   require building the explicit AlgEquiv (e.g. a generic-flatness / miracle-flatness / Cohen-Macaulay
   argument), and is any of that in Mathlib v4.29? (We could not find generic-flatness or
   miracle-flatness in v4.29 — confirm or correct.)
4. **The cleaner alternative:** is there a way to get `HasGoingDown` (or the height shift directly)
   WITHOUT flatness — e.g. the section gives a retraction making `mult` admit a section on the chart,
   which forces going-down by a soft argument? Or is flatness genuinely required?
5. Bottom line: GO or NO-GO on landing a chart-flatness gating fact for `(2,2,2), r=1` THIS run, and if
   NO-GO, what is the single precise wall.
