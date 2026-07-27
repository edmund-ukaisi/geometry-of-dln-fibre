<task>
Lean 4 + Mathlib v4.29. I must prove `MeasurePreserving eWrap` where `eWrap` is a
coordinate-permutation homeomorphism from `Fin 21 -> R` to a nested matrix-tuple
pi-type, wrt the `volume` (nested-pi Lebesgue) measures on both sides. I want the
CLEANEST Lean route + the exact idiom for the one fiddly step. This is genuinely
just "a permutation of 21 coordinates preserves product Lebesgue measure", but the
formalisation is awkward because of a scattered layout, dependent Fin types, and an
opaque banked flatten.

## The objects (verbatim shapes)

Dimension vector `dvec : Fin 3 -> N := ![3,3,4]`.

`Tuple dvec := (i : Fin 2) -> Matrix (Fin (dvec i.succ)) (Fin (dvec i.castSucc)) R`
i.e. layer 0 is a `Matrix (Fin 3) (Fin 3) R`, layer 1 is a `Matrix (Fin 4) (Fin 3) R`.
`Matrix m n R` is reducibly `m -> n -> R`. `volume` on `Tuple dvec` is the nested
`Measure.pi` Lebesgue (the whole codebase treats it that way; NO matrix-normed-space
measure appears -- I am NOT going through `LinearMap.det`/addHaar; I want raw-pi tools).

`eWrap : (Fin 21 -> R) ~=t Tuple dvec` (Homeomorph), defined so that every tuple entry
equals exactly ONE input coordinate `u k` (coefficient 1). Explicitly:
  (eWrap u) 0 (r:Fin 3) (c:Fin 3) = A0 u r c, with A0 u = !![u 20, u 2, u 3; u 0, u 4, u 6; u 1, u 5, u 7]
  (eWrap u) 1 (a:Fin 4) (b:Fin 3) = A1 u a b = u (8 + 4*b + a)
It also has an explicit inverse `eInv` (reads entries back), and left_inv/right_inv/continuities
are all proven; `eWrap` is a genuine Homeomorph already in the file. NOTE the layout is
SCATTERED: layer-0 uses input coords {0..7, 20} (the pivot 20 = A0(0,0) breaks contiguity),
layer-1 uses coords 8..19.

Goal (the exact statement I must discharge, currently an unproven hypothesis):
  `MeasurePreserving eWrap (volume : Measure (Fin 21 -> R)) (volume : Measure (Tuple dvec))`

## Banked / available machinery (all confirmed present)

- `measurePreserving_tupleFlat`, `measurePreserving_canonFlatten`: give a MP MeasurableEquiv
  `Tuple d ~=m (Fin (flatDim d) -> R)`. BUT the reindex uses `Fintype.equivFin` (OPAQUE), so I
  cannot match `eWrap` to it coordinate-by-coordinate. `flatDim dvec` is a `Finset.sum` (= 21
  after reduction, but not syntactically `Fin 21`).
- `eMatFlat p q : (Fin p -> Fin q -> R) ~=m (Fin (p*q) -> R)` with `measurePreserving_eMatFlat`,
  and `eMatFlat p q D k = D (k / q) (k % q)` (computable: sigmaEquivProd ∘ finProdFinEquiv;
  finProdFinEquiv (i,j) = j + n*i). Importable.
- `MeasurableEquiv.piFinTwo (a : Fin 2 -> Type) : (∀i, a i) ~=m a 0 × a 1`, `volume_preserving_piFinTwo`.
- `MeasurableEquiv.sumPiEquivProdPi X : (∀ i:ι⊕ι', X i) ~=m (∀i:ι, X(inl i))×(∀i:ι', X(inr i))`,
  `measurePreserving_sumPiEquivProdPi_symm`.
- `MeasurableEquiv.arrowCongr' (eα:α≃β) (eβ:γ≃δ) : (α→γ)~=m(β→δ)`, `volume_preserving_arrowCongr'`
  (any index equiv; refl on ℝ). `(arrowCongr' e refl) u = u ∘ e.symm`.
- `MeasurableEquiv.piCongrLeft`, `volume_measurePreserving_piCongrLeft (α) (f:ι'≃ι)`.
- `MeasurableEquiv.piCurry` (curried ~=m sigma-uncurried) + `measurePreserving_piCurry`.
- `finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m+n)`, `finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)`.
- Precedent decode idiom in-repo (paramsEquivFlat_decode): unfold the piCurry/arrowCongr' composite
  via `MeasurableEquiv.coe_piCurry_symm`, `Equiv.arrowCongr_apply`, `Equiv.symm_apply_apply`, `rfl`.

## What I've figured out / the obstacle

Any explicit MP flatten I build reduces to a fixed "canonical" coordinate order; matching it to
`eWrap`'s scattered order requires an explicit 21-element bijection somewhere. Two candidate routes:

(A) Mirror `tupleFlat` but replace the opaque `Fintype.equivFin` reindex with an EXPLICIT
    `rho : Fin 21 ≃ tupIdx dvec` where `tupIdx dvec = Σ q:(Σ i:Fin 2, Fin (dvec i.succ)), Fin (dvec q.1.castSucc)`.
    Then the decode is `rfl`: `myFlat.symm u i r c = u (rho.symm ⟨⟨i,r⟩,c⟩)`, and if I DEFINE
    `rho.symm` = eWrap's exact read table the match is `rfl`. Cost: build `rho` over the DEPENDENT
    sigma `tupIdx` and prove it's an Equiv (round-trips). I'd define `w : tupIdx -> Fin 21` via
    `.val` arithmetic (case on i for the two tables), `rho := (Equiv.ofBijective w hbij).symm`, and
    hope `hbij` (injective, finite) closes by `decide`. Worry: the dependent-sigma `decide` (21^2
    pairs, dependent Fin equality) and the `< 21` bound proof for `w` (bound depends on i).

(B) Build a canonical flatten via combinators (piFinTwo -> eMatFlat 3 3 × eMatFlat 4 3 ->
    sumPiEquivProdPi.symm -> arrowCongr' finSumFinEquiv), MP trivially, then compose with an
    explicit `pi : Fin 21 ≃ Fin 21` (decide round-trips, NO dependent types) chosen so
    `eWrap = cFlat.symm ∘ arrowCongr' pi refl`, proven by `funext k; fin_cases k <;> rfl/decide`
    on the FORWARD direction `cFlat (eWrap u) = u ∘ pi.symm`. Cost: hand-computing pi's 21 entries
    through the combinator chain (error-prone), but no dependent-type friction.

## What I need from you

1. Pick the route (A, B, or a better one I've missed) that a Lean expert would actually take to
   MINIMISE thrash, and say why. If there is a slicker Mathlib idiom for "an explicit coordinate
   permutation between two finite pi-Lebesgue spaces is measure-preserving" that sidesteps both,
   name it.
2. For the chosen route, give the precise Lean skeleton (definitions + the key tactic lines),
   especially: the exact idiom to build the explicit bijection and discharge its round-trips WITHOUT
   getting stuck on dependent Fin casts, and the exact tactic to close the coordinate-matching.
3. Flag the concrete failure modes (where `decide` will choke, where `rfl` won't fire, cast diamonds)
   and the workaround for each.
</task>

<output_contract>
Section 1: ROUTE VERDICT — chosen route + one-paragraph why + any slicker idiom I missed (or "none").
Section 2: SKELETON — concrete Lean (v4.29) for the chosen route: defs, the bijection idiom, the MP
  chain, the matching tactic. Real lemma names.
Section 3: FAILURE MODES — bullet list: where it breaks + the fix.
Keep it tight; skeleton over prose.
</output_contract>

<grounding_rules>
Mathlib is v4.29 — if unsure a lemma exists at that pin, say so and give the most likely name +
a fallback. Mark anything you're inferring about lemma signatures vs. certain. Do not invent
lemma names; if you don't know one, say "verify: <likely name>".
</grounding_rules>
