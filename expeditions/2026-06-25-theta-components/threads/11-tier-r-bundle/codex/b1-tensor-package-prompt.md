<task>
Lean 4 + Mathlib (pinned v4.29.0). I need the cleanest sorry-free construction of one `AlgEquiv`.

SETUP (all already defined, names verbatim, namespace `DLNFibre.Core`):
- `k : Type u`, `[Field k]`.
- `SchurVar q p r : Type` is a finite type (it is `(Fin r × Fin r) ⊕ ((Fin r × Fin (q-r)) ⊕ (Fin (p-r) × Fin r))`, `[Fintype]`/`[DecidableEq]` available).
- `detSchurS q p r : MvPolynomial (SchurVar q p r) k` (a determinant polynomial; nonzero, `detSchurS_ne_zero` available).
- `SchurLoc q p r := Localization.Away (detSchurS (k:=k) q p r)`  -- a `k`-algebra, an `IsDomain`.
- `F := sweepFibreRing k d r hp hq` is some commutative `k`-algebra (`CommRing`, `[Algebra k F]`); treat it abstractly as `F : Type u, [CommRing F], [Algebra k F]`.
- `chartGfib := MvPolynomial.map (algebraMap k F) (detSchurS (k:=k) q p r)  :  MvPolynomial (SchurVar q p r) F`.
  (i.e. the `F`-coefficient image of `detSchurS`.)

GOAL — construct, sorry-free:
    Localization.Away chartGfib  ≃ₐ[k]  SchurLoc q p r ⊗[k] F
(or the equally-good `F ⊗[k] SchurLoc`; I can flip with `Algebra.TensorProduct.comm`.)

Mathlib API I have found and believe relevant (file paths are under `.lake/packages/mathlib/Mathlib/`):
1. `MvPolynomial.algebraTensorAlgEquiv R A : A ⊗[R] MvPolynomial σ R ≃ₐ[A] MvPolynomial σ A`
   with simp lemma `algebraTensorAlgEquiv_symm_map (x) : (algebraTensorAlgEquiv R A).symm (map (algebraMap R A) x) = 1 ⊗ₜ x`.
   So with `R=k, A=F, σ=SchurVar`: `(algebraTensorAlgEquiv k F).symm chartGfib = 1 ⊗ₜ detSchurS`.
2. In `RingTheory/Localization/BaseChange.lean`:
   - `instance IsLocalization.Away.tensor [IsLocalization.Away r A] : IsLocalization.Away (algebraMap R S r) (S ⊗[R] A)`
   - `instance IsLocalization.Away.tensorRight [IsLocalization.Away r A] : IsLocalization.Away (algebraMap R S r) (A ⊗[R] S)`
   - `noncomputable abbrev IsLocalization.Away.tensorEquiv (S) [IsLocalization.Away r A] : S ⊗[R] A ≃ₐ[S] Localization.Away (algebraMap R S r)`
   - `IsLocalization.tensorProduct_tensorProduct (M : Submonoid A) (B) [...] [IsLocalization M B] ... : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[R] S) M) (B ⊗[R] S)`
   - `IsLocalization.algEquiv (M) (S₁) (S₂) [IsLocalization M S₁] [IsLocalization M S₂] : S₁ ≃ₐ[R] S₂` (canonical iso between two localizations at the same submonoid).

The crux: `Away chartGfib` localizes `MvPolynomial SchurVar F` at the submonoid `powers chartGfib`.
`chartGfib` is the image of `detSchurS ∈ MvPolynomial SchurVar k` under `map (algebraMap k F)`.
And `MvPolynomial SchurVar F ≅ F ⊗[k] MvPolynomial SchurVar k` (algebraTensorAlgEquiv) carries `chartGfib ↦ 1 ⊗ₜ detSchurS`.
So morally `Away chartGfib ≅ Away (1 ⊗ₜ detSchurS in F ⊗ MvPolynomial SchurVar k) ≅ F ⊗[k] (Away detSchurS) = F ⊗[k] SchurLoc`.

What I am unsure about:
(a) The exact, lowest-friction lemma chain to go from `Away chartGfib` to `F ⊗[k] SchurLoc` — whether to
    (i) transport `IsLocalization.Away` along `algebraTensorAlgEquiv` to put an `IsLocalization.Away (1 ⊗ₜ detSchurS)` instance on `MvPolynomial SchurVar F`, OR
    (ii) prove `Localization.Away chartGfib` is `IsLocalization.Away` of something on the tensor side and invoke `IsLocalization.algEquiv` / `tensorRightEquiv`.
(b) How to discharge the `IsLocalization.Away (algebraMap k S detSchurS) (...)` shape — note `algebraMap k S detSchurS` is NOT what appears; the localizing element is `detSchurS` viewed inside `MvPolynomial SchurVar k` and then `map`-ped. So `R` in `IsLocalization.Away.tensor` should be `MvPolynomial SchurVar k` (the base whose element we invert), `S = F`?? but `F` is not a `MvPolynomial SchurVar k`-algebra. This mismatch is the thing I keep tripping on.
(c) Whether `IsLocalization.Away.tensorEquiv` wants base `R = k` (so `S ⊗[k] A` with `S = SchurLoc`, `A = ?`) — clarify which of `R,S,A` maps to `k`, `F`, `MvPolynomial SchurVar k`, `SchurLoc`.

Resolve the base-ring assignment explicitly. Give me the precise term/tactic proof skeleton (real Mathlib lemma names) for the goal `AlgEquiv`, with each `IsLocalization`/`IsScalarTower` instance I must supply named, and flag any instance-diamond or `algebraMapSubmonoid`-vs-`powers` defeq friction I will hit at the v4.29 pin.
</task>

<output_contract>
1. The base-ring/`R,S,A,B,M` assignment table for whichever Mathlib lemma(s) you pick (be explicit which symbol = k, F, MvPolynomial SchurVar k, SchurLoc).
2. The recommended chain (numbered steps), each step naming the real Mathlib lemma and the resulting type.
3. A concrete Lean proof skeleton (`noncomputable def … : … ≃ₐ[k] … := …`), tactic or term, that I can paste and iterate. Use `↦` not `=>`.
4. Pitfalls: which instances must be supplied by hand, any `algebraMapSubmonoid`-vs-`Submonoid.powers` defeq issue, any `Localization.Away` vs generic-`IsLocalization` mismatch, and the `≃ₐ[k]` vs `≃ₐ[SchurLoc]`/`≃ₐ[F]` scalar-restriction friction.
</output_contract>

<grounding_rules>
You are reasoning about Mathlib v4.29.0. If you are not sure a lemma name/signature exists at that pin, say so explicitly and give the conceptual step + a `grep` I should run to confirm, rather than inventing a name. Flag inference vs known-fact.
</grounding_rules>
