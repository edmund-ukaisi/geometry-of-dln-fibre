# Statement card — G2-2b graph-ideal elimination seams

Two reusable, hole-free `Core` seams landed by tide G2-2b. Both feed the localized determinantal
base presentation (`Iad = J`, `height J = C`) and the G2-3 total presentation.

## Seam 1 — `ker_aeval_eq_graphIdeal` (Deliverable 1)

**Module:** `lean/DLNFibre/Core/MvPolynomialKerAeval.lean` (commit `e4b85042`).
**Pure `MvPolynomial`; no DLN/RepCoord dependency.**

| Name | Statement | Status |
|---|---|---|
| `graphIdeal (c : ι → R)` | `Ideal.span (Set.range fun i ↦ X i − C (c i))` | def |
| `sub_C_mem_ker_aeval` | `X i − C (c i) ∈ ker (aeval c)` | Proved |
| `sub_C_aeval_mem_graphIdeal` | `p − C (aeval c p) ∈ graphIdeal c` (any `p`, any `ι`) | Proved |
| `ker_aeval_eq_graphIdeal` | `RingHom.ker (aeval c).toRingHom = graphIdeal c` | **Proved** |
| `aeval_surjective` | `Function.Surjective (aeval c)` | Proved |
| `graphIdealQuotientEquiv` | `MvPolynomial ι R ⧸ graphIdeal c ≃ₐ[R] R` | Proved (def) |
| `graphIdeal_isPrime [IsDomain R]` | `(graphIdeal c).IsPrime` | Proved |

- **Hypotheses:** `[CommRing R]`, `c : ι → R`, **arbitrary** `ι` (NO `Finite`/`Fintype`). `IsDomain R`
  only for `graphIdeal_isPrime`.
- **Faithfulness:** the multivariate analogue of `Polynomial.ker_evalRingHom`
  (`ker (eval x) = span {X − C x}`). Name = content: it is the kernel-equals-graph-ideal fact, not a
  generation claim.
- **Route (the new bit):** the `⊆` is the **translation identity** `p − C (aeval c p) ∈ graphIdeal c`
  by `MvPolynomial.induction_on` (`mul_X` step: `p·Xᵢ − C(v·cᵢ) = p·(Xᵢ − C cᵢ) + (p − C v)·C cᵢ`).
  This dodges the universe friction the predecessor hit with `Finite.induction_empty_option` +
  `optionEquivLeft`, and is strictly more general (no finiteness).
- **Axioms:** `[propext, Classical.choice, Quot.sound]`.

## Seam 2 — `height_graphIdeal_eq` (the `height J ≥ C` engine)

**Module:** `lean/DLNFibre/Core/GraphIdealHeight.lean` (commit `096291ba`). Imports
`MvPolynomialKerAeval` + `NullstellensatzCodim`.

| Name | Statement | Status |
|---|---|---|
| `ringKrullDim_quotient_graphIdeal_eq` | `ringKrullDim (MvPolynomial σ (MvPolynomial τ k) ⧸ graphIdeal c) = Nat.card τ` | Proved |
| `height_graphIdeal_eq` | `(graphIdeal c).height = Nat.card σ`, `c : σ → MvPolynomial τ k` | **Proved** |

- **Hypotheses:** `[Field k]`, `σ τ : Type u`, `[Finite σ] [Finite τ]`, `c : σ → MvPolynomial τ k`.
- **Meaning:** the block graph ideal eliminating the `σ`-block of `MvPolynomial σ (MvPolynomial τ k)`
  (`≅ MvPolynomial (σ ⊕ τ) k`) has height `= #σ`.
- **Route:** the field catenary `height_add_ringKrullDim_quotient_eq_card` (LANDED, `NullstellensatzCodim`)
  on `MvPolynomial (σ ⊕ τ) k` via `sumAlgEquiv`, with quotient dim `= #τ` (Seam 1's
  `graphIdealQuotientEquiv`) ⟹ `height = (#σ+#τ) − #τ = #σ`. Avoids the
  localization-preserves-dimension subtlety (Codex `heightJ` consult: routes A/B sprawl).
- **Non-vacuity / witness:** for the DLN base chart `(2,2,2), r=1`, `#B22block = (p−r)(q−r) = 1 = C`,
  `#SchurVar = r(p+q−r) = 3 = δ`, `#vars = pq = 4 = C+δ`. The lemma at `σ = B22block`, `τ = SchurVar`
  gives `height = 1 = C`. (Concrete witness probe to be added once the reindex lands.)
- **Axioms:** `[propext, Classical.choice, Quot.sound]`.

## Seam 2b — `height_coordIdeal_eq` (the coordinate-ideal-height target)

`Core/GraphIdealHeight.lean` (commit `6f7f2b35`). `height_coordIdeal_eq : (Ideal.span (Set.range
fun i ↦ X i) : Ideal (MvPolynomial σ (MvPolynomial τ k))).height = Nat.card σ` — the `σ`-block
coordinate ideal has height `#σ` (it is `graphIdeal (fun _ ↦ 0)`). The target the elimination's
translation automorphism transports the Schur graph ideal `J` to. Sorry-free, axiom-clean.

## Seam 3 — the reindex + detΔ-localization bridge (`DeterminantalBaseElimination.lean`)

Commits `36817e5f`, `8784c8af`, `cce4016e`, `c0cd6e2f`. All sorry-free, axiom-clean.

| Name | Statement | Status |
|---|---|---|
| `B22block` / `SchurVar` | the eliminated / free Schur coordinate types | def |
| `card_B22block` / `card_SchurVar` | `#B22block = (p−r)(q−r) = C` / `#SchurVar = r(p+q−r) = δ` | Proved |
| `finSplit` (+`_castLE`) | `Fin n ≃ Fin r ⊕ Fin (n−r)`; pivot ↦ `Sum.inl` | def / Proved |
| `repCoordReindex` (+`_pivot`) | `RepCoord (dStratum q p) ≃ B22block ⊕ SchurVar`; pivot coord ↦ Δ-block | def / Proved |
| `mult_stratum_eq` / `multPoly_stratum_apply` | `mult (dStratum q p) A = A 0`; `multPoly … a b = X ⟨0,(a,b)⟩` | Proved |
| `detSchurS` | `det` of the Δ-coordinate matrix in `MvPolynomial SchurVar k` | def |
| `renameEquiv_detPivot` | `detΔ ↦ rename Sum.inr detSchurS` (SchurVar-only) | Proved |
| `blockAlgEquiv` | `A_eng ≃ₐ[k] MvPolynomial B22block (MvPolynomial SchurVar k)` | def |
| `blockAlgEquiv_detPivot` | `detΔ ↦ C detSchurS` (detΔ lives in the SchurVar coefficients) | **Proved** |

## Handed off to thread 13 (`base-elimination-transport`) — NOT landed here
The final localization transport assembling the above into the public interface: localize
`blockAlgEquiv` at `detΔ`/`detSchurS` ⟹ `A_loc ≃ₐ MvPolynomial B22block Sd` (`Sd = Localization.Away
detSchurS`, via `MvPolynomial.isLocalization` + `IsLocalization.Away.awayMapₐ`); `height J = C` via
the translation auto + `height_coordIdeal_eq` + `IsLocalization.height_map_of_disjoint`; `Iad = J` by
`Ideal.height_strict_mono_of_is_prime` (landed `height Iad = C` + `height J = C`, the honest hard
direction `Iad ⊆ J`); expose `A_loc/Iad ≅ₐ[k] Sd` (J stays internal; {domain, dim δ} derive from the
equiv). Interface resolved by controller: expose the equiv. All three modules aggregated into
`DLNFibre.lean` (controller, lines 110–118). Seams 1+2 reviewer-audited FIDELITY PASS; Seam 3 +
Seam 2b awaiting fidelity read.
