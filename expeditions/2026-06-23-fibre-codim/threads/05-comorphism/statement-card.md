# Statement card — MultComorphism: the coordinate-ring map of `mult` and the fibre ideal (L4.6, F1)

Module `lean/DLNFibre/Core/MultComorphism.lean` (new file, imports `Core.Setup`, `Core.OrbitCodim`,
`Core.NullstellensatzCodim`, `Mathlib.RingTheory.Nullstellensatz`). Import to be appended to
`DLNFibre.lean` (single-writer; controller wires it). Sorry-free, axiom-clean (`propext,
Classical.choice, Quot.sound`). Commit `15bdcb63` (Lean module); card-SHA pinned at the next commit.

**Scope (name = content).** The coordinate-ring map for the multiplication map `mult` and the
identification of the fibre `mult⁻¹(B)` as a zero-locus / coordinate-ring quotient. The construction
exploits that `mult` is defined over **any** `CommRing` (`Core.Setup.mult`): the product-entry
polynomials are `mult` applied to the **generic** tuple over `MvPolynomial (RepCoord d) k`, so no new
recursion is introduced — `multPoly`/`eval_multPoly` ride the existing `multPrefix`/`mult` and their
`rfl` step lemmas. The first two deliverables (`multPoly`, `eval_multPoly`) live over `[CommRing k]`;
the fibre-ideal and comorphism deliverables specialise to `[Field k]` / `[IsAlgClosed k]`.

**Notation.** `RepCoord d = Σ i, Fin (d i.succ) × Fin (d i.castSucc)` (one coordinate per matrix
entry, `Core.OrbitCodim`); `canonicalCoord d : Tuple d ≃ (RepCoord d → k)` the entry-flattening
(`canonicalCoord_apply : canonicalCoord d A ⟨i,a,b⟩ = A i a b`); `eval`/`aeval`/`zeroLocus`/
`vanishingIdeal` Mathlib's `MvPolynomial` Nullstellensatz objects (`K := k`). `B : Matrix (Fin
d_N) (Fin d_0) k` the target matrix; `fibre d B = {A | mult d A = B}` (`Core.Setup`).

---

> **Claim 1 (generic product entries).** `multPoly d r c` is the `(r,c)` entry of `mult` applied to
> the generic tuple `genericTuple` (each entry its own variable `X ⟨i,a,b⟩`), a polynomial in
> `MvPolynomial (RepCoord d) k`.
>
> - **Lean:** `multPoly (d : Fin (N+1) → ℕ) : Fin (d (Fin.last N)) → Fin (d 0) → MvPolynomial
>   (RepCoord d) k := fun r c ↦ (mult d (genericTuple d)) r c`; `genericTuple d i a b = X ⟨i,a,b⟩`
>   (`genericTuple_apply`).
> - **Gloss.** Reuses the existing `mult`/`multPrefix` over the polynomial ring; no re-derived
>   recursion. `[CommRing k]`.
> - **Proved.** Definitional. **Assumed / Cited / Deferred.** none.

> **Claim 2 (the bridge — load-bearing).** Evaluating the generic product entry `multPoly d r c` at
> the coordinates of any tuple `A` reproduces the actual product entry `(mult d A) r c`.
>
> - **Lean:** `eval_multPoly (d) (A : Tuple d) (r) (c) : eval (canonicalCoord d A) (multPoly d r c) =
>   (mult d A) r c`. `[CommRing k]`.
> - **Gloss / proof.** `eval (canonicalCoord d A) : MvPolynomial (RepCoord d) k →+* k` is a ring hom,
>   so it commutes with the matrix product. The spine `map_eval_multPrefix` proves entrywise that the
>   `eval`-image of the generic prefix product equals the actual prefix product, by `Fin.induction` on
>   `multPrefix`: base `multPrefix_zero` + `Matrix.map_one`; step `multPrefix_succ` + `Matrix.map_mul`
>   + `map_eval_genericTuple` (the single-variable case `eval (canonicalCoord d A) (X ⟨i,a,b⟩) = A i a
>   b`, by `canonicalCoord_apply`). `eval_multPoly` reads this at `j = Fin.last N`.
> - **Proved.** Full equality for every tuple. **Assumed / Cited / Deferred.** none (Mathlib's
>   `Matrix.map_mul`, `Matrix.map_one`, `eval_X` used at their genuine signatures).

> **Claim 3 (fibre as zero-locus).** The image of the fibre under the canonical flattening is exactly
> the common zero-locus of `{multPoly d r c − C (B r c)}`.
>
> - **Lean:** `image_fibre_eq_zeroLocus [Field k] (d) (B) : canonicalCoord d '' (fibre d B) =
>   zeroLocus k (Ideal.span (fibreGenSet d B))`, where `fibreGenSet d B = Set.range (fun rc ↦ multPoly
>   d rc.1 rc.2 − C (B rc.1 rc.2))`. Helper `mem_zeroLocus_fibreGenSet` characterises membership as
>   `∀ r c, eval x (multPoly d r c) = B r c`.
> - **Gloss / proof.** Membership chase: `x ∈ zeroLocus (span …) ↔ ∀ rc, aeval x (multPoly − C(B)) = 0`
>   (`zeroLocus_span`), `aeval = eval` (`aeval_eq_eval`), `… = 0 ↔ eval x (multPoly) = B` (`sub_eq_zero`);
>   then `eval_multPoly` + `Matrix.ext` close both directions (`A ∈ fibre ↔ mult d A = B` entrywise).
> - **Proved.** Full set equality. **Assumed.** `[Field k]` (`zeroLocus`/`vanishingIdeal` are
>   field-indexed in Mathlib). **Cited / Deferred.** none.

> **Claim 4 (fibre vanishing ideal = radical of generator ideal).** Over an algebraically closed
> field, the vanishing ideal of the fibre's image is the radical of `fibreGenIdeal d B`.
>
> - **Lean:** `vanishingIdeal_image_fibre_eq_radical [IsAlgClosed k] (d) (B) : vanishingIdeal k
>   (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical`, where `fibreGenIdeal d B =
>   Ideal.span (fibreGenSet d B)`.
> - **Gloss / proof.** Rewrite the image as a zero-locus (Claim 3) and apply the strong Nullstellensatz
>   `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` (the engine's `Core.NullstellensatzCodim` uses
>   the same Mathlib lemma).
> - **Proved.** Full equality. **Assumed.** `[IsAlgClosed k]` — needed only here (the strong
>   Nullstellensatz); `[Field k]` carried from the section. **Cited.** Mathlib's
>   `vanishingIdeal_zeroLocus_eq_radical` (strong Nullstellensatz), used not reproved. **Deferred.** none.

> **Claim 5 (the comorphism + `Ideal.map` identification).** The fibre generator ideal is the
> extension of `B`'s maximal ideal along the comorphism of `mult` — the "fibre coordinate ring =
> `R_total ⧸ m_B · R_total`" object the height-squeeze (F2) consumes.
>
> - **Lean:** `multComap (d) : MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k →ₐ[k] MvPolynomial
>   (RepCoord d) k := aeval (fun rc ↦ multPoly d rc.1 rc.2)` (`multComap_X : multComap d (X rc) =
>   multPoly d rc.1 rc.2`); `maxIdealOfPoint d B = Ideal.span (Set.range (fun rc ↦ X rc − C (B rc.1
>   rc.2)))`; `fibreGenIdeal_eq_map_maxIdealOfPoint (d) (B) : fibreGenIdeal d B = Ideal.map (multComap
>   d).toRingHom (maxIdealOfPoint d B)`.
> - **Gloss / proof.** `Ideal.map_span` reduces the goal to "`multComap` carries the generating set of
>   `maxIdealOfPoint` to the generating set of `fibreGenIdeal`"; a `Set`-image chase using `multComap (X
>   rc − C (B rc.1 rc.2)) = multPoly d rc.1 rc.2 − C (B rc.1 rc.2)`.
> - **Proved.** Full ideal equality. **Assumed.** `[Field k]`. **Cited / Deferred.** none. (The stretch
>   `MvPolynomial (RepCoord d) k ⧸ vanishingIdeal(fibre) ≃ₐ coordinate ring of the fibre` was NOT
>   pursued — Claims 4 + 5 already pin the object; not in F1 scope.)

> **Non-vacuity witness.** At the `(2,2,2)` witness (`Setup.dWitness`, `Setup.tupleWitness` over `ℤ`),
> `eval (canonicalCoord dWitness tupleWitness) (multPoly dWitness r c) = (!![1,2;3,7]) r c` for every
> `(r,c)` — `eval_multPoly` reproduces the actual product (in-file trailing `example`, via the
> committed `Setup` product computation `mult dWitness tupleWitness = !![1,2;3,7]`).

---

## Audit

- `lean/scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- `scripts/lb` green (3697 jobs whole library); `scripts/lb DLNFibre.Core.MultComorphism` green, no
  errors and no line-length / unused-arg warnings in the new code.
- `#print axioms` on `eval_multPoly`, `image_fibre_eq_zeroLocus`, `vanishingIdeal_image_fibre_eq_radical`,
  `fibreGenIdeal_eq_map_maxIdealOfPoint`: `[propext, Classical.choice, Quot.sound]` only.
- Fidelity review (Lean ↔ informal claim): PENDING (reviewer).
- **Status: sorry-free.**

## Judgement calls

- **`eval_multPoly` stated with `eval`, fibre lemmas with `aeval`/`zeroLocus`.** The thread spec wrote
  the bridge with `eval`; Mathlib's `zeroLocus`/`vanishingIdeal` are defined with `aeval`. Bridged once
  in `mem_zeroLocus_fibreGenSet` via `aeval_eq_eval` (`= rfl` at `k = K`). `eval_multPoly` kept in `eval`
  form (cleaner ring-hom-over-matrices statement).
- **`multPoly`/`eval_multPoly` over `[CommRing k]`, not `[Field k]`.** They need no field; stating them
  at the weakest class that carries `mult` (matching `Setup`) keeps the witness over `ℤ` and lets the
  field/alg-closed hypotheses enter only where the Nullstellensatz needs them (Claims 4–5).
- **`[IsAlgClosed k]` is exactly the hypothesis Claim 4 needs (no more).** Claim 3 (zero-locus) is over
  any field; only the radical identity (Claim 4) consumes the strong Nullstellensatz. Claim 5
  (`Ideal.map`) is field-only, no alg-closure.
- **`fibreGenIdeal` named for content** — it is the *generator* ideal `span {multPoly − C(B)}`, the
  fibre's vanishing ideal only up to radical (Claim 4 names that as `.radical`), not asserted equal.
