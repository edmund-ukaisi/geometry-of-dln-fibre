<task>
Lean 4 + Mathlib v4.29 formalisation. I am computing `height J = C` for a localized
determinantal base ideal, and need the LOWEST-FRICTION route (fewest brittle steps,
maximal reuse of LANDED engine lemmas). This is a checkpoint: I want to commit to a
route before grinding, and to know which sub-lemma is the genuine wall.

SETTING (all LANDED, sorry-free, in the engine `DLNFibre.Core`):
- k : Field, [IsAlgClosed k] [CharZero k]. p q r : ℕ, r ≤ p, r ≤ q.
- A_eng := MvPolynomial (RepCoord (dStratum q p)) k, where RepCoord (dStratum q p) is a
  Fintype with `Nat.card = p*q` (one var per entry of a single p×q matrix). Call pq := p*q.
- detΔ : A_eng — the top-left r×r minor of the generic matrix (`detPivotPoly`).
- A_loc := Localization.Away detΔ. Iad := (sigmaIdeal (dStratum q p) r).map (algebraMap A_eng A_loc).
- sigmaIdeal (dStratum q p) r is PRIME (= vanishing ideal of the rank-≤r determinantal
  variety, [IsAlgClosed k]); detΔ ∉ sigmaIdeal (witness diag(I_r,0)).
- LANDED: `height Iad = C` where C = (p−r)(q−r), via `IsLocalization.height_map_of_disjoint`.
- LANDED catenary on the UN-localized polynomial ring (key reusable bridges):
    * `height_add_ringKrullDim_quotient_eq_card [Finite σ] (p : Ideal (MvPolynomial σ k)) [p.IsPrime]
       : (p.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ p) = (Nat.card σ : WithBot ℕ∞)`
    * `affine_domain_height_add_ringKrullDim_quotient_eq` (height + dim quotient = dim domain, for
       prime in a quotient of MvPolynomial (Fin n) k).
    * `varietyDim_productRankLocusLE_stratum : varietyDim (...) = r*(p+q−r) = δ` (so δ = dim of the
       determinantal base; C + δ = pq).
- Deliverable 1 (just LANDED by me): `ker_aeval_eq_graphIdeal (c : ι → R) [CommRing R] :
   RingHom.ker (aeval c).toRingHom = graphIdeal c` for ARBITRARY ι (no Finite). Consequences:
   `graphIdealQuotientEquiv : MvPolynomial ι R ⧸ graphIdeal c ≃ₐ[R] R`, `graphIdeal_isPrime [IsDomain R]`.

THE GOAL: `height J = C` (as ℕ∞), where J is the localized Schur graph ideal:
  - reindex A_eng ≃ₐ[k] MvPolynomial B22block (MvPolynomial SchurVar k), B22block = Fin(p−r)×Fin(q−r)
    (so #B22block = C), SchurVar = (Fin r×Fin r)⊕(Fin r×Fin(q−r))⊕(Fin(p−r)×Fin r) (#SchurVar = δ).
  - localize at detΔ: A_loc ≃ₐ[k] MvPolynomial B22block Sd, Sd := Localization.Away detΔS,
    detΔS ∈ MvPolynomial SchurVar k.
  - J corresponds to graphIdeal forcedB22, forcedB22 : B22block → Sd the forced Schur value
    (= algebraMap (B21·adjΔ·B12 entry) * invSelf detΔS).
  - Then MvPolynomial B22block Sd ⧸ graphIdeal forcedB22 ≃ₐ Sd (Deliverable 1).

The crux I am unsure about: getting `height J = C` rigorously. Two candidate routes:

ROUTE A (comap to A_eng + catenary on A_eng):
  height J = height (J.comap (algebraMap A_eng A_loc))  [IsLocalization.height_comap, any ideal]
  = pq − dim(A_eng / J₀)  [catenary on A_eng, J₀ := J.comap, needs J₀ prime]
  then need dim(A_eng/J₀) = δ. But A_loc/J ≅ Sd and A_loc/J ≅ (A_eng/J₀) localized at image of detΔ.
  Does dim(A_eng/J₀) = δ follow from dim Sd = δ? This needs "localizing an affine DOMAIN at one
  nonzero element preserves Krull dimension" (D(f) dense in an irreducible variety). Is that in
  Mathlib v4.29? If not, how heavy to build?

ROUTE B (catenary directly in MvPolynomial B22block Sd):
  height (graphIdeal forcedB22) = dim(MvPolynomial B22block Sd) − dim(quotient = Sd) = (#B22block + dim Sd) − dim Sd = #B22block = C.
  Needs: a catenary identity for the polynomial ring MvPolynomial B22block Sd over the BASE RING Sd
  (not over a field), and dim(MvPolynomial B22block Sd) = #B22block + dim Sd. Is there a clean
  Mathlib v4.29 lemma `ringKrullDim (MvPolynomial (Fin n) R) = n + ringKrullDim R` for Noetherian R?
  And a catenary/equidimensional identity over a general Noetherian base?

ROUTE C (something I'm missing — e.g. compute dim Sd directly and reduce height J to height of a
  coordinate ideal via translation/automorphism so it's literally `height (span of #B22block vars)`).
  Note: graphIdeal forcedB22 is the IMAGE of the coordinate ideal span{X_b : b ∈ B22block} under the
  translation automorphism X_b ↦ X_b + C(forcedB22 b) of MvPolynomial B22block Sd. height is invariant
  under ring automorphism. height(span of the n coordinate variables) in MvPolynomial (Fin n) R — is
  there a clean lemma that this = n (for R a domain / Noetherian)? That would dodge BOTH the catenary
  and the localization-dimension subtlety entirely. Is `MvPolynomial.X` coordinate-ideal height
  available, or `Polynomial.span_X`-type results, in v4.29?
</task>

<output_contract>
1. VERDICT: which route (A / B / C / other) is lowest-friction in Lean v4.29, in 2–3 sentences.
2. For the chosen route: the ordered list of Mathlib v4.29 lemma names (exact, grep-confirmable) +
   any LANDED engine lemma above it reuses. Flag any lemma you are NOT confident exists at v4.29.
3. THE WALL: the single sub-lemma most likely missing/hard, and its cheapest workaround.
4. If Route C (coordinate-ideal-height) is viable: the exact lemma for `height (span {X i | i}) = n`
   (or `= Nat.card` of the var type) over a domain/Noetherian base, or a 4–6 line proof sketch if it
   must be built (e.g. via the graphIdeal_isPrime quotient iso + a catenary, or via an explicit prime chain).
Keep it tight. Lemma names over prose.
</output_contract>

<grounding_rules>
Flag every lemma name as (confident-exists-v4.29) or (unsure — verify). Distinguish "this lemma
exists" from "this lemma applies here". If you don't know whether a Mathlib lemma exists at v4.29,
say so rather than inventing a plausible name. Mathlib v4.29 is the hard constraint.
</grounding_rules>
