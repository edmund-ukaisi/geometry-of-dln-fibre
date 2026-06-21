<task>
Lean 4 + Mathlib (pinned to v4.29.0). I am proving a general commutative-algebra lemma and want
you to red-team the proof ASSEMBLY (not write Lean code — diagnose the skeleton, name pitfalls,
confirm/deny each step is supported by the API below).

GOAL THEOREM (network-free CA):
  For [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing S] [Module.Flat R S],
  a prime Q : Ideal S with [Algebra.QuasiFiniteAt R Q],
  prove  Q.height = (Q.under R).height.

VERIFIED Mathlib API at this pin (exact signatures I read in source):

1. instance Algebra.HasGoingDown.of_flat [Module.Flat R S] : Algebra.HasGoingDown R S
   (so flatness gives HasGoingDown by inference).

2. lemma Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown [IsNoetherianRing S]
     [Algebra.HasGoingDown R S] (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
     P.height = p.height + (P.map (Ideal.Quotient.mk (p.map (algebraMap R S)))).height
   The "fibre" second summand is the height of the image of P in S ⧸ pS, where pS := p.map (algebraMap R S).

3. abbrev Algebra.QuasiFiniteAt (R) (p : Ideal S) [p.IsPrime] : Prop := QuasiFinite R (Localization.AtPrime p)

4. lemma Algebra.QuasiFiniteAt.eq_of_le_of_under_eq {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
     (h1 : P ≤ Q) (h2 : P.under R = Q.under R) [Algebra.QuasiFiniteAt R Q] : P = Q
   (Only needs QuasiFiniteAt R Q. P.under R := P.comap (algebraMap R S).)

5. lemma Ideal.primeHeight_eq_zero_iff {I : Ideal R} [I.IsPrime] :
     primeHeight I = 0 ↔ I ∈ minimalPrimes R
   where minimalPrimes R := (⊥ : Ideal R).minimalPrimes ; Minimal/IsMin under ⊆.

6. lemma Ideal.height_eq_primeHeight [I.IsPrime] : I.height = I.primeHeight

7. theorem Ideal.comap_minimalPrimes_eq_of_surjective {f : R →+* S} (hf : Surjective f) (I : Ideal S) :
     (I.comap f).minimalPrimes = Ideal.comap f '' I.minimalPrimes
   and Ideal.map_comap_of_surjective, Ideal.comap_map_of_surjective, RingHom.ker (Quotient.mk I) = I (Ideal.mk_ker).

MY PROPOSED SKELETON (set p := Q.under R, so Q.LiesOver p holds by Ideal.LiesOver via under):
  Step A. By (2)+(1): Q.height = p.height + J.height, where J := Q.map (Quotient.mk pS), pS := p.map (algebraMap R S).
  Step B. Reduce to J.height = 0.
  Step C. J is prime in S⧸pS, and pS ≤ Q (because Q.LiesOver p ⟹ pS = (Q.under R).map algebraMap ≤ Q via map_comap_le).
          So J.comap (mk pS) = Q (map_comap_of_surjective uses pS = ker ≤ Q).
  Step D. J.height = J.primeHeight (J prime) = 0 ⟺ J ∈ minimalPrimes(S⧸pS) by (5).
  Step E. Prove J minimal: take prime K ≤ J in S⧸pS. Let K' := K.comap (mk pS). Then pS ≤ K' ≤ Q.
          - K' ≤ Q : comap monotone of K ≤ J, and J.comap = Q.
          - K'.under R = p : from pS ≤ K' get p ≤ K'.under R (comap of pS, le_comap_map);
            from K' ≤ Q get K'.under R ≤ Q.under R = p. So K'.under R = p = Q.under R.
          - By (4) QuasiFiniteAt.eq_of_le_of_under_eq K' Q (K'≤Q) (K'.under R = Q.under R) [needs QuasiFiniteAt R Q]: K' = Q.
          - Then K = K'.map (mk pS) (map_comap_of_surjective, pS ≤ K') = Q.map (mk pS) = J. So K = J. Minimal. ∎
</task>

<output_contract>
  1. VERDICT: does this skeleton assemble from the listed API? (yes / yes-with-fixes / no).
  2. Step-by-step audit: for EACH of A–E, state SUPPORTED / NEEDS-CARE / BROKEN with the precise reason
     (instance availability, a missing monotonicity/`under`/`comap` lemma, a `FiniteHeight` requirement, an
     `ℕ∞` arithmetic subtlety in `p.height + 0 = p.height`, the direction of `minimalPrimes` `Minimal` unfolding).
  3. The SINGLE most likely failing goal and the lemma that closes it.
  4. Is there a SHORTER assembly (e.g. a direct `Q ∈ (pS).minimalPrimes` route, or avoiding the quotient by
     working in S directly) that is more robust? If so sketch it; if not say the quotient route is the right one.
  5. Confirm: does `primeHeight_eq_zero_iff` need `[FiniteHeight]`? (I believe NOT — it's the bottom case.)
     And does the `+ 0` cancellation in `ℕ∞`/`ℕ∞ → WithBot` need anything beyond `add_zero`?
</output_contract>

<grounding_rules>
  Only the 7 API facts above are confirmed-present. If a step needs a lemma NOT in that list, flag it as an
  ASSUMED dependency I must verify by `rg` before building — do not assume it exists. Distinguish
  "supported by listed API" (fact) from "Mathlib probably has this" (inference). Keep it tight.
</grounding_rules>
