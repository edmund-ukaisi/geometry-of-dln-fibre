1. **No.** The bare `RingEquiv` between the two quotient rings is enough. No properness/no-drop argument is needed; that is only for localization/open-subset dimension arguments.

2. **Yes.** `Ideal.quotientEquiv` is the right lemma. In Mathlib v4.29 its hypothesis is `J = I.map (e : R →+* S)`. For `I = J_E.comap e`, discharge with:
   `Ideal.map_comap_eq_self_of_equiv e J_E`
   or, equivalently, `Ideal.map_comap_of_surjective (e : R →+* R) e.surjective J_E`.
   `Ideal.map_comap_of_equiv` exists, but it is not the clean direct lemma for this goal.

3. **Actual gaps to watch:** ensure all statements use the same `d : Fin (N+1) → ℕ` convention; many chart lemmas are `Fin (N+2)`. Also carry the endpoint-distinct/N≥1 hypothesis if deriving (e) from rank-normal-form base change. No universe issue apparent.