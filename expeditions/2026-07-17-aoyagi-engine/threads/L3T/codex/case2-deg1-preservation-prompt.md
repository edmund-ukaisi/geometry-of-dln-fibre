<task>
Adjudicate whether a Lean leaf's Deg1-support conjunct is DERIVABLE from its hypotheses. Re-derive; don't trust me.

SAME setting as before (ℝ^D, polynomial world). Definitions:
- IgnoresCoords c S V := ∀ w∈V, ∀ m∈S, ∀ t, c (update w m t) = c w.
- Deg1SupportedOn resid S V := ∀ j, ∃ c : Fin D → (ℝ^D→ℝ),
    (∀i, ContinuousOn (c i) V) ∧ (∀u∈V, resid j u = ∑_{i∈S} c i u * u i) ∧ (∀i, IgnoresCoords (c i) S V).
  NOTE: Deg1SupportedOn ⟹ resid j 0 = 0 for all j (sum of c i(0)*0).

FOLD DATA at child `p.extend ed` (interior, so NOT terminal). center = ed.center, pivot ∈ center.
edgeShear = a polynomial bijection sh with sh 0 = 0 and (sh u) pivot = u pivot.
blockBlowupMap center pivot w: j=pivot ↦ w pivot; j∈center\{pivot} ↦ w pivot * w j; j∉center ↦ w j.
σ := blockBlowupMap center pivot ∘ sh.
quotMap u := fun k ↦ blockBlowupCoordQuot pivot k (sh u), where blockBlowupCoordQuot pivot k w = (if k=pivot then 1 else w k).
Note quotMap 0 = e_pivot (the basis vector: 1 at pivot, 0 elsewhere), since sh 0 = 0.

The child residual (FIXED def), δ ∈ {0,1} = edgeδ (a Bool off the state):
  foldResid_child j u = (if δ=1) foldResid_p j (quotMap u)         -- "strict transform"
                        (if δ=0) foldResid_p j (σ u)               -- pure pullback
Provable crux (seat-L4): foldResid_p j (σ u) = (u pivot) * foldResid_p j (quotMap u)   -- so δ=0 child = u_pivot * (δ=1 child).

HYPOTHESIS (this is ALL you have about the residual):
  (H) Deg1SupportedOn foldResid_p center ℝ^D.    -- pivot ∈ center; c may depend on the pivot's coefficient freely

GOAL: ∃ C' (a center), Deg1SupportedOn foldResid_child C' ℝ^D.

MY WORRY:
  Compute foldResid_child j 0.
   δ=1: foldResid_p j (quotMap 0) = foldResid_p j (e_pivot). By (H), = ∑_{i∈center} c_{j,i}(e_pivot)*(e_pivot)_i
        = c_{j,pivot}(e_pivot) (only i=pivot survives). Since c_{j,pivot} ignores center and e_pivot agrees with 0
        off center, c_{j,pivot}(e_pivot) = c_{j,pivot}(0). So foldResid_child j 0 = c_{j,pivot}(0).
   If the parent residual has a genuine pivot term with c_{j,pivot}(0) ≠ 0 (e.g. foldResid_p j = u_pivot, a valid
   Deg1 residual on center with c_{j,pivot}≡1), then foldResid_child j 0 ≠ 0, so foldResid_child is NOT Deg1SupportedOn
   ANY C' (Deg1 forces value 0 at origin). Hence the goal FAILS for such a parent → the leaf is false-as-stated.
   δ=0: child = u_pivot * (δ=1 child); if δ=1 child is degree-1, δ=0 child is degree-2 (also not Deg1 unless the
   degree-1 factor's coefficient avoids the center).

COUNTER-CONSIDERATION (does the DLN structure rescue it?): for a REAL parent from the construction, foldResid_p is
built from coreGen (product of N≥2 matrix layers), whose Deg1 coefficients c_{j,pivot}(u) are themselves products of
DEEPER-layer coordinates, which VANISH at 0 — so c_{j,pivot}(0)=0 there and the child DOES vanish at 0. But the leaf
quantifies over FREE (p, ed, hinv); nothing in (H) forces c_{j,pivot}(0)=0.
</task>

<output_contract>
1. VERDICT: is "∃ C', Deg1SupportedOn foldResid_child C'" derivable from (H) alone? {DERIVABLE, NOT-DERIVABLE/FALSE, DEPENDS}.
2. If NOT-DERIVABLE: give the cleanest explicit parent (foldResid_p, center, pivot) making it fail, for δ=1 and δ=0.
3. What is the MINIMAL extra hypothesis on foldResid_p that makes it derivable? (Candidates: "foldResid_p j 0 = 0 and a stronger 'no-pivot-in-support' / single-center-coord form"; or "Deg1 on center\{pivot} + pivot-coefficient vanishes"). State the cleanest one and the child center C' it yields.
4. Does the extra hypothesis need to also handle the shear (sh) so that (sh u)_i for i∈center\{pivot} is expressible in raw coords u_k? i.e., is Deg1 preservation possible at all with a NON-trivial shear, or does it require sh to be center-preserving?
Keep under ~450 words. Flag INFER vs KNOW.
</output_contract>

<grounding_rules>
Reason only from the given definitions. Name any unstated fact you rely on.
</grounding_rules>
