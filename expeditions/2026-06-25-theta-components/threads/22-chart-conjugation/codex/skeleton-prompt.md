<task>
I am formalising in Lean 4 + Mathlib v4.29 the "locally trivial bundle" content of
Lehalleur–Rimányi Lemma 4.6 for the multiplication-map fibre of a directed-line-network (DLN).

SETUP (all already formalised, sorry-free):
- A dimension vector d : Fin (N+1) → ℕ. A "tuple" A assigns to each edge i a matrix
  A i : Mat (Fin (d i.succ)) (Fin (d i.castSucc)). `mult d A` is the ordered matrix product
  (last factor on the left), a matrix Mat (Fin (d last)) (Fin (d 0)).
- Coordinate ring of the tuple space: MvPolynomial (RepCoord d) k, where
  RepCoord d = Σ i : Fin (N+1), Fin (d i.succ) × Fin (d i.castSucc).
- `multPoly d r c : MvPolynomial (RepCoord d) k` = the generic product entry (r,c).
- The base-change group G_d = ∏_v GL_{d_v} acts on tuples by
  (P • A)_i = P_{i.succ} · A_i · (P_{i.castSucc})⁻¹.
- `baseChangePullback P : MvPolynomial (RepCoord d) k →ₐ[k] MvPolynomial (RepCoord d) k`
  is the coordinate-ring incarnation of A ↦ P • A (an aeval substitution); it is an AlgEquiv
  `baseChangeAlgEquiv P` with inverse `baseChangePullback P⁻¹`. Key fact:
  `eval x (baseChangePullback P f) = eval (canonicalCoord d (P • canonicalCoord.symm x)) f`.

THE TOP-LEFT CHART (the "e_β" tower, built ONLY at the top-left r×r pivot, ~hundreds of LoC):
- `ΔPdeep d r hp hq` = determinant of the TOP-LEFT r×r submatrix of `Matrix.of (multPoly d)`
  (selectors `Fin.castLE` — first r rows, first r cols).
- `sweepSigma k d r` = the rank-≤r product locus; `vanishingIdeal (sweepSigma)` its ideal;
  `sweepSigmaRing = MvPolynomial(RepCoord d)/vanishingIdeal(sweepSigma)`.
- `chartDsig = mk (vanishingIdeal sweepSigma) (ΔPdeep)` — the localizing element.
- `chartGfib`, `SchurVar (d 0)(d last) r`, `detSchurS`, `sweepFibreRing` — the Schur-side ring
  built around the FIXED top-left block decomposition: pivot index `Fin r`, complement rows
  `Fin (d last) ∖ first r`, complement cols `Fin (d 0) ∖ first r`.
- `chartLocalizedAlgEquiv` (= e_β) : `Localization.Away chartDsig ≃ₐ[k] Localization.Away chartGfib`,
  needs `[Infinite k]`. This is the single top-left trivialization.

THE GOAL (task: per-pivot conjugation skeleton):
The per-minor open cover of Mat^{=r} is by charts `minorChart s t` = {(s,t) minor invertible},
for injective row selectors s : Fin r → Fin (d last) and col selectors t : Fin r → Fin (d 0).
The top-left chart is (s,t) = (castLE, castLE). To earn `locallyTrivial` I need a trivialization
e_{s,t} at EVERY pivot, plus the (already-built, ambient) transition cocycle transported onto them.

The proposed route: an END-FACTOR permutation. Take P : G_d with P_{last} = (permutation matrix
σ taking the s-rows to the first r positions), P_0 = (permutation matrix τ for the t-cols),
P_i = 1 for 0 < i < last. Then `mult (P • A) = σ · (mult A) · τ⁻¹`, so the (s,t) minor of mult A
becomes the top-left minor of mult(P•A). The claim is that `baseChangeAlgEquiv P` (the coordinate
change) CONJUGATES the entire top-left chart construction to its (s,t) analogue, so
e_{s,t} := (transport of e_β along baseChangeAlgEquiv P). Then per-pivot LocalTrivializationDatum
+ the ambient cocycle ⟹ earned locallyTrivial.

WHAT I NEED ADJUDICATED. Be concrete and skeptical. This direction has been a tower (5 rungs);
the prior tide flagged the skeleton as "plausible-but-not-automatic".
</task>

<output_contract>
Answer in these sections, terse:

1. DOES THE CONJUGATION ACTUALLY TRANSPORT THE WHOLE CHAIN? For each of
   {vanishingIdeal(sweepSigma), ΔPdeep, chartDsig, chartGfib / SchurVar / detSchurS / sweepFibreRing,
   chartLocalizedAlgEquiv}, state whether baseChangeAlgEquiv P carries the top-left object to a
   genuinely-equal (s,t) object, to an isomorphic-but-not-equal one, or NOT at all — and WHY.
   Flag the specific place(s) the naive "transport e_β" fails (I expect: the Schur-side ring is tied
   to the *top-left block index types* Fin r / complements, which the permutation does NOT literally
   fix — it permutes WITHIN Fin(d last) and Fin(d 0), so the top-left r×r block of mult(P•A) is the
   (s,t) minor, but the schur-side ring of the d-system is unchanged. Is that an obstruction or is it
   exactly what makes it work?).

2. THE CLEANEST CORRECT FORMULATION. What is the RIGHT statement to prove? Options:
   (a) e_{s,t} := baseChangeAlgEquiv P precomposed/postcomposed so that
       `Away (ΔPdeep at (s,t)) ≃ₐ Away chartGfib` — i.e. define the (s,t) localizing element as the
       (s,t) deep minor, show baseChangeAlgEquiv P sends chartDsig(top-left) to it (or vice versa),
       and define e_{s,t} = e_β ∘ (that localization iso). Does this need the full Schur-side
       conjugation, or only that the (s,t) deep minor pulls back to the top-left one under the
       coordinate change (a determinant identity, which is cheap)?
   (b) Something else.
   Give the EXACT chain of AlgEquivs and which ones are cheap (localization initiality / determinant
   identity) vs expensive (genuine Schur-generator conjugation).

3. CAN I AVOID RE-DERIVING THE SCHUR SIDE? The fibre ring `sweepFibreRing` and Schur generators are
   defined for the d-system at the top-left, NOT per-pivot. If e_{s,t} is built by composing e_β with
   the localization iso `Away(deep-(s,t)-minor) ≃ₐ Away(chartDsig top-left)` induced by
   baseChangeAlgEquiv P, then e_{s,t} lands in `Away chartGfib` — the SAME fibre+schur ring as e_β.
   Is that a feature (all pivots trivialize to the same product, transitions are automatic) or a bug
   (the bundle's fibre should be intrinsic, and using the same chartGfib for all pivots is fine since
   the fibre IS the same up to the cocycle)? Does this actually deliver a coherent atlas?

4. THE HONEST MINIMAL DELIVERABLE if the full skeleton exceeds one tide. Rank, cheapest first:
   - (i) the determinant/ideal conjugation lemmas (baseChangeAlgEquiv P sends top-left ΔPdeep to
     deep-(s,t)-minor; sends vanishingIdeal(sweepSigma) to itself — since sweepSigma is G_d-stable);
   - (ii) one non-top-left pivot worked end to end as a LocalTrivializationDatum;
   - (iii) the full per-pivot family + cocycle transport ⟹ locallyTrivial.
   For each, state the dependency and rough LoC. Which is the right stopping point for ONE module?

5. IS THERE A HIDDEN FURTHER RUNG? Name the single most likely place this tower reveals ANOTHER rung
   (e.g. the cocycle "transport onto the trivializations" being more than the ambient cocycle).
</output_contract>

<grounding_rules>
Distinguish what you can PROVE from the setup vs what you INFER about the Lean encoding (you cannot
see the files). Flag any step where you are guessing the Lean definition's exact shape. If the
conjugation route is fundamentally sound but the Schur-side equality is only "iso not eq", say so
plainly and tell me whether that iso is cheap (localization universal property) or expensive.
</grounding_rules>
