<task>
Independent fidelity audit of a Lean 4 / Mathlib formalisation against an informal mathematical certificate. I am the reviewer. Judge whether the Lean statements faithfully render the informal claims. Do NOT trust my framing; reason from the definitions.

SETTING (algebraic geometry of matrix-tuple multiplication):
- d : Fin (N+1) → ℕ a dimension vector. `mult d A` = product of the N matrix factors of a tuple A.
- `productRankLocusLE d r` = {A | rank(mult d A) ≤ r}. Call its (flattened) Zariski closure image Σ̄^r.
- `fibre d B` = {A | mult d A = B}, the preimage mult⁻¹(B). DISTINCT from Σ̄^r.
- `multPoly d a b` = generic (a,b)-entry of the product, a polynomial in coordinate ring R = MvPolynomial (RepCoord d) k.
- `fibreGenIdeal d E` = span { multPoly d a b − C(E a b) : a,b }  (the GENERATOR ideal, NOT its radical).
- `normalForm (d last)(d 0) r` = E = diag(I_r, 0), the rank-r normal form.
- `ΔPdeep d r` = det of the top-left r×r submatrix of (Matrix.of (multPoly d)). The "deep pivot minor detΔ".
- `sigmaIdeal d r` = vanishingIdeal(Σ̄^r) (the radical/reduced vanishing ideal of the closed locus).
- `cTheta d` := Nat.choose (qipM d) (qipDelta d).natAbs   i.e. C(m, |δ|).
- `dminus d r` := fun k ↦ d k − r  (ℕ truncated subtraction).
- `topComponents d r h` := { p ∈ (sigmaIdeal d r).minimalPrimes | p.height = (cCodim d r h).toNat }.
- `numTop d r h` := card of Kostant partitions of (d,r) attaining the min codimForm.

THE INFORMAL CERTIFICATE (thread 04) says, verbatim in spirit:
"detΔ ≡ 1 on the entire fibre SCHEME (not just no top component in V(detΔ)). detΔ is a UNIT in O(fibre)=R/J where J = fibreGenIdeal. The fibre ideal J = (mult(A)_ij − E_ij) forces mult(A)=E=diag(I_r,0) in R/J, so its top-left r×r block = I_r, hence detΔ=det(I_r)=1, i.e. detΔ−1 ∈ J. No radicality / IsAlgClosed / CharZero needed. r=0 gives det(0×0)=1."

THE LEAN THEOREMS (all build green, axiom-clean [propext, Classical.choice, Quot.sound]):
(1) ΔPdeep_sub_one_mem_fibreGenIdeal : ΔPdeep d r hp hq − 1 ∈ fibreGenIdeal d (normalForm (d last)(d 0) r hp hq).  [any field, any d, r ≤ d last, r ≤ d 0]
(2) isUnit_mk_ΔPdeep_fibreGenIdeal : IsUnit (Quotient.mk (fibreGenIdeal d E) (ΔPdeep d r)).
(3) fibreLocalizationAwayDetΔ_algEquiv : Q ≃ₐ[Q] Localization.Away (mk (ΔPdeep d r)), Q = R ⧸ fibreGenIdeal d E. (via IsLocalization.atUnits.)
(4) numTop_eq_cTheta_dminus : (Monotone d) → (∀k, r ≤ d k) → nonempties → numTop d r hr' = cTheta (dminus d r). Assembled from numTop_rankShift (numTop (d−r) 0 = numTop d r), numTop_zero_eq_cTheta (numTop e 0 = cTheta e, for Monotone e), monotone_dminus.
(5) ncard_topComponents_eq_cTheta_dminus : [IsAlgClosed][CharZero] → (Monotone d) → (∀k,r≤d k) → nonempties → (topComponents d r hr').ncard = cTheta (dminus d r). Stacks numTop_eq_ncard_topComponents (numTop d r = #topComponents of Σ̄^r) onto (4).

KEY FIDELITY QUESTIONS:
A. Does theorem (1) faithfully render the certificate's "detΔ ≡ 1 on the rank-r fibre"? Specifically: is membership in fibreGenIdeal (the generator ideal, not its radical) the RIGHT object to match "≡ 1 on the fibre scheme / unit in O(fibre)=R/J"? Or is there a mismatch (e.g. should it be the radical / vanishing ideal to mean "on the fibre")?
B. Is the cTheta = C(m,|δ|) identification correct, and are the hypotheses (Monotone d, ∀k r≤d k) the genuinely-needed ones (not over/under-stated)?
C. Theorem (5) counts top components of Σ̄^r (= productRankLocusLE, the closed rank-≤r LOCUS), NOT the fibre mult⁻¹(E). The card explicitly defers the fibre count as "the remaining wall". Is naming it `ncard_topComponents_eq_cTheta_dminus` (no "fibre" in the name) honest, given topComponents is defined via sigmaIdeal = vanishingIdeal(Σ̄^r)? Flag any overclaim where a Σ̄^r result could be read as a fibre result.
D. Any naming concern (name ≠ content) on any of the five.
</task>

<output_contract>
Per question A–D: a one-word verdict (FAITHFUL / OVERCLAIM / MISNAMED / MIS-SCOPED / UNDERCLAIM) + 2-4 sentences of precise reasoning. Then an overall PASS / REVISE. Be terse and adversarial; a specific structural objection beats vague worry.
</output_contract>

<grounding_rules>
Reason from the definitions given. Mark clearly any claim that is INFERENCE (from the structure I described) vs a FACT you can derive rigorously. If a question is under-determined by the info given, say what extra fact you'd need to check rather than guessing. Do not invent Mathlib lemma behaviour you are unsure of.
</grounding_rules>
