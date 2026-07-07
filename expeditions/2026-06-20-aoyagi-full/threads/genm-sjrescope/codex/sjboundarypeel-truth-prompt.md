<task>
Red-team a Lean measure-theory inequality for TRUTH (provable vs false vs vacuous). This is a fidelity review of a `sorry`'d theorem — I need to know if the STATEMENT is true (so the sorry is honest) or false (so the sorry launders a false claim).

All integrals are lintegrals over ℝ≥0∞. Definitions:
- frobSq(P) = Σ entries² of matrix P (≥ 0).
- rmatMul A B = matrix product; prod(chain)(A') = product of the layer matrices of a width-chain.
- paramsBoxM(chain) 1 = the [−1,1]-cube of the parameter tuple for that chain (compact, finite volume).
- matBox m n 1 = the [−1,1]-cube of m×n real matrices.
- pivotChart ρ κ = { A : Matrix (Fin m)(Fin n) ℝ | the t×t minor selected by embeddings ρ:Fin t↪Fin m, κ:Fin t↪Fin n is invertible }. On it, rank A ≥ t.
- Banked: pivotLocus_eq_iUnion t : {A | t ≤ A.rank} = ⋃_{ρ,κ} pivotChart ρ κ.
- routeMLayerBoxIntegral M c' 1 = ∫_{A ∈ paramsBoxM M 1} ofReal(frobSq(prod M A)^(−c')).
- CLOSED front-split lemma (given, proven): routeMLayerBoxIntegral M c' 1 = ∫_{A'∈paramsBoxM(tailChain M)1} ∫_{A0∈matBox (M0)(M1) 1} ofReal(frobSq(rmatMul A0 (prod(tailChain M) A'))^(−c')).
- gammaPeelIntegral M t ρ κ c' = ∫_{A'∈paramsBoxM(tailChain M)1} ∫_{A0∈ matBox(M0)(M1)1 ∩ pivotChart ρ κ} ofReal(frobSq(rmatMul A0 (prod(tailChain M) A'))^(−c')).
- minAdm M ∈ ℕ. For a chain with M0=0 or M1=0 (min(M0,M1)=0), minAdm M = 0 (given, proven).
- c' : NNReal, so c' ≥ 0.

QUESTION. Is this TRUE / provable for a general-L width vector M : Fin (L+3)→ℕ?

theorem sjBoundaryPeel (M) (c' : NNReal) (hc' : (c':ℝ) < (minAdm M : ℝ)/2) :
  routeMLayerBoxIntegral M c' 1
    ≤ ∑_{t ∈ Finset.Icc 1 (min (M0)(M1))} ∑_{ρ:Fin t↪Fin M0} ∑_{κ:Fin t↪Fin M1} gammaPeelIntegral M t ρ κ c'.

The sum starts at t=1 (EXCLUDES t=0). Address specifically:
(a) min(M0,M1)=0 edge: RHS sum is empty (Icc 1 0 = ∅) so RHS=0. Is LHS forced 0, or is hc' vacuous (contradiction) so the theorem holds trivially?
(b) Dropping the rank-0 point {A0=0} from matBox: is {0} null in the matrix Lebesgue volume? What does that require (M0·M1 ≥ 1)? Does the front-split integrand at A0=0 matter?
(c) Does the cover {matBox ∩ pivotChart ρ κ}_{(ρ,κ), t=1} really cover matBox∖{0}? Does subadditivity + nonneg t≥2 slack give box ≤ ∑?
(d) The integrand can be 0^(−c') where frobSq=0. Does the rpow-of-zero convention affect the ≤ direction, given LHS and RHS use the IDENTICAL integrand?
Is there ANY way the inequality is FALSE (not just hard to prove)?
</task>

<output_contract>
1. VERDICT: one of {TRUE-provable, FALSE, VACUOUSLY-TRUE-only}. One line.
2. Load-bearing reason (≤5 sentences).
3. Per (a)-(d): one-line adjudication each.
4. Any failure mode that makes it FALSE, or "none found".
Be terse. Flag inference vs certainty.
</output_contract>

<grounding_rules>
State explicitly when a claim is a mathematical certainty vs an inference about the likely Lean formalisation. Do not assume lemmas exist beyond those listed as banked.
</grounding_rules>
