1. VERDICT: BOUNDED-WITH-NAMED-RISK. [Inference] This looks mathematically bounded, but only if the general cov-bearing interior chart is fixed to the live-LDU decoder.

2. THE INTERIOR MONOMIAL-DET COV — [Inference] BOUNDED, and not my #1 mathematical risk. LDU gives `det K = product of diagonal pivots` on the chosen big-cell parametrization; zero pivots are coordinate hyperplanes/null sets, not a non-null degeneracy. [Repo-contingent guess] The risk is not the determinant identity itself, but threading that parametrization through the exact Lean chart/cov interface for opaque sizes.

3. THE MAP-EQUALITY (phiStructured = composeFold over opaque variable-length widths) — [Inference] This is the #1 risk, but it sounds like bounded dependent-cast engineering, not a genuine obstruction, provided both sides were designed from the same decoder semantics. [Repo-contingent guess] Cheapest discriminating test: instantiate the variable-length fold on the already-proven `(3,3,3,3)` interior anchor and prove definitional/propositional equality to the existing hand chart before generalizing.

4. THE TWO PRIOR RISKS (exhaustiveness deepRank≤deepRows ∀M; smeared rational-cov interface) —  
[Inference] `deepRank ≤ deepRows ∀M`: BOUNDED, likely combinatorial/witness-packaging unless a concrete counterexample appears.  
[Inference] smeared rational-cov interface: BOUNDED, but interface-heavy; poles on Gram-minor zero sets are standard null-set exclusions, not new math.

5. THE TRAP: [Inference] The bounded verdict is wrong if the RATE identity, the live-LDU monomial determinant, and the `cov` field are silently being proved for three extensionally different `phi`s.

6. If BOUNDED-WITH-NAMED-RISK: [Inference] Operator scope decision: canonicalize the general interior branch around one live-LDU decoder as the only cov-bearing chart, and reject/freezing any free-K or dead-leaf contracts that cannot satisfy monomial `cov`.