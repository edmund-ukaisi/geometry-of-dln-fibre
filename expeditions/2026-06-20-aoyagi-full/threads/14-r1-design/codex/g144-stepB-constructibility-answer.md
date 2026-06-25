1. **Yes, as stated for the actual construction.** Fact: in `(2,2,2)`, `lemma2Fwd` sends the residual to
`E² + F0² + (qE + δG)² + (qF0 + δH)²`, which is still coupled. The clean form `E²+F0²+δ²(G²+H²)` would require clearing `qE,qF0` through division by `δ` on the bad chart. So the next blow-up, not `lemma2Fwd`, is doing the decoupling work. Caveat: this proves failure of the proposed regular Schur clearing, not a universal no-exotic-diffeomorphism theorem.

2. **Yes.** The ΣM drop is combinatorial: after a hard pivot, `S = D - ba` is a legitimate reduced factor coordinate by the triangular change `D ↔ S+ba`, with determinant `1`. No `S⁻¹` is used. Rank-deficiency of `S` at the origin is exactly the new deepest singular node, not an obstruction.

3. **I find no stall in the coupled case, provided the dispatcher treats empty-Schur/width-one nodes as terminal/Fubini-product nodes rather than forcing another Schur step.** Exact mechanism: use coordinates `(E,S,...)`; on an `E`-pivot chart the residual has a unit square and terminates. On an `S`-pivot chart, `E=sE'`, `S=sS'`, hence
`Q = s²(‖E'‖² + ‖bE' + S'Γ‖²)`,
the same coupled form on the reduced chain. Thus `ΣM` drops by pivot row+col removal. Tests: `(2,3,2)→(1,2,2)` then smooth; `(3,2,3)→(2,1,3)` then width-one/Fubini; `(3,3,3)→(2,2,3)→(1,1,3)` then terminal. Multi-drop cases serialize into mixed C1/C2 steps; all-equal widths keep supplying pivots until width-one/smooth.

4. **Verdict: sound on this sub-obligation.** No clean exact c-o-v is needed; the monomial blow-up plus coupled recursion terminates. The remaining obligation is dispatcher exhaustiveness/formalization, not an algebraic stall.