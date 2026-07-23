<task>
Red-team the induction of a "descent lemma" about matrix products. Find any config where it FAILS, or any
gap/missing case in the proof structure. Do not rubber-stamp; try to break it.
</task>

<setup>
Fixed widths d_0,…,d_N (all ≥1). Layer-m matrix A_m has shape d_{m+1} × d_m. The prefix product is
P_L := A_L · A_{L-1} · … · A_0  (shape d_{L+1} × d_0).
Running min: wmu(n) := min(d_0, …, d_n)  (non-increasing in n).
"Cleared columns" of layer m: { c : 0 ≤ c < wmu(m+1) }.
couplingCoords(0..L) := { entry A_m[r,c] : m ≤ L, c < wmu(m+1), r > c }  (below-diagonal entries of cleared
columns). These are the variables a "clearing" operation sets to 0.
</setup>

<lemma>
DESCENT LEMMA: for every L and every "remnant row" index r with r ≥ wmu(L+1) (and r < d_{L+1}), every entry
P_L[r,k] (all k) lies in the ideal ⟨couplingCoords(0..L)⟩ — equivalently, P_L[r,k] vanishes identically when
all couplingCoords(0..L) are set to 0.
</lemma>

<proposed_proof>
Downward induction on L, peeling P_L = A_L · P_{L-1}:
  P_L[r,k] = Σ_j A_L[r,j] · P_{L-1}[j,k],   j ranges over 0..d_L−1.
Split each term by j:
  (i)  j < wmu(L+1):  since r ≥ wmu(L+1) > j, A_L[r,j] is a below-diagonal entry of a cleared column, i.e.
       A_L[r,j] ∈ couplingCoords(L). So the term is in the ideal.
  (ii) j ≥ wmu(L+1):  claim j ≥ wmu(L), so P_{L-1}[j,k] ∈ ⟨couplings(0..L-1)⟩ by the induction hypothesis
       (row j of P_{L-1} is a remnant row at level L-1). The claim uses: whenever this case is non-empty
       (d_L > wmu(L+1)), we are in the regime wmu(L+1) = wmu(L).
Base / termination: the recursion descends only through case (ii) (uncleared columns). It terminates at the
BOTTLENECK layer B := argmin(d_0..d_{L+1}), where d_B = wmu(L+1); there ALL columns are cleared
(col < wmu(B+1) = d_B), so case (ii) is empty and every term is case (i). The recursion never goes below B.
</proposed_proof>

<questions>
1. Is step (ii)'s claim "j ≥ wmu(L+1) (and this case non-empty) ⟹ j ≥ wmu(L)" correct? Specifically: can
   there be an index j with wmu(L+1) ≤ j < wmu(L) that the recursion feeds into the IH, where the IH's
   remnant-row hypothesis (j ≥ wmu(L)) is not met — a genuine gap? Or does "case (ii) non-empty ⟹
   wmu(L+1)=wmu(L)" hold, closing it?
2. Is the termination sound — does the recursion always reach a bottleneck layer with all columns cleared
   before hitting a layer-0 uncleared output column (which would have no deeper layer to recurse into)?
   Consider d_0 > wmu(1) (layer 0 has uncleared output columns).
3. Any r with r ≥ wmu(L+1) but the lemma vacuous (no such r)? Does vacuity ever hide a real case?
4. Give a concrete (d, L, r, k) counterexample if the lemma is false, or confirm the proof closes.
</questions>

<grounding_rules>
Reason from the definitions only. wmu is non-increasing. A_m has shape d_{m+1} × d_m so a valid row index of
A_m is < d_{m+1} and a valid col index is < d_m. Treat the matrices as generic (independent entries).
</grounding_rules>
