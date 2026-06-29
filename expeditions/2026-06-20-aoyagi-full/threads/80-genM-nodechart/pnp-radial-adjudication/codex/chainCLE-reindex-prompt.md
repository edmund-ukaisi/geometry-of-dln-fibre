<task>
Pin the coordinate-equivalence (CLE) for a "chaining" factor in a composeFold-based Jacobian determinant
proof (Lean/Mathlib), over OPAQUE width tuples. Derive the structure yourself from the chain recursion;
do not assume the framing below is right.
</task>

<setup>
A structured "achiever chart" phi : R^N -> R^N for a width tuple M=(M_0,...,M_L) is built from per-boundary
data. Define widths Text_k (a descent: Text_0=M_0, Text_1=M_0, then decreasing) and Wext_k = M_k.
The chart's layer-s output matrix (s=0..L-1), shape Fin(Wext_s) x Fin(Wext_{s+1}), is
  A_s = chainA(N_s, W_s, C_{s+1}) = [ C_{s+1} - N_s·W_s ;  W_s ]    (kept rows over lift rows),
where the "kept" block is the first Text_{s+1} rows and "lift" is the last c_s = Wext_s - Text_{s+1} rows.
Here:
  - C_{s+1} (shape Text_{s+1} x Wext_{s+1}) is the "transition block" BUILT from boundary (s+1)'s frame data
    (its Schur frame), NOT a fresh input coordinate; it is produced by the deeper factors in the composition.
  - W_s (shape c_s x Wext_{s+1}) is a chart input coordinate (the "lift" slot).
  - N_s (shape Text_{s+1} x c_s) is a fixed matrix parameter at this factor.
The flat coordinate space R^N packs the L layer matrices: layer s occupies a contiguous block
Fin(Wext_s * Wext_{s+1}) at offset sum_{j<s} Wext_j*Wext_{j+1}.

In a "composeFold" determinant proof, phi = B ∘ blowup, and B = composeFold of per-boundary factors
[schur_s, chain_s, ldu_s]. Each factor is conjugated to a self-map of R^N via a CLE
  E : (R^N) ≃L (block-space × R),  factor = E.symm ∘ (factorMap × id_R) ∘ E.
The chain factor is chainUnitCLM N_s : (W, C) ↦ (W, C - N_s·W) on (W-block × C-block); it needs
  E_chain_s : (R^N) ≃L ( (W_s-block) × (C_{s+1}-block) ) × R.
We have the BANKED finSplit row laws: chainA_apply_castAdd (kept row i -> (C - N W) i j) and
chainA_apply_natAdd (lift row a -> W a j), i.e. row index of Fin(Wext_s) splits via
finSplit (Text_{s+1} + c_s = Wext_s) into kept (castAdd) and lift (natAdd).
</setup>

<questions>
1. Where does the C_{s+1} block live as FLAT coordinates? Is it (i) the KEPT-ROW block of layer s (the first
   Text_{s+1} rows of layer s's flat block), or (ii) a coordinate slot belonging to boundary s+1 (a "next
   boundary" slot requiring a cross-boundary index shift)? Reason from "A_s = [C_{s+1} - N_s W_s ; W_s]"
   (so C_{s+1} - N_s W_s occupies layer s's kept rows) vs "C_{s+1} is built from boundary s+1's data".
   Give the EXACT Fin index map for the C-block of E_chain_s.

2. Is the chain factor's CLE E_chain_s therefore derived from the FLAT (output/layer) coordinatization
   (layer-s block + finSplit row-split via chainA_apply_castAdd/natAdd) rather than from the per-boundary
   INPUT (chart-role) coordinatization that schur_s/ldu_s use? If so, the chain factor lives on a DIFFERENT
   coordinate side than schur/ldu — does that break the single-composeFold-on-one-ambient picture, or is it
   fine because every factor is just SOME self-map of R^N (composeFold only needs each factor to be a self-map,
   not to share one coordinatization)? Flag any soundness risk.

3. The s=L-1 (deepest/leaf) case: C_L = u·Rfin (the live leaf), shape Text_L x Wext_L. When Text_L > 0 the
   leaf is live; when Text_L = 0 (the last drop is 0) the leaf is EMPTY (0 rows) and the layer is all-lift.
   Does the s=L-1 chain factor need a SEPARATE reindex branch, or does "C_{s+1} = layer-s kept rows" fold
   UNIFORMLY over all s including L-1 (the leaf being just the instance where C_L's content is u·Rfin / empty)?
   Reason about whether Text_L=0 (empty kept block) is a degenerate-but-uniform case or a separate branch.
</questions>

<output_contract>
Q1: verdict (kept-row-of-layer-s vs next-boundary-slot) + the exact Fin index map. Q2: verdict on whether
the chain CLE is flat-side-derived and whether mixing coordinatizations across factors is sound. Q3: uniform
fold vs separate leaf branch, with the Text_L=0 degeneracy handled. Mark proof vs heuristic.
</output_contract>

<grounding_rules>
Reason from the chainA = [C - N W ; W] structure and the flat layer packing. Don't rubber-stamp; if the
chain factor genuinely sits on the output side (creating an eIn != eOut situation), say so and assess whether
composeFold still works (each factor a self-map of R^N).
</grounding_rules>
