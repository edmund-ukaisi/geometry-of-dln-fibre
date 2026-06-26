1. **Q1 verdict:** Yes. By FACT 1+2, `deepestEFull` is threshold-effective, while `hconj` is pivot-aligned; FACT 3 proves the mismatch survives a nontrivial trailing `QL`.

2. **Q2 ranked routes:**

**Best: R1. Sound, local, but definition-level cost.**  
Make `deepestEFull` pivot-aware by undoing `colPerm_J` before the final pivot reindex, or equivalently read the framed last layer in pivot coordinates. Then it targets the same object as `hconj`:
`reindex(rThr,pivotThr J)(M_noQL·QL)`.  
This should make `Sfull = Sconj`, assuming the rewritten framed-product identity is proved with the trailing `QL` in the right place. Cost: update the PIN1/reg-straightening interface and all lemmas expecting the old threshold-effective `deepestEFull`.

**Second: R2. Sound in principle, higher global cost.**  
Pre-permute output columns so the pivot set becomes `{0..r-1}`. Rank is preserved by a fixed column permutation, and squared Frobenius loss is invariant under a fixed orthogonal column permutation if consistently applied/absorbed into `QL`. Must check: all appearances of `B`, `prod`, endpoint frames, and theorem statements are relabelled coherently. Cost: global convention shift; likely many normalization and indexing lemmas change.

**Third: R4. Sound as diagnosis, expensive.**  
Accept the current bridge is false and re-architect the controller around distinct threshold and pivot residuals, or make the final Phi consume pivot-aligned coordinates directly. This is robust but broader than necessary if R1 is available.

**Rejected: R3. Unsound.**  
Changing conjunct (b) to threshold residual and then asserting threshold `Sreg =` pivot `Sreg` is false in general. A column permutation preserves total Frobenius energy of the whole matrix, not the selected expression `sum(P00-1)^2 + sum(P01)^2 + sum(P10)^2`.

3. **Q3 decisive:** No. `Sreg` is not invariant under changing the column split from `pivotThr J` to `rThr`. The permutation can move columns across the left/right block boundary, so entries migrate between `P00`, `P01`, and omitted `P11`; moreover the `-1` subtraction is attached to the diagonal of the `r x r` corner, so moving which columns occupy that corner changes which entries are compared to `1`.

4. **Fact status:** Q1 uses FACT 1–3 directly. R1–R2 soundness are inferences requiring the named checks; R3 rejection follows from the block-split/corner algebra and is confirmed by the stated witness.