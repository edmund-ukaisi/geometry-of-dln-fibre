1. **RECOMMENDATION:** Pick **(i)** for the public ambient API; use a proof-only chain view only as a derived helper.

2. **DECIDING ARGUMENT:** the downstream objects are indexed by the same fixed dimension vector and by intervals `0 ≤ i ≤ j ≤ N`. In (i), `Σ^r : Set (Tuple d)`, fibres, `d k`, and `submult A i j : Matrix (Fin (d j)) (Fin (d i)) k` all live over the same first-class `d`. That is exactly the paper’s shape. The Fin transport pain is local proof friction; hiding `d` or reversing it makes the mathematical API fight you everywhere.

3. Your inference is **morally correct but logically too strong**. Fixed-d Sets are possible in (ii): define something like
   ```lean
   ChainOf d := Chain k (d 0) [d_N, d_{N-1}, ..., d_1]
   SigmaRank r : Set (ChainOf d) := { C | C.mult.rank = r }
   ```
   So fixed-d does not force a product space. But (ii) makes paper indices into reversed-list offsets, which will pollute rank patterns and Kostant formulas. For (iii), a fixed-d Set needs a subtype/predicate such as `{ R : Rep k (d N) (d 0) // HasDims d R }`; that recovers the hidden data by proof, not by type, and is the wrong bedrock.

4. **Top risks and mitigations:**

   **Risk 1:** every theorem about `mult` reopens `Fin.succ`/`castSucc` transport.
   **Mitigation:** do not let downstream proofs unfold `mult`. Prove a small API immediately: `prefix_zero`, `prefix_succ`, `mult_eq_prefix_last`, `submult_self`, `submult_step`, and `submult_comp` for `i ≤ j ≤ l`. Mark only boundary/step lemmas as `[simp]`.

   **Risk 2:** full-product recursion is awkward for interval products.
   **Mitigation:** define `submult` first, then define `mult A := submult A 0 N`. Prove rank lemmas on `submult` by interval-length induction. I’d expect Nat recursion on interval length to be easier than a generic `Fin.fold`, because the matrix type changes with the endpoint.

5. **HYBRID:** yes. Public layer: product-space (i). Proof layer: derived bridge
   ```lean
   asChain A i j
   asChain_mult : (asChain A i j).mult = submult A i j
   ```
   Use the chain view to get definitional multiplication proofs, but keep all paper-facing Sets and formulas over `Tuple d`.