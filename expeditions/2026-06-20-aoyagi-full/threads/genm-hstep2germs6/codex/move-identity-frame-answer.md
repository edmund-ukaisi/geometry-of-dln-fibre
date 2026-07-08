1. **YES: obstruction real under the stated generic triangular-frame assumptions.**

`hmove` fixes the framed moved layer:
`C'_s = movedC(C)_s`. Since `dev ↦ corM + Pf_s dev Qf_s` is affine-bijective, the pre-frame reads are then uniquely forced:
`dev'_s = Pf_s⁻¹ (C'_s - corM) Qf_s⁻¹`.

So there is no remaining freedom to also choose the clean frame-free `movedC(decode)` reads.

Concrete scalar block check: take an interior layer with
`P = [[1,0],[p,1]]`, `Q = [[1,q],[0,1]]`, and framed moved layer
`C'_s = [[1+x,0],[0,t]]`. This is a case where `movedC` is identity on that layer. Then hmove forces
`decode(psi)_s = corM + P⁻¹(C'_s-corM)Q⁻¹`, whose Schur core is

`Sch(decode(psi)_s) = t + p q x/(1+x)`,

while the framed moved Schur core is `Sch(C'_s)=t`. Thus the hsub4 frame-free product generically differs from the framed `movedC` product/Score. If only `P₂₁ ≠ 0`, use an upper-triangular test layer with `Y ≠ 0`; if only `Q₁₂ ≠ 0`, use a lower-triangular test layer with `Z ≠ 0`.

Exception branch: if the frames satisfy the stronger condition `P corM Q = corM`, equivalently block-diagonal with `P₁₁Q₁₁=1`, and core blocks telescope, then Schur-equivariance can rescue the construction. But that is stronger than the triangular hypotheses you stated.

2. **Yes: the fix is to move hsub3reg to the frame-free decode chain.**

If `deepestChain(decode(psi q)) = movedC(deepestChain(decode q))`, then the same abstract `regBlocks_movedC` preserves the unframed product’s `{11,12,21}` blocks.

Endpoint frames do not create the same obstruction for regular energy. For endpoint block-lower `P0` and block-upper `QL`,

`(P0 M QL)₁₁`, `(P0 M QL)₁₂`, and `(P0 M QL)₂₁`

depend only on `M₁₁,M₁₂,M₂₁`, not on `M₂₂`. So preserved frame-free regular blocks remain preserved after endpoint framing. This is computed from block multiplication.

For the core/Score side, endpoint Schur factors are fixed endpoint bookkeeping. If the existing `Schur(prod decode) → Score` tie is already banked, it should still apply. If not, that is a separate fixed-endpoint transport lemma, not the per-layer interior-frame obstruction.

3. **NEEDS-REARCHITECT.**

Closing `hstep2` as currently banked, by building one `psiSplitRawGen` plus the framed-chain `hmove` consumed by `deepestEFull_sq_sum_eq_of_chain_movedC`, is not reachable under generic non-diagonal triangular interior frames.

You need either a re-banked hsub3reg lemma stated on the frame-free decode chain, or a much stronger frame-normality theorem making the interior affine frames Schur-equivariant. Under the assumptions as written: **NEEDS-REARCHITECT**.