**Verdict:** hnode has the right shape for the hard-pivot 2-factor Schur node. It is faithful as a **local squeeze contract** for the residual `‖Â·A2‖²`, with the monomial blow-up factor kept out. It is not, by itself, a certificate that the data came from the actual blow-up chart.

1. **Form (1): faithful.**  
Fact: with `Â = [[1,a],[b,D]]`, `A2 = [[β],[Γ]]`, and `E = β + aΓ`,
```text
Â A2 = [ E
         bE + (D - b a)Γ ].
```
So the Frobenius square is exactly
```text
∑j E_j^2 + ∑i,j (b_i E_j + (SΓ)_ij)^2.
```
There is no cross term between the top row and lower rows because these are different matrix entries in the Frobenius norm. The only regular-core coupling is inside `(b_i E_j + SΓ_ij)^2`. This matches the green `schur_row_decomp` contract in [g132-squeeze-exists-statement-prompt.md](/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g132-squeeze-exists-statement-prompt.md:8).

Adversarial caveat: do not replace this by the stronger literal clean form `∑E² + ∑(SΓ)²` for the original Frobenius norm. The Schur row operation is not orthogonal; the coupled lower block is the correct norm-level residue.

2. **Reduced core (2): faithful, with one scope condition.**  
Fact for the 2-factor node: the reduced core is `‖S·Γ‖²`, where `S = D - b a`. This is the smaller Schur-reduced matrix-chain factor times the reduced second factor. The local witness says exactly that the hard-pivot block gives `S = D - b·a` and residual `S·Bred` as the smaller zero-core [g127-per-node-adapted-basis-WITNESS.md](/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g127-per-node-adapted-basis-WITNESS.md:31).

Inference: for the full L-layer chain, hnode must be paired with the separate `redEmbed`/reduced-chain contract saying this `Γ` is the correct reduced next factor or tail. hnode’s equation `(2)` is enough for the squeeze, but the geometric statement “this is the next recursion node” lives in that reduced-chain discharge.

3. **Bounded `b` is the right condition.**  
Fact: `p_ij = b_i E_j` satisfies
```text
∑i,j p_ij^2 = (∑i b_i^2)(∑j E_j^2) ≤ T^2 ∑j E_j^2.
```
That is exactly what the abstract Young-inequality squeeze needs, giving constants of the stated type [g132-squeeze-exists-statement-prompt.md](/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/codex/g132-squeeze-exists-statement-prompt.md:12).

No hidden `b → 0` requirement is needed for uniform two-sided comparability. Local boundedness is sufficient; `b → 0` only improves constants. If `b` were unbounded on every neighborhood, this proof would fail.

4. **Omissions / hidden breakages.**  
Fact: the `x²` monomial from `A1 = xÂ` is correctly excluded here. The repo’s lane split also records that blow-up contributes the monomial Jacobian/weight, while Schur straightening contributes no monomial weight [GeneralR1Recursion.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean:55), [g126-per-node-bridge-certificate.md](/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/14-r1-design/g126-per-node-bridge-certificate.md:26).

Fact: `w.1 = E` may depend on lower/tail variables before the coordinate split, but the hard pivot makes `β ↦ E = β + aΓ` triangular with identity coefficient. That is the right way to make `E` the regular coordinate.

Fact: unit coefficients are correct for standard Frobenius loss and hard pivot `Â[0,0]=1`. If a later formulation inserts weighted norms or a non-orthogonal transformed generator norm, hnode would be too strict.

Fact: the form guarantees the same zero set as `Φ = ∑E² + ‖SΓ‖²`:
```text
flatCore = 0 ⇔ E = 0 and bE + SΓ = 0 ⇔ E = 0 and SΓ = 0 ⇔ Φ = 0.
```
The lower squeeze prevents faster vanishing.

5. **Too weak?**  
Yes as a recognizer; no as a contract.

Inference: arbitrary bounded `bcol` and arbitrary `SΓ` satisfying `(1)-(3)` need not come from a real Schur chart. So hnode should not be sold as “the blow-up produced this” unless there is a separate lemma proving hnode from actual block data.

But as a theorem contract, it is appropriately tight: the squeeze conclusion uses exactly the displayed algebra, `G² = ‖SΓ‖²`, and bounded `b`. The downstream discharge should prove:
```text
bcol = b,
SΓ = (D - b a)Γ,
w.1 = β + aΓ,
flatCore = ‖Â A2‖²,
G² = dlnLoss(reduced),
local boundedness of b.
```
If those are the obligations, the downstream proof is chasing the right shape.