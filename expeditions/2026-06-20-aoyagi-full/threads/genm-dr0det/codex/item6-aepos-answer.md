**Q1**

1. **(a)** Best. Use one raw `Hmat 0` entry, not full `UPoly/sqSum` machinery. Banked pieces already say `VvalGen = sqSumHmat0` and `VvalGen ≥ 0`; only an Efp-specific entry polynomial/eval bridge is new. See [RouteMAchieverVvalPoly.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a0213cdd57ec2cc21/lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverVvalPoly.lean:307) and [RouteMGenLeafIntegrand.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a0213cdd57ec2cc21/lean/DLNFibre/DLN/RLCT/Validate/RouteMGenLeafIntegrand.lean:30).
2. **(b)** Second. Sound, but do not claim a pure monomial globally: the product entry is likely `x_p * (W00 + other E*W terms)`. It is nonzero, but proving product readback through `chartParamsGen` is probably castier than using `Hmat`.
3. **(c)** Third. No direct banked “Efp unit is eval of nonzero poly” lemma. Reusable bricks exist: `GenBlkMap`, `chainOfMt_map`, `sqSumHmat0_map`, `VvalGen_eq_sqSumHmat0`, `ae_eval_ne_zero`; they are not already instantiated for `genBlkFlatEfp`.

**Q2**

Winner lemma chain:

1. Define `EfixedReaderGen` / `genBlkFlatEfpGen` over `MvPolynomial`, mirroring `EfixedReader` and `genBlkFlatEfp` where the E pivot is constant `1`. The real decoder is already pinned at [RouteMInteriorDeepRank0.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a0213cdd57ec2cc21/lean/DLNFibre/DLN/RLCT/Validate/RouteMInteriorDeepRank0.lean:64).
2. Prove `genBlkFlatEfpGen_genBlkMap_eval`: evaluation maps the polynomial Efp decoder to `genBlkFlatEfp x`.
3. Define `HentryEfpPoly` as the selected entry of the polynomial chain’s raw `Hmat 0`; prove `eval_HentryEfpPoly`.
4. Prove `HentryEfpPoly_ne_zero` by a sparse witness: E pivot fixed to `1`, `Wblk 1 (0,0)=1`, all other relevant coordinates `0`. Use banked `chain_A_liftRow`, `Hmat_pivot`, and `rmatPad_natAdd_natAdd`; see [RouteMAchieverWitnessInterior.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a0213cdd57ec2cc21/lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:60) and [RouteMAchieverWitnessInterior.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a0213cdd57ec2cc21/lean/DLNFibre/DLN/RLCT/Validate/RouteMAchieverWitnessInterior.lean:221).
5. `MvPolynomial.ae_eval_ne_zero` + `VvalGen_eq_sqSumHmat0` + a small `sqSumHmat0_pos_of_entry_ne_zero` + `VvalGen_nonneg`.

Hardest sublemma: `genBlkFlatEfpGen_genBlkMap_eval`, specifically the `Rmat` field with `Function.update 1`, `rmatPad_map`, and the pivot branch of `EfixedReader`.

**Q3**

Yes, the single-entry route is sound and likely cheapest.

Pick the raw `Hmat 0` entry with row `ρ` of value `Text M (tach M) 2 = 0`, transported as `rhoAt M (tach M) 1 0 ...`, and output column `0 : Fin (Wext M 2)`. This is the deepRank=0 analogue of the existing witness row. The W-coordinate is the first lift coordinate read by `readW ... ⟨0, by decide⟩ ...`, i.e. `Wblk (0+1) (0,0)`.

Important caveat: in the unit `V`, the selected quotient entry is not `x_p * W00`; the radial `x_p` has been stripped. The product entry has the `x_p` factor. The H-entry has a coefficient-`1` `W00` term and may have other `E*W` terms, so prove nonzero by sparse evaluation, not by asserting a global monomial formula.

**Q4**

The wall is dependent indexing, not the math: making the Efp polynomial decoder map through `eval` and aligning the `ρ`/`W00` indices through `rmatPad`, `chainA`, and `Function.update`.

Also check you have `0 < Wext M 2`; without a nonempty output column the target a.e.-positivity is false.

**VERDICT**

Use route **(a)**: one `Hmat 0` entry polynomial, sparse witness, zero-set nullity, then sum-of-squares positivity.

First lemma to prove: `genBlkFlatEfpGen_genBlkMap_eval`.