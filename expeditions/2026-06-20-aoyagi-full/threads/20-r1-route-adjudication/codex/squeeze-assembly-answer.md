**Q-A**  
[INFERENCE] Verdict: No; at corank ≥ 2, hnode cannot honestly satisfy both the rank-1 Schur form and `redCore_eq`.

[FACT] The stated Schur identity has cross term `bcol ⊗ Erow`, hence rank at most 1.  
[FACT] In the `(3,3,4)`, `t=1` peel, the residual coupling is `Δ · S` with `Δ` free `2×2` and generically rank 2.  
[FACT] The width-chain reduced core is `redChain(1,3,3,4) = (1,4)`, a smooth `1×4` loss.  
[FACT] The actual residual germ is the product core `‖ΔS‖²`, not `‖Y‖²` for a free `1×4` matrix.  
[INFERENCE] Thus the shared RLCT value `2` is only a value coincidence, not a measure-preserving germ identification.

**Q-B**  
[INFERENCE] Verdict: The additive split can be sound only if the coupled `Δ` block lives inside `G²`; treating it as smooth is wrong.

[FACT] The peel gives `F ∼ ‖T‖² + ‖ΔS‖²`, with `T` a clean `1×4` block.  
[FACT] The smooth block contributes `4/2 = 2`.  
[FACT] The product block `‖ΔS‖²` has RLCT value `2`, far below the smooth `12/2 = 6`.  
[INFERENCE] Therefore the sound arithmetic is `2 + rlct(‖ΔS‖²) = 4`.  
[INFERENCE] Replacing `‖ΔS‖²` by the smooth width-chain leaf `‖Y‖²` preserves the number in `(3,3,4)` but not the germ.

**Q-C**  
[FACT] Verdict: Squeeze proves equality of RLCTs under comparability; it does not compute singular RLCTs.

[FACT] `c₁Φ ≤ F ≤ c₂Φ` at the same point gives `rlct(F)=rlct(Φ)`.  
[FACT] It does not determine `rlct(Φ)` or `rlct(G²)`.  
[FACT] The split `rlct(‖E‖² + G²) = nReg/2 + rlct(G²)` already uses analytic integration, e.g. Fubini/polar estimates.  
[FACT] Any passage from resolved monomial data `(dᵢ,kᵢ,hᵢ)` to `monomialThreshold(dᵢ,kᵢ,hᵢ)` imports the normal-crossing monomial RLCT theorem.  
[INFERENCE] Thus Route B must import monomial-to-RLCT extraction at singular reduced cores or resolved leaves; squeeze alone cannot derive the RHS infimum.

**Q-D**  
[INFERENCE] Verdict: hnode is sound only on the narrow scope “corank ≤ 1 at every binding peel”; at corank ≥ 2 binding branches it is unsatisfiable as stated.

[INFERENCE] Scope predicate: for every recursive node on every `minAdm`-attaining rank profile, the chosen peel rank `t` satisfies `min(M₀−t, M₁−t) ≤ 1`.  
[FACT] Under that predicate, the residual first-layer coupling has rank capacity at most 1, so `bcol ⊗ Erow` can represent it.  
[FACT] If `M₀−t ≥ 2` and `M₁−t ≥ 2`, the residual block contains a genuine free `≥2×2` matrix `Δ`.  
[FACT] Then the actual coupling is generically rank ≥ 2, as in `(3,3,4)` with `ΔS`.  
[INFERENCE] Enforcing `redCore_eq` there either drops the `Δ` coupling or replaces it by a non-isomorphic width-chain germ; numerical equality is not enough.

Single most load-bearing thing that would make hnode sound general-L: a genuine measure-preserving germ isomorphism identifying every corank ≥ 2 residual product core `‖ΔS‖²` with the claimed width-chain reduced loss, not merely matching its RLCT value.