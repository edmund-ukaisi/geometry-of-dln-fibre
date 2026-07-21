**Q1.** Yes—derived under the stated global-bijection and all-chart hypotheses.  
Start with a closed cube \(K\) containing a ball. Recursively apply each shear inverse, choose a max-modulus pivot, and use zero ratios when the whole block vanishes.  
Finite depth and polynomial boundedness give pathwise coordinate bounds \(B_{p,j}\). Set
\(\mathrm{dom}_p=\{z:\lvert z_j\rvert\le B_{p,j}\ \forall j\}\).  
Every \(x\in K\) then has some leaf lift \(z\in\mathrm{dom}_p\) with \(g_p(z)=x\); no properness theorem is needed.

**Q2.** The resulting cover is full: the escaping set is \(\varnothing\).  
Pivot ties escape nowhere: choose either maximizer, and closed boxes include ratio values \(\pm1\).  
Pivot zero means the whole center block is zero; choosing all ratios zero reconstructs it.  
Exceptional divisors are source loci mapping onto those center points, not omitted target loci.  
Global polynomial shears and their inverses omit no points and create no exceptional set.  
Only an implementation that divides without a zero case would unnecessarily discard center loci.

**Q3.** Argmax controls center ratios, while spectators inherit the bounds of the current intermediate point.  
A polynomial shear inverse maps each bounded compact box to a bounded set, so all mixed spectator coordinates remain bounded through finite depth.  
Nevertheless, each affine leaf source must be explicitly truncated: use a closed coordinatewise box containing all routed lifts.  
No topological compactification is needed; the unrestricted affine chart itself is not compact.

**Q4.** Finite growth at finite maximum depth is sufficient; even a much worse finite recurrence would not obstruct existence.  
Shrinking \(\rho\) is optional for boundedness and may not shrink dimensionless ratio coordinates.  
The real formal pitfall is reusing a unit-cube atom after a shear has produced bounds such as \(2\).  
Use a radius-parametric or anisotropic-box atom; then every finite inflated block still has an argmax and is covered.

**Q5.** With `dom` fixed, use  
`∃ ρ : ℝ, 0 < ρ ∧ volume (Metric.ball 0 ρ \ ⋃ p : Leaf, g p '' dom p) = 0`.  
Represent bounds by `B : Leaf → Fin N → ℝ` and `dom p := {z | ∀ j, |z j| ≤ B p j}`; prove these boxes compact.  
First prove the stronger set inclusion, making the set difference literally empty.  
The main Lean risk is pathwise coherence: one-node `reparam_image` does not automatically commute with child unions, changed centers, and dependent path compositions.

**Q6.** Most likely failure—inference—is that a shear fails to conjugate the *next actual center* to the claimed coordinate block on every chart, especially at pivot zero or a join.  
Then two-level generic-point checks miss an exceptional-stratum failure, and the tree fold is not justified.  
The cheapest decisive test is a symbolic local commuting-square proof for every recursion constructor, with no pivot-nonzero assumption.  
Check polynomial inverse, exact reconstruction, next-center identification, and coordinate bounds; one failed constructor isolates genuine new mathematics.