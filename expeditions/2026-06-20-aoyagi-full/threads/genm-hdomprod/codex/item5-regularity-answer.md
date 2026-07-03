**A**
**STATED-CEILING-ARTIFACT.** Load-bearing reason: from the facts you gave, every step before the final globalisation is either genuinely `C^∞` or preserves the same regularity parameter `n`, and the only explicit downgrade to `1` is the call `exists_contDiff_eventuallyEq_of_contDiffOn (n := 1)`. So, assuming the quoted Mathlib signature is accurate, `ContDiffAt.to_localInverse` does preserve `C^n` with no derivative loss for `n ≠ 0` (standard IFT fact, and also what your signature says), and switching the bump step to `n := 2` should give a global `C²` residual `q`. Then `h = q ∘ (fun t => (0,t))` is `C²` as a composition with a linear `C^∞` map.  
Inference about downstream RLCT code: I see no analytic reason higher regularity would break anything; any place that only needs `C¹` can recover it from `C²` by downgrade.

**B**
- Minor-determinant division: **No**. Standard analysis says the inverse is smooth on the neighborhood where the chosen minor stays invertible; there is no new singularity at the basepoint.
- Global-vs-local `C²`: **No**. If your `exists_contDiff_eventuallyEq_of_contDiffOn` really is parametric in `n`, then local `C²` near `t₀` can be bump-globalised to a global `C²` map agreeing near `t₀`; so the second peel’s global hypothesis is an interface demand, not a real analytic extra.
- Bump product regularity: **No**. Standard fact: `χ ∈ C^∞` and `g ∈ C^k` imply `x ↦ χ(x) • g(x)` is `C^k` because scalar multiplication is a smooth bilinear map.

**C**
For the **cheapest route to `ContDiff ℝ 2 q`**, the minimal change is:
1. Change the conclusion/interface of `dln_hchart_residual` to return `ContDiff ℝ 2 q`.
2. Inside it, change the globalisation call from `exists_contDiff_eventuallyEq_of_contDiffOn (n := 1)` to `(n := 2)`.

Nothing upstream needs to change for the `C²` target if your current chain already produces local `ContDiffOn ℝ 2` before the bump, as you stated.

For a **parametric `k` / `C^∞` version**, you would also need to generalise the hard-coded-`2` interfaces:
1. `contDiff_chartΦ`
2. `exists_boundedUnit_chart_of_contDiffAt`
3. `contDiffOn_rawResidVec`
4. any exported regularity theorem for `splitHomeo.symm` that is currently only stated at `2`

From your description, **none of these looks like a real analytic blocker**; the only likely Lean-side caveat is that the IFT wrapper should probably assume `k ≠ 0` (or `1 ≤ k`), mirroring the current `hn : (2 : ℕ∞) ≠ 0`.