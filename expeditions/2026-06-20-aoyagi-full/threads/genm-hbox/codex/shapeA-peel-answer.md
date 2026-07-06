**Verdict**

**NO-GO.** The Shape-A arity-descent peel is **not buildable as stated**. It already fails on `(2,2,2,2)` in the `t=1` front-rank chart. The precise obstruction is:

`frobSq(A^0 A^1 A^2)` does **not** factor as  
`(pivot/Schur monomial)^2 × frobSq(redChain 1 child) × bounded unit`.

After the front Schur split, the loss is a **mixed sum** with a shared downstream tail, not a product. So the codim-1 Schur direction does not give the claimed `+1/2` exponent shift by Tonelli.

1. **Q1: explicit `(2,2,2,2)`, `t=1`, `a ≠ 0` computation**

Write
`A^0 = L diag(a,s) R`, with
`λ := c/a`, `μ := b/a`, `s := d - cb/a`,
`L = [[1,0],[λ,1]]`, `R = [[1,μ],[0,1]]`.

Absorb `R` into `A^1` by `B := R A^1` (Jacobian `1`). Let
`C := B A^2 = [u; v]`, where `u,v ∈ R^{1×2}` are the two rows of `C`.

Then
`A^0 A^1 A^2 = L [a u; s v] = [a u; λ a u + s v]`,
so
`F := frobSq(A^0 A^1 A^2)` is
`F = (1+λ^2)a^2 ||u||^2 + 2 λ a s <u,v> + s^2 ||v||^2`.

On a bounded pivot chart (`|λ| ≤ 1` after standard normalization), this gives the uniform comparison
`F ≍ a^2 ||u||^2 + s^2 ||v||^2`.

That is the obstruction. The pulled-back ideal is
`<u_1,u_2, s v_1, s v_2>`,
not `s · J_child` and not just the `(1,2,2)` child ideal.

Two concrete contradictions to the proposed factorization:

- Take `A^1 = A^2 = I`. Then `u = (1,μ)`. On `s=0`, `F = (1+λ^2)a^2(1+μ^2) > 0` generically. So no factorization with any positive Schur power can hold.
- Take `A^2 = I` and `A^1 = R^{-1} [[0,0],[1,0]]` (valid on `|μ|≤1`). Then `u=0`, `v=(1,0)`, so `F = s^2 > 0`. So no factorization through the `(1,2,2)` child `u` can hold either.

So the answer to Q1 is **no**.

2. **Q2: exponent bookkeeping**

The arithmetic `c' - 1/2 < 1` is fine, but the analytic step that would justify it is false.

- `t=1`: fails for the reason above.
- `t=2`: only works on well-conditioned full-rank pieces. As `det(A^0) → 0`, the constants blow up and control must pass to the rank-1 analysis, which is exactly where Shape A fails.
- `t=0`: not the decisive issue, but it is already not a clean literal `redChain 0 M` child in the positive-width box theory.

So the whole-box cover does **not** close under this recursion.

3. **Q3: wide-front pushforward**

This is **not** the real obstruction.

After normalized rank-`t` pivoting, the reduced first factor has the form `V = [I_t, B]` with bounded `B`. Then `W := V A^1` is a pushforward of box measure, but its density is uniformly bounded on a larger box. Columnwise:
`w = x_I + B x_J`,
so for fixed `x_J` there is a unique `x_I`; hence the density is bounded by the volume of the `x_J`-box, uniformly. In general one gets a bound like `2^{(M_1-t)M_2}` on an enlarged box.

So the “child is not literally a box variable” issue is fixable. If the multiplicative factorization existed, this pushforward would not kill Tonelli. The real failure is the mixed form
`J_u + Δ J_v`,
not the measure pushforward.

4. **Q4: overall buildability**

For this Shape-A route: **NO**. This is not a `1000-2000` LoC proof-engineering job.

The hidden monument is a genuine **monomialization / normal-crossings problem for the product map along determinantal incidence strata**. In concrete terms, one must resolve mixed ideals of the form
`<T·tail, Δ S·tail>`
rather than recurse on a single `redChain t M` box child. That is exactly the kind of richer state carried by the fuller Aoyagi `(S,J)` / `diag(b)` recursion.

So:

- **GO/NO-GO on `(2,2,2,2)`: NO-GO.**
- **Precise obstruction:** on the `t=1` chart the loss is comparable to `a^2||u||^2 + s^2||v||^2`, not to a monomial times the `(1,2,2)` child. The codim-1 Schur variable is not an independent factor of the loss.

This matches the failure class already recorded locally in [verify-r1-shortcut.md](/home/ubuntu/workspace/geometry-of-dln-fibre/theory/aoyagi-2023-reproduction/verify-r1-shortcut.md:35) and [verify-r1-light-recursion.md](/home/ubuntu/workspace/geometry-of-dln-fibre/theory/aoyagi-2023-reproduction/verify-r1-light-recursion.md:49).