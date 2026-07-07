**1. Verdict**

**(a) bounded-iterated-explicit**, with an important correction to Claim-A’s wording.

Aoyagi’s coupled `diag(b)` recursion is a sequential explicit chart construction. It is not a call to abstract Hironaka, and Case 1’s shared-divisor merge is not a simultaneous principalisation. The formal work is large, but it is bounded chart algebra plus a divisor-support ledger.

The caveat: this is true for the **native Aoyagi `(S,J)` blow-up route**. If one first integrates out a block and creates a Gram determinant such as `det(Q_b Q_bᵀ)` over a degenerate matrix product, then completing that atom route really does become a determinantal/multi-ideal principalisation problem. That is Claim-B’s real warning, but it is about the wrong route for this question.

**2. Are Claim-A And Claim-B The Same Object?**

Only if Claim-A’s “single-radial-per-block” means:

- one radial for the **current Aoyagi equal-run/residual block**;
- old exceptional variables are carried in the `b_i`;
- Case 1 may reuse an existing divisor and add exponent to it;
- the state records which generators share which exceptional variables.

Under that interpretation, Claim-A and the coupled `diag(b)` construction are the same object.

But coupled `diag(b)` does **more** than a fresh-per-block or per-row iteration. A fresh model that gives new independent variables to each row/block forgets sharing. That is exactly why threshold-only/per-row models fail: they cannot distinguish `⟨δx,δy⟩` from `⟨δ₁x,δ₂y⟩`.

**3. Case-1 Merging**

Case 1(1) is a bounded explicit blow-up chart, not a simultaneous move.

More precisely: the center is a coordinate center contained in an already-existing exceptional divisor. In the chart where the existing `u_{s,k}` is the radial coordinate, the partial block is written

```text
d_ij = u_{s,k} d'_ij
```

so no fresh exceptional variable is introduced in that chart. The Jacobian contribution from the partial block is added to the existing divisor’s exponent. This is “merge exponents” in the ledger, but analytically it is still an ordinary sequential coordinate blow-up chart.

The alternative Case 1(2) chart introduces a new `u_{S,J+1}` and advances `J`. Both are explicit finite chart moves.

**4. What Is Genuinely New**

The genuinely new content is not abstract resolution. It is the **carrier bookkeeping**:

- maintain `SJState`: `(S,J)`, residual block `D_J`, and the monomials `b_i`;
- partition the `b_i` by equal runs;
- update the support map saying which exceptional variables divide which generators;
- implement Case 1 exponent merging into an existing divisor;
- prove the relative chart lemma: old exceptional variables remain passive monomial prefactors while the active block is reduced by `Z`-independent unit row/column transforms;
- prove termination and the terminal monomial endpoint `Σ b_i²`.

That is substantial formalization work, but bounded by the finite `(S,J)`/equal-run recursion for the given widths.

**5. Per-Row Undercount**

Yes: the per-row undercount shows naive per-block/per-row tracking fails. It does **not** show the Aoyagi shared-tracking route fails.

The lesson is:

```text
fresh independent divisors  -> wrong invariant
shared divisor ledger       -> correct invariant
```

The shared support is necessary, but it is recorded by the sequential `diag(b)` recursion. It does not force a simultaneous principalisation unless you choose the Gram-det/atom route and then try to recover the missing sharing afterward.