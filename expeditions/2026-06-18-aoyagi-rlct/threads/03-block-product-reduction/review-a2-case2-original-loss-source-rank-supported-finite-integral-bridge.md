# Review: A2 Case 2 original-loss source-rank-supported finite-integral bridge

Reviewer: xhigh `Locke the 3rd`.

Verdict: PASS.

## Findings

No concrete findings.

## Fidelity Check

The Lean theorem is scoped as a support restatement.  The docstring keeps the
noncoverage and nontransport caveats explicit.  The added rank hypotheses are
exactly the existing Case 2 support hypotheses: base-product rank `hprod`,
first-edge rank `hr0`, and the uniform successor selected-entry rank equation
`hr1`.

The proof calls the source-stratum endpoint-basis original-loss theorem,
obtains `mu.restrict sourceStratum = mu` from the existing Case 2 support
theorem, rewrites

```text
mu.restrict (U inter sourceStratum) = mu.restrict U
```

and then reuses the finite integral.  The final integrand, target, endpoint
bases, density, exponent, and radius witnesses match the source-stratum
theorem; only the final measure is changed.

## Nonclaim Check

The reproduction and statement card accurately describe the support-only
boundary.  No overclaim was found about source-rank coverage, selected-entry
source/image equality, external source-prior transport, Jacobian comparison
for such a prior, normal crossings, pole order, or RLCT.

The reviewer did not rerun the focused Lean build.  The controller's focused
build and hygiene gates are recorded in the thread ledger.
