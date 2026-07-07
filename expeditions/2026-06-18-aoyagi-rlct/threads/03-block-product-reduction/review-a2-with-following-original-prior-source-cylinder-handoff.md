# Review - A2 With-Following Original-Prior Source-Cylinder Handoff

Date: 2026-07-07.

## Source-Boundary Check

Reviewer: xhigh read-only sidecar `Aristotle the 2nd`.

Verdict: PASS.  The theorem is bounded-density bookkeeping over the
original-volume source-cylinder handoff.

The checked calculation sets `mu := originalVolume`, `C := chartPiece`,
`nu := sourceRef`, and `f E := ofReal (density E)`.  Since

```text
originalPrior = mu.withDensity f,
```

the hypotheses

```text
MeasurableSet C
∀ᵐ E ∂ mu.restrict C, density E <= Kprior
mu.restrict C <= Dvol * nu
```

give

```text
originalPrior.restrict C <= (ofReal Kprior * Dvol) * nu.
```

The reviewer identified `restrict_withDensity_ofReal_le_smul_of_restrict_le_smul_of_ae_le`
as the direct Lean helper.

## Lean-Route Check

Reviewer: xhigh read-only sidecar `Socrates the 2nd`.

Verdict: the statement shape and proof route are correct, and no helper lemma
is needed.

The recommended proof first calls the new original-volume source-cylinder
theorem, then applies the real-density restriction helper to the original
prior density upper bound.  The final scalar is

```text
Cprior = ofReal Kprior *
  (((cHaar^-1 : NNReal) : ENNReal) * (Cdet * eps^-1)).
```

## Boundary

The theorem must keep explicit: measurable chart piece, source-cylinder
support `chartPiece subset sourceChart '' (V inter sourceCylinder)`, the
source-density lower bound on `baseJ.restrict V`, `eps != 0`, `eps !=
infinity`, and the prior-density upper bound on
`originalVolume.restrict chartPiece`.

It does not prove source-cylinder support, source-density positivity,
prior-density boundedness, determinant/raw Haar transport, Haar normalization,
readback domination, finite-integral transfer, source/source-rank coverage,
normal crossings, pole order, or RLCT.  It does not use the quiver paper or
quiver Lean evidence.
