# Review - A2 Source-Level External-Measure Density Handoff

Date: 2026-06-30.

## Verdict

PASS. Xhigh reviewer `Feynman the 2nd` found no formal, mathematical, or Lean
API issue in the current diff.

## Mathematical Scope

The helper

```text
restrict_withDensity_le_smul_restrict_of_ae_le
```

is correctly scoped: the a.e. density bound is with respect to `mu.restrict s`,
and the conclusion is the local domination

```text
(mu.withDensity f).restrict s <= c * mu.restrict s.
```

The source-level bridge remains local and conditional. It assumes the
restricted equality against `sourceImageMeasure.withDensity externalDensity`,
an a.e. bound on `externalDensity` with respect to
`sourceImageMeasure.restrict sourceLocal`, and `Cext < infinity`.

## Source Fidelity

The theorem derives only source domination and product domination before using
the existing full-product socket. It does not claim original prior identity,
Haar transport, source-rank coverage, normal crossings, pole order, or RLCT.

## Residual Risks

- The public theorem name says `externalSourceMeasure_eq_withDensity`; adding
  `restrict` or `local` would make the local nature clearer. The statement and
  docstring are explicit enough, so this is not a correctness issue.
- The `[SFinite nu]` assumption is a real caller obligation required by the
  product-domination API. It is expected for the intended Haar measure, but
  downstream wrappers must supply or infer it.
