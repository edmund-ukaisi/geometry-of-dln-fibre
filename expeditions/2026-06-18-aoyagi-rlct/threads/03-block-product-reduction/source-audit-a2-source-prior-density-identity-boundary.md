# Source Audit - A2 source-prior density identity boundary

Date: 2026-06-30.

## Verdict

Aoyagi gives the analytic template for a local bounded-density theorem, but
does not state the project-specific passive-theta source-prior transport
identity.  The next non-wrapper theorem must be a concrete coordinate-change
identity or a local Haar/source-measure transport theorem.

## Aoyagi Anchors

- p. 5, Definition 1: RLCT is defined using an analytic loss `F` and a
  `C^\infty` compactly supported density `phi` near `w*`; when `phi(w*) != 0`,
  Aoyagi suppresses `phi` from the notation.
- p. 6, Hironaka display: after a coordinate map `pi`, the pullback density
  has the usual prior-times-Jacobian form.  This supports the general shape
  "prior times coordinate Jacobian", not this expedition's specific
  passive-theta identity.
- p. 8, main DLN theorem assumptions: the prior density `phi(w)` is
  `C^\infty`, compactly supported, and satisfies `phi(w*) > 0`.
- pp. 10-11, Lemma 2: the Schur block coordinate change is explicit when
  `A1` is invertible:

  ```text
  F2 = -A1^{-1} A2
  F3 = -A3 A1^{-1}
  C4 = -A3 A1^{-1} A2 + A4.
  ```

- pp. 11-13, Theorem 3: the product-reduction induction repeats this block
  coordinate change and reaches the p.13 product-difference form.
- p. 15 and pp. 16-21: the blow-up charts record monomial differential factors
  and pivot/row/column substitutions.  These are source anchors for later
  Jacobian-factor formalisation, not an already-proved passive-theta
  source-prior identity.

## Conditional Theorem Shape

Let

```text
sourceChart : Theta -> Source
readback    : Source -> Theta
S = sourceChart '' V
thetaReference = passiveSource.withDensity jacobianDensity
```

For an intended source/original prior measure `m_phi`, define

```text
pulledBackPrior =
  Measure.map readback (m_phi.restrict S).
```

The desired domination follows from the coordinate-change identity

```text
pulledBackPrior =
  (thetaReference.withDensity g).restrict V
```

plus local boundedness `g <= C` a.e. on `V`.  Aoyagi's smooth positive
compactly supported prior and determinant/pivot-unit conditions support local
boundedness after this identity is available.

## What Remains To Formalize

- The passive-theta source chart is a local analytic coordinate chart with the
  correct measurable image and inverse/readback on the intended source slice.
- The Jacobian/reference measure used in Lean is exactly the source-prior
  coordinate-change reference, up to a smooth unit.
- The original/source prior restricted to the local image is the pushforward
  of this theta-domain density.
- For the full original DLN prior, regular p.13 variables must be included;
  passive-theta alone is only the source-side part.

## Kill Conditions

- Do not claim domination for arbitrary `externalMeasure`; singular measures
  such as Dirac masses break it.
- Do not treat smoothness of `phi` alone as source-prior transport.
- Do not use one passive-theta chart as global support or source-rank coverage.
- Do not identify the selected-entry signed-box measure with full
  determinant-chart Haar measure without a transport theorem.
- Do not omit passive or regular variables when comparing to the original
  ambient DLN prior.
- Do not use quiver-paper evidence.
