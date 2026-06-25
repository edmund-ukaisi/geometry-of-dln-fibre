# Codex consult — is there a varietyDim-ONLY path lighter than building the full product iso `e`?

Lean 4 + Mathlib v4.29. CRITICAL scope finding: the chart `AlgEquiv` route (c)'s rung 2 needs is
ESSENTIALLY the product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg` that a PRIOR tide (R2-3b-4)
attempted and **never finished** (it remains a hypothesis in the repo, never a committed `def`). The
prior wall was Lean-mechanical: descending the gauge `gaugeEquiv` through the localization (at `ΔP`)
AND the quotient (by the cut ideal), then proving the coordinates SPLIT as `SchurLoc ⊗ FibreAlg`.

I only need a `varietyDim` (Krull-dim) statement: `varietyDim(chart) = δ + varietyDim F`. I have
LANDED:
- `varietyDim_eq_of_coordRingAlgEquiv` — transports `varietyDim` across a coordinate-ring `AlgEquiv`.
- `ringKrullDim_quotient_radical` — radical-insensitivity (so I work with reduced/`vanishingIdeal`).
- `gaugeEquiv` (universal coordinate-change `AlgEquiv` on the UNquotiented polynomial ring, over any
  `CommRing`), the sweep `Σ^r = H·F`, `multComap`, `Sred`, `SchurLoc`, `schurToSred`.
- `SchurLoc = Localization.Away detSchurS` of a polynomial ring; Mathlib has `MvPolynomial.krullDim
  _of_isNoetherianRing` (`dim R[X_1..X_n] = dim R + n`).

## The question

Building the full `e` (an `AlgEquiv` with both directions + round-trips through a
localized-quotient ring) is heavy and previously stalled. For a DIMENSION-only conclusion, is there a
LIGHTER path that avoids constructing the full `AlgEquiv`? Candidates:

1. **Inequality squeeze instead of iso.** `varietyDim(chart) ≤ δ + dim F` AND `≥ δ + dim F`
   separately, each via a one-directional regular map (a surjection/closed-immersion of coordinate
   rings) rather than a full iso. A surjection `A ↠ B` gives `dim B ≤ dim A`; an injection of
   f.g. domains gives `dim A ≤ dim B`. Could the two inequalities be gotten from the two `AlgHom`
   directions WITHOUT proving they're mutually inverse (the round-trips were the heavy part)? Does the
   reducible case break the domain-injection direction?

2. **The unquotiented gauge + ideal-image bookkeeping.** `gaugeEquiv` is a clean `AlgEquiv` on the
   UNquotiented `MvPolynomial (RepCoord d) k`. It carries `vanishingIdeal(chart)` to
   `vanishingIdeal(gauged chart)`. If the gauged chart's vanishing ideal VISIBLY splits as
   `(SchurLoc-coords ideal) + (fibre-coords ideal)` — i.e. the gauged coordinates separate into δ
   free base directions ⊗ the fibre — can I read `varietyDim` off the split WITHOUT a tensor `AlgEquiv`,
   e.g. via `MvPolynomial` variable-partition + `krullDim` of the polynomial extension? The gauge is
   an iso on the unquotiented ring (no localization/quotient descent needed THERE) — does staying
   unquotiented and only quotienting at the end dodge the descent that walled `e`?

3. **`δ`-free-directions directly.** Maybe avoid `SchurLoc ⊗ FibreAlg` entirely: show the chart
   coordinate ring is `≅ FibreAlg-coords localized-polynomial-extended by δ Schur variables`, so
   `dim = dim F + δ` directly via `MvPolynomial.krullDim_of_isNoetherianRing` + localization. This is
   the polynomial-extension route stated as a coordinate-ring iso to `(FibreAlg)[X_1..X_δ]_loc` rather
   than a tensor — is that iso EASIER to build than the symmetric tensor `e` (it's the same content,
   but maybe a cleaner Lean target)?

4. **Is the descent genuinely unavoidable?** The prior `e` needed gauge-descent through
   `Localization.Away ΔP ⧸ IadDeep`. For the dimension statement, can I work on the UNquotiented +
   UNlocalized ring as long as possible, applying the gauge `AlgEquiv` there, and only take
   `vanishingIdeal`/`ringKrullDim` at the end — so the localization/quotient interchange that walled
   `e` never arises?

Tell me: (a) which path is lightest for a DIMENSION-only conclusion, (b) whether any path genuinely
avoids the localized-quotient gauge-descent that stalled `e`, (c) an honest module estimate for the
lightest path, and (d) if NO path is materially lighter than the full `e` (i.e. rung 2 just IS
building `e`, which stalled), say so — that is a scope escalation, and the fallback is citing `hSweep`.
Be adversarial: I suspect the dimension-only framing should be lighter than the full reduced-iso, but
I need to know if the gauge-descent is the irreducible core either way.
