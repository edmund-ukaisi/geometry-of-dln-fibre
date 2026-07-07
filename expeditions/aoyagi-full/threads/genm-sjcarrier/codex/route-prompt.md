# Decorrelated route check — Gram c.o.v. vs pure radial, for a matrix-integral finiteness

You are a decorrelated second opinion. My leaning is WITHHELD. Adjudicate a concrete measure-theory /
resolution-of-singularities question. Be terse and decisive.

## Setup (exact)

Fix integers `t ≥ 1`, `p = M₀−t ≥ 1`, `q = M₁−t ≥ 1`, and a "tail" parameter `A'` ranging over a
compact box `Z` of finite volume. For each `A'` we have a fixed matrix product `Q = prod(tail)(A')`,
split by rows into `Q_p` (t rows) and `Q_b` (`q'`-ish rows), where `Q_b : (M₁−t) × n`. On a pivot chart
the front factor `A₀ = fromBlocks A B C D` has invertible `t×t` pivot `A`, and the Schur block split
gives, EXACTLY,

    frobSq(A₀ · Q) = frobSq(A·Q̃_p) + frobSq(C·Q̃_p + Γ·Q_b),

with `Q̃_p = Q_p + A⁻¹B·Q_b`, `Γ = D − C A⁻¹ B` a free `p×q` matrix (freed by a measure-preserving
shear `D ↦ Γ`). We want finiteness, at `c' < ½·minAdm(M)`, of the JOINT integral over `(A₀, A')`:

    J = ∫_{A' ∈ Z} ∫_{A₀ ∈ box ∩ chart} ( frobSq(A₀·Q) )^{−c'} dA₀ dA'.

Two routes are on the table to reduce the inner `Γ`-integral:

**Route G (Gram change of variables).** Substitute `Γ ↦ Γ·Q_b` (Gram c.o.v.). When `Q_b Q_bᵀ` is
positive definite (full row rank), this is exact and gives
`∫_Γ (w + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'} dΓ = det(Q_b Q_bᵀ)^{−p/2} · Cresid · (w + ‖C·Q̃_p·(I−P)‖²)^{−(c'−pq/2)}`,
`w = frobSq(A·Q̃_p)`. Then integrate this over `A'`. (This is a banked exact lemma for the full-rank slice.)

**Route P (pure radial, no Gram c.o.v.).** Keep `Γ` as a chart coordinate over its box; blow up ONE
radial `u` for the current block via `frobSq((u•Δ)·Q) = u²·(residual)`; charge `u` by the block codim;
recurse layer by layer; reach a monomial `(∏uⱼ²)·(unit)` at the end; finiteness by a coordinatewise
monomial endpoint. `Γ` is NEVER integrated out against `Q_b`; NO Gram determinant ever forms. The
per-step isotropic shape consumed is `∫_{A'∈Z} ∫_{Δ∈box} (frobSq Δ + W(A'))^{−c'}` with `W ≥ 0`.

## The questions

1. To land the inner residual in the ISOTROPIC form `∫_{A'} ∫_{Δ∈box} (frobSq Δ + W(A'))^{−c'} dΔ dA'`
   (Δ entering through its OWN frobenius norm, no `det(Q_bQ_bᵀ)` Jacobian weight), is Route G (the Gram
   c.o.v. `Γ↦Γ·Q_b`) the correct move — or does Route G INEVITABLY produce the `det(Q_bQ_bᵀ)^{−p/2}`
   Gram-Jacobian form, which is NOT the isotropic form? I.e., can a Gram c.o.v. `Γ↦Γ·Q_b` ever output
   the isotropic `frobSq Δ + W` shape, or is that a category error?

2. `Q_b = A_{k,b}·(deeper product)` is rank-DEFICIENT on a positive-measure locus of `A'` (for depth
   ≥ 3). On that locus Route G's `det(Q_bQ_bᵀ)^{−p/2}` diverges. Doing Route G "jointly over (A₀,A')"
   (integrating the Gram-det weight over `A'` rather than bounding it pointwise): does this rescue
   finiteness by a clean measure-theoretic change-of-variables + Fubini, OR does it require a genuinely
   new joint principalisation / normal-form of `det(Q_bQ_bᵀ) = ‖∧^q Q_b‖²` for the matrix PRODUCT
   `Q_b`, tracking shared exceptional-divisor support at corank ≥ 2?

3. Bottom line: if the goal is the isotropic per-step shape (Route P's consumable), is doing the Gram
   c.o.v. `Γ↦Γ·Q_b` the right first step, or a wrong-route step that lands in the Gram-Jacobian world
   (Route G) that then walls on the degenerate strata? One-paragraph verdict.
