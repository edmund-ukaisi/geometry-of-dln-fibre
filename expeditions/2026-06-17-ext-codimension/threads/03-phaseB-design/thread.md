# Thread 03 — Phase-B AG-construction design (phaseB-design, scout)

Read-only recon/design. Charts the Lean route for the GEOMETRIC `codim O_M = dim Ext¹(M,M)` (Voigt),
which the operator chose to BUILD (option B), not cite. Codex consult (xhigh, hypothesis-withheld)
in `codex/standardness-{prompt,answer}.md` — independently reproduced the map and sharpened it.

## Mathlib coverage probe (grepped, this pin v4.29)

ABSENT (the AG desert, confirmed):
- algebraic groups / group schemes / LinearAlgebraicGroup — none.
- Lie algebra of a matrix group as a packaged object — none.
- scheme-theoretic Zariski tangent space — none (only KaehlerDifferential / Module.Cotangent of a
  ring extension; not a "tangent space at a point of a variety").
- variety dimension; `dim orbit = dim G − dim Stab` — none. `MulAction.orbitEquivQuotientStabilizer`
  is PURELY cardinality / group-equiv — zero dimension content.
- Chevalley constructible image, fibre-dimension theorem, generic flatness — none.
- determinantal-variety / rank-locus codimension — none.
- `dim R/I = dim R − height I` equality (catenary / equidimensional) — none. Only INEQUALITIES:
  `ringKrullDim_quotient_le`, Krull height `Höhensatz` as `height ≤ spanrank`.
- transcendence-degree = Krull-dimension for f.g. domains over a field — NOT assembled (Noether
  normalization file exists as a backbone, but the dimension=trdeg chain is not built).

PRESENT (the linear-algebra ground, all already used in Phase A):
- LinearMap.range/ker/finrank, rank-nullity, `Submodule.finrank_quotient_add_finrank`,
  `LinearEquiv.finrank_eq`, `Module.finrank_prod/pi`.
- ringKrullDim, topologicalKrullDim, Ideal.height, Krull's height theorem, MvPolynomial Krull dim
  (= card vars, Noetherian). dimension THEORY exists but only to the inequality level.
- MulAction.orbit / orbitRel / stabilizer (cardinality only).

## The math (both routes, from synthesis §5 + Codex, concur)

Target: `codim_Rep O_M = dim Ext¹(M,M)`. Glue identity (Phase-A objects only):
  `⟨d,d⟩ = dim G − dim Rep`, `dim O = dim G − dim Aut(M)`, `Stab = Aut(M) = ker δ_M` open in End(M),
  so `codim O = dim Rep − dim O = dim Hom − ⟨d,d⟩ = dim Ext¹`. The Hom−Euler identity IS Voigt.

Route (a) tangent/Voigt: `T_M O = im δ_M`; orbit smooth ⇒ `dim O = finrank im δ_M`; orbit open dense
in closure ⇒ `dim Ō = dim O`; `codim = finrank C¹ − finrank im δ = finrank coker δ = dim Ext¹`.
Route (b) orbit–stabiliser fibre dim: `dim O = dim G − dim Stab`, `dim G = finrank C⁰`,
`dim Stab = finrank ker δ`; same finish.

Both need the SAME geometric core that Mathlib lacks: converting a polynomial orbit map into a
geometric dimension-of-image-closure statement (locally-closed orbit + smoothness/separability +
dim-closure=dim-orbit + smooth ⇒ dim=tangent OR fibre-dim theorem). Codex: "the break is not the
linear algebra; it is the missing dimension theory for images/orbit closures."

## Codex-sharpened shortcut (the type-A rank-locus route)

For equioriented type A, the orbit closure is the explicit quiver rank locus
  `Ō = { A : rankPattern A ≤ rankPattern M (pointwise) }`  (closure-order ↔ rank-pattern order).
This is the ONE place the existing engine (`RankPattern`, `BaseChange.rankPattern_smul`,
`Orbit.rankPattern_eq_iff_orbit`, the orbit↔Kostant bijection) plugs into the geometry: the orbit
closure has an explicit ideal-theoretic description (products of minors of `submult`). BUT its
codimension formula is itself a large determinantal/quiver-rank-locus AG build — not elementary, not
in Mathlib. Promising as the cleanest single ASSUMED bridge; not a from-scratch shortcut to the value.

## Verdict (see message to controller for the ladder)

There is NO Lean-feasible from-scratch route to the geometric codimension at this pin that avoids
building a substantial AG dimension-theory library (irreducibility, locally-closed orbits,
dim-of-image-closure, smooth⇒dim=tangent, OR catenary `dim R/I = dim R − ht I`). The linear identity
`linCodim(M) := finrank C¹ − finrank im δ_M = dim Ext¹(M,M)` is a ~1-day wrapper on Phase A. The
geometric bridge `linCodim = codim_Rep Ō` is the genuine ocean.
