<task>
Lean 4 + Mathlib v4.29.0 (pinned). I am formalising the geometry of fibres of deep linear
networks via type-A quiver representations. I need the LIGHTEST FAITHFUL definition of the
**codimension of a Zariski-closed subset of affine space kⁿ** (k a field), as a `ℕ` (or `ℤ`),
that is (a) mathematically standard and faithful, (b) a small bounded down-payment — the
DEFINITION only, NOT the deep dimension theorems — and (c) lets a FUTURE theorem
`codimRep (orbitRankLocus M) = orbitLinearCodim M` be both meaningful and dischargeable.

CONCRETE SETTING.
- `Rep_d` is a finite-dimensional k-vector space: `Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k`. It is (non-canonically) `k^n` with `n = Σ_i d(i.succ)*d(i.castSucc)`. It carries `Module k`, `AddCommGroup`, and is `FiniteDimensional k` (a finite product of matrix spaces).
- `orbitRankLocus M : Set (Tuple d)` is a Zariski-closed determinantal subset (vanishing of minors of interval sub-products — i.e. cut out by polynomial equations in the matrix entries).
- `orbitLinearCodim M : ℕ` is already defined and = `finrank k (cochain1 d d) − finrank k (range δ_M)` = `finrank (Ext¹(M,M))`. It is the TANGENT/expected codimension.
- The future "Voigt" theorem will assert geometric codim = this tangent codim. I am NOT proving it now; it is an explicit hypothesis `hVoigt`. I only need `codimRep` to be DEFINED faithfully so the hypothesis is meaningful.

CANDIDATE PRIMITIVES I am weighing (tell me which is the right faithful-and-light choice at the v4.29 pin, and the exact Mathlib names/types):
1. `topologicalKrullDim` of the closed subset with the subspace Zariski topology, with codim = (krullDim of ambient) − (krullDim of subset). Concern: is there a usable Zariski-topology instance on `Tuple d` / `k^n` at this pin? Or must I coordinatise via `MvPolynomial`?
2. `Ideal.height` of the vanishing ideal `I(orbitRankLocus M)` inside `MvPolynomial (Fin n) k` (then codim = height, by the Hilbert Nullstellensatz / catenary dimension theory). Concern: this forces me to coordinatise `Tuple d` as `MvPolynomial (Fin n) k` and build the vanishing ideal — how heavy is that AS A DEFINITION (not the height theorems)?
3. ambient `finrank` − (dimension of the subset), where "dimension of a closed subset" is itself defined via `topologicalKrullDim` of the subspace topology. 
4. Something else standard I'm missing at this pin.

KEY CONSTRAINT: the definition must be FAITHFUL (an actual codimension, not a placeholder), but it is acceptable that the DISCHARGE of `hVoigt` (proving geometric = tangent codim) is deferred to a large later AG sub-expedition. So I want the def that minimises scaffolding NOW while remaining the genuine notion.

What is ALREADY in Mathlib v4.29 (please be concrete, these may differ from later versions):
- `topologicalKrullDim`, `Order.krullDim`, `Ideal.height`, `Ideal.primeHeight`, `ringKrullDim`.
- Is there a Zariski-topology / `PrimeSpectrum` bridge usable to put a krull-dim on a `Set (k^n)` WITHOUT MvPolynomial coordinatisation?
- `Module.finrank` for the ambient dimension.

DECISION I NEED: PREFERRED route = a real `codimRep` def with a standard primitive (bounded — def only). FALLBACK = if a faithful `codimRep` needs substantial variety/scheme scaffolding (a rabbit hole), use the abstract form: the conditional theorem just takes `(codimO : ℕ)` and `(hVoigt : codimO = orbitLinearCodim M)`, documenting codimRep/codimO as a B-full definition. Tell me whether the PREFERRED route is bounded-enough to do NOW, or whether FALLBACK is the disciplined call — and WHY.
</task>

<output_contract>
1. VERDICT (one line): PREFERRED (which primitive) or FALLBACK, and the single reason.
2. The recommended `codimRep` Lean signature/def (or the abstract-parameter form if FALLBACK), with exact Mathlib v4.29 names you are confident exist. Flag any name you are NOT sure exists at v4.29.
3. SCAFFOLDING COST of the preferred route, itemised (what must be built just for the DEFINITION to typecheck — coordinatisation? topology instance? vanishing ideal?). Estimate in Lean declarations, not time.
4. Whether the future `hVoigt`/Voigt discharge is genuinely possible against your recommended def (i.e. is the def the right target).
5. Any trap at the v4.29 pin specifically.
</output_contract>

<grounding_rules>
Distinguish what you KNOW exists in Mathlib v4.29 from what you INFER or recall from a later version — flag every uncertain lemma/def name explicitly as "verify at pin". Do not invent Mathlib names. If you are unsure whether a Zariski topology instance on an abstract f.d. vector space exists at this pin, say so rather than assuming.
</grounding_rules>
