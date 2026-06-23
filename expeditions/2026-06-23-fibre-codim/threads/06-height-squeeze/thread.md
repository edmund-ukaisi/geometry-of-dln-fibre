# thread 06 — height-squeeze (Tide F2, formalisation / tide — the conceptual crux)

**Type:** formalisation (tide) · `OPENED → SPECIFY/DESIGN → CHECKPOINT(no-skip) → PROVE → AUDIT`.
This is the geometric heart of LR Lemma 4.6. It is design-sensitive (reducibility), so **do the design
+ API probe first and report the lemma chain at a hard checkpoint before any grinding.** A wrong route
here wastes a long tide.

## The target (Core codim identity — the whole geometric content of Lemma 4.6)
Over `[Field K] [IsAlgClosed K] [CharZero K]`, for `d : Fin (N+1) → ℕ`, `B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) K`:

    0 < N → B.rank = r → (∀ k', r ≤ d k') →
      codimRepCanonical (fibre d B)
        = codimRepCanonical (productRankLocusLE d r) + ((r * (d 0 + d (Fin.last N) - r) : ℕ) : ℕ∞)

The RHS first summand is `cCodim d r` (Brick A, `SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim`),
so equivalently `codimRepCanonical (fibre d B) = cCodim d r + r(d_0+d_N−r)`. This is **exactly**
`BundleShiftInterface.cited_bundle_shift` at the Core/`K` level (F3 does the thin DLN-layer wiring with
`B.map ι`). New module under `Core/` (e.g. `Core/FibreCodim.lean`).

## Route steer (controller): the two-inequality SANDWICH, NOT flatness
`codimRepCanonical Z = Ideal.height (vanishingIdeal (canonicalCoord '' Z))`. So the target is a height
identity. Prove `height(vanishingIdeal(fibre)) = cCodim + shift` by two inequalities, mirroring how
Brick A computed the Σ̄^r side:

- **Lower bound** (`height ≥`): the fibre is cut out in the ambient `Rep_d` (or in a top component of
  Σ̄^r) by the `multComap`-pullbacks of `B`'s coordinates — `fibreGenIdeal = Ideal.map multComap (maxIdealOfPoint B)`
  (F1). **Krull's height theorem** bounds the codim of a variety cut by `c` equations by `c` — NO flatness.
  Count the equations to the shift. (`Ideal.height_le_...`/`Ideal.span` Krull bounds — probe the exact name.)
- **Upper bound** (`height ≤`): the landed **affine-domain equidimensionality**
  `AffineDomainDimension.affine_domain_height_add_ringKrullDim_quotient_eq` (`height p + dim(A⧸p) = dim A`
  for `A = MvPolynomial⧸prime`, NO flatness). Apply per (top) component.

## The known subtlety — reducibility (this is where the design effort goes)
`codimRepCanonical = height(vanishingIdeal) = iInf` over minimal primes (the **min-codim / top**
components). Σ̄^r is reducible when θ>1; the fibre likely is too. Brick A handled this via
`sigmaIdeal d r = sInf (orbitIdeals d r)` + `minimalPrimes_sigmaIdeal_eq` (minimal primes = orbit
ideals), giving `codimRepCanonical = iInf (orbit codim) = cCodim`. **The design question to resolve at
the checkpoint:** what are the minimal primes of `vanishingIdeal(fibre)` (equiv. of `radical(fibreGenIdeal)`,
F1), and how do their heights relate to the orbit-ideal heights `+ shift`? The bundle `mult : Σ̄^r →
Mat^{rk=r}` should match fibre-components to Σ̄^r-components with codim `+ r(d_0+d_N−r)`. Pin this
correspondence (possibly: the fibre over `B` of the bundle restricted to each top orbit-component) before
proving.

## Read first (substrate)
- `Core/MultComorphism.lean` — F1: `multComap`, `fibreGenIdeal`, `vanishingIdeal_image_fibre_eq_radical`,
  `fibreGenIdeal_eq_map_maxIdealOfPoint`, `eval_multPoly`.
- `Core/SigmaCodim.lean` — Brick A: `codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal`,
  `…_eq_iInf_orbitCodim`, `sigmaIdeal_eq_sInf_orbitIdeals`, `minimalPrimes_sigmaIdeal_eq`. **The
  reducibility template.**
- `Core/AffineDomainDimension.lean` — `affine_domain_height_add_ringKrullDim_quotient_eq` (equidim, no
  flatness); `height_eq_ringKrullDim_of_isMaximal`.
- `Core/NullstellensatzCodim.lean` — the catenary bridge `height_vanishingIdeal_add_varietyDim_eq_card`
  (needs `IsPrime` — so per-component) + `varietyDim`.
- `Core/DeterminantalStratumDim.lean` — the thermometer `dim Mat^{rk=r} = r(n+m−r)` (the shift value).
- `Core/FlatQuasiFiniteHeight.lean` — the going-down/height-additivity pattern (only if the sandwich
  needs a height-equality step; the steer is to avoid flatness).
- `lean/CLAUDE.md` — zero sorry/axiom/native_decide; `decide +kernel`; `↦`; name=content; bedrock.

## Process — SPECIFY/DESIGN-first, HARD checkpoint (no-skip)
1. **DESIGN + PROBE:** pin the exact Lean statement; resolve the minimal-prime / reducibility
   correspondence (the crux above); pin the two-inequality lemma chain; probe the Krull-height and
   affine-domain API with `example` blocks (keep as durable contracts). **Fire a decorrelated
   `local-codex-consult`** (authenticated, xhigh) on the route + the reducibility handling; save the
   prompt/answer under `threads/06-height-squeeze/codex/`.
2. **CHECKPOINT (report to controller, no-skip):** the pinned statement + the minimal-prime
   correspondence + the lemma chain + the Codex read + a go/no-go. **Proceed to PROVE only if the route
   is clearly viable in this run.** If it walls (the minimal-prime correspondence is not tractable at
   v4.29, or an inequality needs absent machinery), STOP and report — recommend the fallback: discharge
   the witness range **`r ≤ 1`** cleanly (where the fibre structure is simplest) + roadmap general `r`.
   Do NOT grind a doomed route or weaken the statement.
3. **PROVE** to green, then **AUDIT.**

## AUDIT gate (if proved)
`scripts/lb` green (whole library, via the shared store — never bare `lake build`/`cache get`);
`scripts/sorries` 0; `#print axioms` on the headline = `[propext, Classical.choice, Quot.sound]`.
**Core only — never import `DLNFibre.DLN`.** Don't edit the aggregator (report the import line).
Witness: `(2,2,2), r=1` ⟹ `codimRepCanonical(fibre) = 1 + 3 = 4`.

## Scope
**Just F2** (the Core codim identity). The DLN-layer `BundleShiftInterface` discharge is **F3** (thin
wiring, separate tide). Don't touch other worktrees or any stash. In-repo memory only.

## Report
(i) the design verdict — the minimal-prime correspondence + the lemma chain (or the wall + fallback
recommendation); (ii) if proved: theorem name + signature, green/sorries/axioms, module path +
aggregator import line; (iii) the decorrelated-Codex read; (iv) any v4.29 API friction for the gotchas log.
