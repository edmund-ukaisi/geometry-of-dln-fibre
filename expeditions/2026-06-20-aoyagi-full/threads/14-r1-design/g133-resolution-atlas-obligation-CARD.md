# R1.6 residual → the Lean-grade `IsResolutionAtlas` obligation (statement card) (pp-hall, 2026-06-22, #133)

**The formaliser target.** Pin the one R1.6 residual I named in #132 — the connection between the
pivot-tree's branches and the admissible rank strata — into a PRECISE Lean-grade obligation (the
statement, NOT the proof), stated so `resolution_charts` (`Skeleton.lean:1017`) can consume it.

## FIDELITY CORRECTION up front: SURJECTION, not bijection
The controller's task said "bijection". The faithful obligation is a **surjection** `paths ↠ Adm M` +
codim-match, NOT a bijection. The pivot-tree's root-to-leaf PATHS **outnumber** the admissible strata
(the (2,2,2) build had 24 leaves for 3 strata: pivot-coordinate × affine-minor choices multiply the
leaf count). For the value `⨅_paths monomialThreshold` only **surjectivity** matters — many paths hitting
the same stratum carry the same threshold and don't change the `⨅`. Bijectivity is a red herring (and
would be FALSE). So the obligation is: every admissible stratum is *reached* (surjectivity = "no missed
branch") + every center's codim is admissible + multiplicity-1 (= "no undershoot"). [`g133_surjection_not_bijection.py`.]

## The carrier objects (already in the Lean library — `Foundations/Lambda.lean`)
- `Adm M : Finset (Fin L → ℕ)` — the **admissible rank-stratum index set**: exponent vectors
  `T : Fin L → ℕ` with weak-decrease, last `= 0`, block bounds (`admPred`). This IS the rank-stratum
  lattice of `{∏C = 0}` (the level/rank sequence). `Adm_nonempty` is green.
- `Mval M T : ℤ` — the **codimension** of stratum `T` (`= ∑_j (tPrev−T_j)(M_{j+1}−T_j)`); `Mval_nonneg`
  green on `Adm`.
- `lambdaCore M = ½·(Adm M).inf' Mval` — the core RLCT; `= aoyagiLambda` for `r = 0`.
- `axisRatio h k = (h+1)/(2k)`; `axisRatio (c−1) 1 = c/2` (`axisRatio_regularSeq`, green).
- `monomialThreshold d k h = ⨅_j axisRatio (h_j) (k_j)` (S2 `monomial_rlct.1`, the cited axiom).
Verified non-vacuous: `Adm`/`Mval`/`min` for `(2,2,2)→3`, `(3,3,3)→7`, `(2,2,2,2)→3` match the
`lambdaCore` ground truth (`g133_bijection_obligation.py`).

**Natural carrier confirmed:** the obligation lives on the **DLN-side** `Adm M`/`Mval` cone (the rank
stratum index), NOT directly on the `Core.RankPattern` inclusion-exclusion inversion. `Core.RankPattern`
(cumul↔diff, Gabriel multiplicities) is the *abstract quiver-orbit ↔ rank-pattern* machinery — it is the
right home for the eventual PROOF that the pivot branches enumerate the strata (the quiver-orbit ↔
rank-pattern translation does load-bearing work there), but the *obligation statement* `resolution_charts`
consumes is phrased over `Adm M`/`Mval` (the value side A1 already computes). So: **state the obligation
over `Adm M`; carry the proof through `Core.RankPattern` / the Gabriel rank-pattern lattice.**

## The obligation (statement only — `IsResolutionAtlas` + the value-consequence)

```text
-- The chart-tree data (an instance of resolution_charts' existential witness, + the stratum tag):
--   ι : Type, [Fintype ι]            -- the root-to-leaf PATHS of the pivot tree (the leaves)
--   d : ι → ℕ                        -- per-path chart dimension (# exceptional + free coords)
--   k h : (i:ι) → Fin (d i) → ℕ      -- per-path monomial exponents (k = F-vanishing, h = Jacobian)
--   stratum : ι → (Fin L → ℕ)        -- the rank stratum the path's BINDING (min-codim) center cuts

structure IsResolutionAtlas (M : Fin (L+1) → ℕ)
    (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i:ι) → Fin (d i) → ℕ)
    (stratum : ι → (Fin L → ℕ)) : Prop where
  /-- (A) admissibility: every path's binding center is an admissible rank stratum (codim = Mval). -/
  stratum_admissible : ∀ i, stratum i ∈ Adm M
  /-- (S) SURJECTIVITY = EXHAUSTIVENESS (the residual real work): every admissible stratum is reached
      by some path. ⟹ no missed branch ⟹ ⨅ not an over-estimate. -/
  stratum_surjective : ∀ T ∈ Adm M, ∃ i, stratum i = T
  /-- (K) multiplicity-1 on every exceptional divisor (multilinearity, #132): k_E = 1. -/
  mult_one : ∀ i, ∀ j : Fin (d i), k i j = 1
  /-- (C) per-path codim-match: the path's monomial threshold = ½·(its binding stratum's codim).
      [⨅_j axisRatio (h i j)(k i j) = ½·Mval, the binding divisor (k=1, h=Mval−1) realising c/2.] -/
  threshold_eq : ∀ i, monomialThreshold (d i) (k i) (h i)
                        = (1 / 2 : ℝ≥0∞) * ((Mval M (stratum i)).toNat : ℝ≥0∞)

/-- THE CONSEQUENCE `resolution_charts` consumes (proof = pure ⨅-rearrangement; STATEMENT here). -/
theorem resolution_value_of_atlas (M : Fin (L+1) → ℕ)
    (ι : Type) [Fintype ι] (d : ι → ℕ) (k h : (i:ι) → Fin (d i) → ℕ) (stratum : ι → (Fin L → ℕ))
    (hatlas : IsResolutionAtlas M ι d k h stratum) :
    (⨅ i : ι, monomialThreshold (d i) (k i) (h i)) = ENNReal.ofReal (lambdaCore M) := by
  sorry  -- STATEMENT ONLY
```

### Why `resolution_value_of_atlas` follows (the assembly, for the formaliser)
`⨅_i monomialThreshold (d i)(k i)(h i)`
`= ⨅_i ½·(Mval M (stratum i)).toNat`            — `threshold_eq` (C)
`= ½·⨅_i (Mval M (stratum i)).toNat`            — `⨅` commutes with the constant `½` (ENNReal)
`= ½·⨅_{T ∈ Adm M} (Mval M T).toNat`            — `stratum_admissible` (A: image ⊆ Adm) +
                                                  `stratum_surjective` (S: image ⊇ Adm) ⟹ image = Adm M
`= ½·(Adm M).inf' Mval`  `= ofReal (lambdaCore M)` — `lambdaCore` def + `Mval_nonneg` (toNat↔ℤ on Adm).
The `min`-over-image = `min`-over-`Adm` step is EXACTLY where surjectivity (S) bites: without it the
image could be a proper subset missing the minimiser, making `⨅` too big (an over-estimate — the
incomplete-cover failure). `mult_one` (K) is what makes `threshold_eq`'s `½·codim` honest (no `x^k`/`(x²+y²)²`
deflation); it is used inside the proof of (C), or stated alongside as the certificate that (C)'s ratio is
the regular-sequence value.

## Per-conjunct status (what each rests on — caveats next to the claim)
| conjunct | content | status / source |
|---|---|---|
| `stratum_admissible` (A) | every center ∈ Adm M (recursion pivots only on `{∏C=0}`) | structural; Codex #132 fact 2 — cheap once stated |
| `stratum_surjective` (S) | every admissible stratum reached by some path | **THE residual real work** — the combinatorial core (below) |
| `mult_one` (K) | `k_E = 1` on every divisor | #132 multilinearity (`F = x²·reduced`) — exact-algebra certified |
| `threshold_eq` (C) | path threshold `= ½·Mval(stratum)` | #131 (Schur `S=D−ba`, `codim S(t)=Mval(t)`) + `axisRatio_regularSeq` (green) + `monomial_rlct` (S2) |

So three of four conjuncts are certified/structural; **(S) surjectivity is the single residual** — the
"branch set ⊇ admissible-rank-stratum set" claim.

## (S) — the residual, stated for its eventual proof
The pivot tree's branch at level `s` is the **resolved rank** of the active factor (which minor is the
nonzero pivot). A root-to-leaf path's `stratum` is the tuple of per-level resolved ranks (its binding
center). (S) says: for every admissible `T ∈ Adm M`, some path resolves exactly the ranks `T`. This is
the statement that the recursion's rank-resolution choices **enumerate** the admissible cone — equivalently
(Gabriel / type-A), that every rank pattern of `{∏C=0}` arises from some sequence of pivot/minor choices.
This is where `Core.RankPattern` (the cumul↔diff rank-pattern bijection, Prop 3.1) and `Core.OrbitKostant`
/ `Core.RankLocusClosed` are the natural proof carriers: the rank strata of `{∏C=0}` are indexed by the
nested rank patterns, and the blow-up's pivot choices realise each. The DANGER (S) rules out: a "missed
branch" — an admissible `T` with no path — which would drop a stratum from the `⨅`-image and over-estimate.

## Scope note (keep the levels separate — CLAUDE.md precision)
`resolution_charts` / this obligation is **core-only** (`rlctAtOn(dlnLoss M 0) 0`, `M = H − r` the reduced
widths). The regular `[−r²+r(H⁰+Hᴸ)]/2` shift is L2/Fubini (`product_reduction`), NOT here. `IsResolutionAtlas`
carries no `nReg` — it is purely the singular-core value-match `⨅ = ofReal(lambdaCore M)`. Do not fold the
regular shift in; `aoyagiLambda` assembles the two via `deepest_point_reduction` + `product_reduction`
downstream.

## Most likely thing to break this
The `threshold_eq` (C) statement uses `monomialThreshold = ½·Mval(stratum)` as an EQUALITY per path. The
honest per-path fact is `monomialThreshold_i = ½·(min codim of centers ALONG path i)`, and `stratum i`
must be DEFINED as that binding (min-codim) center — not the leaf rank tuple — for the equality to hold.
If `stratum` is mis-defined as the leaf (terminal rank-0 tuple) rather than the binding center, (C) is
false (the leaf codim ≠ the path's threshold). The card defines `stratum` = the binding center; the
formaliser must thread that definition. (Alternatively, weaken (C) to `≥ ½·min_t Mval` per path + a single
`∃ path achieving = ½·min_t Mval`; that also closes `resolution_value_of_atlas` and is laxer on `stratum`.)

## Next
Hand `IsResolutionAtlas` + `resolution_value_of_atlas` (statements) to the formaliser as the R1.6 target;
the three certified/structural conjuncts (A,K,C) wire from #131/#132 + green lemmas, and (S) surjectivity
is the combinatorial core to prove via `Core.RankPattern`/Gabriel. Decorrelation: this is a single-model
(pp) statement-design pass over the existing Lean types; the Codex leg on the *math* (route + 5 hinges)
already ran in #132 (converged) — a Codex pass on the *statement shape* is optional belt-and-suspenders,
not gating (the statement is mechanical given #131/#132). Builds on #132 (the 5 hinges), #131 (ideal-membership
/ codim), `Foundations/Lambda.lean` (`Adm`/`Mval`/`lambdaCore`), `Skeleton.lean` (`resolution_charts`,
`axisRatio`, `monomialThreshold`), `Core.RankPattern` (the proof carrier for (S)).
Scripts: `g133_*` in `g129-scripts/`.
