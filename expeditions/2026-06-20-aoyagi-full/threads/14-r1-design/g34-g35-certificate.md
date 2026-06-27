# G3.4 cover-exhaustiveness + G3.5 chart↔value seam — CERTIFICATE (pp-hall, 2026-06-21)

**Task #115 (route-before-lines for #113).** Validate decorrelated (pp-hall + Codex) the two #113
back-half spots on the first non-trivial general-M cases, before fm sinks #113 lines:
- **(G3.4)** does the pivot-branch × affine-minor chart family COVER a nbhd of `0 ∩ {core=0}` for
  GENERAL M (exhaustiveness — rule out ALL strata, not just (2,2,2)'s 24 leaves)?
- **(G3.5)** does the chart-exponent min REALISE `½·min_t Mval` for general M — is the binding
  monomialThreshold the A1 achiever's (the chart↔value seam — where R1's value could need A1)?

**Verdict: BOTH SOUND.** G3.4 cover-exhaustive; G3.5 chart-value match holds and is INDEPENDENT of the
A1 arithmetic. One honest scope-condition flagged (the load-bearing hypothesis the formaliser must
respect). Two decorrelated legs converged: pp-hall exact algebra + Codex (xhigh, hypothesis withheld).

## The load-bearing identity (exact, verified all test cases): codim S(t) = Mval(t)
The stratum `S(t) = {rank(C^(1)···C^(j)) = t_j}` (with `t_L=0` on `{prod=0}`) has GEOMETRIC codimension
EXACTLY `Mval(t) = Σ_{j=1}^L (t_{j-1}−t_j)(M^{j+1}−t_j)` (`t_0:=M¹`). Verified by the rank-locus
dimension formula (`g35_codim_general.py`, `g35_generic_stratum.py`) for L=2:
`(2,2,2),(3,3,3),(3,2,3),(4,3,2),(2,3,2)` — all `codim = Mval`, square and non-square; and the L=3
lattice `(2,2,2,2),(3,3,3,3)` matches the Lean `aoyagiLambda` ground truth (`g35_L3_check.py`). This is
the bridge that makes the resolution's divisor ratios = `Mval(t)/2`.

(Subtlety caught, not papered over: the *generator-Jacobian rank* of the product entries CAPS at
`#prod entries` and undershoots `Mval(t)` at deep strata of "thin" products — e.g. (4,3,2) origin:
gen-Jac-rank 8 but `Mval=12`. The geometric *dimension-count* codim, not the naive generator-Jacobian,
is the right invariant; the dim-count gives `codim = Mval` cleanly, `g35_432_interp.py`.)

## G3.4 — COVER-EXHAUSTIVE
- **Partition (FACT).** `t_j = rank(C^(1)···C^(j))` is a well-defined, weakly-decreasing function on
  `{prod=0}` with `t_L=0`; every fibre point has a unique admissible rank vector `t`. So
  `{prod=0} = ⊔_t S(t)` (disjoint, EXACT — not just up to null). For (3,3,3): the 4 strata `t_1∈{0,1,2,3}`
  partition `{A1A2=0}` (numerically confirmed, 20000 samples all land in `t_1∈{0,1,2,3}`,
  `g34_tree_333.py`). Conversely every admissible `t` is realised (nested image subspaces + lift).
- **Atlas reaches every stratum (INFERENCE, both legs).** At a point of `S(t)`, each nonzero partial
  rank `t_j` has SOME nonzero `t_j`-minor; the FULL pivot atlas (all minors / all flag charts, NOT one
  fixed pivot) selects those pivots, and the verified Schur recursion (#109) gives the smaller tail-chain
  with the tail rank vector. Induction over the recursion ⟹ a branch reaches each `S(t)`. A single fixed
  pivot chart WOULD miss pieces; the full atlas does not.

## G3.5 — chart↔value seam, SOUND (every divisor ratio ≥ ½·min_Adm Mval, binding = achiever)
Write `m0 := min_Adm Mval`. The lower bound `rlctAt ≥ ½·m0` needs every divisor ratio `≥ m0/2`. There
are exactly two divisor families; both clear:

**(A) stratum-divisors** — blowing up `S(t)` (codim `Mval(t)`) gives `(k,h)=(1, Mval(t)−1)`, ratio
`Mval(t)/2 ≥ m0/2`. min over these = `m0/2` by definition. ✓

**(B) terminal residual smooth-block cone-divisors** — a leaf bottoming in a nondegenerate
`x_1²+…+x_n²` gives ratio `n_block/2`. **`n_block = Mval(t_leaf)` for the branch's admissible terminal
rank vector** (the FULL accumulated transverse quadratic block, not a leftover) ⟹ `n_block ≥ m0` ⟹ ratio
`≥ m0/2`. ✓ Anchored on (2,2,2): the δ-branch block `n_block=4 = Mval(0,0)`, ratio 2 ≥ binding 3/2
(`g35_recheck_222`-data). **CAVEAT (both legs flag independently):** this is the FULL terminal block —
counting only a *last local smooth summand* would be the WRONG object and need NOT be `≥ m0`. The
formaliser must take the full transverse block (Option A monomializes it; Option B = `smoothBlockND`
gives `n_block/2` directly).

**No intermediate divisor < m0/2 (SOUND, conditional).** Every blow-up center lies in `{prod=0}` ⟹ is
an admissible stratum (`t_L=0`) ⟹ codim `= Mval(t) ≥ m0` (the lower-bound-crux SETTLED in
r1-general-atlas + reconfirmed here). Non-admissible rank vectors give empty rank conditions; pivot
boundaries are outside the chart or belong to lower-rank admissible strata covered by other branches.
The condition: **the resolution inserts NO auxiliary blow-up unidentified with an admissible stratum or
a terminal smooth block** — this IS the flag-resolution / G3.2 strict-transform discipline (#109
witness-confirmed). If an implementation inserted a center off the stratification, that would be a proof
gap — so the formaliser must keep every center a strict transform of an admissible rank stratum.

**Binding = the A1 achiever, and it does NOT need A1 (the seam answer).** Pick an achiever `t*` with
`Mval(t*)=m0` (the GENERIC / largest stratum — verified: the min-Mval stratum is the min-codim one,
`g35_generic_stratum.py`). By G3.4 a branch reaches `S(t*)`; its divisor ratio `= m0/2`. By (A)+(B) no
divisor is smaller ⟹ `⨅ monomialThreshold = ½·min_Adm Mval` EXACTLY. **This chart-value match is a
resolution-plus-Mval fact; the separate A1/Aoyagi arithmetic (`lambdaCore = clean closed form`) is NOT
needed for it** — A1 is an independent confirmation of the same number, not a dependency of the chart
computation. (So R1's value does NOT secretly require A1; they meet only at the final equality
`½·min_Adm Mval = lambdaCore`, which IS A1's job, kept separate.) For (3,3,3): both `S(1,0)`,`S(2,0)`
attain `Mval=7`, binding ratio `7/2` (two achievers — relevant to θ, the order count).

## The first non-trivial general-M cases (exact, all confirm)
| M | strata (codim=Mval) | min_Adm | lambdaCore | achievers | stresses |
|---|---|---|---|---|---|
| (3,3,3) | S(0,0)=9, S(1,0)=7, S(2,0)=7, S(3,0)=9 | 7 | 7/2 | (1,0),(2,0) | **two achievers**, multi-stratum |
| (3,2,3) | 6,5,6 | 5 | 5/2 | (1,0) | non-square middle, single achiever |
| (4,3,2) | 12,8,6,6 | 6 | 3 | (2,0),(3,0) | **deep achiever** (not the first stratum), thin product |
| (2,3,2) | 6,4,4 | 4 | 2 | (1,0),(2,0) | wide middle |

The achiever-local rlct = `½·codim(achiever)` directly: at a generic achiever point, `{prod=0}` is a
SMOOTH codim-`m0` complete intersection ⟹ local rlct `m0/2` (verified (3,3,3): gen-Jac-rank 7 ⟹
`rlctAtOn = 7/2`, `g35_smooth_point_rlct.py`). The deepest point (origin) has the LARGER codim
(`Mval(0,…)`), so its OWN local depth exceeds `m0/2` — but `rlctAtOn(core) 0 = m0/2` because the
binding exceptional resolves the achiever stratum, which is in the origin's closure (the fibre core is a
cone). Consistent with the D1 reading (#112): the origin is not the min-local-rlct point, but the
resolution AT the origin sees the achiever's binding divisor.

## Net for the route-before-lines gate (#113)
G3.4 + G3.5 are **construction, not open math** — the cover is exhaustive, every divisor ratio
`≥ ½·min_Adm Mval`, the binding is the achiever, and the chart-value match is A1-independent. The
formaliser may proceed on #113's back half, carrying **three load-bearing conditions** into the lines:
1. **Full pivot atlas** (all minors / flag charts), not one fixed pivot — else strata are missed (G3.4).
2. **Full terminal residual block** (`n_block = Mval(t_leaf)`), not a last local summand — else the
   block-ratio bound `≥ m0/2` can fail (G3.5(i)).
3. **Every center an admissible-stratum strict transform** (the G3.2 #109 discipline) — no auxiliary
   off-stratification blow-up, else an intermediate divisor could undercut (G3.5(ii)).
With these, `rlctAtOn(core) 0 = ⨅ monomialThreshold = ½·min_Adm Mval`, the lower bound is sound, and
the A1 bridge `½·min_Adm Mval = lambdaCore` stays a separate (already-done) seam. **GATE: GO.**

Decorrelation: pp-hall exact algebra (10 scripts in `g34-g35-scripts/`: strata lattice, codim=Mval all
cases L=2+L=3, generic-stratum=achiever, smooth-point rlct, the sub-block worry + its resolution) +
Codex xhigh (independent, hypothesis withheld: G3.4 EXHAUSTIVE, G3.5(i)(ii)(iii) SOUND, the SAME
full-block caveat, the SAME A1-independence). Converged. Consult banked at
`codex/g34-g35-{prompt,answer}.md`.
