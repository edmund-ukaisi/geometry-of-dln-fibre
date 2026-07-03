# Do the last two headline walls UNIFY? — D1 ≥-leg blow-up vs R1-UPPER box-finiteness (genm-wallunify-pnp)

Read-only pen-and-paper adjudication (aoyagi-full). Question: does Aoyagi's explicit Section-5 monomial
blow-up (which the D1 ≥-leg uses, computing `rlct = ½·codim` at the deepest point) YIELD R1-UPPER's
box-finiteness `RouteMBoxThresholdFinite` (equivalently `rlct ≥ ½·minAdm`)? Source read at canonical
`expeditions/2026-06-20-aoyagi-full/`; Aoyagi PDF `pdftotext -layout` → `/tmp/aoyagi-2024-dln.txt`
(line refs below); Lean objects read directly.

---

## VERDICT: WALLS-UNIFY (with a named, bounded finite-cover proviso).

**R1-UPPER box-finiteness IS the `≥`-leg (finiteness-below-threshold half) of Aoyagi's blow-up equality.**
It is NOT a separate analytic content from the blow-up — it is one of the two directions the blow-up
produces. An honest proof of Aoyagi's resolution equality `rlctAtOn(core) 0 = ⨅ monomialThreshold`
(Skeleton:1228 `resolution_charts`), done the standard chartwise way over an actual box neighbourhood,
**establishes R1-UPPER along the way**. The `hbox : RouteMBoxThresholdFinite` hypothesis is therefore
**provable by the same machinery** — it is moot as an *independent* wall, becoming a corollary of the
resolution.

The ONE genuine (bounded) residual that keeps it from being a pure `rfl`-consequence: A's exact-value
statement is *pointwise at the origin*, whereas B (box finiteness) needs the resolution atlas to give a
**finite cover of the whole box**, so `∫_box |F|^{−c'}` is a *finite sum* of chart-monomial integrals with
unit factors uniformly bounded away from 0/∞. This finite-cover bookkeeping is standard resolution theory
(not new mathematics), and — decisively — it is **already the exact shape of the current Lean `cover_le`
field** (see §3). So it is not a wall; it is the assembly the from-scratch `RouteMBoxThresholdFinite` was
independently trying to build the hard way.

The precise correction this forces to the Items-115/116 framing: R1-UPPER is NOT a *separate* research
wall requiring a *new* "simultaneous rank-flag blow-up." The simultaneous rank-flag blow-up it needs **IS
Aoyagi's Section-5 recursive blow-up** — the D1 machinery. Items 115/116 correctly diagnosed that the
*two-matrix Schur corank recursion* cannot reach the `½·minAdm` sum-staircase; the true resolution is
Aoyagi's, which the D1-de-risk threads already validated as uniform-in-`v` and bounded.

---

## 1. The object identities (the crux, all confirmed)

### R1-UPPER = the `≥`-leg of the RLCT at the deepest point

Aoyagi Def 1 (`/tmp/aoyagi-2024-dln.txt:369-390`) and the Lean `rlctAt` (`Rlct.lean:71`) are the SAME
object: `λ(F) at w* = sSup{ c' : ∫_U |F|^{−c'}φ < ∞ }`. Hence, at the deepest point (origin), definitionally:

- `rlctAt ≥ ½·codim` ⟺ every `c' < ½·codim` has `∫_U |F|^{−c'} < ∞` ⟺ **`RouteMBoxThresholdFinite`**
  (`RouteMBoxReduction.lean:165`: `∀ c' < ½·minAdm, routeMLayerBoxIntegral M c' 1 < ⊤`).
- `rlctAt ≤ ½·codim` ⟺ `∫_U |F|^{−c'} = ∞` for `c' > ½·codim` ⟺ the **box-divergence achiever**
  (`RouteMLayerCoverGE.routeMCore_box_diverges_achiever`, the `hdiv` atom).

So the file *name* "R1-UPPER" (the upper leg of the hfin **bound on the loss integral**) proves the
**LOWER** RLCT bound `rlct ≥ ½codim`. This direction-relabel is real and was already flagged by the
r1upper wall-review (fallback §): "the citation that delivers `rlct ≥ ½codim` is **Aoyagi's exact
`rlct = ½codim`**, NOT Watanabe's universal `rlct ≤ d/2` (wrong direction, wrong quantity)." My finding
sharpens it: it is not merely that the *citation* is Aoyagi — the *from-scratch* R1-UPPER is literally the
`≥`-half of Aoyagi's blow-up.

### A = Aoyagi's blow-up equality = `resolution_charts` (Skeleton:1228)

`resolution_charts` states exactly `rlctAtOn(core) 0 = ⨅_i monomialThreshold(d_i, k_i, h_i)` — the
finite resolution-chart family with monomial pullback + monomial Jacobian whose thresholds reconstruct the
core RLCT. This is the direct Lean transcription of Aoyagi Section 5: the recursive blow-up terminates
(S=L+1) in the **exact ideal equality** `⟨∏C^(s)⟩ = ⟨diag(b_1,…,b_M)⟩` (`:2338`, a normal-crossing form),
then "**Candidates for the log canonical threshold** … are `½·min{M_{s,k} : t̃_{s,k}=0}`" (`:2342-2350`) —
the standard monomial read-off.

## 2. Why the blow-up gives BOTH bounds (sub-question 1: YES)

A blow-up along a smooth submanifold is a **proper birational map, an isomorphism off a measure-zero
exceptional divisor**. The transported integral is an **exact change of variables** (with the explicit
Jacobian `∏ u_{s,k}^{M_{s,k}−1}`, `:1415-1454`), NOT an inequality:

    ∫ ‖∏C‖^{−c'} dc  =  ∫ ‖monomial‖^{−c'} · ∏|u|^{M−1} du   (on each chart, up to the unit factor).

In the normal-crossing coordinates the local integral `∫_{|u|<ε} ∏|u_j|^{−2k_j c'}·∏|u_j|^{h_j} du` is a
product of 1-D integrals `∫_0^ε u^{h_j − 2k_j c'} du`, which is **finite ⟺ `h_j − 2k_j c' > −1` ⟺
`c' < (h_j+1)/(2k_j)`** and **`= ∞` at/above**. The single monomial exponent decides *both* directions
simultaneously — this is precisely `monomialThreshold` + `monomialIntegrand_integrable_of_lt` (finiteness
below) and the sharp `∫_0^ε u^{−1} = ⊤` boundary divergence (`monomialIntegrand_lintegral_box_eq_top`,
above). Decorrelated Codex (xhigh, hypothesis withheld) independently: "BOTH-BOUNDS: YES — the same
normal-crossing form gives both finiteness for every `c' < ½min` and divergence when some `ν_i − cN_i ≤ 0`."

Theorem 4 (`:1282-1307`, the homogeneity/deepest-point comparison) is only needed to argue the *deepest
point is the global inf* over the fibre — it is a D1-scoping lemma, ORTHOGONAL to the both-bounds question.
For `RouteMBoxThresholdFinite` (stated at the origin box), the blow-up-at-the-origin gives the exact value
at the origin, both bounds, with no appeal to Theorem 4.

## 3. Architecture: R1-UPPER's box route is REPLACEABLE (sub-question 2: SUBSUMED)

The current L=2 assembly already treats the two legs as the two halves of ONE equality. `IsRouteMCover`
(`RouteMBridge.lean:47`) has exactly two analytic fields:

- **`cover_le`** (`:63`): `∫_U |F|^{−c'} ≤ C · Σ_i ∫_{unitBox} monomial_i`, `C < ⊤`. The box integral over
  the WHOLE neighbourhood `U` dominated by the **finite sum over ALL charts** `i`. This is exactly
  "finite-cover of the box" — and it is the field discharged by `hfin` = `RouteMBoxThresholdFinite` (=
  R1-UPPER).
- **`cover_ge_div`** (`:69`): `(∃ i, threshold_i ≤ c') → ∫_Ω |F|^{−c'} = ∞`. Needs just **ONE** diverging
  leaf. This is `hdiv` = the achiever.

`routeM_rlctAtOn_eq_iInf` (`:79-104`) assembles the **equality** `rlctAtOn F 0 = ⨅ monomialThreshold` by
`le_antisymm`: the `≤` direction from `cover_ge_div` (one branch), the `≥` direction from `cover_le` (whole
cover). `r1_resolution_interface_L2` (`R1ResolutionInterfaceL2.lean:76`) is then `rlctAtOn(core) 0 =
lambdaCore` via `routeMLayerCover_of_atoms hfin hdiv` + the value lane — i.e. the L=2 `resolution_charts`,
built out of the two box atoms.

**So `resolution_charts` (the unified Aoyagi blow-up equality) subsumes `RouteMBoxThresholdFinite`:**
proving `resolution_charts` *chartwise over the box* (the honest way) produces `cover_le` = the box
finiteness as its `≥`-half. The `hbox` hypothesis at `RouteMSchur.lean:426` becomes a corollary — moot as a
standalone wall. The ∀-L endgame should therefore be **ONE unified Aoyagi-blow-up build** producing
`resolution_charts` (⟹ `rlctAtOn = lambdaCore` both bounds), NOT a separate from-scratch box-finiteness via
the two-matrix Schur corank recursion.

## 4. The asymmetry that generated the "two walls" illusion (and why it dissolves)

The `≤`-leg (`hdiv`) and the `≥`-leg (`hfin`) draw on **different amounts** of the resolution — this is the
real content behind Items 115/116, sharpened:

- `≤`-leg / divergence: needs divergence along **ONE branch** — the minimum-threshold *achiever* leaf
  (`RouteMLayerCoverGE.lean:14`, "one diverging leaf suffices"). Its chart is **single-pivot** (`F = z²·U`,
  `|det Dφ| = |z|^{minAdm−1}`, one binding axis; smeared-derisk §3). A single Aoyagi blow-up branch.
- `≥`-leg / finiteness (R1-UPPER): needs the box integral finite **everywhere below threshold** ⟹ the
  **WHOLE cover** — all branches of the blow-up, so no direction of the box escapes to `∞`. This is the
  `[1,2,3]`-staircase-at-`(3,3,3,3)` phenomenon (r1upper wall-review): the finiteness must absorb the
  *sum* of per-boundary codims, which no single two-matrix step reaches.

The `RouteMLayerCoverGE.lean:37-44` docstring states the sharp reason the point-bound does NOT give either
box atom for free: `rlctAtOn ≤ t` (the squeeze) is an `sSup` bound constraining only `c' > t` strictly, and
does not decide the boundary. **Both box atoms need genuine chartwise integral estimates.** Aoyagi's blow-up
supplies BOTH (the whole atlas gives `cover_le`; any branch gives `cover_ge_div`) — so it is ONE object
delivering both, not two walls. The two-matrix Schur recursion (the *current* R1-UPPER route) reaches only
the min-boundary and thus walls at `(3,3,3,3)` — but that is a limitation of *that route*, not of the
finiteness itself, exactly as `genm-d1scope` found the D1 "Morse-Bott WALL" was an artefact of the wired
IFT-chart route, not of Aoyagi's actual argument.

## 5. Registers

- **Claim (load-bearing):** `RouteMBoxThresholdFinite M` (R1-UPPER) = the `cover_le` / `≥`-leg /
  finiteness-below-threshold half of Aoyagi's resolution equality `rlctAtOn(core) 0 = ⨅ monomialThreshold`
  (= `resolution_charts`, Skeleton:1228). It is subsumed by a chartwise proof of that equality; it is NOT a
  distinct analytic content. The ∀-L build should be ONE Aoyagi-blow-up producing `resolution_charts` both
  bounds; `hbox` at RouteMSchur:426 is then a corollary, moot as an independent wall.

- **Most likely to break the "unify" verdict (the honest proviso, bounded):** the finite-COVER-of-the-box
  bookkeeping. Aoyagi's read-off is *germ-level at the origin*; box finiteness needs `π⁻¹(box)` covered by
  **finitely many** normal-crossing charts with unit factors uniformly bounded above/below, so
  `∫_box |F|^{−c'}` is a *finite* sum of chart-monomial integrals (Codex-flagged residual-risk; = the Lean
  `cover_le` shape). If the recursive blow-up's chart family were *infinite* or the pullback of the box left
  the polydiscs, the sum could fail to be finite. It does NOT: the D1-uniform-derisk (`genm-d1uniform-aoyagi`)
  proved the `(S,J)` induction terminates in a **finite** chart family for every `M` (bounded lex measure
  `(S,J,#u)`), and each chart's pullback of a bounded parameter box stays in a polydisc (the substitutions
  `d = u·d'` are proper). So the proviso is a bounded assembly, not a wall — but it is the one thing a
  formaliser must MACHINE-CHECK to make "A ⟹ B" airtight (do NOT assume germ ⟹ box for free).

- **Next construction that would settle the open part:** state `resolution_charts` (or the L=2
  `r1_resolution_interface_L2`) so that its `≥`-direction *is* `cover_le`, and confirm the L=2 `cover_le`
  (`RouteMSchurRectCapB.lean:489`, general `(m,n,p)`) is exactly the finite-chart-sum bound the general-L
  Aoyagi atlas produces — i.e. verify the L=2 `cover_le` is the two-chart specialisation of the ∀-L
  Aoyagi-atlas `cover_le`, not a coincidence of the two-matrix corank recursion. If it is (expected), the
  ∀-L R1-UPPER is retired as a corollary of the one Aoyagi resolution build, and the endgame collapses from
  two efforts to one.

## Decorrelated Codex (xhigh→high, hypothesis withheld)
`codex/unify-answer.md` (+ `unify-q-sharp.md`, `unify-prompt.md`): independent first-principles read (no
code, no web, my conclusion withheld). Verdict matched: **(1) BOTH-BOUNDS YES** (same normal-crossing form
gives finiteness-below + divergence-above); **(2) B SUBSUMED in A** ("B is exactly the lower-bound half of
A, provided A is proved by the standard chartwise resolution over an actual box, not merely a germ-level
symbolic read-off"); **(3) residual-risk** = the finite-chart box cover with uniformly-bounded unit
factors. Codex independently surfaced the germ-vs-box proviso that is the load-bearing nuance of this
adjudication — full decorrelation on the verdict AND on the one caveat. (Two earlier consult attempts spun
on repo `grep` under `--sandbox read-only` from inside the repo tree; re-run from an isolated `/tmp` cwd
returned the clean answer — infra note, not substantive.)
