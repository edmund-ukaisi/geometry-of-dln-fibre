# General-corank N4 lift — the research-adjacent obstruction (STOP+report, 2026-06-28)

**Context.** The (3,3,4) depth-2 (corank-2) weld is CLOSED (`core_schur2_lt_top`, sorry-free, S2-free,
reviewed). The next charge is the ∀M N4 (`routeMCore_threshold_lt_top`) — the WellFounded-on-corank
recursion lifting the corank-2 weld to arbitrary corank. Before sinking a multi-hundred-line Lean build, I
assessed the general-corank step (decorrelated Codex xhigh + my own reading). **Verdict: genuine
research-adjacent obstruction, NOT laborious plumbing.** Reporting per the controller's STOP+decorrelate
instruction.

## Why corank-2 does NOT generalize by plumbing

The corank-2 weld TERMINATES the recursion in ONE step: after the N2b split (j=1),
`‖R·S‖² ≥ c₀·(‖(R·S)_row0‖² + ‖Sc·S_row1‖²)`, the residual `Sc` is **1×1 (a scalar)**, so
`‖Sc·S_row1‖² = Sc²·∑(S_row1)²` is ALSO a Morse leaf. Both pieces are Morse blocks → close directly. There
is **no genuine "recurse on the corank-1 core"** — corank-1 IS a Morse leaf. The recursion machinery is
never exercised at corank 2; corank-3 is where the corank-(r−1) Schur core is first a non-leaf and the
real recursion appears.

## The two sharp obstructions (Codex-confirmed, my reading concurs)

### O1 — the nested `j×j`-MINOR cover (new cover machinery, not in repo)
The cert §3 design covers the inner R-space by "`j×j`-minor-invertible open neighbourhoods — a nested
`argmaxCellOn` over the `j×j` MINORS of R". But the existing `argmaxCellOn`/`pivotBlowupOn` machinery
(`S1G5Charts`) only handles **coordinate functions** (`Fin N → ℝ`). The `j×j` minors are **degree-`j`
polynomials in the entries, not coordinates** — there is no "blow up the minor coordinate". Covering by
"which `j×j` minor is max-modulus" + the associated minor-normalized blow-up **Jacobian formula** is new
covering machinery (a maximal-minor-stays-bounded-away-from-zero lemma + its Jacobian) — sizeable
research/programming, NOT routine plumbing.

### O2 — the Sc-core pushforward (the SMALLEST sharp paper-first obstruction)
To recurse on `‖Sc·S_bot‖²` (Sc = `(r−1)×(r−1)`) via the corank-`(r−1)` inductive hypothesis, one would
treat Sc as a fresh `(r−1)×(r−1)` integration variable. But `Sc = M22 − M21·M11⁻¹·M12` is a **rational
(nonlinear) function of R's entries** — its "entries" are NOT free coordinates of the integration domain.
So the clean "fresh matrix" induction lacks a justified change-of-variables. What is needed is a
**pushforward density estimate**: on the minor-dominant chart, the law of `Sc(R)` (as R ranges over the
chart) dominates / is comparable to a free `(r−1)×(r−1)` matrix box, so that
`∫_R ‖Sc(R)·S_bot‖^{−2c'}` is controlled by the IH `∫_C ‖C·S_bot‖^{−2c'}` over a free C-box. This
inequality (Sc-pushforward ≼ free-matrix) is the **smallest sharp statement** that must be settled on
paper before Lean work continues. If it fails, the recursion plan breaks.

### What is NOT an obstruction (plumbing — settled)
- **S-row sharing**: the block-Gauss shear splits the top `j` rows from the bottom `r−j` rows,
  measure-preserving; disjoint after the shear (the existing corank-2 mechanism scales). Not the bottleneck.
- **Threshold arithmetic**: `r²/2` vs `(r−1)²/2 + j·p/2` (the Morse gain) closes formally; no analytic gap.
- The N2b split itself (`schur_minorPivot_split`) is general-`r`, PROVED.

## Recommendation

The two obstructions (O1 the minor-cover machinery, O2 the Sc-pushforward density) are **paper-first**: a
`pen-and-paper` seat (or decorrelated Codex) should adjudicate O2 (the Sc-pushforward inequality) — the
sharpest gate — and design O1 (the minor-dominant chart cover + its Jacobian) before a formaliser sinks
the Lean build. The corank-2 weld stands as the validated base case; the general-corank inductive STEP is
the genuine new mathematics.

**Suggested first paper-step (Codex's): on each chart where a fixed `j×j` minor is dominant, prove the
Jacobian + Schur-complement bounds admit constants independent of the remaining entries.** If that fails,
the recursion plan breaks; if it holds, design the Lean "minor-dominant chart" cover interface, then port
the corank-2 machinery onto it. Validate at corank-3 (one dominant `2×2` minor) first.

## Status of the Lean (banked, this is a clean handback)
`RouteMSchurDepth2` has the FULL corank-2 weld sorry-free, axiom-clean, reviewed (`core_schur2_lt_top` +
all support). The general-corank lift is NOT started in Lean (would be premature given O1/O2). Branch
`genm-recstep-wt`, merged with the integrated depth-2 weld.
