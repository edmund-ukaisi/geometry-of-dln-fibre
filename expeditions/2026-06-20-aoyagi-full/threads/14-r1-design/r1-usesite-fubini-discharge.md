# R1 use-site discharges the abstract S1Fubini hyps — confirmation + 2 obligations

- **Seat:** `pp` (design). **Read-only; /tmp scratch; no Lean.** Task #11.
- **Context:** S1Fubini adopted in ABSTRACT-CORE form: `rlctAt(Σxᵢ² + core, w) = n/2 + rlctAt(core, w)`
  with `core`'s threshold + `hGne` (core ≥0, ≢0 a.e.) + `hcore_top` (divergence above threshold) as
  HYPOTHESES. This relocates the monomial+S2 obligation to R1's per-chart use-site. Verdict: **CLEAN,
  with TWO concrete obligations the use-site must include** (pp + decorrelated Codex, identical).

## Sub-check 1 — chart core in S2's domain: CLEAN with ONE obligation (the main one)

R1's resolution gives, per chart, `core∘φ = unit·∏_j |y_j|^{2k_j}` (monomial × NONVANISHING UNIT) and
Jacobian weight `unit'·∏_j |y_j|^{h_j}` — **NOT a pure monomial.** S2 (`monomial_rlct`, pure monomial)
does **NOT apply verbatim.** **OBLIGATION 1 (the main hidden gap, both flag it):** absorb the units
FIRST via the bounded-unit comparability `rlctAt(unit·G, unit'·w) = rlctAt(G, w)` (on a shrunk chart
`unit, unit'` are continuous nonvanishing ⇒ bounded between positive constants ⇒ same convergence
threshold). This is the **`rlct_unit_invariant`** lemma ALREADY in Skeleton (S1-level). With units
absorbed, S2 applies to the pure monomial. *Caveat (Codex):* if `unit` has zeros it is not a unit and
the normal-crossing data is incomplete — R1's construction must guarantee genuine nonvanishing units
(it does: the resolution's `unit_i` are nonvanishing by construction, design-doc §2/§6).

## Sub-check 2 — hGne + hcore_top: CLEAN, with ONE subtlety on the endpoint

- **hGne** (core ≥0, ≢0 a.e.): holds for the monomial. All-`k_j=0` gives `core∘φ = unit` (≡ a nonzero
  unit, NOT ≡0), so hGne still holds; that chart is nonsingular (rlct=⊤), `{core=0}` doesn't meet it,
  and it DROPS OUT of the min — harmless. A genuinely ≡0 chart would fail hGne, but the
  principalization produces none on the full-dim cover (flag: R1 must ensure no ≡0 chart, or discard).
- **hcore_top** (divergence above threshold): **OBLIGATION 2 / subtlety.** For STRICT `c' > λ` it
  follows order-theoretically from `λ = sSup(admissible-c)` + the admissible set being a DOWN-SET
  (monotonicity of `|G|^{−c'}` in `c'`) — NOT a separate analytic fact. BUT **divergence AT the
  endpoint `c' = λ` is NOT automatic from the sSup value** — it needs the endpoint/lintegral bridge
  (for the monomial: `∫|y|^{h−2kλ} = ∫|y|^{−1} = ∞` at the threshold). So: **check what `hcore_top`
  literally asks.** If strict-above (`c'>λ`), it's FREE from the sSup down-set property. If it asks
  `≥λ` or literal `∫=∞` AT λ, the use-site needs the small endpoint divergence fact (the monomial
  `∫|y|^{−1}=∞`, S2-adjacent). Flag for fm-2/fm: pin `hcore_top`'s exact form.

## Sub-check 3 — composition with the cover (min over charts): CLEAN

`n = r(H¹+H^{L+1}) − r²` is FIXED by the rank-r reduction (L2/Thm-3), UPSTREAM of the core
resolution. R1's core charts act only on the core (`M⁽ˢ⁾`-block) variables, varying the `y`-exponents
`(k,h)`, NOT `n`. So `n` is **chart-independent** ⟹ `min_chart(n/2 + λ_chart) = n/2 + min_chart λ_chart
= n/2 + λ_core`. Clean factorisation. GAP only if the cover mixed different rank-reductions / regular-
core splittings (it does not — one reduction, then resolve the core). ✓

## Sub-check 4 — relocation matching: CLEAN if all match (pp + Codex list identically)

The relocation is clean iff: (a) the S1 weight `w` = the chart Jacobian weight used in S2; (b)
`core_chart` and `w` live on the SAME `y`-variables the Fubini integrates; (c) the full chart loss is
EXACTLY `Σxᵢ² + core_chart` (the regular `x`-block + the core `y`-block, disjoint); (d) units absorbed
(obligation 1); (e) the quadratic `x`-block is independent of the resolution chart (it is — `n` fixed
upstream). All hold for R1 by construction; the one thing to NOT gloss is (d).

## NET — confirmed CLEAN, two obligations the use-site MUST include

R1's per-chart use-site DOES cleanly discharge S1Fubini's hyps, with:
1. **OBLIGATION 1 (unit absorption):** apply `rlct_unit_invariant` to strip the chart's nonvanishing
   `unit`/`unit'` BEFORE invoking S2 — else S2 is applied to `unit·monomial` (the main hidden gap).
   Lemma already exists (S1-level).
2. **OBLIGATION 2 (hcore_top endpoint):** if `hcore_top` asks strict-above, it's free from the sSup
   down-set property; if it asks `≥λ`/literal `∫=∞` at λ, add the monomial endpoint divergence fact.
   Pin `hcore_top`'s exact statement with fm-2.
Both are light and local; neither is a redesign. This confirms (A) the abstract S1Fubini form is sound
to relocate, and sharpens R1.2 (the per-chart S2 invocation must route through unit-absorption) and
R1.5 (the min-over-charts factorises because `n` is upstream-fixed). No hidden gap that breaks the
architecture; the two obligations are the price of the abstract form, and both are already-in-hand or
trivial.
