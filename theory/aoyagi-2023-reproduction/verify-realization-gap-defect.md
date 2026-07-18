# Verified read-off defect #4: not every admissible stratum is realized (the realization gap)

**Status: VERIFIED DEFECT (2026-07-19) — the recursion's t̃=0 leaf-profile set is a PROPER subset
of the admissible set at interior-bottleneck widths; the λ formula (min over Adm) SURVIVES because
every minimizer is realized. Never state "profile-set ⊇ Adm" or "== Adm" for the recursion.**

## The defect
The read-off (p.22) takes the minimum of `Mval` over the admissible strata `Adm(M)`, implicitly
treating every admissible profile as appearing among the recursion's t̃=0 leaf divisors. That
implicit stratum-completeness is FALSE (in the corrected FIX-A form of the recursion, and the
obstruction is chooser- and branch-independent — the nondeterministic tree fails it too):

- Witness `M = (3,3,4,2,3)`: profiles `(2,2,2,0)` and `(3,2,2,0)` are in `Adm(M)` but are NEVER
  realized at t̃=0 — the corresponding divisors sit at level `2 = r_4` (the running-min width at
  layer 4), and a layer clears only levels strictly below its running min (`occ_above` tops at
  `r_S − 1`), so they are stranded at t̃=2 forever ("running-min saturation freezing").
- Scope: NOT a corner case — `P(M) ⊊ Adm(M)` in 84/351 instances (widths ≤ 3, L ≤ 4), exactly
  the interior-bottleneck widths; the mechanism coincides (0 mismatch / 791 instances) with the
  p.15 full-chain defect's width-drop stranding (`verify-p15-fullchain-defect.md`) — one
  mechanism, two faces.

## The corrected statement (exact characterization)
`P(M) = { a ∈ Adm(M) : Clearable(a) }`, where `Clearable(a)` := every strict descent after the
birth layer starts below the running min (`a^{S−1} < r_S` whenever `a^S < a^{S−1}`, `S > b(a)`).
Two-way verified: exact recursion over 847 instances (0 counterexamples, both inclusions) + an
independent Codex derivation with the hypothesis withheld. The ⊇ half is witnessed by an explicit
state-free steering rule and an anchor descent invariant; the ⊆ half by the `occ_above` range
obstruction. Cert: `expeditions/2026-07-17-aoyagi-engine/threads/12-realization/
cert-o5-realization.md` (+ battery + Codex artifacts alongside).

## What survives (why the paper's theorem stands)
The read-off VALUE is unaffected: **every `Mval`-minimizer is Clearable, hence realized.**
Envelope-splice argument (cert §3): the running-min-envelope prefix contributes exactly 0 to
`Mval`, so replacing a non-clearable profile's prefix (which is non-envelope at its first bad
descent, hence contributes > 0) by the envelope produces an admissible sibling with strictly
smaller `Mval`, leaving all terms from the bad descent onward unchanged. Hence
`min over P(M) = min over Adm(M)` via the bridge: `P ⊆ Adm` (proven in Lean, `leaf_mem_Adm`) +
`minAdm ∈ P` (the certified minimizer-realization). Cross-checked at all 847 instances.

## Consequence for the Lean engine
- `IsFullMonomialization` / the assembly must NOT carry a `⊇ Adm` or `== Adm` conjunct
  (hold order, expedition journal tick 148). The o5-∈ target is `minAdm ∈ terminalExponents`.
- `terminalExponents` stays t̃=0-restricted: the stranded strata live at t̃ > 0, and an
  unrestricted `∀ k` quantifier re-admits them (companion fact in
  `verify-case2-rawwidth-defect.md`; fork 12(b)(ii)).
- The full `⊇ Clearable-Adm` completeness (the strongest true statement) is certified and
  formalisable, sequenced post-critical-path.

## How it was missed, then found
The four pre-committed kill instances ((2,2,2), (3,3,4), (2,2,2,2), (2,2,3,2)) are ALL
bottleneck-free — `P = Adm` there — so the `== Adm` battery kill sat green while the general
claim was false (the shallow-instance confound, second occurrence in this expedition; lesson:
pre-committed battery sets must include the known failure mechanism, here width-drop/interior
bottleneck). Found by the o5-∈ realization certificate's scoped scan (widths ≤ 4, L ≤ 5, exact
recursion, cross-validated against the original validated simulator).
