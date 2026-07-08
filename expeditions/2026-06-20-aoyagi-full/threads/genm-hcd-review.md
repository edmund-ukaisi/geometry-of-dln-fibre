# Fidelity review — hcd (Producer-1 diffeo-triple leaf #3, `genm-hcd`)

**Reviewer:** `revhcd` (decorrelated Codex xhigh). **Verdict: clean PASS all 4 dims — hcd banked as reviewed.**
Target: `DeepestPsiHcdGen.lean` @ `60da628d`. Reviewed 2026-07-08. (Recorded by controller — reviewer's worktree
writes don't reach canonical.) **This completes the fully-reviewed Producer-1 diffeo triple (hraw0 + hderiv0 + hcd).**

## Per-dimension
1. **FIDELITY / CONSUMER-MATCH — PASS (token-level identical).** Consumer `contDiff_deepestPsiCutRaw`/
   `contDiff_deepestPsiFlatCut` (`DeepestPsiFlatCutGen.lean:64-69,100-107`) demand `hcd : ∀ q ∈ tsupport (fun y =>
   ((χ y:ℝ))), ContDiffAt ℝ (⊤:ℕ∞) (fun q => psiSplitRaw q − q) q`, χ : ContDiffBump 0. `hcd_psiSplitRawGen` (:734-738)
   is that EXACTLY with `psiSplitRaw := psiSplitRawGen H r hr hL J Pf Qf` — same `tsupport` token, same `⊤` (=∞), same
   `·−·`, same χ type. `psiSplitRawGen` is the real joint move (repacks the 4 psiReadBlk blocks; image = movedC(...)),
   NOT identity. Codex: MATCH.
2. **hχ HONESTY — PASS (genuine, not laundering).** `psiInvBundle` = det≠0 of the 3 families (chain-corner /
   partProd-corner / nMix), consumed only as `hdet` inputs to `contDiffAt_ringInverse_entry` (whose signature REQUIRES
   `(M x).det ≠ 0` — matrix inverse is ContDiffAt only on the invertible locus). Det-nonzero is strictly WEAKER than
   the ContDiffAt conclusion; smoothness comes from the independent 20-lemma entrywise ladder. `Ring.inverse` is total
   (=0 off units) ⟹ outside the region the deviation is genuinely non-smooth (1/t-type) ⟹ hχ does real work. Codex:
   HONEST.
3. **NON-VACUITY — PASS.** `psiInvBundle_zero` (:750, given `hJfront`): bundle holds at 0 (all 3 families = 1).
   `eventually_psiInvBundle` (:769): `∀ᶠ q in 𝓝 0` via det-continuity + finite-range ∀k + trivial tail. Region = a
   genuine non-empty nbhd of 0.
4. **BUILD — PASS.** Independent worktree @60da628d; forced `#print axioms` on hcd_psiSplitRawGen /
   contDiffAt_psiSplitDeltaGen_at / eventually_psiInvBundle = clean-three, no sorryAx (psiInvBundle_zero transitively).
   Target file 0 sorry. (Library sorries elsewhere — incl. `deepest_gauge_construction` — are OFF hcd's transitive
   closure.)

## Deferred-wiring caveat (CONTROLLER action at the "=" assembly — not an hcd defect)
`eventually_psiInvBundle` (∀ᶠ q in 𝓝 0) alone does NOT discharge `hχ` for a PRE-CHOSEN χ. The Producer-1 top-level
"=" assembly (wiring the diffeo triple into `deepestPsiFlatCut`'s `hcontdiff`) must PICK a small-radius χ with
`tsupport χ ⊆ region` — via `ContDiffBump.tsupport = closedBall center rOut`, choosing rOut small enough that the
closedBall sits in the invertibility region (from `eventually_psiInvBundle`). Legitimate deferred wiring. Also:
`hJfront` is an extra hyp on the two discharge lemmas (not on hcd_psiSplitRawGen / contDiffAt_psiSplitDeltaGen_at) —
honest (the nbhd-of-0 argument needs the canonical front embedding). **Remember this when doing the "=" assembly.**
