# P2.c Codex consult — cocycle proof vet + triple-cocycle scoping

Decorrelated second-opinion (gpt-5.x, `xhigh`) fired during the P2.c crux rung.

- `cocycle-prompt.md` — the contract: (A) vet the landed 2-fold round-trip proof, (B) adjudicate
  whether the target-side triple cocycle is within this rung's reach.
- `cocycle-answer.md` — Codex's reply.

## Verdicts (Codex, decorrelated — matched the thread's own analysis)

- **(A) Landed proof: SOUND.** No implicit-arg weakening — the identity elaborates on
  `targetChartLoc C D ≃ₐ[k] targetChartLoc C D`, so `AlgEquiv.refl (R := k)` carries the intended type;
  statement faithful. Only "fragility" is dependence on `overlapTransition`'s parenthesization + rewrite
  order — by-design (the parenthesization was fixed in P2.b for exactly this collapse), not a correctness
  concern.
- **(B) Target-side TRIPLE cocycle: NEEDS-NEW-SUBLIBRARY → scope out.** The raw composite
  `overlapTransition D E ∘ overlapTransition C D` is ILL-TYPED (codomain `targetChartLoc D C` ≠ domain
  `targetChartLoc D E`); the triple cocycle is only meaningful after restricting all three 2-fold
  transitions to the common triple overlap `D(C)∩D(D)∩D(E)`. The base side avoids this by living on
  `awayTriple` at a single submonoid throughout; there is NO target-side `awayTriple`-analogue yet. The
  load-bearing missing piece is a custom restriction/naturality lemma
  (`restrict_overlapTransition_to_triple_eq_tripleTransition`) on top of a new target-side triple
  localization object + triple transport. No shortcut through the existing 2-fold `AlgEquiv`s.
- Codex's "cheaper partial" (a generic transported-cocycle lemma over arbitrary fixed transports Φ₁Φ₂Φ₃)
  was NOT landed: Codex itself flagged it "does not yet say the existing double `overlapTransition`s
  satisfy the triple cocycle" — i.e. an unanchored lemma not tied to the atlas charts. Landing it without
  the restriction lemma is visible-progress, not bedrock; deferred with the rest of the triple to P2.c′/P2.d.
