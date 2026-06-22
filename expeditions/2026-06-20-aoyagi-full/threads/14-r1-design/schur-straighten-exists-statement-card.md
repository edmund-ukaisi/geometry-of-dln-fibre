# Statement card — `schur_straighten_exists` (det-1 Schur straightening existence, (A) lane)

> **SUPERSEDED (2026-06-22, controller Decision A).** The CANONICAL lemma is
> `schur_straighten_of_data` on `origin/fm-2/consolidate-aoyagi-full` @d82b381 — same re-hypothesised
> form (the team's independent reconstruction; converged with mine hypothesis-for-hypothesis). The name
> `schur_straighten_exists` was DROPPED. This card is retained as the DECORRELATED record of the
> FALSE-as-stated catch (O1/O2/O3, Codex g128) that corroborated Decision A. The fidelity note at the
> bottom (IsSchurStraighten lacks `χ 0 = 0` / `u`-nonvanishing) was routed to pp2.

- **Status:** SUPERSEDED by `schur_straighten_of_data` (canonical, GREEN on consolidate). Original work:
  `origin/fm2/crux-recover` @17bcd33 (redundant — do NOT integrate the Lean; keep only this card + the
  g128 artefacts).
- **Seat:** fm2 (formaliser). The (3) MP-of-transvection follow-on is on `origin/fm2/mp-transvection`.
- **The catch (corroborates Decision A).** The handed *abstract* `schur_straighten_exists` statement was
  unprovable (see below). The `IsSchurStraighten` STRUCTURE is UNCHANGED; the fix re-attached the
  theorem's hypotheses (= `schur_straighten_of_data`).

## The handed statement was FALSE (DEFECTIVE-SPECIFY)

Original (abstract, universal `nReg N N'`, arbitrary `flatCore`, no relating hypothesis):

```text
theorem schur_straighten_exists (M) (S : ChainDimSplit M) (nReg N N' : ℕ)
    (flatCore : (Fin N → ℝ) → ℝ) :
    ∃ flatRedCore redEmbed (χ : (Fin nReg→ℝ)×(Fin N'→ℝ) ≃ₜ (Fin N→ℝ)) u
      (active : Finset (Fin N')) (p : Fin N'),
      IsSchurStraighten M S nReg flatCore flatRedCore redEmbed χ u active p
```

Three independent refutations (Codex-decorrelated, `codex/g128-schur-straighten-specify-{prompt,answer}.md`):

- **O1 (decisive).** The existential closes over `p : Fin N'`. At `N' = 0`, `Fin 0` is empty ⟹ no
  witness `p` ⟹ proposition unsatisfiable. Independently `active : Finset (Fin 0)` cannot be `Nonempty`.
- **O2 (independent).** `χ : (Fin nReg→ℝ)×(Fin N'→ℝ) ≃ₜ (Fin N→ℝ)` is a homeomorphism of finite-dim real
  spaces ⟹ `nReg + N' = N`. Mismatched inputs (e.g. `nReg=0,N'=0,N=1`) admit no `χ`.
- **O3 (germ-tie, weaker).** `redCore_eq` + `factor` force `flatCore ∘ χ =ᶠ u · (∑q.1² + dlnLoss S.red 0
  (redEmbed q.2))` — constrains the germ of an *arbitrary* `flatCore`. (Codex caveat: not airtight alone
  since `u` is free-signed and `redEmbed 0` need not zero the red core — but O1/O2 already refute.)

## The proven statement (re-hypothesised theorem; structure unchanged)

```text
theorem schur_straighten_exists (M) (S : ChainDimSplit M) (nReg N N' : ℕ)
    (flatCore : (Fin N → ℝ) → ℝ)
    (redEmbed : (Fin N' → ℝ) → Params S.red)
    (χ : (Fin nReg→ℝ)×(Fin N'→ℝ) ≃ₜ (Fin N→ℝ))
    (u : (Fin nReg→ℝ)×(Fin N'→ℝ) → ℝ)
    (hmp : MeasurePreserving χ volume volume) (humeas : Measurable u)
    (active : Finset (Fin N')) (p : Fin N') (hpa : p ∈ active) (hane : active.Nonempty)
    (hfactor : (fun q => flatCore (χ q)) =ᶠ[nhds 0]
        (fun q => u q * ((∑ i, q.1 i ^ 2) + dlnLoss S.red 0 (redEmbed q.2)))) :
    ∃ flatRedCore redEmbed' χ' u' active' p',
      IsSchurStraighten M S nReg flatCore flatRedCore redEmbed' χ' u' active' p'
```

The re-attached hypotheses are exactly the ties the geometric application supplies, matching Codex's
minimal-fix (chose the *stronger* "provide the actual χ" route for the dim tie):
- `χ` + `hmp` (MP) — supplies O2's dim match implicitly and the measure-preserving chart.
- `p`/`active`/`hane` — supplies O1's `Fin N'` inhabitation directly.
- `hfactor` — supplies O3's geometric `flatCore` germ (the `(uᵢ,ψᵢ)` adapted basis / Schur factorisation,
  `L·A·R = blockdiag[1, D−ba]`, witnessed #127).
- `measure_drops` — NOT a hypothesis; discharged by the new derivable lemma `ChainDimSplit.measure_drops`
  (`∑ S.red < ∑ M` from `hsum` + `hdrops`). Confirms Codex's "verify ChainDimSplit proves the drop" note.

## English gloss

Given a measure-preserving det-1 Schur chart `χ` whose pull-back of the post-blow-up core `flatCore`
factors near the deepest point as a measurable unit `u` times (regular smooth block `∑q.1²` + the
strictly-smaller reduced-chain core `dlnLoss S.red 0`), with an active-coordinate pivot `p`, there
exists the `IsSchurStraighten` datum the recursion consumes. The proof is the immediate witness
(`flatRedCore` := the displayed red-core form; `redCore_eq` := `rfl`).

## Honest scope / what is NOT here

- This is the **existence-packaging** lemma. The heavy geometric CONSTRUCTION — producing the MP chart
  `χ` and the germ `hfactor` from a post-blow-up *unit pivot* (sub-lemmas (1) `hardPivot_schur_blockId`,
  (2) per-node decoupling, (3) MP-of-transvection) — is downstream and is NOT discharged by this lemma.
- **Fidelity flag for reviewer / controller (Codex "missed obstruction"):** the LOCKED `IsSchurStraighten`
  structure does not require `χ 0 = 0` (so "near the deepest point `χ 0`" is not pinned to the origin) nor
  `u` to be a *nonvanishing* local unit. Not needed for soundness of THIS lemma, but it weakens the
  semantic content of the datum for the RLCT transport downstream. Surfaced, not silently changed.
