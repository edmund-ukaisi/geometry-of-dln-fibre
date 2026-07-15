# j=r saturated-shell adjudication — VERDICT (jreqadjud, decorrelated Codex-concurring)

**VERDICT: (b)-NEEDS-ARITY-IH** — the stepasm skeleton's separate hole (b) `deeperFlagSaturatedShell_finite`
is CORRECT; keep it separate from (a). Decorrelated Codex (conclusion withheld) independently agreed
(`DIFFERENT-SIMPLER-ARGUMENT`, identical Q1–Q4). Codex reproducibility: `codex/jreq-{prompt,answer}.md`.

## Why separate (not a collapse into (a))
The degeneracy does NOT make `deeperFlag_shell_le` FALSE at j=r (it's typed `j ≤ r`, type-applies, statement
true). Rather the head-split's LOAD-BEARING PROOF CONTENT goes VACUOUS — so (b) is not the same proof as (a);
forcing Brick D to cover j=r would thread empty-block case-splits through the pivotDom crux for zero gain.

## Exact arithmetic (0 violations / 9288 chains, arity 3–5, widths 1–6)
- j=r ⟹ `u = t+r = min(M₀,M₁)` EXACTLY ⟹ `min(M₀−u, M₁−u) = 0` ⟹ **peelCharge M u = 0** (exponent shift a no-op).
- Banked `minAdm_le_peelCharge_add_redChain` at peelCharge=0 ⟹ **minAdm M ≤ minAdm(redChain u M)** ⟹
  `c' < ½·minAdm M ≤ ½·minAdm(redChain u M)` STRICTLY (tight 7936/9288, harmless — same strict-c' as the j=0 cut).
  minAdm gates it cleanly, unconditionally.

## What D-A/D-B/S3 do at min(a,b)=0
- a=M₀−u=0: corner+Ccross empty ⟹ corank energy ≡ 0; freedSchurLoss = frobSq(P·Q̃ₚ) (pivot only). S3 Gram
  exponent a/2=0 ⟹ det^0 ≡ 1 (absent factor, NOT 0⁰). D-B/S3 VACUOUS.
- b=M₁−u=0: corank block empty; freedSchurLoss = frobSq(P·Q_top)+frobSq(C·Q_top) ≥ pivot; surviving C-rows only
  ADD a nonneg term (drop for domination).
- The pivotDom crux (σ-coupled C-absorption) has NOTHING to control — no corner Gram divisor exists.
  `hpiv`/`hcvg`/`hrange` are UNUSED at j=r (corner-fits-in-strong-subspace constraints, spurious here).
  ⟹ **hole (b) is pivotDom-INDEPENDENT + hypothesis-light — build it in PARALLEL, before the crux lands.**

## The exact separate argument (`deeperFlagSaturatedShell_finite`, concl `shellSpineIntegrand M u κ ε r ⟨r,_⟩ c' < ⊤`), given hjeq:j=r, hIH
1. hjeq ⟹ u=min(M₀,M₁), peelCharge=0, min(a,b)=0.
2. shell ⊆ univ (monotone) — shell restriction NOT needed at j=r.
3. freedSchurLoss ≥ frobSq(P·Q̃ₚ) (empty corner / drop C-term) ⟹ (freedSchurLoss)^{−c'} ≤ (frobSq(P·Q̃ₚ))^{−c'}.
4. D-A radial blow-up + det-1 clear (banked `pivotBlock_radial_blowup`, `frobSq_schur_split_inv`,
   `prod_headSplit`) ⟹ pivot energy → decLoss = commonDivisor²·frobSq(prod(redChain u M) z); surviving rows
   integrate vs weight ≡ 1 → finite const.
5. = C·(cornerComparator (redChain u M) ![1] ![minAdm−1]).integral c', C<⊤; comparator adm
   (`cornerComparator_adm`), closed by hIH via the step-1 threshold. LOAD-BEARING (not dead): `singularShell_iUnion`
   covers j:Fin(r+1), so j=r is a genuine shell in hole (d)'s cover sum.

## Most likely to break
Step 4's Lean fill needs the banked D-A / front-peel lemmas to ACCEPT the degenerate corner widths (a=0 or b=0).
If `pivotBlock_radial_blowup`/`prod_headSplit` were stated only for min(a,b)>0, (b) needs a tiny dedicated
empty-corner peel lemma — still NO new math. Boundary: at j=r, hc' reads 0<c'; the c'=0 case is trivial
(integrand ≡ 1, finite box measure).

## Packaging directive
Add strict `hjr : j<r` to `headSplit_domination`/`deeperFlag_spineToCore` (endgame-plan item 2 anticipated this);
do NOT attempt a uniform j≤r Brick-D proof. `deeperFlag_shell_le` (RouteMSJDeeperFlagCore.lean) is typed j≤r —
either tighten to j<r, or accept its j=r instance is reachable only by this separate degenerate argument.
