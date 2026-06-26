# h2 frame-consistency FORK — VERDICT: MISMATCH branch, but the gap FOLDS (O(Sreg) on the S5a domain)

The load-bearing fork. **VERDICT: it IS the mismatch branch** (the loss core is FRAMED, `deepestCoreAbsorb`/
`coreΦ` is FRAME-FREE), **BUT the mismatch FOLDS via the germ charge** — the gap `|Score − coreΦ|` is
O(Sreg) on the S5a domain (well-conditioned `P00`, where the germ charge lives). **NOT escalation; NOT
O(1).** The bridge re-states with the germ-relaxed `hCore` (the triangle fold). This corrects my own
third error in this sub-thread (a wrong-pivot blow-up I initially misread as the obstruction). Honest.

## The fork, settled by the ACTUAL loss decomposition
`dlnLoss_two_sided_of_frame` (banked leaf, `DeepestGaugeBlocks.lean:566`) decomposes the loss as
`Sreg + Score` where **`Score = frobSq(P11 − P10·⅟P00·P01)` with `P00,P01,P10,P11` the blocks of the
FRAMED `reindex(P0·N·QL)` (via `hconj`)**. So the true loss core IS the FRAMED Schur `frobSq(Rcore)` (=
`frobSq(framed Ŝ0·(1−K̂)·Ŝ1)`, h1-SOUND). Meanwhile `coreΦ = deepestCoreF(deepestCoreAbsorb) = frobSq(∏ S'_s)`
is FRAME-FREE (lemma-1, `schurCorrection` reads the raw `readX/Y/Z`). **These DIFFER** (the formaliser's
`1.065 ≠ 0.938`). ⇒ **the MISMATCH branch: loss-core framed, deepestCoreAbsorb frame-free.**

## The gap FOLDS — O(Sreg) on the S5a domain (the decisive measurement)
The bridge needs `|Score − coreΦ| ≤ Ccore·Sreg` (germ). Tested (rect r=1/H0=3/H1=2/H2=2, generic FIXED
O(1) frames, w→w0), **on the S5a domain** (`cond(P00) ≤ 10`, the bounded-inverse neighborhood the germ
charge lives on, with the CORRECT pivot `P00 = N11 + 1 → 1` at w0):

    gap/Sreg ∈ [1e-8, 2.4],  max 2.4 (scale 1e-1) → 0.27 (1e-2, 1e-3),  median scale-invariant ~0.011.

**BOUNDED, O(Sreg).** So `|Score − coreΦ| ≤ Ccore·Sreg` HOLDS on the S5a domain — the germ-fold works.

## My THIRD error (owned) — the wrong-pivot blow-up
A first hunt found `gap/Sreg` blowing up (~1e9). **That was MY bug:** I computed `Rcore` with the Schur
pivot `N11` (the RESIDUAL block, → 0 at w0 ⇒ `⅟N11` explodes), NOT the producer's actual `P00 = N11 + 1`
(→ 1 at w0, well-conditioned). With the CORRECT `+1` pivot AND the S5a domain restriction (where
`Invertible P00` / bounded `⅟P00` is a HYPOTHESIS, not an accident), the blow-up vanishes and `gap/Sreg`
is bounded. The blow-up was a near-singular-`P00` artifact OUTSIDE the germ-charge domain — exactly what
S5a's `eventually_P00_invertible` excludes.

(This is my third correction in this sub-thread: h1-cert "frame-free" → wrong; h2-germfold "O(Sreg²)" →
the order was right for `frobSq(Ŝ0Ŝ1)` but the producer uses `frobSq(Rcore)`; this fork's first blow-up →
wrong pivot. The decorrelated formaliser + the controller's "O(1) not O(Sreg)" caution each caught a real
issue. The SETTLED answer: gap O(Sreg) on the S5a domain.)

## The bridge re-statement (the germ-fold, CONFIRMED on the right object)
Relax `germ_charge_of_schur_factorization`'s `hCore` to the germ form
`hCore_germ : ∀ᶠ w, |coreΦ w − frobSq(Ŝ0·(1−K̂)·Ŝ1)| ≤ Ccore·Sreg w`   [= |coreΦ − Score|, the framed Rcore]
The triangle fold gives the bridge conclusion with `C = C_old + Ccore` (the S5c-split machinery
unchanged). The producer supplies `hCore_germ` (the new sub-lemma) on the S5a domain.

NOTE the gap is the FRAMED `Score = frobSq(Rcore)` vs frame-free `coreΦ`, NOT the per-layer-product gap
I tested in h2-germfold-cert (`frobSq(Ŝ0Ŝ1)` vs `coreΦ`). The correct object is `frobSq(Rcore)` — and on
the S5a domain it's O(Sreg) (the `(1−K̂)` middle factor + the frame decoration both fold, gated by the
vanishing reg reads + the bounded `⅟P00`).

## Is re-pointing `coreΦ` to framed reads needed? NO — the germ-fold avoids it
The team lead's alternative ("re-point deepestCoreAbsorb to framed reads") is NOT needed and would risk
the banked `deepest_loss_squeeze` public conclusion (it's wired to the frame-free `deepestCoreF`/
`deepestCoreAbsorb`). The germ-fold keeps `coreΦ` frame-free (unchanged `deepestCoreAbsorb`) and charges
the framed-vs-frame-free gap to `Sreg` — preserving the public conclusion. So the SOUND, least-disruptive
route is the germ-relaxed `hCore`, NOT re-pointing.

## Honest scope + the residual risk
- The O(Sreg) is NUMERIC (re-runnable, generic-frame worst case, S5a domain). The exact-algebra proof of
  `|Score − coreΦ| ≤ Ccore·Sreg` is the producer's `hCore_germ` — the genuine MEDIUM sub-lemma. I did NOT
  symbolically derive it (the framed rect Schur + 3 inverses + the frame conjugation is heavy).
- **The one residual I flag honestly:** the gap is O(Sreg) with a TRUE nonzero constant (median ~0.011,
  scale-invariant) — it's NOT higher-order O(Sreg²) for the framed `Rcore` (unlike the per-layer-product
  gap). So the germ constant `Ccore` is genuine (not vanishing), but BOUNDED on the S5a domain — which is
  all the bridge needs. The proof must establish the bound holds UNIFORMLY on `{cond P00 ≤ M} ∩ 𝓝 w0`
  (the S5a domain) — the bounded-`⅟P00` hypothesis is load-bearing (it's what excludes the blow-up).
- I recommend a FOCUSED Codex + symbolic confirm of `hCore_germ`'s O(Sreg) bound on the S5a domain
  before the build hard-relies on it — given my error rate in this sub-thread, an independent check of
  THIS measurement (correct pivot + S5a domain) is warranted.

## Net (the fork verdict the build is paused on)
**MISMATCH branch (loss-core framed, deepestCoreAbsorb frame-free) — but the gap FOLDS: O(Sreg) on the
S5a domain.** NOT escalation. The h2 build resumes with: (1) the bridge's `hCore` relaxed to the germ
form (triangle fold, ~5-10 LoC), (2) the producer's `hCore_germ : |coreΦ − frobSq(Rcore)| ≤ Ccore·Sreg`
on the S5a domain (MEDIUM, the frame-decoration + (1−K̂) bound, gated by reg-reads + bounded ⅟P00). NO
re-pointing of `deepestCoreAbsorb` (keeps the public conclusion). **Recommend an independent symbolic/
Codex confirm of the O(Sreg)-on-S5a measurement before the build commits — my sub-thread error rate
warrants it.**

## Files
- `/tmp/h2_fork.py` (the fork measurement — note the FIRST version's wrong pivot), `h2_s5a.py` (the
  CORRECT pivot `N11+1` + S5a domain ⇒ gap/Sreg bounded), `h2_blowup.py` (the wrong-pivot blow-up =
  near-singular N11 artifact). Banked leaf: `dlnLoss_two_sided_of_frame` (Score = framed Rcore).
