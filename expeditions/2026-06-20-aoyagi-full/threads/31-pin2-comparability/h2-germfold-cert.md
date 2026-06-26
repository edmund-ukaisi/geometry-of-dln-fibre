# h2 frame discrepancy — VERDICT: O(Sreg), the bridge re-states cleanly (germ fold)

The formaliser's numeric check reshaped h2: h1 SOUND (framed-LDU cores reproduce `Rcore` EXACTLY,
`Rfr=Rcore`), but h2's exact `hCore : coreΦ = frobSq(S0·S1)` is FALSE under nontrivial frames (`1.065 ≠
0.938`). The decisive question: **is the discrepancy `frobSq(framed S0·S1) − coreΦ` itself O(Sreg)?**
**VERDICT: YES — it is O(Sreg) (in fact O(Sreg²)).** So the bridge re-states cleanly with a germ-relaxed
`hCore` (the 8th-catch pattern: exact → germ fold). NOT the deeper-problem escalation. All numeric
(re-runnable) + the bridge-fold algebra exact. Read-only.

## The decisive sweep (re-runnable)
Reproduced the formaliser's regime (L=2, rect r=1/H0=3/H1=2/H2=2, generic FIXED nontrivial frames),
swept the deviation `w → w0`:

    |frobSq(framed Ŝ0·Ŝ1) − coreΦ| / Sreg   (median):  7.7e-4 (1e-1) → 7.6e-6 (1e-2) → 7.6e-8 (1e-3)
    |frobSq(framed Ŝ0·Ŝ1) − coreΦ| / Sreg²  (median):  1.8e-2  — SCALE-INVARIANT (bounded).

So `disc = O(Sreg²)` — strictly higher-order than `Sreg`. The germ relax `|coreΦ − frobSq(S0·S1)| ≤
Ccore·Sreg` HOLDS with huge slack (`disc = O(Sreg²) ≤ Ccore·Sreg` on a bounded-Sreg nbhd, `Sreg ≤ Bs`).
(Generic frames tested = the worst case; the structured deepest frames are at least as good.)

## Why O(Sreg) (the mechanism — the frame decoration is gated by the vanishing reg reads)
The framed per-layer Schur `Ŝ_s = Schur(Pf_s·(corM_s + dev_s)·Qf_s)`, frame-free `S'_s = Schur(corM_s +
dev_s) = T_s − Z_s(1+X_s)⁻¹Y_s`. At `w0` (dev=0): the deepest frame brings `corM_s` to the rank-r normal
form, so `Ŝ_s(0) = Schur(corM-framed) = 0` AND `S'_s(0) = 0` (both vanish — confirmed by the sweep → 0).
Near w0, the frame's Schur-distorting effect enters ONLY through the off-diagonal frame blocks acting on
the vanishing reg reads `Y_s,Z_s = O(√Sreg)` (the X-cols/rows-vanish structure of the deepest layer makes
the deepest frame's distortion a higher-order effect). So `Ŝ_s − S'_s = O(√Sreg·(per-layer dev))`, and
the PRODUCTS' difference `frobSq(Ŝ0 Ŝ1) − frobSq(S'0 S'1) = O(Sreg²)`. The frames are O(1) gauge constants,
but their CORE-Schur distortion is gated by the regular reads, which vanish at w0 — exactly the germ-fold
pattern (the 8th catch: exact `Score=coreΦ` false, the discrepancy ∈ ideal(reg) ⇒ charged to Sreg).

## The bridge re-statement (CLEAN — one triangle step, ~5-10 LoC)
RELAX `germ_charge_of_schur_factorization`'s `hCore`:

    -- WAS (exact, FALSE under frames):
    --   (hCore : ∀ᶠ w in 𝓝 w0, coreΦ w = frobSq (S0 w * S1 w))
    -- NOW (germ, TRUE — the frame decoration folded):
    (Ccore : ℝ) (hCcore : 0 ≤ Ccore)
    (hCore_germ : ∀ᶠ w in 𝓝 w0, |coreΦ w - frobSq (S0 w * S1 w)| ≤ Ccore * Sreg w)

The proof absorbs it by ONE triangle step (the S5c-split machinery UNCHANGED):

    frobSq R − coreΦ = (frobSq R − frobSq(S0 S1)) + (frobSq(S0 S1) − coreΦ)
    |frobSq R − coreΦ| ≤ |frobSq R − frobSq(S0 S1)|  +  |frobSq(S0 S1) − coreΦ|
                       ≤ C_old·Sreg  [the EXISTING S5c-split: 2·|cross| + frobSq D]  +  Ccore·Sreg
                       = (C_old + Ccore)·Sreg.

So the bridge conclusion `∃ C, |frobSq R − coreΦ| ≤ C·Sreg` holds with `C = C_old + Ccore`. The S5c
difference-of-squared split + Cauchy-Schwarz (the bridge's existing `hRem`/`hMcb` machinery) is
untouched; only `hCore`-exact → `hCore_germ` + the triangle fold. (Exactly the in-sum-fold pattern: same
shape as the 8th catch's `Score≍coreΦ` and the (b)-comparability — the producer already consumes
two-sided germ charges, so the relaxed bridge feeds the squeeze unchanged.)

## The producer's new sub-lemma (the `hCore_germ` it must supply)
    theorem coreΦ_germ_charge … :
      ∃ Ccore ≥ 0, ∀ᶠ w in 𝓝 w0,
        |deepestCoreF (deepestCoreAbsorb (split w)).2.1 − frobSq (Ŝ0 w · Ŝ1 w)| ≤ Ccore · Sreg w
where `Ŝ_s` = the FRAMED per-layer Schur (from h1's LDU on `reindex(F_s)`), `coreΦ = frobSq(∏ S'_s)`
(lemma-1, frame-free). Proof: `Ŝ_s − S'_s` carries the frame off-diag × the vanishing reg reads
(`Y_s,Z_s = O(√Sreg)`), so `|frobSq(Ŝ0 Ŝ1) − frobSq(S'0 S'1)| ≤ Ccore·Sreg` — SAME structure as h3's
remainder (Cauchy-Schwarz on the off-diag-Schur blocks paired with the regular reads). Routes through the
banked `frobenius_mul_le` + the reg-read-vanishing facts (the deepest layer's X-cols/rows vanish).

## What this resolves about my h2-frame-cert (the prior honest correction)
My h2-frame-cert said "real frame obligation, h2 NOT clean" — CORRECT (the frames don't exactly cancel).
But it left the discrepancy-order UNSETTLED ("could not settle the per-layer framed-vs-frame-free"). **NOW
SETTLED: the discrepancy is O(Sreg) (O(Sreg²) even), so it folds into the germ charge — NOT a wall, a
clean bridge relax.** The "deeper problem / escalate" branch is RULED OUT.

## Honest scope
- The O(Sreg) is numeric (re-runnable sweep, generic frames = worst case; median scale-invariant at
  `disc/Sreg²`). The exact-algebra proof of `|frobSq(Ŝ0 Ŝ1) − frobSq(S'0 S'1)| ≤ Ccore·Sreg` is the
  producer's `coreΦ_germ_charge` (the genuine new work, ~MEDIUM, the h3-style Cauchy-Schwarz on the
  frame-off-diag × reg-read terms). I did NOT exact-derive the symbolic `Ŝ_s − S'_s` expansion (the rect
  blocks + 3 inverses are heavy); the numeric sweep + the mechanism (reg-read-gated) are the evidence.
- The bridge relax (the triangle fold) is exact and ~5-10 LoC.

## Net (the verdict the build is paused on)
**YES — the discrepancy is O(Sreg). The bridge re-states cleanly** (relax `hCore` to the germ form
`|coreΦ − frobSq(S0 S1)| ≤ Ccore·Sreg`; the S5c-split proof absorbs the extra term by one triangle step).
The producer supplies `coreΦ_germ_charge` (the frame-decoration O(Sreg) bound, h3-style). NOT the
deeper-problem escalation. The h2 build can RESUME with: (1) the bridge re-stated (germ hCore), (2) the
producer's `coreΦ_germ_charge` (the new MEDIUM sub-lemma).

## Files
- `/tmp/h2_disc2.py` (the decisive sweep, re-runnable: disc/Sreg → 0, disc/Sreg² bounded),
  `bridge_relax.py` (the triangle-fold re-statement). The 8th-catch precedent: `s5c-atom-statement-card.md`
  (the same exact→germ-fold pattern for `Score≍coreΦ`).
