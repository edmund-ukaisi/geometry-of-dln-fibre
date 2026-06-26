# h2 (♦) proof design — VERDICT: (♦) is FALSE; it refutes the published squeeze-with-coreΦ. ESCALATION.

**Commission:** design the proof of `(♦) : |Score − coreΦ| ≤ η·(Sreg + coreΦ)`, η→0.
**Result:** `(♦)` is **FALSE**. A reachable, exact chart curve violates it with ratio ≡ 1 (not →0).
The same curve refutes the **published `deepest_loss_squeeze` conclusion as stated** (lower bound, with
`coreΦ`). Triply confirmed: my exact algebra + decorrelated Codex (xhigh) + decorrelated pp-pin2-rearch
(its own sympy + Codex). This is a **build-stopping escalation** for the producer close. The headline
`rlct = ½·codim` is NOT disproved, but the intermediate squeeze route is unsound as stated.

---

## The counterexample (exact, reachable, in S5a)

L=2, r=1, widths H0=2, H1=3, H2=2 (M0=1, M1=2, M2=1). Scale t→0, per-layer reads (all → 0):

    A0 = A1 = I,   Y0 = [0, t],   Z1 = [t; 0],   Y1 = [−t²],   Z0 = [−t²],
    T0 = [t, −t³],   T1 = [0; t].

Raw layers `W0 = corner + dev0`, `W1 = corner + dev1`. Then EXACTLY (sympy + numpy, raw-parameter level):

    W0·W1 = [[1,0],[0,0]] = B   ⟹  loss = ‖prod − B‖² = 0   (the point is ON the fibre mult⁻¹(B))
    P00 = 1  (cond = 1, deep in S5a),  P01 = 0,  P10 = 0   ⟹  Sreg = 0
    S0 = T0 − Z0·Y0 = [t, 0],   S1 = T1 − Z1·Y1 = [t³; t]   ⟹  S0·S1 = t⁴,  coreΦ = t⁸
    K = Z1·Y0 = [[0,t²],[0,0]]  (nilpotent rank-1),   Rcore = S0·(I−K)·S1 = 0   ⟹  Score = 0

So:  `loss/(Sreg + Score) = 1.0000` (the banked frame leaf holds), but
`loss/(Sreg + coreΦ) = 0/t⁸ → 0`, and `|Score − coreΦ| / (Sreg + coreΦ) = t⁸/t⁸ ≡ 1`.

**The mechanism:** the per-layer Schur cores S0, S1 are individually nonzero and their product S0·S1 ≠ 0,
but the GLOBAL Schur complement Rcore = S0·(I−K)·S1 = 0 because `K = Z1·Y0` is a nilpotent rank-1 map
that exactly cancels the product (a "tilted kernel": `Y0·Z1 = 0` so P00 = I, but `Z1·Y0 ≠ 0`). `coreΦ`
counts ‖∏ per-layer cores‖² and OVERCOUNTS; the loss tracks ‖global Schur‖² = Score = 0.

## Why no chart constraint saves it (reachability — settled, decorrelated)

- The reads `Y0 = readY_0`, `Z1 = readZ_1`, `T0, T1` (cores), `Y1, Z0` are FREE independent coordinates
  (`regGaugeSlotEquiv` homeomorphism onto the full per-layer X/Y/Z index set, `DeepestSplitReindex.lean:543`;
  cores a separate slot; `DeepestSplitConcrete.lean:202/214/226` round-trips reads = raw deviations).
- The seven frame facts + front pivot do NOT impose equations among the reads (`hcorner` normalizes the
  fixed basepoint, not nearby split points). `B = diag(1,0)` is a valid front-pivot target.
- The cutoff χ=1 holds (all reads → 0 ⟹ inner ball) ⟹ `coreΦ = frobSq(∏ S'_s)` EXACTLY
  (`deepestCoreF_coreAbsorb_eq_prodSchur`, `DeepestGaugeConstruction.lean:1941`). coreΦ = t⁸ confirmed.
- pp-pin2-rearch (decorrelated) + Codex (decorrelated) both found NO excluding constraint.

## What this refutes, precisely

- **`(♦)` is false** (the commissioned charge). Equivalently the producer's germ-charge `sorry`
  (`DeepestGaugeConstruction.lean:~2667`, statement `|frobSq(Rcore) − coreΦ| ≤ ½(Sreg+coreΦ)`) has a
  FALSE statement: the curve enters every nbhd of w0 in S5a∩S5b with LHS = t⁸ > ½·t⁸ = RHS.
- **The published `deepest_loss_squeeze` (`:2794`) conclusion as stated (with `coreΦ`) is false** on the
  lower bound: `c₁·(Sreg_E + coreΦ) ≤ loss` forces `c₁ ≤ 0` on this curve. (The UPPER bound survives;
  coreΦ overcounts.) The earlier "the folded squeeze survives" measurements were on cancellation curves
  WITHOUT the tilted kernel — they missed this sharper adversary. This is the genuinely new finding.
- The cert's own "germ-vs-box" defense (`s5c-r2-cert.md`; the `W=I+ηE₁₂` witness at
  `DeepestGaugeConstruction.lean:2474`) is REFUTED: it claimed the box ratio fails only OFF-germ with
  O(1) off-pivot data. This curve is a genuine germ path (all reads O(t)) where the cert's order count
  (`∏S = O(ε²)`, `R−∏S = O(ε⁴)`) is WRONG — anisotropic alignment makes `∏S` and `R−∏S` the SAME order
  (both Θ(t⁴)), cancelling to R = 0. The cert misidentified the failure locus.

## The failure locus (thin, but nonempty in U — enough to refute ∀)

`{loss = 0, Sreg = 0, coreΦ > 0}` = fibre points where the regular blocks vanish AND the per-layer cores
don't pairwise-cancel (S0·S1 ≠ 0) while the global Schur Rcore = 0. Off this exact tuning, loss grows to
match coreΦ and `loss/(Sreg+coreΦ)` recovers to ~1 (verified: random perturbation gives min ratio 0.998).
So the failure is NOT on an open set under generic perturbation — but `∀ w ∈ U` is refuted by ANY point
in `U` where it fails, and this thin locus is nonempty in every nbhd of w0 within S5a.

## The fix — restate with `Score = frobSq(Rcore)` (NOT cosmetic)

- The SOUND core is `Score = frobSq(Rcore)` (global Schur), which `loss` genuinely tracks:
  `loss ≍ Sreg + Score` is the BANKED frame leaf (`dlnLoss_two_sided_of_frame` / `core_comparability_squeeze`),
  verified = 1.0000 on the curve. Restate the squeeze + the producer's conjuncts (d')/(e') with `Score`.
- **This is NOT a free relabel.** `{Score = 0} = {Rcore = 0}` matches the loss's reduced-core vanishing
  (shares the loss zero locus); `{coreΦ = 0} = {∏S = 0}` is STRICTLY SMALLER (∏S ≠ 0 is open in the
  fibre). A bracket with a smaller zero locus gives a LARGER (wrong) RLCT. So the `coreΦ` form is
  genuinely unsound, not cosmetically different.
- With `Score`, the abstract bridge collapses to TRIVIAL: `loss ≍ Sreg + Score` is the frame leaf
  directly; there is no `(♦)`/germ-charge `sorry` at all (the `germ_charge_of_core_charge` shape, but with
  the conclusion already = the leaf). The ~30-LoC bridge + `(♦)` residual VANISH. The downstream
  `rlctAtOn_squeeze` (`S1NonMPTransport.lean:119`) consumes `Sreg_E + Score`.

## RLCT impact — the genuine open question (for the operator's scope call)

The headline `rlct = ½·codim` is NOT refuted by this curve. But it must be RE-DERIVED from `Sreg_E + Score`
(the sound bracket), and whether `rlctAtOn(Sreg_E + Score) = rlctAtOn(Sreg_E + coreΦ)` at w0 is a
SEPARATE Newton-polytope / blow-up question I did NOT certify. The two brackets have different zero loci
(coreΦ overcounts on the thin tilted-kernel sub-fibre), so the per-fibre core contribution to the RLCT
could differ. **Most likely:** the leading w0 blow-up exponent coincides (Score is the faithful core, and
the paper's codimension count is via the global Schur / Ext, not the per-layer product), so the headline
survives via the `Score` route — but this needs a dedicated leading-order RLCT computation, NOT assumed.

## Honest difficulty read (the commission's ask)

- Proving `(♦)` is **impossible** (it is false). My earlier numeric "robust Θ(t²)→0" measurements were on
  an insufficient adversary family (cancellation without the tilted kernel); the tilted-kernel germ path
  defeats every norm-bound AND the statement itself. I was wrong that `(♦)` was true; this consult found
  the genuine counterexample. (Recording the error plainly: across this sub-thread the additive route,
  then the coreΦ-denominator route, then `(♦)` itself each looked true under a too-narrow adversary set;
  the tilted kernel is the decisive one.)
- The REAL fix (restate with `Score`) is **modest** for the squeeze itself: `loss ≍ Sreg + Score` is the
  banked leaf, so the squeeze-with-Score is ~READY (delete the `coreΦ` substitution + the dead germ
  charge). 1 tide.
- The RLCT re-derivation from `Sreg_E + Score` is the **genuine remaining work** and is **multi-tide /
  needs a pen-and-paper leading-order pass first** (Newton polytope of `Sreg + Score` at w0 vs the
  paper's codimension). This is the load-bearing open content now — NOT `(♦)`.

## EXACT build state (the staked `sorry`)

The producer ALREADY wired the `(♦)` repair in: `DeepestGaugeConstruction.lean:2667` is a `sorry` whose
statement `hcharge` (`:2639–2662`) is EXACTLY `(♦)`:
`|frobSq(Rcore) − coreΦ| ≤ ½·(Sreg + coreΦ)`, with `coreΦ = deepestCoreF (deepestCoreAbsorb (split w)).2.1`.
The producer consumes it (`refine ⟨1, 2, 2, 1, 1, …⟩`, `:2668`) to emit the folded conjuncts with `coreΦ`
(`:2536–2547`), which `deepest_loss_squeeze` (`:2794`) consumes. **So the in-progress build rests on a
`sorry` (`:2667`) with a FALSE statement** — exactly the case `lean/CLAUDE.md`'s sorry-gate names ("a
`sorry` with a wrong statement misleads. Fix wrong statements first"). The doc cites "thread a8a8b2ff" for
the `(♦)` proof; that proof cannot exist (`(♦)` is false).

## Verdict for the build
- DO NOT formalise `(♦)` or the coreΦ-squeeze — both are false as stated. The `sorry` at `:2667` has a
  FALSE statement and must be re-stated before any proof attempt.
- Restate the producer conjuncts (`:2536–2547`) and `deepest_loss_squeeze` (`:2794`, `:2831–2841`) with
  `Score = frobSq(Rcore)` (global Schur) in place of `coreΦ`. Then the folded charge is the BANKED frame
  leaf `loss ≍ Sreg + Score` directly — the `(♦)` `sorry` DISAPPEARS (no germ charge needed; γ₁=γ₂=1, or
  fold of the leaf). This is the modest, sound 1-tide fix for the squeeze.
- Commission a pen-and-paper RLCT pass: does `rlctAtOn(Sreg_E + Score) = C/2` at w0? (the new last
  load-bearing obligation, since the downstream RLCT was being read off `Sreg_E + coreΦ`). The headline is
  gated on THIS, not on `(♦)`. coreΦ and Score have different zero loci (coreΦ overcounts on the thin
  tilted-kernel sub-fibre), so the RLCT re-derivation is genuine, not cosmetic.

## Artifacts (re-runnable; mine + decorrelated)
- `/tmp/h2confirm/codex_curve.py`-style exact verify; the tilted-kernel exact curve in this doc's sympy.
- `/tmp/h2confirm/chart_reachability.py` (raw-level loss=0, coreΦ=t⁸).
- Codex: `codex/h2-diamond-{prompt,answer}.md` (found the counterexample), `codex/h2-squeeze-refute-{prompt,answer}.md`.
- pp-pin2-rearch decorrelated confirm (agentId ad67c6b4df2936a76): reachable=YES, coreΦ=t⁸=YES,
  fix=Score (not cosmetic, different zero locus), false-statement `sorry` at `:2667`.
