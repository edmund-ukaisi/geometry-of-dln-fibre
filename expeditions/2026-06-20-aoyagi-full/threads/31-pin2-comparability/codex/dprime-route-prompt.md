<task>
Lean 4 + Mathlib v4.29 formalisation. I must close 2 `sorry`s (the folded core (d')/(e'))
inside a producer theorem `framedParams_split_eq_frame_raw` (L = 2 deep-linear-network case,
`hL2 : 2 ≤ L`, FRONT pivot `J = frontEmbed`). I want a decorrelated sanity check on the
CLEANEST route before I commit several hundred LoC.

## The two goals (per `w ∈ U`, `U ∈ 𝓝 w0`)

With these named objects (all in scope at the sorry):
- `Mw := Matrix.reindex rThr pivThr (P0 * (prod H (paramsEquivFlat.symm w) - B) * QL)`
  (the conjugated residual, M×M with M = H0+HL-r, block-split at r),
- `P00 := Mw.toBlocks₁₁ + 1` (Invertible, from S5a `eventually_P00_invertible`, `P00 w0 = 1`),
- `P01 := Mw.toBlocks₁₂`, `P10 := Mw.toBlocks₂₁`, `P11 := Mw.toBlocks₂₂`,
- `Sreg := (∑(P00−1)² + ∑P01²) + ∑P10²`  (the three regular block energies),
- `Score := ∑((P11 − P10·⅟P00·P01) i j)²`  (= frobSq of the global Schur complement `Rcore`),
- `coreΦ := deepestCoreF H r (deepestCoreAbsorb H r hr hL (split w)).2.1`.

GOAL (d'):  `Sreg + Score ≤ γ₂·(Sreg + coreΦ)`   (γ₂ a fixed positive const, indep of w)
GOAL (e'):  `Sreg + coreΦ ≤ γ₁·(Sreg + Score)`   (γ₁ a fixed positive const)

These fold via γ₁ = γ₂ = 1 + C once I have the IN-SUM charge `|Score − coreΦ| ≤ C·Sreg` on U.
(The standalone `Score ≍ coreΦ` is KNOWN FALSE for M>1, germ counterexample verified — must be in-sum.)

## What is BANKED (sorry-free, axiom-clean), with exact Lean signatures

1. `deepestCoreF H r y := dlnLoss (deepestM H r) 0 ((paramsEquivFlat (deepestM H r)).symm y)`,
   and `dlnLoss M 0 A = ∑ i, ∑ j, ((prod M A - 0) i j)^2 = frobSq (prod M A)`.
   At L=2, `prod M A = A 0 * A 1` (two layers).

2. `deepestCoreAbsorb = coreShearHomeo (schurCutoffShift) …` where
   `coreShearHomeo shift _ q = (q.1, (q.2.1 + shift (q.1, q.2.2), q.2.2))` (ADD-form, rfl-true).
   `schurCutoffShift = χ • schurShiftRaw`, and `schurShiftRaw p = paramsEquivFlat M (schurCorrection p)`,
   `schurCorrection p s = -(readZ p s) * (1 + readX p s)⁻¹ * (readY p s)`.
   On a 𝓝 w0 (the `χ=1` set), `schurCutoffShift = schurShiftRaw`. (Need: a lemma `χ=1 on a nbhd of w0`;
   I have `schurCutoffShift_zero`, `continuous_schurCutoffShift`, and the cutoff inhabits a unit ball.)

3. `schur_core_germ_comparability {M} (S0 S1 K R) (hR : R = S0*(1-K)*S1) :`
     `(R - S0*S1 = -(S0*K*S1))`
     `∧ frobSq (R - S0*S1) ≤ frobSq S0 * frobSq K * frobSq S1`
     `∧ frobSq R = frobSq (S0*S1) + 2*(∑i∑j (S0*S1) i j * (R - S0*S1) i j) + frobSq (R - S0*S1)`
     `∧ (∑i∑j (S0*S1) i j * (R - S0*S1) i j)^2 ≤ frobSq (S0*S1) * frobSq (R - S0*S1)`.

4. `layer_schur_blockDiag (X Y Z T) [Invertible (1+X)] :`
     `fromBlocks 1 0 (-(Z*⅟(1+X))) 1 * fromBlocks (1+X) Y Z T * fromBlocks 1 (-(⅟(1+X)*Y)) 0 1`
       `= fromBlocks (1+X) 0 0 (T - Z*⅟(1+X)*Y)`.  (per-layer Schur diag; S_s := T_s - Z_s⅟(1+X_s)Y_s.)

5. `fullProduct_core_split (P00 P01 P10 P11) [Invertible P00] :`
     Frobenius split of `fromBlocks (P00-1) P01 P10 P11` energy into the 4 block sums,
     AND `P11 i j = (P10·⅟P00·P01) i j + (P11 − P10·⅟P00·P01) i j` (the leak/Rcore split).

6. The producer body already has, per layer s (at L=2, s ∈ {0,1}):
   `F w s = framedLayer` decoding to `reindex(corner) + Pf_s · reindex(fromBlocks X_s Y_s Z_s T_s) · Qf_s`,
   where (X_s,Y_s,Z_s) = readX/readY/readZ from reg+spec slots, T_s = core read.
   And `hRegBlocks : reindex(prod (F w)) = fromBlocks 1 0 0 0 + Mw`.  (front pivot, clean telescope.)
   `endpoint_telescoping_eq` gives `prod(F w) = P0·prod(A w)·QL` cleanly (front pivot).

7. `frobenius_mul_le`, `frobenius_triple_le`, `frobInner_sq_le`, `frobSq_neg/_nonneg`, `core_comparability_squeeze`.

## The crux I want vetted

The IN-SUM charge `|Score − coreΦ| ≤ C·Sreg` needs:
(A) `coreΦ = frobSq (S0*S1)` where `S_s = T_s - Z_s⅟(1+X_s)Y_s` (decode lemma, "routine"); and
(B) `Rcore = P11 − P10·⅟P00·P01 = S0·(1-K)·S1` for the SAME S0,S1 and some K with frobSq K ≤ c·Sreg.
    This is the block-LDU of `Mw = reindex(prod F w) - fromBlocks 1 0 0 0`'s Schur complement,
    identified with the per-layer-Schur product via `layer_schur_blockDiag` telescoped over 2 layers.
Then S5c (item 3) + Cauchy-Schwarz charges the cross term + remainder to Sreg.

## Questions (rank by leverage)

1. Is there a SHORTER route to (d')/(e') that AVOIDS explicitly constructing `S0,S1,K` and proving
   `Rcore = S0(1-K)S1`? e.g.: can I get the in-sum charge purely from `core_comparability_squeeze`
   (item 5/its squeeze) applied to a DIFFERENT split, treating `coreΦ` as a black box bounded by
   frobSq of the product directly? Or is the explicit S0,S1,K identification unavoidable?

2. For the explicit route: at L=2 the framed product is `corner + Pf0·B0·Qf0` times `corner + Pf1·B1·Qf1`
   reindexed. The Schur complement of a 2-layer block product. Concretely, what is the cleanest Lean
   statement of the "telescoped block-LDU" lemma — i.e. given two block layers C0 = fromBlocks (1+X0) Y0 Z0 T0
   and C1 = fromBlocks (1+X1) Y1 Z1 T1 (both with invertible (0,0) after framing), the Schur complement
   of C0·C1 equals S0·W·S1 with W = 1 - (something O(Y,Z)) ? Give the EXACT middle-factor W and the
   EXACT K so that R = S0·(1-K)·S1. (The cert claims W = I - Z1·A⁻¹·Y0, A = global pivot.) Verify the
   algebra symbolically if you can.

3. Is the front-pivot corner-framing (Pf, Qf units; the corner = fromBlocks 1 0 0 0) going to make
   the per-layer (0,0) block exactly `1 + X_s` (so `layer_schur_blockDiag` applies verbatim), or does the
   Pf/Qf conjugation perturb the block structure in a way that breaks the clean `S_s = T_s - Z_s⅟(1+X_s)Y_s`
   identification? This is my biggest build-risk worry.

4. Honest verdict: is closing BOTH (d') and (e') in this tide realistic as ~several-hundred LoC, or is
   there a hidden hard sub-lemma (the telescoped block-LDU) that is itself a multi-hundred-LoC build?
   If the latter, what is the smallest HONEST partial deliverable (e.g. lemma 1 `coreΦ = frobSq(S0S1)`
   proven, lemma 2 left as a precisely-stated sorry)?
</task>

<output_contract>
Answer the 4 questions in order, each ≤ 8 sentences. For Q2 give the explicit W and K (algebra).
End with a one-line VERDICT: either "EXPLICIT route, achievable" or "needs telescoped-LDU sub-lemma,
partial deliverable = X". Flag any step where you are INFERRING vs computing.
</output_contract>

<grounding_rules>
You cannot see the repo. Reason from the signatures given. Where you assume a Mathlib lemma exists,
say so. Distinguish algebra you actually verified from algebra you recalled. Do not invent Lean lemma
names; describe the math and let me find the lemma.
</grounding_rules>
