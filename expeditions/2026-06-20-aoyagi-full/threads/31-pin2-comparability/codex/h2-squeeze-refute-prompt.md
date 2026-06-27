<task>
Adjudicate whether a reachable chart curve REFUTES a published two-sided "loss squeeze" conclusion (not
just an intermediate lemma). I have an exact curve; I need you to find any chart constraint that excludes
it, OR confirm the squeeze conclusion is false as stated. Be adversarial against MY claim of refutation.
</task>

<setup>
L=2 DLN, deepest point = rank-r corner. Chart: w ↦ split w = (reg, core, spec), a homeomorphism;
per-layer reads X_s,Y_s,Z_s (reg/spec) and core T_s are free independent coordinates.
Published theorem `deepest_loss_squeeze` concludes: ∃ c₁,c₂>0, ∃ U ∋ w0, ∀ w ∈ U,
    c₁·(Sreg_E + coreΦ) ≤ loss(w) ≤ c₂·(Sreg_E + coreΦ),
where loss = ‖∏ layers − B‖²_F, coreΦ = frobSq(∏_s S'_s) the per-layer Schur cores
S'_s = T_s − Z_s A_s^{-1} Y_s (A_s = I+X_s), and Sreg_E ≍ Sreg = ‖P00−I‖²+‖P01‖²+‖P10‖² (the regular
product-block energies; front pivot makes Sreg_E = Sreg exactly).
It is PROVED via folded conjuncts: Sreg + Score ≍ Sreg + coreΦ, where Score = frobSq(Rcore),
Rcore = global (1,1)-Schur complement of the framed deviation = S0(I−K)S1, K = Z1 P00^{-1} Y0.
And the BANKED frame leaf gives loss ≍ Sreg + Score (Score = global Schur). So the squeeze's soundness
rests on Sreg + Score ≍ Sreg + coreΦ.

THE CURVE (r=1, M0=M2=1, M1=2; widths H0=2,H1=3,H2=2), scale t→0:
  A0=A1=I (=1),  Y0=[0, t],  Z1=[t; 0],  Y1=[−t²],  Z0=[−t²],  T0=[t, −t³],  T1=[0; t].
Computed EXACTLY (sympy + numpy, raw-parameter level, building actual layers and the actual loss):
  P00 = 1 (cond=1, deep in S5a),  P01 = 0,  P10 = 0  ⇒  Sreg = 0.
  S0 = T0 − Z0 Y0 = [t, 0],  S1 = T1 − Z1 Y1 = [t³; t]  ⇒  S0 S1 = t⁴,  coreΦ = t⁸.
  K = Z1 Y0 = [[0,t²],[0,0]] (nilpotent rank-1),  Rcore = S0(I−K)S1 = 0  ⇒  Score = 0.
  prod = B exactly  ⇒  loss = 0 (≈1e-36 numerically).
So: loss/(Sreg+Score) = 1.0000 (the frame leaf holds), but loss/(Sreg+coreΦ) = 0/t⁸ → 0, and
(Sreg+coreΦ)/(Sreg+Score) = t⁸/0 = ∞. The squeeze LOWER bound c₁(Sreg_E+coreΦ) ≤ loss needs c₁ ≤ 0.
The mechanism: per-layer cores S0,S1 are nonzero and S0·S1 ≠ 0, but the global Schur Rcore = S0(I−K)S1
= 0 because K=Z1Y0 is a nilpotent rank-1 map cancelling the product. coreΦ counts ‖S0 S1‖² (overcounts);
the loss tracks ‖Rcore‖² = Score = 0.
</setup>

<questions>
1. Is this curve REACHABLE as a genuine split-w path under the published hypotheses (front pivot J =
   frontEmbed; the seven frame facts: Pf,Qf units, interior-trivial Qf0=PfL=I, the corner normalization
   hcorner, Pi·P0=1)? The reads X_s,Y_s,Z_s,T_s are claimed FREE. Is there any constraint among them
   (e.g. from the corner normalization, the gauge/spectator routing, or the cutoff χ=1 inner ball — note
   all reads →0 so we are in the inner ball) that EXCLUDES Y0=[0,t], Z1=[t;0], T0=[t,−t³]? Find it if it
   exists; otherwise confirm reachable.
2. If reachable: does this REFUTE the published `deepest_loss_squeeze` conclusion (with coreΦ) as stated?
   The frame leaf loss ≍ Sreg+Score is sound; the failure is the substitution Score→coreΦ. Confirm or
   find my error.
3. Is the squeeze RESCUABLE by restating coreΦ as the GLOBAL Schur core frobSq(Rcore) = Score (which the
   loss genuinely tracks)? Would that change the downstream RLCT consequence (the core's contribution to
   the real-log-canonical threshold)? I.e. is coreΦ (per-layer product) vs Score (global Schur) a
   cosmetic restatement or a genuine change to the proven quantity?
4. Severity read: is this a build-stopper for the producer close, and does it touch the headline RLCT =
   ½·codim result, or only the intermediate squeeze statement?
</questions>

<output_contract>
- Separate FACT (exact algebra / reachability) from INFERENCE.
- Give a clear yes/no on (a) reachability, (b) refutation of the squeeze-as-stated, (c) rescuability by
  Score-instead-of-coreΦ.
- If you find a chart constraint that excludes the curve, name it precisely — that would SAVE the squeeze.
</output_contract>

<grounding_rules>
- The reads are free/independent (verified: regGaugeSlotEquiv is a homeomorphism onto the full per-layer
  X/Y/Z index set; cores T_s are a separate free slot).
- coreΦ = frobSq(∏ per-layer Schur cores) EXACTLY on the inner ball (banked
  deepestCoreF_coreAbsorb_eq_prodSchur); all reads →0 so the curve is on the inner ball.
- Do not assume my refutation is correct; the highest-value output is either a chart constraint that
  excludes the curve (saving the squeeze) or independent confirmation that it's reachable and refuting.
</grounding_rules>
