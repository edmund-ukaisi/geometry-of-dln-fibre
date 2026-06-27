<task>
Design a proof of a germ inequality (♦) in matrix calculus. It is TRUE (numerically robust) but every
crude energy-product bound I try has a hole. I need the genuine leading-order structure that closes it.
Be ruthless about whether this is provable cleanly or needs deep germ analysis.
</task>

<setup>
L=2, real matrices, block grid (r ⊕ M_s). Per-layer free coordinates (all O(t), small):
  X_s (r×r), Y_s (r×M_{s+1}), Z_s (M_s×r), T_s (M_s×M_{s+1}), s=0,1.  A_s := I + X_s.
Framed product blocks:
  P00 = A0 A1 + Y0 Z1,  P01 = A0 Y1 + Y0 T1,  P10 = Z0 A1 + T0 Z1,  P11 = Z0 Y1 + T0 T1.
Per-layer Schur cores:  S_s = T_s − Z_s A_s^{-1} Y_s.
Global Schur complement:  Rcore = P11 − P10 P00^{-1} P01 = S0 (I − K) S1,  K = Z1 P00^{-1} Y0.
  D := Rcore − S0 S1 = −S0 K S1 = −(S0 Z1) P00^{-1} (Y0 S1).
Energies:
  Sreg = ‖P00−I‖²_F + ‖P01‖²_F + ‖P10‖²_F.
  coreΦ = ‖S0 S1‖²_F.   Score = ‖Rcore‖²_F.
Identity (exact): Score − coreΦ = 2⟨S0S1, D⟩_F + ‖D‖²_F.   |⟨S0S1,D⟩| ≤ √(coreΦ·‖D‖²_F) (Cauchy-Schwarz).

THE GOAL:  (♦)  |Score − coreΦ| ≤ η(t)·(Sreg + coreΦ),   η(t) → 0 as t → 0.
(verified numerically: η = Θ(t²), robust on ALL of S5a {cond P00 ≤ 10}, including two adversarial
families below.)

WHY the (Sreg+coreΦ) denominator (not coreΦ alone, not Sreg alone): two reachable adversarial curves
collapse one denominator each (the coordinates are FREE; X1,Y0,Z1 are "spectator" coords NOT in Sreg,
but they enter the product blocks):
  (reg-cancel) tune X1 so P00=I exactly, null P10, shrink P01 to Θ(t³):  Sreg=Θ(t⁶), coreΦ=Θ(t⁴), gap=Θ(t⁶).
     Here coreΦ DOMINATES the denominator and absorbs the gap.  gap/coreΦ → 0 (Θ(t²)).
  (prod-cancel) M1≥2, tune T0,T1 so S0·S1 = 0:  coreΦ=Θ(t⁸)→0 fast, Sreg=Θ(t²), gap=Θ(t⁸).
     Here Sreg DOMINATES.  gap/Sreg → 0.
  (double) both at once: gap/(Sreg+coreΦ) → 0 (Θ(t²)) still — neither alone, the SUM works.

WHAT I FOUND (and its hole):
 * fD := ‖D‖²_F.  D = −(S0 Z1) P00^{-1} (Y0 S1), so fD ≤ ‖P00^{-1}‖²_op · ‖S0 Z1‖²_F · ‖Y0 S1‖²_F
   ≤ ‖P00^{-1}‖²_op · ‖S0‖²_F‖Z1‖²_F · ‖Y0‖²_F‖S1‖²_F  (iterated Frobenius sub-mult).  [VERIFIED bounded]
 * This fD-bound DOES close (♦) numerically (the implied η → 0 in all modes incl. double).  BUT proving
   √(coreΦ·fD_bound) ≤ η(Sreg+coreΦ) needs the ANTI-CORRELATION: when ‖Y0‖²‖Z1‖² is large (reg/prod
   cancel), coreΦ is correspondingly tiny — the PRODUCT coreΦ·‖Y0‖²‖Z1‖² stays controlled, but no single
   energy-product inequality `coreΦ·fY0·fZ1 ≤ C(Sreg+coreΦ)^k` is uniformly bounded (verified: blows up
   in the "double" family).  So crude energy bounds discard the cancellation.
</setup>

<questions>
1. What IS η explicitly (leading order)?  Is it Θ(t²) = Θ(max reg/spec read magnitude squared) = Θ(‖K‖_op)?
   Give the leading-order expression for Score − coreΦ and identify the rate.
2. The crux: how is the gap controlled by (Sreg + coreΦ) without a single energy-product bound?  Is there
   a clean inequality of the form  |⟨S0S1, D⟩| ≤ η·(Sreg + coreΦ)  that uses the STRUCTURE
   D = −(S0 Z1)P00^{-1}(Y0 S1) AND the fact that Y0·Z1 appears in P00−I (⊆ Sreg)?  Specifically:
   - ⟨S0 S1, S0 Z1 P00^{-1} Y0 S1⟩ — can this be re-grouped (cyclic/adjoint) so that the Y0,Z1 appear as
     Y0·Z1 or Z1·Y0 (which is ≤ Sreg-controlled via P00−I = X0+X1+X0X1+Y0Z1), times a coreΦ-controlled
     factor (S0,S1 inner products)?  Try the trace/adjoint manipulation
     ⟨S0S1, S0 Z1 ⅟P00 Y0 S1⟩ = tr( (S1 S1ᵀ S0ᵀ S0) Z1 ⅟P00 Y0 ) and bound it.
3. Does the bound need ‖Y0 Z1‖ ≤ ‖P00−I‖ + ‖X0+X1+X0X1‖ (i.e. Y0Z1 = (P00−I) − (A0A1−I))?  The
   A0A1−I = X0+X1+X0X1 part is O(t) — is it charged to Sreg too (it's NOT in Sreg directly)?  Is that a
   problem, or does it sit in the cores/elsewhere?
4. HONEST DIFFICULTY: is (♦) provable in one focused step (a clever Cauchy-Schwarz/trace regrouping
   tying ⟨S0S1,D⟩ to √coreΦ·√Sreg·(small)), or does it genuinely need a multi-step leading-order Taylor
   expansion (compute the O(t⁶)/O(t⁸) leading forms and bound term by term)?  Estimate the LoC / number
   of sub-lemmas for a Lean formalisation, and whether any Mathlib pieces (trace, op-norm, Cauchy-Schwarz
   for Frobenius inner product, ‖AB‖_F ≤ ‖A‖_op‖B‖_F) suffice or new infrastructure is needed.
</questions>

<output_contract>
- Separate FACT (provable algebra) from INFERENCE (leading-order heuristics).
- Give the explicit η rate and the cleanest inequality chain you can find for (♦).
- If a clean one-step proof exists, give it. If not, say so plainly and outline the multi-step route + LoC.
- The KEY deliverable: the regrouping/inequality that ties ⟨S0S1, D⟩ to √(coreΦ·Sreg)·(small) or to
  η·(Sreg+coreΦ) WITHOUT a single uniformly-bounded energy-product (which I showed fails).
</output_contract>

<grounding_rules>
- The coordinates X_s,Y_s,Z_s,T_s are FREE/independent; Y0,Z1,X1 are not in Sreg but enter the product
  blocks (so Sreg depends on them).  P00−I = (X0+X1+X0X1) + Y0Z1.
- ‖P00^{-1}‖_op is bounded on S5a (cond ≤ 10).  All reads → 0 as t → 0.
- Do not assume my fD-bound route is the intended one; if a different regrouping is cleaner, give it.
</grounding_rules>
