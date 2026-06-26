<task>
Decorrelated red-team of a single derivative-survival claim in a Lean RLCT formalisation. Re-derive
independently; tell me if my reasoning is wrong. Do NOT rubber-stamp.
</task>

<setting>
Deep linear net, L=2, H=[2,2,2], r=1. Two 2x2 matrices C0,C1; loss = ‖C0·C1 − corM‖², corM=[[1,0],[0,0]].
Near the deepest point a gauge chart gives coords split into THREE slots:
  reg/spectator coords:  X0,Y0,Z0,X1,Y1,Z1  (6 of them; "reg" = 3, "spectator" = 3)
  core coords:           T0,T1               (a SEPARATE slot)
Each layer: C_s = [[1+X_s, Y_s],[Z_s, T_s]].

Two candidate "regular residual" maps E : coords → (3 reg-block values), used to build an RLCT chart:
  E_zero (current, "deepestEPivot"): the 3 reg blocks of the T:=0 product C0|_{T0=0}·C1|_{T1=0}.
    Domain: (reg,spectator) only — does NOT take the core slot.
  E_full (proposed repair): the 3 reg blocks of the FULL product C0·C1. Domain: ALL coords incl core.
Reg blocks of a 2x2 product P: (P11−1, P12, P21).

A prior result PIN1 proved: the map  r0 ↦ E_zero(r0, spectator=0)  has strict Fréchet derivative at 0
equal to an INVERTIBLE linear map F (a "frame factor", block-triangular, invertible from two unit
hypotheses). PIN1 is closed and axiom-clean. The repair swaps E_zero → E_full inside the chart.
</setting>

<facts_established_by_me>
- FULL reg blocks: P11−1 = X0X1+X0+X1+Y0Z1, P12 = (1+X0)Y1 + Y0·T1, P21 = (1+X1)Z0 + T0·Z1.
- T=0 reg blocks: same but WITHOUT the leak terms Y0·T1 (in P12) and T0·Z1 (in P21).
- So E_full − E_zero = (0, Y0·T1, T0·Z1) — purely DEGREE-2 (each a product of two distinct coords).
</facts_established_by_me>

<questions>
1. Independently compute the Jacobian (Fréchet derivative) at 0 of E_full w.r.t. ALL coords
   (X0,Y0,Z0,X1,Y1,Z1,T0,T1). Re-derive; don't trust mine.
2. Is the (reg,spectator)-restricted derivative of E_full at 0 EQUAL to that of E_zero at 0?
   (i.e. does PIN1's invertible F survive verbatim?) State the reasoning (the leak terms are degree-2).
3. What is the CORE-direction derivative block of E_full at 0 (∂E_full/∂T0, ∂E_full/∂T1)?
   Is it zero? If so, what does that mean for the chart: does E_full's FULL derivative at 0 factor as
   F (on reg/spec) ⊕ 0 (on core)?
4. ARCHITECTURE judgment: an RLCT chart peels the "regular" directions via a local diffeo with
   invertible reg-Jacobian (PIN1's F) at 0, leaving the core. If E_full's derivative at 0 is F⊕0
   (invertible on reg/spec, zero on core), is PIN1's fact RE-USABLE as-is for E_full, or does the
   chart need a genuinely NEW derivative fact about E_full (e.g. the joint reg+core behaviour)? Reason
   about whether "the reg-slice (core held at 0) has derivative F" is the right input, or whether the
   chart needs the derivative of E_full along the core direction too.
</questions>

<output_contract>
Per question: VERDICT (one line) + reasoning. Mark exact-algebra vs inference. If my degree-2 ⟹
fderiv-survives reasoning has a hole, say where. End with: "PIN1 [SURVIVES verbatim / needs a new
analog / is orphaned] under the E_zero→E_full swap because ___."
</output_contract>

<grounding_rules>
Re-derive the Jacobian yourself. Distinguish exact algebra from chart-architecture inference.
</grounding_rules>
