<task>
Pin the EXACT structural identity tying a producer's global Schur block to a per-layer Schur core, for a
Lean RLCT formalisation. Concise (<500 words). Reason from the stated structure.
</task>

<context>
A gauge-chart producer (front-pivot, so all column splits are threshold rThr — clean telescope applies)
supplies, for w near a deepest point w0, blocks P00,P01,P10,P11 = the (1,1)/(1,2)/(2,1)/(2,2) blocks of
  reindex(rThr,rThr)( P0 · (∏A(w) − B) · QL )   [the loss product, conjugated by endpoint frames].
The producer's CORE residual is the GLOBAL Schur complement  Rcore(w) = P11 − P10·P00⁻¹·P01  (M×M).

Separately, a banked object `deepestCoreAbsorb` (a measure-preserving "cutoff Schur shear") maps the
chart coords q ↦ (q.1, (q.2.1 + schurShiftRaw(q.1,q.2.2), q.2.2)), where on a nbhd of w0:
  schurShiftRaw(q) = paramsEquivFlat(M)( s ↦ −Z_s·(1+X_s)⁻¹·Y_s )   [the per-layer Schur correction]
and X_s,Y_s,Z_s are the per-layer gauge reads. So (coreAbsorb q).2.1 decodes to the per-layer cores
  S_s = T_s − Z_s·(1+X_s)⁻¹·Y_s   (T_s the raw core read).
The core energy is  coreΦ(w) = deepestCoreF((coreAbsorb (split w)).2.1) = ‖∏_s S_s‖²_F  (the product of
per-layer Schurs, squared-Frobenius).

A BANKED atom `schur_core_germ_comparability` (the "S5c atom") supplies, in the form Rcore = S0·W·S1
(W = I − Z1·A⁻¹·Y0 → I a middle factor; for general L the telescope R = S0·W0·S1·W1·…·S_{L-1}):
  |frobSq(Rcore) − frobSq(∏S)| ≤ C·Sreg   on a 𝓝 of w0  (the germ charge, ∏S = ∏ per-layer Schur).

The producer needs the folded core conjuncts (d')/(e'):  frobSq(Rcore) ≍ coreΦ  with γ₁=γ₂=1+C
(two-sided), to feed the loss squeeze.
</context>

<questions>
1. THE EXACT IDENTITY: is the producer's Rcore = P11 − P10 P00⁻¹ P01 (from the framed-product blocks)
   EQUAL to ∏S (the per-layer Schur product) exactly, or only Rcore = S0·W·S1 (the middle-factor form)
   so they differ by the S5c-charged term? Pin the precise relationship. KEY sub-question: the producer's
   Rcore is the GLOBAL Schur of the WHOLE conjugated loss product ∏A−B; the per-layer ∏S is the product
   of per-LAYER Schurs. These are equal ONLY up to the middle factors W_k (the S5c result: Rcore=S0 W S1).
   So the bridge is: (block-LDU) the framed-product blocks P00,P01,P10,P11 satisfy
   P11 − P10 P00⁻¹ P01 = S0·W·S1, AND coreΦ = ‖∏S‖² = ‖S0 S1‖². Confirm both halves + that S5c then
   charges |frobSq(S0 W S1) − frobSq(S0 S1)| ≤ C·Sreg, closing (d')/(e'). Is there an EXACT equality
   anywhere (e.g. Rcore = ∏S when W=I, i.e. front pivot / W→I), or is it always the germ charge?
2. THE ROUTE (build-ready): how does the producer's Rcore (from reindex(rThr,rThr)(P0(∏A−B)QL) blocks)
   connect to S0·W·S1 (per-layer Schurs of the framed reconstruction)? This is a block-LDU on the
   TELESCOPED product. The framed product ∏(framedParamsPivot) = the corner + per-layer (corM+P reindex
   (fromBlocks X Y Z T) Q); its (1,1)/(1,2)/(2,1)/(2,2) blocks, after the rThr reindex, give P00..P11,
   and the Schur P11−P10 P00⁻¹ P01 = the LDU middle-factor product S0 W S1 (banked S5c, R=S0 W S1).
   So the bridge = (i) the framed product blocks = the loss product blocks (front pivot ⇒ (b)-exact,
   already established) + (ii) S5c's R=S0 W S1. List the load-bearing sub-lemmas + which are banked
   (S5c atom, deepestCoreAbsorb facts) vs new.
3. The coreΦ = ‖∏S‖² identity: (coreAbsorb (split w)).2.1 decodes via paramsEquivFlat(M).symm to the
   per-layer S_s, and deepestCoreF = ‖∏ of those‖². Confirm this is an EXACT equality (the shift ADDS
   −Z(1+X)⁻¹Y to the raw core T, giving S = T−Z(1+X)⁻¹Y exactly; deepestCoreF = ‖∏‖²) — modulo the cutoff
   χ=1 on the nbhd. Any subtlety (the cutoff bump, the paramsEquivFlat round-trip)?
</questions>

<output_contract>
1. Q1: exact relationship (Rcore = S0 W S1, NOT = ∏S exactly; S5c charges the difference). Where (if
   anywhere) it's an exact equality.
2. Q2: the block-LDU route + load-bearing sub-lemmas (banked vs new) + the precise new identity statement.
3. Q3: coreΦ = ‖∏S‖² exact (modulo cutoff) — confirm + any round-trip/cutoff subtlety.
Mark exact vs inference. End: "The producer's (d')/(e') closes via [exact Rcore=∏S / the S5c germ charge
on Rcore=S0 W S1]; the NEW structural identity needed is ___."
</output_contract>
