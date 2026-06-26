<task>
RED-TEAM + advise on the cleanest Lean architecture to DEFINE a reparametrization Ψ, before I build it.
This is a DLN-RLCT formalisation (Lean4/Mathlib v4.29). Verified-exact pen-paper cert in hand; the
question is purely the Lean encoding of Ψ.

GOAL: close `hstep2`: `rlctAtOn Φscore wstar = rlctAtOn Φcore wstar` (flat coords `x : Fin N → ℝ`), via a
banked reduction `rlctAtOn_diffeo_bridge_of` needing: Ψ : (Fin N→ℝ)→(Fin N→ℝ) with (i) ContDiff⊤,
(ii) HasStrictFDerivAt Ψ (e:≃L) wstar, (iii) Ψ wstar = wstar, (iv) `Φcore ∘ Ψ =ᶠ[𝓝 wstar] Φscore`.

THE ENCODING (load-bearing — this is the crux):
- `split : (Fin N→ℝ) ≃ₜ DeepestSplit` is a banked smooth affine chart (ContDiff⊤ both ways, deriv = a CLE).
  `DeepestSplit = (Fin nReg→ℝ) × ((Fin nM→ℝ) × (Fin nG→ℝ))`. Slots: q.1=reg, q.2.1=core, q.2.2=spectator.
- `Φcore x = REG(x) + deepestCoreF (coreAbsorb (split x)).2.1`,  `Φscore x = REG(x) + Score x`.
  `REG(x) = ∑ i, (regStraighten (split x)).1 i ^2`,  and `(regStraighten q).1 = deepestEFull q` (banked).
- `deepestEFull q` reads the THREE reg blocks (P00−1, P01, P10) of the FULL framed product
  `prod(framedParamsPivot ... q)`, packed via `regResidualPack` (a transparent Fin-equiv).
- The per-layer framed block at layer s is `framedLayer = (corner) + P_s · fromBlocks (X_s) (Y_s) (Z_s) (T_s) · Q_s`
  where (X_s,Y_s,Z_s) = readX/Y/Z (q.1, q.2.2) s  [reg+spectator slots, NOT core], and
  T_s = (paramsEquivFlat(deepestM)).symm q.2.1 s  [the per-layer core block, decoded from the core slot].
- So at the LAST layer: T1 lives in q.2.1 (core slot); Y1 = readY(q.1,q.2.2)(last) lives in q.1/q.2.2 via
  `regGaugeSlotEquiv : (q.1,q.2.2) ≃ₜ (RegGaugeIdx → ℝ)` (a homeomorph un-flattening BOTH reg+spectator
  slots jointly, then `readY` selects the last-layer Y tag).

THE Ψ (cert, verified exact ~1e-17): act on (T1, Y1) only, holding the framed product's reg blocks fixed.
  P00 = A0·A1 + Y0·Z1, P10 = Z0·A1 + T0·Z1 (NO T1, NO Y1 — fixed automatically).
  P01 = A0·Y1 + Y0·T1 (has both). Closed form: T1' := W⁻¹·[(1−K)S1 + Z1A1⁻¹Y1 + Z1A1⁻¹A0⁻¹Y0T1],
  Y1' := Y1 + A0⁻¹·Y0·(T1 − T1'). Then P01' − P01 = A0(Y1'−Y1)+Y0(T1'−T1) = Y0(T1−T1')+Y0(T1'−T1)=0
  (the A0·A0⁻¹=I cancel). So deepestEFull∘Ψ = deepestEFull EXACTLY (REG preserved), AND the core absorb
  gives deepestCoreF(coreAbsorb(split(Ψx))).2.1 = Score x (E1, banked frobSq_prod_absorbed_eq_rcore).
A0 = 1+readX(...0), A1 = 1+readX(...1), Y0=readY(...0), Z0=readZ(...0), Z1=readZ(...1), W=I+Z1A1⁻¹A0⁻¹Y0.

<questions>
1. ARCHITECTURE: what is the cleanest way to DEFINE Ψ_split : DeepestSplit → DeepestSplit (then Ψ_flat =
   split⁻¹ ∘ Ψ_split ∘ split)? The friction: "change Y1" means modifying (q.1, q.2.2) through the
   `regGaugeSlotEquiv` un-flattening (Y1 is the last-layer Y-tag of regGaugeSlotEquiv(q.1,q.2.2)), and
   "change T1" means modifying q.2.1 through `paramsEquivFlat(deepestM).symm` at the last layer. Options I see:
   (A) Define Ψ_split directly on slots: new_q.2.1 := paramsEquivFlat(...).symm-encode the modified core
       tuple (last layer ↦ T1', else same); new (q.1,q.2.2) := regGaugeSlotEquiv.symm of the modified
       RegGaugeIdx-function (last-layer Y tag ↦ Y1', else same). I.e. encode/decode through both equivs.
   (B) Avoid slot surgery: define Ψ_split as `coreShearHomeo`-style ADD maps composed (one for the core
       shift T1−T1' ∈ q.2.1, one for the Y1 shift ∈ q.1/q.2.2). Since T1'−T1 and Y1'−Y1 are functions of
       the reads, this is a "shift" added to two slots — is the `coreShearHomeo` pattern (already banked,
       adds shift(reg,spec) to the core slot) the right primitive, generalized to also shift the reg slot?
   Rank (A) vs (B) for Lean tractability + for getting the THREE antecedents (ContDiff⊤, strict-deriv=id,
   fix wstar) cheaply. Which gives the cleanest `Φcore∘Ψ =ᶠ Φscore`?

2. KEY RISK: for E2 (deepestEFull∘Ψ = deepestEFull), I need the modified Y1' to flow back through
   `readY(Ψ_split q's (q.1,q.2.2))(last) = Y1'` AND readX/readZ/all-other-layer-reads UNCHANGED, AND the
   core T1' to flow through `(paramsEquivFlat.symm (Ψ's q.2.1))(last) = T1'`, others unchanged. With option
   (A) (encode/decode through the equivs), are these "read-after-write" identities clean (the equiv
   round-trips), or is there a trap (e.g. readY also reads spectator entries that overlap, or the
   regGaugeIdxSplit interleaves reg+spectator so a single Y-tag write touches both slots messily)? Flag the
   single most likely failure mode.

3. Is there a way to AVOID re-deriving the framed-product block algebra (P00,P01,P10) entirely, and instead
   prove `deepestEFull (Ψ_split q) = deepestEFull q` by showing the framed product `prod(framedParamsPivot
   (Ψ_split q))` EQUALS `prod(framedParamsPivot q)` as a MATRIX (since the reg blocks are read off it)? I.e.
   is the cleanest E2 "the whole last-layer framed matrix is unchanged" rather than "each of P00/P01/P10 is
   unchanged"? The last-layer framed matrix is `corner + P·fromBlocks X Y Z T·Q`; Ψ changes Y↦Y1', T↦T1',
   so the matrix changes UNLESS P·(ΔY,ΔT block)·Q = 0 — but the cert says only the PRODUCT's reg blocks are
   fixed, not the last factor. So per-layer the matrix DOES change; only the product's P00/P01/P10 are fixed.
   Confirm I must work at the PRODUCT-block level (P00,P01,P10 of the full prod), not per-layer. Any banked
   lemma giving prod's blocks from the two-grouping (G0·G1) that I should route through?
</questions>

<output_contract>
3 numbered sections. Q1: pick (A) or (B) with a one-paragraph why + the 2-3 key lemmas each needs. Q2:
the single most-likely failure mode + how to test it cheaply first. Q3: YES/NO must-work-at-product-level
+ the route. Terse, concrete, Lean-flavored. Flag INFERENCE vs what follows from the stated encoding.
</output_contract>
