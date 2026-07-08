1. **Q1**

[computed-from-given-algebra] Using the repo convention
`blockSchur(fromBlocks A Y Z T) = T - Z A⁻¹ Y`, set `MY = movedY(Cq_0)`, `MT = movedT(Cq_0)`, `Zm = Z0edit0`, `Am = 1 + P11·X`. Since `(Pf_0⁻¹)₂₁ = -P21·P11⁻¹`, the decode blocks are:
```text
Adec = P11⁻¹ + X = P11⁻¹·Am
Ydec = P11⁻¹·MY
Zdec = Zm - P21·Adec
Tdec = MT - P21·Ydec
```

Then
```text
Schur(decode_0)
= Tdec - Zdec·Adec⁻¹·Ydec
= MT - P21·Ydec - (Zm - P21·Adec)·Adec⁻¹·Ydec
= MT - Zm·Adec⁻¹·Ydec
= MT - Zm·Am⁻¹·MY
= blockSchur(movedC Cq_0)
= (1 - K_0)·S_0.
```

**AGREE.** One-line reason: the lower-frame `P21` row-operation cancels inside the `11`-pivot Schur, and the `P11` factor cancels via `Adec = P11⁻¹·Am`, `Ydec = P11⁻¹·MY`.

2. **Q2**

[computed-from-given-algebra] Interior layers are clean: `Pf_s = Qf_s = 1`, so decode Schur equals framed/moved Schur directly.

[inference] The last layer is the symmetric cancellation: right multiplication by a block-upper frame `Q = fromBlocks Q11 Q12 0 1` leaves `T - Z A⁻¹Y` invariant:
```text
Schur(D·Q) = Schur(D).
```
The given `deepBlkZ_last = 0` is exactly the boundary normal-form input needed for the forced readback to be the symmetric one-sided version.

[inference] Therefore the forced boundary reads plus interior identity reads give:
```text
∏_s Schur(decode(psi q)_s)
= ∏_s Schur(movedC Cq_s)
= blockSchur(partProd Cq L)
```
by the banked moved-chain Schur recursion. The endpoint frames then telescope the frame-free product to the framed product used in `Score`. There is no leftover boundary factor; the cancellation closes the loop, assuming the existing endpoint/corner `B` normalization lemma is the standard one already used by the banked route.

3. **Q3**

**Verdict: REACHABLE-AS-BANKED.**

[computed-from-given-algebra] The prior obstruction depended on nontrivial interior frames. Under the corrected boundary-only regime, the boundary frames are Schur-invisible in exactly the needed one-sided sense.

[inference] Key lemmas to prove: `blockSchur_leftLower_22_one_cancel`, `blockSchur_rightUpper_22_one_cancel`, `layer0_decodeSchur_forcedReads_eq_movedSchur`, `last_decodeSchur_forcedReads_eq_movedSchur`, and the endpoint telescope/Score rewrite. This is bounded Lean plumbing with block/cast/inverse bookkeeping, not new math.