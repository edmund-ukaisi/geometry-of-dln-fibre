# Fidelity review: does this Lean encoding faithfully match the informal certificate?

You are a decorrelated second reviewer. I give you (A) an informal math certificate's definitions and
(B) a Lean formalisation's definitions. Judge INDEPENDENTLY whether (B) faithfully encodes (A). Do NOT
assume they match; hunt for a discrepancy (wrong index range, wrong factor order, a sign, a missing/extra
term, a circular definition). State your verdict + any discrepancy with the exact structure.

## Setup (shared, non-controversial)
A chain of 2x2-block matrices, layer s: C_s = [[A_s, Y_s],[Z_s, T_s]] over a commutative ring, block rows
indexed r (fixed) and m_s (varying). Partial products Q_s = C_0·C_1·…·C_{s-1} (Q_0 = I), written
Q_s = [[B_s, R_s],[D_s, H_s]]. Full product at depth L is P = Q_L. All A_s, B_s, N_s below are units.

Normalised data:
  u_s = B_s^{-1} R_s        (r x m_s)
  V_s = Z_s A_s^{-1}        (m_s x r)
  N_s = I + u_s V_s         (r x r)
  W_s = blockSchur(Q_s) = H_s − D_s B_s^{-1} R_s     (Schur complement of the partial product)
  S_s = blockSchur(C_s)     (per-layer Schur core)
  K_s = off-pivot coupling (K_0 = 0);   S̃_s = (I − K_s) S_s

## (A) The certificate's construction (informal ground truth)
The move edits one down-block Z_0 to:
  Z'_0 = (V_0 + ΔV_0)·A_0
where ΔV_0 = a_L − ã_L is the mismatch of two left-column accumulators:
  a_0 = 0,   a_{s+1} = a_s + W_s · V_s · N_s^{-1} · B_s^{-1}                  (original chain)
  ã_0 = 0,   ã_{s+1} = ã_s + Ŵ_s · V_s · N_s^{-1} · B_s^{-1}                 (edited chain)
with  Ŵ_0 = I,   Ŵ_{s+1} = Ŵ_s · (I − K_s) · S̃_s.
Claim to be encoded: with this Z'_0, the moved chain preserves P_21 (= D_L).

## (B) The Lean definitions (to be judged for fidelity to A)
Let `bs j := blockSchur (partProd C j)` (this is W_j), `wHat j := wHatAccum C j`, `V j := vDown C j`,
`N j := nMix C j`, `B j := (partProd C j).toBlocks₁₁`, `A0 := (C 0).toBlocks₁₁`, `Z0 := (C 0).toBlocks₂₁`.

  wHatAccum C 0       = 1
  wHatAccum C (k+1)   = wHatAccum C k * (1 - Kcoup C k) * schurTilde C k
      where schurTilde C k = (1 - Kcoup C k) * blockSchur (C k)      -- i.e. (I − K_k)·S_k = S̃_k

  hTermLC C j = (blockSchur (partProd C j) - wHatAccum C j) * vDown C j
                  * Ring.inverse (nMix C j) * Ring.inverse (partProd C j).toBlocks₁₁
  deltaV0 C L = ∑_{j ∈ range L} hTermLC C j
  Z0edit0 C L = (C 0).toBlocks₂₁ + deltaV0 C L * (C 0).toBlocks₁₁

(Matrix multiplication is left-associative; `Ring.inverse` is the two-sided inverse on units.)

## Questions (answer each)
1. Does `wHatAccum` match the cert's Ŵ recursion EXACTLY, including that the factor after Ŵ_k is
   (I − K_k)·[(I − K_k)·S_k] = (I−K_k)^2 S_k? Is that squared (I−K_k) what the cert intends given
   Ŵ_{s+1} = Ŵ_s·(I−K_s)·S̃_s with S̃_s = (I−K_s)S_s? Flag if you think the cert intends a single (I−K_s).
2. Does `deltaV0 C L` equal the cert's ΔV_0 = a_L − ã_L = ∑_{j<L}(W_j − Ŵ_j)·V_j·N_j^{-1}·B_j^{-1}?
   Check the per-term factor order and the summation range.
3. Does `Z0edit0 C L` equal the cert's Z'_0 = (V_0 + ΔV_0)·A_0, given V_0 = Z_0·A_0^{-1} so
   V_0·A_0 = Z_0? (I.e. is (C 0)₂₁ + ΔV_0·A_0 = (V_0 + ΔV_0)·A_0?)
4. Is `wHatAccum` genuinely independent of the Z_0 override (so defining deltaV0 via wHatAccum, then
   Z0edit0 via deltaV0, is NOT circular)? It is defined purely from C via Kcoup and schurTilde.
5. Any other fidelity concern: vacuity, a hidden over-strong hypothesis, an off-by-one on the range,
   or an index mismatch between the cert's "inclusive" K_k and a Lean "first-j-layers" partProd fold.
