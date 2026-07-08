[FACT] **Layer 0 verdict:** Q1 yes, `f_0(0)=0`; Q2 yes, `Df_0(0)=0`.

[FACT] **Last-layer verdict:** Q1 yes, `f_{L-1}(0)=0`; Q2 yes, `Df_{L-1}(0)=0`.

[FACT] **Mechanism:** Let `E_s = movedC_s - C_s`. The boundary decoders are linear maps in their argument `D`, and their coefficients `Pinv, P21, Qinv, Q12` are constant in `q`.

[FACT]
```text
Layer 0:     C_0 - corM = P_0 rawDev_0        because Q_0 = I.
             forcedDecodeLeft(P_0, P_0 R) = R.
             f_0 = forcedDecodeLeft(P_0, E_0).

Last layer:  C_last - corM = rawDev_last Q_last because P_last = I.
             forcedDecodeRight(Q_last, R Q_last) = R.
             f_last = forcedDecodeRight(Q_last, E_last).
```

[FACT] Since fixed linear maps preserve vanishing order, `E_0 = O(||q||^5)` gives `f_0 = O(||q||^5)`, and `E_last = O(||q||^3)` gives `f_last = O(||q||^3)`. No frame-created first-order term survives.

[INFERENCE] If by “actual leading order” you mean sharp nonzero leading term, that is not derivable from the stated big-O facts alone; the exact derived claim is “at least order 5” at layer 0 and “at least order 3” at the last layer.

[FACT] The answer depends on `Q_0 = I` at layer 0 and `P_last = I` at the last layer. If `Q_0` were nontrivial, the left decode would leave `rawDev_0 Q_0 - rawDev_0` as a possible first-order term. If `P_last` were nontrivial, the right decode would leave `P_last rawDev_last - rawDev_last` as a possible first-order term.

[FACT] Invertibility of `P11` and `Q11` is load-bearing to define `Pinv/Qinv` and prove the decode identities. Since the frames are fixed at `wstar`, no neighbourhood invertibility is needed here; a neighbourhood condition would matter only if the inverses varied with `q`.

[FACT] **Most likely failure mode:** the implementation decodes with only the boundary-side frame while an opposite-side frame is secretly nontrivial. Cheapest exact check: symbolically verify
```text
forcedDecodeLeft(P0, P0 * R) - R = 0
forcedDecodeRight(Qlast, R * Qlast) - R = 0
```
for a generic block variable `R`. This catches the surviving first-order frame terms immediately.