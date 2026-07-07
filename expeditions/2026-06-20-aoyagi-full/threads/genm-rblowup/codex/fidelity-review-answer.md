1. HOLDS: `(uM)Q = u(MQ)`, so every entry is scaled by `u` and squares sum to `u²`.

2. HOLDS: top is `AQ_p + BQ_b = A(Q_p + A⁻¹BQ_b)`; bottom is `CQ_p + DQ_b = C Q̃ + ΓQ_b` since `CA⁻¹BQ_b` cancels with `−CA⁻¹BQ_b`.

3. HOLDS: the exact bottom block is `C Q̃ + ΓQ_b`, not `ΓQ_b`; counterexample: scalars `A=B=C=D=1`, `Q_p=0`, `Q_b=1` gives bottom `1` but `ΓQ_b=0`.

4. HOLDS: non-orthogonal unit-triangular row/column operations do not preserve Frobenius norm pointwise; decoupling is a change-of-variables/Jacobian statement, consistent with the exact original-coordinate identity keeping `C Q̃`.

Final: the claimed corank-step identity is EXACT as stated: YES.