[VERDICT] **correction EXISTS (germ), high confidence.**  
No obstruction if the remaining Schur-gauge freedom is used. There is an exact analytic construction using only inverses of matrices near identity.

[DOF]  
For all `L`, it suffices to keep every pivot `A_s` fixed, edit the up blocks `Y_s`, and, for `L >= 3`, edit one down block, most cleanly `Z_0`.

`Y`-only:
- enough for `L=2`;
- generically not enough for `L>=3`, already for scalar cores `m=1`.
So there is no scalar/non-scalar rescue: noncommutativity is not the obstruction. The obstruction is that after replacing `S_s` by `(I-K_s)S_s`, the normalized left column `P21 P11^{-1}` changes through later down blocks. A single `Z_0` correction fixes exactly. Pivot edits are not required.

[FORM]  
Use LDU variables
```text
U_s = A_s^{-1}Y_s,      V_s = Z_s A_s^{-1},
C_s = L(V_s) diag(A_s,S_s) U(U_s).
```

For the original chain define partial normalized data
```text
u_s = B_s^{-1}R_s,      v_s = D_s B_s^{-1},      W_s = H_s - D_s B_s^{-1}R_s
```
where `Q_s=C_0...C_{s-1}=[[B_s,R_s],[D_s,H_s]]`. Put
```text
N_s = I_r + u_s V_s,
M_s = I_{m_s} - V_s N_s^{-1} u_s = I - K_s,
S~_s = M_s S_s          (M_0=I).
```

Keep `A_s` fixed. First edit the up variables by
```text
U~_s = U_s + A_s^{-1} N_s^{-1} u_s (S_s - S~_s).
```
Equivalently,
```text
Y~_s = Y_s + N_s^{-1} u_s (S_s - S~_s).
```
This makes the new partial `B_s` and `u_s` equal to the old ones for every `s`, hence preserves `P11` and `P12`.

Now compute two left-column recursions:
```text
v_0 = 0,       v_{s+1} = v_s + W_s V_s N_s^{-1} B_s^{-1},

W^~_0 = I,     W^~_{s+1} = W^~_s M_s S~_s,
v^~_0 = 0,     v^~_{s+1} = v^~_s + W^~_s V_s N_s^{-1} B_s^{-1}.
```
Set
```text
Delta V_0 = v_L - v^~_L,
V~_0 = V_0 + Delta V_0,     V~_s = V_s for s>=1.
```
That is,
```text
Z~_0 = V~_0 A_0,     Z~_s = Z_s for s>=1.
```
Finally define
```text
T~_s = S~_s + Z~_s A_s^{-1} Y~_s.
```

Orders in `eps`: `K_s=O(eps^2)`, so `S~_s-S_s=O(eps^3)`. The gauge edits start later:
```text
Y~_s-Y_s = O(eps^4),      Z~_0-Z_0 = O(eps^5) for L>=3,
```
and `Z~_0-Z_0=0` for `L=2`. Thus `D(psi-id)(0)=0`.

[CHECK]  
Cheapest exact test: scalar `r=m=1`, `L=3`, `A_s=1`. Verify symbolically that the above formulas give
```text
P~11=P11,  P~12=P12,  P~21=P21,
S~0 S~1 S~2 = S0 M1 S1 M2 S2.
```
The same scalar case refutes `Y`-only analyticity: with fixed `v_i`, the `P11` and `P21` equations force an edited `U_0=x` satisfying
```text
x = u_0 v_1 / (v_1 + s_1 v_2/(n_1 n_2)),
```
with `n_1=1+u_0v_1`; this is not a power series at the origin.