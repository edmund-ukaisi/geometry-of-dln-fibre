#!/usr/bin/env python3
"""Verify the GENERIC clearing step of Aoyagi's fold recursion (Case 1(2) / Case 2).

Claim (my reconstruction from pp.16-21):
 After the blow-up chart normalizes the pivot d'_{J+1,J+1}=1, the residual block is
   D' = [[1, beta],[gamma, delta]]   (beta = first row tail, gamma = first col tail, delta = deep block)
 Q  = [[1, -beta],[0, I]]        (paper's Q, applied on the RIGHT: D'' = D'.Q)
 P̂  = [[1,0],[-gamma, I]]        (the b'-conjugate of paper's P, applied on the LEFT)
 Then:
   (i)   D'' = D'.Q            = [[1,0],[gamma, delta - gamma*beta]]   (first ROW cleared; Schur in SE)
   (ii)  P̂.D'' = D'''         = [[1,0],[0, delta - gamma*beta]]       (first COL cleared)
   (iii) new residual  D_{J+1} = delta - gamma*beta   (the Schur complement, pivot 1)
   (iv)  Q, P̂ regular (det 1); C^{(S+1)} -> Q^{-1} C^{(S+1)} keeps  D'.C  invariant.
   (v)   paper's P = diag(b') P̂ diag(b')^{-1} has entries  -b'_i/b'_{J+1} * d''_{i,J+1}
         and is REGULAR (polynomial) iff  b'_{J+1} | b'_i  (divisibility chain).
"""
import sympy as sp
ok = True

# block sizes: pivot 1 + p tail rows + q tail cols
p, q = 3, 4   # arbitrary tail sizes (M(S)-J-1 = p, M^{(S+1)}-J-1 = q)
beta  = sp.Matrix(1, q, sp.symbols(f'be0:{q}'))
gamma = sp.Matrix(p, 1, sp.symbols(f'ga0:{p}'))
delta = sp.Matrix(p, q, sp.symbols(f'de0:{p*q}'))

Dp = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.Matrix([[1]]), beta),
        sp.Matrix.hstack(gamma, delta))                     # D' = [[1,beta],[gamma,delta]]
Q  = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.Matrix([[1]]), -beta),
        sp.Matrix.hstack(sp.zeros(q,1), sp.eye(q)))         # Q = [[1,-beta],[0,I]]  (q+1 square)
Ph = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.Matrix([[1]]), sp.zeros(1,p)),
        sp.Matrix.hstack(-gamma, sp.eye(p)))                # P̂ = [[1,0],[-gamma,I]] (p+1 square)

Dpp  = sp.expand(Dp * Q)                                    # (p+1) x (q+1)
schur = sp.expand(delta - gamma*beta)                       # p x q

# (i) first row cleared, SE = Schur complement
row_cleared = all(Dpp[0, j] == 0 for j in range(1, q+1)) and Dpp[0,0] == 1
se_is_schur = sp.expand(Dpp[1:, 1:] - schur) == sp.zeros(p, q)
col_preserved = sp.expand(Dpp[1:, 0] - gamma) == sp.zeros(p,1)
print(f"(i)  D''=D'.Q : first row cleared={row_cleared}; SE block = delta-gamma*beta (Schur)={se_is_schur}; first col still gamma={col_preserved}")
ok &= row_cleared and se_is_schur and col_preserved

# (ii) P̂.D'' clears first column, leaves diag(1, Schur)
Dppp = sp.expand(Ph * Dpp)
target = sp.Matrix.vstack(
        sp.Matrix.hstack(sp.Matrix([[1]]), sp.zeros(1,q)),
        sp.Matrix.hstack(sp.zeros(p,1), schur))
ddd_ok = sp.expand(Dppp - target) == sp.zeros(p+1, q+1)
print(f"(ii) P̂.D''.= diag(1, delta-gamma*beta) : {ddd_ok}")
ok &= ddd_ok

# (iv) regularity + C recoordinatization keeps product invariant
detQ = sp.expand(Q.det()); detP = sp.expand(Ph.det())
reg_ok = (detQ == 1 and detP == 1)
# next-layer matrix C : (q+1) x m ; D'.C == D''.(Q^{-1} C)
m = 2
C = sp.Matrix(q+1, m, sp.symbols(f'c0:{(q+1)*m}'))
prod_inv = sp.expand(Dp*C - Dpp*(Q.inv()*C)) == sp.zeros(p+1, m)
print(f"(iv) det Q={detQ}, det P̂={detP} (regular={reg_ok}); D'.C == D''.(Q^-1 C) (recoord invariant)={prod_inv}")
ok &= reg_ok and prod_inv

# (v) b'-conjugation: paper's P = diag(b') P̂ diag(b')^{-1}, entries -b'_i/b'_{J+1} d''_{i,J+1}
#    and P diag(b') D'' = diag(b') D'''  (keeps diag(b') factored out front).
bp = sp.Matrix(p+1, 1, sp.symbols(f'bp0:{p+1}'))           # b'_{J+1..M(S)} : p+1 of them
Db = sp.diag(*[bp[i] for i in range(p+1)])
Ppaper = sp.expand(Db * Ph * Db.inv())
# entries of first column below pivot:  -b'_i/b'_{J+1} * gamma_i  (d''_{i,J+1}=gamma_i since Q doesn't touch col0)
entries_ok = all(sp.simplify(Ppaper[i,0] - (-bp[i]/bp[0]*(-(-gamma[i-1,0])))) == 0 for i in range(1,p+1))
# careful: P̂[i,0] = -gamma_{i-1}; conj gives bp_i/bp_0 * (-gamma_{i-1}) = -bp_i/bp_0 gamma_{i-1}
entries_ok = all(sp.simplify(Ppaper[i,0] - (-bp[i]/bp[0]*gamma[i-1,0])) == 0 for i in range(1,p+1))
conj_keeps = sp.expand(Ppaper*Db*Dpp - Db*Dppp) == sp.zeros(p+1, q+1)
print(f"(v)  paper P = diag(b') P̂ diag(b')^-1: entries -b'_i/b'_(J+1) d''_(i,J+1) ={entries_ok}; "
      f"P diag(b') D'' = diag(b') D''' ={conj_keeps}")
ok &= entries_ok and conj_keeps

print("\nGENERIC CLEARING STEP:", "PASS" if ok else "FAIL")
import sys; sys.exit(0 if ok else 1)
