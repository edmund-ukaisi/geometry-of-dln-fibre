import sympy as sp
# The clean general bound chain (SQUARE r=M0), conditioning: |P1_ii|>=delta/2, |P1_ij|<=eta (i!=j), |P2|<=eta.
# 1) Row diagonal dominance margin:  gamma = delta/2 - (r-1)*eta.
#    With eta = delta/(4(r-1)) (r>=2): gamma = delta/2 - delta/4 = delta/4 > 0.  (r=1: gamma=delta/2.)
#    => P1 strictly diagonally dominant => INVERTIBLE (Levy-Desplanques). So det(P1)!=0 EVERYWHERE on the
#       conditioned box (not just a.e.) => det(P1^T P1)=det(P1)^2 > 0 => cancellation UNCONDITIONAL on box.
# 2) Varah bound: ||P1^{-1}||_inf <= 1/gamma = 4/delta (r>=2), 2/delta (r=1).
# 3) ||Lam0||_inf = ||P1^{-1} P2||_inf <= ||P1^{-1}||_inf * ||P2||_inf.
#    ||P2||_inf (max abs row sum) <= s*eta = s*delta/(4(r-1)).
#    => ||Lam0||_inf <= (4/delta)*(s*delta/(4(r-1))) = s/(r-1)   (delta-independent). r=1: <= (2/delta)*(s*delta/4)=s/2.
# 4) decoded deep-top entry |z*Hbar_aj - (Lam0 S_bot)_aj| <= |z|*|Hbar_aj| + ||Lam0||_inf * (max row of S_bot)
#    <= delta*Hbarmax + (s/(r-1))* (M2 * eta).  For containment <= K*delta choose eta, Hbarmax suitably.
for r,s,M2 in [(2,1,1),(2,2,2),(3,2,2),(1,3,3),(5,2,2)]:
    eta = sp.Rational(1,4) if r==1 else sp.Rational(1, 4*(r-1))  # in delta units
    gamma = sp.Rational(1,2) - (r-1)*eta
    invbound = 1/gamma
    P2inf = s*eta
    lambound = invbound*P2inf
    print(f"r={r},s={s},M2={M2}: eta/delta={eta}, gamma/delta={gamma}>0 => P1 strictly DD => det!=0 on box; "
          f"||P1^-1||_inf<= {invbound}/delta, ||Lam0||_inf<= {sp.nsimplify(lambound)} (delta-free)")
print()
print("KEY: strict diagonal dominance => det(P1)!=0 EVERYWHERE on the conditioned box, so the off-pole")
print("hypothesis det(P1^T P1)!=0 is DISCHARGED on the box (unconditional), not merely a.e.")
