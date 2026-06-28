import sympy as sp
# scalarGram_cancel_of_rankOneColumns (r=1 case):
# P : m x (s+1), with every column j = mu_j * (column 0), and ||col0||^2 = sum_i P[i,0]^2 != 0.
# P1 = P[:,:1] (=col0), P2 = P[:,1:]. Lam0 = (P1^T P1)^{-1} P1^T P2 (1 x s).
# Claim: P1 * Lam0 = P2.
for (m, s) in [(2,1),(3,2),(1,3),(4,2),(2,3)]:
    col0 = sp.Matrix(m,1, lambda i,j: sp.Symbol(f'a{i}'))
    mus = [sp.Symbol(f'mu{k}') for k in range(s)]
    cols = [col0] + [mus[k]*col0 for k in range(s)]
    P = sp.Matrix.hstack(*cols)           # m x (s+1)
    P1 = P[:, :1]; P2 = P[:, 1:]
    Lam0 = (P1.T*P1).inv()*P1.T*P2         # 1 x s
    lhs = P1*Lam0                          # m x s
    diff = sp.simplify(lhs - P2)
    print(f"m={m} s={s}: P1*Lam0 - P2 = {'0 (cancels)' if diff == sp.zeros(m,s) else diff}")
