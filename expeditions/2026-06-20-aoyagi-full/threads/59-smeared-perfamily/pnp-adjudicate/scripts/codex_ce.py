import sympy as sp

# Codex's r>=5 counterexample: B_ii = 1/2, B_ij = -1/(2(r-1)) for i!=j. Check |B_ij|<=1/8 and B*1=0.
for r in [5,6,7,8]:
    off = sp.Rational(-1, 2*(r-1))
    B = sp.Matrix(r, r, lambda i,j: sp.Rational(1,2) if i==j else off)
    ones = sp.ones(r,1)
    rowsum = (B*ones)
    in_box = all(abs(off) <= sp.Rational(1,8) for _ in [0])  # |off| = 1/(2(r-1)) <= 1/8  <=> r-1>=4 <=> r>=5
    print(f"r={r}: |B_ij|={abs(off)} <=1/8? {abs(off)<=sp.Rational(1,8)} | det(B)={B.det()} | B*1 = {rowsum.T.tolist()[0]} (singular if all 0)")
print()
# Confirm the perturbed blow-up: B_ij = off + t, eigenvalue in all-ones dir = ... 
r=5; t=sp.Symbol('t', positive=True)
off=sp.Rational(-1,2*(r-1))
B = sp.Matrix(r,r, lambda i,j: sp.Rational(1,2) if i==j else off+t)
ones=sp.ones(r,1)
print(f"r=5 perturbed: B*1 = {sp.simplify((B*ones)).T.tolist()[0]}  (all = (r-1)*t = {sp.simplify((B*ones)[0])})")
# so smallest 'all-ones' eigenvalue ~ (r-1)t -> 0, inverse blows up. Confirm det -> 0 as t->0:
print(f"  det(B) = {sp.factor(B.det())}  -> 0 as t->0 (the all-ones eigenvalue vanishes)")
