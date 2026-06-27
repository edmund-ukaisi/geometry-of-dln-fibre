import sympy as sp

print("="*78)
print("PART B: R1 single-step Schur row-decomp (the schur_row_decomp Lean fact)")
print("="*78)
# R1 node model: deepest layer A (m x k), B = product of remaining layers (k x n), generic.
# Single-pivot blow-up: A = y0*Ahat, Ahat = [[1, a],[b, D]] (a=1x(k-1), b=(m-1)x1, D=(m-1)x(k-1)).
# core = ||Ahat B||^2.  Bred = B[1:,:].
# schur_row_decomp: lower rows of Ahat·B = b·E_row + S·Bred, S = D - b·a, E_row = B[0,:] + a·Bred.
m, k, n = 3, 3, 4
a = sp.Matrix(1, k-1, lambda i,j: sp.Symbol(f'a_{j}'))
b = sp.Matrix(m-1, 1, lambda i,j: sp.Symbol(f'b_{i}'))
D = sp.Matrix(m-1, k-1, lambda i,j: sp.Symbol(f'D_{i}_{j}'))
Ahat = sp.Matrix(sp.BlockMatrix([[sp.Matrix([[1]]), a],[b, D]]))
B = sp.Matrix(k, n, lambda i,j: sp.Symbol(f'B_{i}_{j}'))
Bred = B[1:k,:]
prod = Ahat*B
E_row = B[0,:] + a*Bred           # 1 x n   (pivot-row product, row 0 of Ahat B)
S = D - b*a                        # (m-1)x(k-1)  single-step Schur complement
lower_claim = b*E_row + S*Bred     # (m-1) x n
lower_actual = prod[1:m,:]
print("row 0 of Ahat·B == E_row ?", sp.simplify(prod[0,:]-E_row)==sp.zeros(1,n))
print("lower rows == b·E_row + S·Bred ?", sp.simplify(lower_actual-lower_claim)==sp.zeros(m-1,n))
# core = ||E_row||^2 + ||lower||^2 = sum E_row^2 + sum (b E_row + S Bred)^2
core = sum(prod[i,j]**2 for i in range(m) for j in range(n))
schur = sum(E_row[0,j]**2 for j in range(n)) + sum((b[i,0]*E_row[0,j] + (S*Bred)[i,j])**2 for i in range(m-1) for j in range(n))
print("core == sum E_row^2 + sum(b E_row + S Bred)^2 ?", sp.expand(core-schur)==0)

# The R1 reduced core is ||S·Bred||^2 -- the SINGLE-STEP Schur complement of ONE layer.
# This IS dlnLoss(red M) 0 with A'=S ((m-1)x(k-1)), B'=Bred ((k-1)x n) -- a GENERIC (m-1)x(k-1)x n product loss.
print("\n--- R1 reduced core = ||S·Bred||^2: a generic (m-1)x(k-1)xn product loss (the REAL child) ---")
print("S is (m-1)x(k-1) =", S.shape, "; Bred is (k-1)xn =", Bred.shape, "; ||S·Bred||^2 = dlnLoss(",m-1,",",k-1,",",n,") 0")

print("\n--- KEY: R1 recurses on the REAL child loss, S is a FREE (m-1)x(k-1) matrix ---")
# At the deepest point of the child, S=W-b·a is itself parametrised freely (W=D free, a,b free),
# so S ranges over ALL (m-1)x(k-1) matrices.  The child is the genuine dlnLoss(red M) loss --
# NOT a product Pi S_s of per-layer Schur cores.  Pi S_s would FIX the inner structure.
print("Is S a free (m-1)x(k-1) matrix as D,a,b vary? S = D - b·a, D free => yes, S free.")
