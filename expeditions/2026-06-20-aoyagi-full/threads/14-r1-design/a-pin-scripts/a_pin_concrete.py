import sympy as sp
# Concrete (2,2,2) r=0, B=0. Deepest = origin. Arbitrary fibre v: A1=[[1,0],[0,0]], A2=[[0,0],[0,1]] (A1A2=0).
# THE (a)-SPLIT AT v: write A1 = v1 + W1, A2 = v2 + W2 (W = local perturbation). Compute the loss germ
# F(v+W) = ||(v1+W1)(v2+W2)||^2 and find its [regular block] + [homogeneous residual core] split.
w = sp.symbols('w0:8', real=True)
W1 = sp.Matrix([[w[0],w[1]],[w[2],w[3]]])
W2 = sp.Matrix([[w[4],w[5]],[w[6],w[7]]])
v1 = sp.Matrix([[1,0],[0,0]]); v2 = sp.Matrix([[0,0],[0,1]])
A1 = v1 + W1; A2 = v2 + W2
P = sp.expand(A1*A2)
F = sp.expand(sum(P[i,j]**2 for i in range(2) for j in range(2)))
print("=== (a)-split at arbitrary v=(A1=[[1,0],[0,0]], A2=[[0,0],[0,1]]) for (2,2,2) ===")
print("Generators P_ij(v+W):")
for i in range(2):
    for j in range(2):
        print(f"  P_{i}{j} =", sp.expand(P[i,j]))
# Linear leading parts (the regular block directions):
vars8=list(w)
print("\nLinear leading parts (regular directions, => smooth quadratic block):")
for i in range(2):
    for j in range(2):
        g=sp.expand(P[i,j]); lin=sum(sp.diff(g,vv).subs({x:0 for x in vars8})*vv for vv in vars8)
        print(f"  lin P_{i}{j} =", lin)
J=sp.Matrix([[sp.diff(sp.expand(P[i,j]),vv).subs({x:0 for x in vars8}) for vv in vars8] for i in range(2) for j in range(2)])
print(f"\nJacobian rank at v = {J.rank()} (= # regular quadratic directions)")
print()
print("THE (a)-SPLIT: solve the rank-J linear generators for rank-J variables (implicit function),")
print("leaving a HOMOGENEOUS residual core in the remaining vars. This is a MORSE/CONSTANT-RANK split")
print("at v -- it depends ONLY on the loss being smooth-of-constant-rank at v, NOT on resolving the core.")
print()
print("RELATION TO #111: #111's schur_chart_exists is at the ORIGIN (v=0), where ALL generators are")
print("homogeneous (no linear part, Jacobian rank 0) -- the split is TRIVIAL there (whole thing = core).")
print("At arbitrary v the split is NON-trivial (Jacobian rank > 0). So the v-split is NOT #111@v.")
