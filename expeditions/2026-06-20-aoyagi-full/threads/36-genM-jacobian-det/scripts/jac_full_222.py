import sympy as sp
# Input flat coords (named per role): the 6 active + 2 dead. Plus the pivot is ONE of the 8.
# The output = paramsEquivFlat(A0,A1) = 8 entries of the two layers.
# A0 = C1 = [[k1, k1*n1],[k1*x1, e1*u + k1*n1*x1]]
# A1 = [[-n1*w0, -n1*w1],[w0, w1]]
# u = x p = the pivot coordinate = structPivot = flat coord 0.
#
# CASE I: pivot is a SEPARATE coordinate from the 6 block coords (i.e. flat coord 0 = the leaf-dead coord, or
#   chartIdxEquiv happens to map coord 0 to a dead slot). Then u is independent.
# CASE II: pivot coincides with one of k1,x1,n1,e1,w0,w1.
# The decoder uses structPivot=<0,hN>. Whatever role flat-0 maps to, u=that coord. Let me test BOTH and
# also test what happens with the proper FIX.

# Build the output as a function of named inputs. Let the 8 inputs be:
k1,x1,n1,e1,w0,w1,d1,d2 = sp.symbols('k1 x1 n1 e1 w0 w1 d1 d2')  # d1,d2 = dead leaf coords
inputs = [k1,x1,n1,e1,w0,w1,d1,d2]

def build_output(u):
    A0 = sp.Matrix([[k1, k1*n1],[k1*x1, e1*u + k1*n1*x1]])
    A1 = sp.Matrix([[-n1*w0,-n1*w1],[w0,w1]])
    # output flat = the 8 entries of A0 then A1 (paramsEquivFlat layout; order is a fixed permutation)
    out = [A0[0,0],A0[0,1],A0[1,0],A0[1,1], A1[0,0],A1[0,1],A1[1,0],A1[1,1]]
    return out

# CASE: u = k1 (pivot coincides with K-entry, a plausible flat-0 assignment)
print("=== CASE u = k1 (pivot = a block coord) ===")
out = build_output(k1)  # u replaced by k1
J = sp.Matrix([[sp.diff(o, v) for v in inputs] for o in out])
print("det J =", sp.simplify(J.det()))
print("(d1,d2 columns):", [sp.simplify(J[:,6].norm()), sp.simplify(J[:,7].norm())], "-> zero columns => det 0")

# CASE: u = d1 (pivot = a dead leaf coord, so u is genuinely separate but d1 still doesn't appear elsewhere)
print("=== CASE u = d1 (pivot = dead leaf coord) ===")
out = build_output(d1)
J = sp.Matrix([[sp.diff(o, v) for v in inputs] for o in out])
print("det J =", sp.simplify(J.det()))
# d2 still a fully dead column
print("col d2 norm:", sp.simplify(J[:,7].norm()))
