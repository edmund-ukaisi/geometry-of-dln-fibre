import sympy as sp, random
random.seed(3)
# Front-pivot deepest corner at firstLayer: rank-r, the rank-r columns are the FIRST r (front pivot),
# tail columns vanish (rank_normal_form_left_only's htail). So A = [[A11, 0],[A21, 0]] (r⊕(a-r) rows,
# r⊕(b-r) cols), with [[A11],[A21]] full column rank r. The left-normalizer P: P·A = corM = [[I,0],[0,0]].
# CLAIM: P can be chosen BLOCK-LOWER ([[P11,0],[P21,P22]]) iff A11 invertible.
def rnd(a,b): return sp.Matrix(a,b, lambda i,j: sp.Rational(random.randint(-3,3),random.choice([1,2,3])))
r, a0, b0 = 1, 1, 1   # m0 tail = a0, b tail = b0; widths a=r+a0, b=r+b0
fails=0; tot=0
for _ in range(8):
    A11 = rnd(r,r)
    if A11.det()==0: continue
    A21 = rnd(a0,r)
    # the corner A (a=r+a0 rows, b=r+b0 cols): first r cols = [[A11],[A21]], tail cols = 0
    A = sp.Matrix(sp.BlockMatrix([[A11, sp.zeros(r,b0)],[A21, sp.zeros(a0,b0)]]))
    # block-lower normalizer: P11=A11⁻¹, P22=I, P21 = -A21·A11⁻¹  → P·A = [[I,0],[0,0]] = corM
    P11 = A11.inv(); P22 = sp.eye(a0); P21 = -A21*A11.inv()
    P = sp.Matrix(sp.BlockMatrix([[P11, sp.zeros(r,a0)],[P21, P22]]))
    PA = sp.simplify(P*A)
    corM = sp.Matrix(sp.BlockMatrix([[sp.eye(r), sp.zeros(r,b0)],[sp.zeros(a0,r), sp.zeros(a0,b0)]]))
    tot+=1
    # check: P block-lower (toBlocks12 = 0), P invertible, P·A = corM
    blockLower = (P[0:r, r:r+a0] == sp.zeros(r,a0))
    if not (blockLower and P.det()!=0 and PA==corM): fails+=1
print(f"block-lower left-normalizer of front-pivot corner: fails={fails}/{tot} (0=Route1 sound)")
print("Note: needs A11 (top-left r×r of corner) invertible — TRUE for front-pivot (rank-r cols are first r, indep).")
