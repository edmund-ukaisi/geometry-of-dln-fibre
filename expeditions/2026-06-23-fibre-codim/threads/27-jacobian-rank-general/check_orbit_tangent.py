# Directly test image(d mult_A) ⊇ {XE - EY} at a profile-[1,1] point of (2,2,2)r1.
# d mult_A(dA)_i = suffix_i dA_i prefix_i.  The orbit-tangent claim: for the endpoint action,
# choosing dA = delta^0_A(X,Y) (X at vertex N=last, Y at vertex 0; inner phi=0):
#   delta^0_A(phi)_i = phi_{i+1} A_i - A_i phi_i.   With only end vertices nonzero:
#   For N=1: factors A_0 (i=0), A_1 (i=1 is last vertex... careful indexing).
#   vertices 0,1,2 (N=2 here -> d=[2,2,2] has N=2!). Wait d=[2,2,2] => N=2, two factors A_0,A_1.
#   End vertices: 0 and 2. phi_0=Y at vertex 0, phi_2=X at vertex 2, phi_1=0 (inner).
#   dA_0 = phi_1 A_0 - A_0 phi_0 = -A_0 Y      (phi_1=0)
#   dA_1 = phi_2 A_1 - A_1 phi_1 = X A_1       (phi_1=0)
#   d mult_A(dA) = suffix_1 dA_1 prefix_1 + suffix_0 dA_0 prefix_0
#     suffix_1 = I (A_{N-1}...A_2 empty? for i=1=last factor index, suffix from 2 = I), prefix_1=A_0
#     suffix_0 = A_1, prefix_0 = I
#   = I*(X A_1)*A_0 + A_1*(-A_0 Y)*I = X (A_1 A_0) - (A_1 A_0) Y = X E - E Y.  GOOD, = orbit tangent.
# So {XE-EY} ⊆ image ALWAYS (it's the image of the specific tangent vectors delta^0_A(X,Y)).
# dim{XE-EY} for E=diag(I_1,0) 2x2: X,Y in gl_2. XE - EY: compute dim.
import sympy as sp
from sympy import Matrix, randMatrix, eye, zeros, symbols
import random
random.seed(3)
d=[2,2,2]; r=1
E=Matrix([[1,0],[0,0]])
# dim {XE - EY : X,Y in gl_2}: map (X,Y)->XE-EY, rank = dim image.
Xs=[[symbols(f'x{i}{j}') for j in range(2)] for i in range(2)]
Ys=[[symbols(f'y{i}{j}') for j in range(2)] for i in range(2)]
X=Matrix(Xs); Y=Matrix(Ys)
out=X*E-E*Y
vars=[Xs[i][j] for i in range(2) for j in range(2)]+[Ys[i][j] for i in range(2) for j in range(2)]
flat=[out[i,j] for i in range(2) for j in range(2)]
Jt=Matrix([[sp.diff(e,v) for v in vars] for e in flat])
print("dim{XE-EY} =", Jt.rank(), " (= delta =", r*(2+2-r),")")
print("V_orbit = T_E Mat^{<=r} = {M: M[1,1]=0}? dim should be 3 (the BR block here is the (1,1) entry).")
# {XE-EY}: which entries can it reach? XE = X*diag(1,0) = first col of X in col0, 0 in col1.
# EY = diag(1,0)*Y = first row of Y in row0, 0 in row1. XE-EY: 
#  [x00 - y00, -y01; x10, 0]. So entry (1,1)=0 always; entries (0,0),(0,1),(1,0) free => dim 3.
# So V_orbit = {M: M[1,1]=0} EXACTLY, dim 3 = delta. CONFIRMED.
