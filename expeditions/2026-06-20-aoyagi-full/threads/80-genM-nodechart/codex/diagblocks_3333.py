"""
Verify the layer-filtration: det J = prod_k det(D_k), D_k = d(layer-k outputs)/d(layer-k owned coords),
and ONLY D_0 carries u.  This is the radial-separation mechanism.
"""
import sys; sys.path.insert(0,'/tmp/radsep')
import sympy as sp
from sympy import symbols, Matrix, eye, zeros
from engine import build_chart, chart_vector

x = symbols('x0:27', real=True); u = x[0]
L=3; M=[3,3,3,3]; t=[3,2,1,0]
blocks={}
blocks[0]={'B':eye(3),'N':zeros(3,0),'W':zeros(0,3),'R':zeros(3,3)}
blocks[1]={'B':Matrix([[x[1],x[1]*x[2]],[x[1]*x[3],x[1]*x[2]*x[3]+x[4]],
            [x[1]*x[3]*x[6]+x[1]*x[5], x[1]*x[2]*x[5]+x[6]*(x[1]*x[2]*x[3]+x[4])]]),
           'N':Matrix([[x[7]],[x[8]]]),'W':Matrix([[x[15],x[16],x[17]]]),
           'R':Matrix([[0,0,0],[0,0,0],[0,0,1]])}
blocks[2]={'B':Matrix([[x[9]],[x[10]*x[9]]]),'N':Matrix([[x[11],x[12]]]),
           'W':Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]]),
           'R':Matrix([[0,0,0],[0,x[13],x[14]]])}
blocks[3]={'Rfin':Matrix([[x[24],x[25],x[26]]])}
A,C = build_chart(L,M,t,blocks,u)

out=[]; out_layer=[]
for k in range(L):
    Ak=A[k]
    for i in range(Ak.rows):
        for j in range(Ak.cols):
            out.append(Ak[i,j]); out_layer.append(k)

owned = {0:list(range(0,9)), 1:list(range(9,18)), 2:list(range(18,27))}

# Full Jacobian, reordered by layer for rows (already grouped) and owner for cols.
col_order = owned[0]+owned[1]+owned[2]
J = sp.Matrix(27,27, lambda i,j: sp.diff(out[i], x[col_order[j]]))
detJ = sp.expand(J.det())
print("full det J =", sp.factor(detJ))

# Verify block lower-triangular: off-diagonal UPPER blocks (layer k rows, layer k'>k cols) are zero.
def block(rows_layer, cols_layer):
    ri=[i for i in range(27) if out_layer[i]==rows_layer]
    cj=owned[cols_layer]
    return sp.Matrix(len(ri),len(cj), lambda a,b: sp.diff(out[ri[a]], x[cj[b]]))

print("\nUpper off-diagonal blocks (should be ZERO for lower-triangular):")
for kr in range(L):
    for kc in range(kr+1,L):
        B=block(kr,kc)
        print(f"  block(row layer {kr}, col layer {kc}) zero? {B.is_zero_matrix}")

print("\nPer-layer diagonal block determinants:")
prod=1
for k in range(L):
    Dk=block(k,k)
    dk=sp.factor(sp.expand(Dk.det()))
    has_u = (u in dk.free_symbols)
    print(f"  D_{k} det = {dk}   carries u? {has_u}")
    prod=prod*Dk.det()
print("\nprod of diagonal dets =", sp.factor(sp.expand(prod)))
print("equals full det? ", sp.simplify(sp.expand(prod)-detJ)==0)
