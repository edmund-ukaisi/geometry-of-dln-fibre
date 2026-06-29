import sympy as sp
x = sp.symbols('x0:27', real=True); u=x[0]
B1 = sp.Matrix([[x[1], x[1]*x[2]],[x[1]*x[3], x[1]*x[2]*x[3] + x[4]],
                [x[1]*x[3]*x[6] + x[1]*x[5], x[1]*x[2]*x[5] + x[6]*(x[1]*x[2]*x[3] + x[4])]])
B2 = sp.Matrix([[x[9]],[x[10]*x[9]]]); N1=sp.Matrix([[x[7]],[x[8]]]); N2=sp.Matrix([[x[11],x[12]]])
W1=sp.Matrix([[x[15],x[16],x[17]]]); W2=sp.Matrix([[x[18],x[19],x[20]],[x[21],x[22],x[23]]])
R1=sp.Matrix([[0,0,0],[0,0,0],[0,0,1]]); R2=sp.Matrix([[0,0,0],[0,x[13],x[14]]]); Rfin3=sp.Matrix([[x[24],x[25],x[26]]])
qN1=sp.Matrix.hstack(sp.eye(2),N1); qN2=sp.Matrix.hstack(sp.eye(1),N2)
C3=u*Rfin3; C2=B2*qN2+u*R2; C1=B1*qN1+u*R1
A0=C1; A1=sp.Matrix.vstack(C2-N1*W1,W1); A2=sp.Matrix.vstack(C3-N2*W2,W2)
F=[]
for A in (A0,A1,A2):
    for i in range(A.rows):
        for j in range(A.cols):
            F.append(sp.expand(A[i,j]))

# Q-C check: does any chart output have u-degree >= 2, or a term u * (two distinct free coords)?
maxudeg=0; bad_u_product=[]
for idx,e in enumerate(F):
    p=sp.Poly(e,*x)
    for mono,coeff in p.terms():
        if mono[0]>maxudeg: maxudeg=mono[0]
        if mono[0]==1:
            others=[k for k in range(1,27) if mono[k]>0]
            tot_other=sum(mono[k] for k in range(1,27))
            if tot_other>=2:   # u times a product / square of free coords
                bad_u_product.append((idx, [(k,mono[k]) for k in others]))
print("max u-degree across all chart outputs:", maxudeg, " (expect 1 -> u is LINEAR everywhere)")
print("chart outputs with u * (product of 2+ free coords):", bad_u_product, " (expect [] -> u multiplies at most ONE free coord)")
# also: which entries are EXACTLY u alone (the pivot '1' direction)?
pivot_alone=[idx for idx,e in enumerate(F) if sp.simplify(e-u)==0]
print("chart outputs equal to exactly u:", pivot_alone)
