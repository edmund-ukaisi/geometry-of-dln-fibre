import sympy as sp

u = sp.Symbol('u')
# free block coords for M222=(2,2,2), t222=(2,1,1)
# Boundary k=1 (GenBlk index 1): K(1x1)=k1, X(1x1)=x1, N(1x1)=n1, E(1x1)=e1, W lift = Wblk(1)<-readW(0): 1x2 = [w0,w1]
k1,x1,n1,e1,w0,w1 = sp.symbols('k1 x1 n1 e1 w0 w1')
# Boundary k=2 (=L, leaf): the schurDim(1)=2 slot feeds readK/X/N/E at k=1 but GenBlk Rfin=0; and Wblk(2)=readW(1)=0.
# Actually Bmat(2) = bmatStack(readK 1, readX 1) but k=2 is leaf, used? Cgen(2)=u*Rfin(2)=0 since k=2 NOT < L=2.
# So the leaf C_2 = 0 regardless. Bmat(2)/Nblk(2)/etc unused in Cgen/Agen (they only use k<L for interior).
# So only boundary k=0 (identity) and k=1 (interior) matter; plus C_2=leaf=0.

# Widths: Wext=[2,2,2], Text=[2,2,1,1].
# k=0 boundary: Text0=2,Text1=2 -> Bmat0 = I_2 (2x2). Nblk0: Text1 x (Wext0-Text1)=2x0 (empty). chainQ at t=2,c=0 -> I_2.
#   Rmat0 = 0. So C_0 = I_2 * I_2 + u*0 = I_2.
# k=1 boundary: Text1=2,Text2=1. Bmat1: Text1 x Text2 = 2x1 = bmatStack(K=k1[1x1], X=x1[1x1]) = [[k1],[x1*k1]].
#   Nblk1: Text2 x (Wext1-Text2) = 1x1 = [[n1]]. chainQ at t=Text2=1,c=Wext1-Text2=1, M'=Wext1=2: [I_1 | N] = [[1, n1]] (1x2).
#   Rmat1 = rmatPad(E): Text1 x Wext1 = 2x2, with E (r_1 x c_1 = 1x1=[[e1]]) placed bottom-right: [[0,0],[0,e1]].
#   So C_1 = Bmat1 * chainQ(N1) + u*Rmat1.
#     Bmat1 (2x1) * chainQ (1x2) = [[k1],[x1*k1]] * [[1, n1]] = [[k1, k1*n1],[x1*k1, x1*k1*n1]]
#     + u*[[0,0],[0,e1]] = [[k1, k1*n1],[x1*k1, x1*k1*n1 + u*e1]]   (the Schur frame [[K,KN],[XK, XKN+uE]])
Bmat0 = sp.eye(2)
C0 = Bmat0*sp.eye(2)  # + u*0
Bmat1 = sp.Matrix([[k1],[x1*k1]])
chainQ1 = sp.Matrix([[1, n1]])
Rmat1 = sp.Matrix([[0,0],[0,e1]])
C1 = Bmat1*chainQ1 + u*Rmat1
print("C0 =", C0)
print("C1 =", C1)

# C_2 = leaf = 0 (Rfin=0). 
C2 = sp.zeros(1,2)  # Text2 x Wext2 = 1x2
print("C2 =", C2)

# Now the layers A_k = chainA(N_k)(W_k)(C_{k+1}), k=0,1.
# A_1 = chainA(N1)(W1)(C2): M'=Wext1=2, t=Text2=1, c=Wext1-Text2=1, m'=Wext2=2.
#   chainA = [[C - N*W],[W]] over rows (t then c). C=C2(1x2), N=N1=[[n1]](1x1), W=W1=Wblk(1)<-readW(0)=[w0,w1](1x2).
#   top (t=1 rows): C2 - n1*W = [0,0] - n1*[w0,w1] = [-n1*w0, -n1*w1]
#   bottom (c=1 rows): W = [w0,w1]
#   So A_1 (2x2) = [[-n1*w0, -n1*w1],[w0, w1]]
W1 = sp.Matrix([[w0, w1]])
A1 = sp.Matrix([[ -n1*w0, -n1*w1],[w0, w1]])
print("A1 =", A1)

# A_0 = chainA(N0)(W0)(C1): M'=Wext0=2, t=Text1=2, c=Wext0-Text1=0, m'=Wext1=2.
#   c=0: no residual rows. chainA = [[C1 - N0*W0]] = C1 (since N0,W0 empty). So A_0 = C1.
A0 = C1
print("A0 =", A0)

# prod = A_0 * A_1  (M0=2 x M2=2)
prod = sp.simplify(A0*A1)
print("prod = A0*A1 =", prod)

# Check prod = u * H for some u-free H
prod_div_u = sp.simplify(prod/u)
print("prod/u =", prod_div_u)
print("Is prod/u u-free?", all(u not in t.free_symbols for t in prod_div_u))
