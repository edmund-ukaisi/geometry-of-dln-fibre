import sympy as sp

x = sp.symbols('x0:27', real=True)
u = x[0]   # the radial pivot u = x 0

# decoder blocks (from B_det3333)
B1 = sp.Matrix([[x[1], x[1]*x[2]],
                [x[1]*x[3], x[1]*x[2]*x[3] + x[4]],
                [x[1]*x[3]*x[6] + x[1]*x[5], x[1]*x[2]*x[5] + x[6]*(x[1]*x[2]*x[3] + x[4])]])  # 3x2
B2 = sp.Matrix([[x[9]],[x[10]*x[9]]])  # 2x1
N1 = sp.Matrix([[x[7]],[x[8]]])        # 2x1   (Text2=2 rows, c1 = Wext1-Text2 = 1 col)
N2 = sp.Matrix([[x[11], x[12]]])       # 1x2   (Text3=1 row, c2 = Wext2-Text3 = 2 cols)
W1 = sp.Matrix([[x[15], x[16], x[17]]])               # 1x3
W2 = sp.Matrix([[x[18], x[19], x[20]],[x[21], x[22], x[23]]])  # 2x3
R1 = sp.Matrix([[0,0,0],[0,0,0],[0,0,1]])             # 3x3
R2 = sp.Matrix([[0,0,0],[0,x[13],x[14]]])             # 2x3
Rfin3 = sp.Matrix([[x[24], x[25], x[26]]])            # 1x3

# Text = [3,3,2,1,0], Wext=[3,3,3,3]
# chainQ(N_k): for boundary k, Q is Text_{k+1} rows? Actually chainQ(N_k) has Text_{k+1} rows? 
# From 222: chainQ(N_1) = [I_{Text2} | N_1], shape Text_{k+1} x Wext_k.  kept cols = I (Text_{k+1}), residual cols = N_k.
# Here for k=1: Text2=2 rows, Wext1=3 cols => chainQ(N1) = [I_2 | N1] = 2x3
chainQ_N1 = sp.Matrix.hstack(sp.eye(2), N1)   # 2x3
# k=2: Text3=1 row, Wext2=3 cols => chainQ(N2) = [I_1 | N2] = 1x3
chainQ_N2 = sp.Matrix.hstack(sp.eye(1), N2)   # 1x3

# C 3 = u * Rfin 3   (1x3)
C3 = u * Rfin3
# C 2 = Bmat2 * chainQ(N2) + u*R2   = (2x1)*(1x3) + u*(2x3) = 2x3
C2 = B2 * chainQ_N2 + u*R2
# C 1 = Bmat1 * chainQ(N1) + u*R1   = (3x2)*(2x3) + u*(3x3) = 3x3
C1 = B1 * chainQ_N1 + u*R1

# Agen k = [ C_{k+1} - N_k W_k ; W_k ] stacked vertically (kept rows then lift rows)
# A0 : boundary 0 identity, c0=0 -> A0 = C1   (Wext0=3 x Wext1=3)
A0 = C1
# A1 : kept rows = C2 - N1 W1 (Text2=2 rows), lift rows = W1 (c1=1 row) => 3 rows x Wext2=3 cols
A1 = sp.Matrix.vstack(C2 - N1*W1, W1)
# A2 : kept rows = C3 - N2 W2 (Text3=1 row), lift rows = W2 (c2=2 rows) => 3 rows x Wext3=3 cols
A2 = sp.Matrix.vstack(C3 - N2*W2, W2)

# flat chart = concat of all entries of A0,A1,A2 (27 entries)
F = []
for A in (A0,A1,A2):
    for i in range(A.rows):
        for j in range(A.cols):
            F.append(A[i,j])
F = sp.Matrix(F)
print("num outputs:", len(F), "(expect 27)")

J = F.jacobian(sp.Matrix(x))
d = J.det()
df = sp.factor(d)
print("raw flat det of chartParams3333 =", df)
