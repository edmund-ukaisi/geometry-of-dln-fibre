import sympy as sp

# (2,2,2,2) r=1: 3 top components, COMP i = {det A_i = 0}, i in {1,2,3}.
# For each component, we need a POINT in it with det P != 0... wait, no: with TOP-LEFT 1x1 minor (P[0,0]) != 0.
# Component {det A_i = 0}: choose the other factors invertible and A_i rank 1 with P rank 1, P[0,0]!=0.
# Realizer of the minimising partition: a rank-1 through-line. Let's exhibit, per component, a point where:
#   (a) det A_i = 0  (on the component)
#   (b) rank P = 1   (in Sigma^1)
#   (c) P[0,0] != 0  (detDelta nonzero) -- the witness point

def mat(name):
    return sp.Matrix(2,2, sp.symbols(f'{name}11 {name}12 {name}21 {name}22'))

# We'll just numerically construct, per component, a witness tuple.
import numpy as np

def P_of(A1,A2,A3):
    return A3@A2@A1

# normal form E = diag(1,0). Want P = E, with det A_i = 0 for the chosen i.
E = np.array([[1.0,0],[0,0]])
I2 = np.eye(2)

cases = []
# COMP 1: det A1 = 0. Take A1 = E (rank1, det 0), A2=A3=I => P=E, P[0,0]=1, det A1=0.
cases.append(("COMP1 detA1=0", E.copy(), I2.copy(), I2.copy()))
# COMP 2: det A2 = 0. Take A2 = E, A1=A3=I => P=E, det A2=0.
cases.append(("COMP2 detA2=0", I2.copy(), E.copy(), I2.copy()))
# COMP 3: det A3 = 0. Take A3 = E, A1=A2=I => P=E, det A3=0.
cases.append(("COMP3 detA3=0", I2.copy(), I2.copy(), E.copy()))

for tag,A1,A2,A3 in cases:
    P = P_of(A1,A2,A3)
    print(f"{tag}: det A1={np.linalg.det(A1):.0f} det A2={np.linalg.det(A2):.0f} det A3={np.linalg.det(A3):.0f} | rank P={np.linalg.matrix_rank(P)} P[0,0]={P[0,0]:.0f} (detDelta) detP={np.linalg.det(P):.0f}")
