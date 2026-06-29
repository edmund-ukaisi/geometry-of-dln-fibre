import sympy as sp
# Confirm det DB = engine (K^4 at (3,3,3), |K|^{r+c}=K^{2+2}) symbolically (K kept symbolic).
u=sp.Symbol('u',real=True); Ksym=sp.Symbol('K',real=True)
X0,X1,N0,N1,E01,E10,E11=sp.symbols('X0 X1 N0 N1 E01 E10 E11',real=True)
Wij=sp.symbols('W00 W01 W02 W10 W11 W12',real=True); lf0,lf1,lf2=sp.symbols('lf0 lf1 lf2',real=True)
w=sp.symbols('w0:18',real=True)
def build_B(wv):
    wu=wv[0]; wK=wv[1]; wX=sp.Matrix([[wv[2]],[wv[3]]]); wN=sp.Matrix([[wv[4],wv[5]]])
    wE01,wE10,wE11=wv[6],wv[7],wv[8]; wW=sp.Matrix([[wv[9],wv[10],wv[11]],[wv[12],wv[13],wv[14]]])
    wlf=sp.Matrix([[wv[15],wv[16],wv[17]]])
    Bmat1=sp.Matrix.vstack(sp.Matrix([[wK]]), wX*wK); qN1=sp.Matrix.hstack(sp.eye(1),wN)
    R1=sp.zeros(3,3); Eblk=sp.Matrix([[wu,wE01],[wE10,wE11]])
    for i in range(2):
        for j in range(2): R1[1+i,1+j]=Eblk[i,j]
    C2=wlf; C1=Bmat1*qN1+R1; A0=C1; A1=sp.Matrix.vstack(C2-wN*wW,wW)
    return [sp.expand(e) for A in (A0,A1) for e in A]
B=build_B(w)
JB=sp.Matrix(B).jacobian(sp.Matrix(list(w)))
# keep wK (=w1) symbolic, randomize the rest to read the K-power
import random; random.seed(9)
sub={w[i]:sp.Rational(random.randint(1,9),random.randint(1,5)) for i in range(18) if i!=1}
detB=sp.factor(JB.subs(sub).det())
print("det DB (wK=w1 symbolic, rest rational) =", detB, " (expect c*w1^4 = engine |K|^{r+c}=K^4)")
P=sp.Poly(sp.expand(JB.subs(sub).det()), w[1])
print("  K-power monomials:", [d for (d,),c in P.terms()], " (expect single (4,))")
