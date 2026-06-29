# Codex-found, here-verified EXACT witnesses that comparability c1*Phi <= F <= c2*Phi FAILS
# on every small ball (F and Phi have DIFFERENT zero sets) — killing the rlctAtOn_squeeze route.
# Objects: 2-2-2 r=1 model of link2_rho_residual. A=Yb=deepBlkY_last, B=Zb=deepBlkZ_0 (fixed consts).
import sympy as sp
t=sp.Symbol('t', positive=True); A,Bc=sp.Rational(3,4),sp.Rational(2,3)
u,v,w,p,q,x,T0,T1=sp.symbols('u v w p q x T0 T1', real=True)
A0=sp.Matrix([[1+u,p],[w,T0]]); A1=sp.Matrix([[1+x,v],[q,T1]])
P=sp.expand(A0*A1); R=[P[0,0]-1,P[0,1],P[1,0]]
C=((T0-(Bc+w)*p/(1+u))*(T1-q*(A+v)/(1+x)))**2
Phi=sum(e**2 for e in R)+C
Rth=[e.subs({T0:T0-Bc*p/(1+u),T1:T1-A*q/(1+x)}) for e in R]
F=sum(e**2 for e in Rth)+C
W1={u:-t**2,x:0,p:t,q:t,v:0,w:0,T0:Bc*t/(1-t**2),T1:A*t}      # F=0, Phi>0
W2={u:-t**2,x:0,p:t,q:t,v:0,w:-Bc*t**2,T0:Bc*t,T1:0}          # Phi=0, F>0
W3=dict(W2); W3[u]=-t**2+t**3                                  # F/Phi ~ const/t^2 -> inf
print('W1: F=',sp.simplify(F.subs(W1)),' Phi=',sp.simplify(Phi.subs(W1)))
print('W2: F=',sp.simplify(F.subs(W2)),' Phi=',sp.simplify(Phi.subs(W2)))
print('W3: F/Phi ~',sp.limit(F.subs(W3)/Phi.subs(W3)*t**2,t,0),'* t^-2')
