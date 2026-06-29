import sympy as sp, itertools, random
print("="*78)
print("SAMPLE the ratio F/Φ over small exact points: does a FIXED c1<=F/Φ<=c2 hold (c1,c2>0)?")
print("  (rlctAtOn_squeeze needs c1Φ<=F<=c2Φ on a nbhd; the constants need NOT be 1/2,3/2.)")
print("="*78)
u,v,w,p,q,x,T0,T1 = sp.symbols('u v w p q x T0 T1', real=True)
Zb,Yb = sp.symbols('Zb Yb', real=True)
A0=sp.Matrix([[1+u,p],[w,T0]]); A1=sp.Matrix([[1+x,v],[q,T1]])
P=sp.expand(A0*A1); R=[P[0,0]-1,P[0,1],P[1,0]]
corrC0=-(Zb+w)*p/(1+u); corrCl=-q*(Yb+v)/(1+x)
C=((T0+corrC0)*(T1+corrCl))**2
Phi=sum(e**2 for e in R)+C
delta0=-Zb*p/(1+u); delta1=-Yb*q/(1+x)
Rth=[e.subs({T0:T0+delta0,T1:T1+delta1}) for e in R]
F=sum(e**2 for e in Rth)+C   # C is the SAME (conjAbsorb, fixed both sides)
# Sample small rational points (reg,spec,core small; Zb,Yb O(1) deepest-pt consts):
random.seed(1)
ratios=[]
fails_lower=0; near0=0
for _ in range(4000):
    sc = random.choice([sp.Rational(1,100), sp.Rational(1,1000)])
    vals={}
    for s in [u,v,w,p,q,x,T0,T1]:
        vals[s]=sp.Rational(random.randint(-9,9),1)*sc
    vals[Zb]=sp.Rational(random.randint(-5,5),7); vals[Yb]=sp.Rational(random.randint(-5,5),7)
    Pv=Phi.subs(vals); Fv=F.subs(vals)
    if Pv==0:
        near0+=1
        if Fv!=0: print("  !! Φ=0 but F!=0 at", {str(k):str(v) for k,v in vals.items()}); 
        continue
    r=sp.nsimplify(Fv/Pv)
    ratios.append(float(r))
import statistics
print(f"  sampled {len(ratios)} pts.  F/Φ:  min={min(ratios):.4f}  max={max(ratios):.4f}  mean={statistics.mean(ratios):.4f}")
print(f"  Φ=0 occurrences: {near0}")
print()
print("If min>0 and max<inf with a GAP from 0 and inf => fixed-constant comparability HOLDS")
print("(c1=min, c2=max).  If min->0 or max->inf as points->0 => comparability FAILS.")
# Check behaviour as points -> 0 specifically (scale a fixed direction):
print()
print("Scaling test along the danger direction (reg=0,core=0,x=0,spec=(p,q)=(t,t)):")
for t in [sp.Rational(1,10),sp.Rational(1,100),sp.Rational(1,1000)]:
    vals={u:0,v:0,w:0,x:0,p:t,q:t,T0:0,T1:0,Zb:sp.Rational(2,3),Yb:sp.Rational(3,4)}
    Pv=Phi.subs(vals); Fv=F.subs(vals)
    print(f"  t={t}:  Φ={sp.nsimplify(Pv)}  F={sp.nsimplify(Fv)}  F/Φ={float(Fv/Pv):.5f}")
