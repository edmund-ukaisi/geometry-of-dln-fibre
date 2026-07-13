import numpy as np

def cayley_Q(a,b,c):
    S=np.array([[0,-c,b],[c,0,-a],[-b,a,0]],float)
    I=np.eye(3)
    return (I-S)@np.linalg.inv(I+S)

def G_of(params):
    l1,l2,l3,a,b,c=params
    Q=cayley_Q(a,b,c)
    G=Q@np.diag([l1,l2,l3])@Q.T
    return np.array([G[0,0],G[1,1],G[2,2],G[0,1],G[0,2],G[1,2]])

def numjac(f,x,h=1e-6):
    n=len(x); J=np.zeros((6,n))
    for i in range(n):
        xp=x.copy(); xm=x.copy(); xp[i]+=h; xm[i]-=h
        J[:,i]=(f(xp)-f(xm))/(2*h)
    return J

rng=np.random.default_rng(0)
print("Test: detDPhi / [Vandermonde(l) * w(a,b,c)] should be CONSTANT (l-independent),")
print("      and w(a,b,c) rational. Check detDPhi/Vandermonde depends only on (a,b,c):")
for trial in range(6):
    a,b,c=rng.normal(size=3)*0.7
    l=sorted(rng.uniform(0.5,3,size=3),reverse=True)
    x=np.array([l[0],l[1],l[2],a,b,c])
    d=np.linalg.det(numjac(G_of,x))
    vand=(l[0]-l[1])*(l[0]-l[2])*(l[1]-l[2])
    # candidate rational Haar density for SO(3) Cayley: 8/(1+a^2+b^2+c^2)^2 (known form up to const)
    w=1.0/(1+a*a+b*b+c*c)**2
    print(f"  a,b,c=({a:+.3f},{b:+.3f},{c:+.3f})  detJ/vand={d/vand:+.5f}  (detJ/vand)/w={d/vand/w:+.5f}")

print("\nNow vary ONLY l (fix a,b,c): detJ/vand must be identical across l:")
a,b,c=0.3,-0.5,0.2
for trial in range(4):
    l=sorted(rng.uniform(0.5,3,size=3),reverse=True)
    x=np.array([l[0],l[1],l[2],a,b,c])
    d=np.linalg.det(numjac(G_of,x))
    vand=(l[0]-l[1])*(l[0]-l[2])*(l[1]-l[2])
    print(f"  l={[round(v,3) for v in l]}  detJ/vand={d/vand:+.6f}")
