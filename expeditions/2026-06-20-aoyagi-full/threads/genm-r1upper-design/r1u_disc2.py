import numpy as np
rng=np.random.default_rng(0)
# J(g,h) ≍ min(g^{-2c'}, g^{-(2c'-1)} h^{-1})  (a=1); RLCT-faithful (constants irrelevant to finiteness)
def J(g,h,cp):
    g=np.maximum(g,1e-300); h=np.maximum(h,1e-300)
    return np.minimum(g**(-2*cp), g**(-(2*cp-1))*h**(-1))
def frob(M): return np.sqrt((M**2).sum(axis=(-1,-2)))

def stab(mk,cp):
    out=[]
    for N in [300_000,1_200_000,4_800_000]:
        g,h=mk(N); out.append(J(g,h,cp).mean())
    return out
def verdict(ms):  # climbing by >1.6x per 4x-N step => divergent
    r1=ms[1]/max(ms[0],1e-9); r2=ms[2]/max(ms[1],1e-9)
    return "DIV" if (r1>1.6 and r2>1.6) else ("~edge" if (r1>1.25 or r2>1.25) else "FIN")

# (2,2,2,2) t=1: R_top 1x2, r_bot 1x2, A2 2x2 ; target 1.5
def c2222(N):
    rt=rng.uniform(-1,1,(N,1,2)); rb=rng.uniform(-1,1,(N,1,2)); A=rng.uniform(-1,1,(N,2,2))
    return frob(rt@A), frob(rb@A)
def f2222(N):
    rt=rng.uniform(-1,1,(N,1,2)); A=rng.uniform(-1,1,(N,2,2)); s=rng.uniform(-1,1,(N,1,2))
    return frob(rt@A), frob(s)
# (3,3,3,3) t=2: R_top 2x3, r_bot 1x3, A2 3x3 ; target 3.0
def c3333(N):
    rt=rng.uniform(-1,1,(N,2,3)); rb=rng.uniform(-1,1,(N,1,3)); A=rng.uniform(-1,1,(N,3,3))
    return frob(rt@A), frob(rb@A)
def f3333(N):
    rt=rng.uniform(-1,1,(N,2,3)); A=rng.uniform(-1,1,(N,3,3)); s=rng.uniform(-1,1,(N,1,3))
    return frob(rt@A), frob(s)

print("Means at N=3e5,1.2e6,4.8e6 ; FIN=stable, DIV=climbing (>1.6x/step). target=(1/2)minAdm.\n")
print("== (2,2,2,2) t=1  target 1.5 ==")
for cp in [1.35,1.45,1.55,1.65]:
    mc=stab(c2222,cp); fz=stab(f2222,cp)
    print(f" c'={cp}: coupled {['%.2f'%m for m in mc]} [{verdict(mc)}]   frozen {['%.2f'%m for m in fz]} [{verdict(fz)}]")
print("\n== (3,3,3,3) t=2  target 3.0 ==")
for cp in [2.7,2.9,3.1,3.3]:
    mc=stab(c3333,cp); fz=stab(f3333,cp)
    print(f" c'={cp}: coupled {['%.2f'%m for m in mc]} [{verdict(mc)}]   frozen {['%.2f'%m for m in fz]} [{verdict(fz)}]")
