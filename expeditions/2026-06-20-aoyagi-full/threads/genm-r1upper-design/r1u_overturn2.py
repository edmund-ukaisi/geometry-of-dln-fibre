import numpy as np
rng=np.random.default_rng(0)
# Multiplier M = ∫_Y (g^2 + ||Y B||^2)^{-a/2} dY over spectator rows Y (box), B fixed rank-deficient.
# ||YB||^2 separates over rows: = sum_r ||y_r B||^2. B = diag-ish with singular values [1,..,1,eps].
# Fit scaling of M vs g (eps fixed small) and vs eps (g fixed small): LOG (slope~0) or POWER (slope<0).

def multiplier(a, nrows, width, sings, g, N=4_000_000):
    # Y: (N, nrows, width); B: width x width diagonal with singular values `sings` (len=width)
    Y=rng.uniform(-1,1,(N,nrows,width))
    B=np.diag(sings)                                  # width x width
    YB=Y@B                                            # (N,nrows,width)
    nrm2=(YB**2).sum(axis=(1,2))
    return ((g*g+nrm2)**(-a/2.0)).mean()* (2.0**(nrows*width))  # box volume factor

def slope(xs,ys):
    lx=np.log(xs); ly=np.log(ys); return np.polyfit(lx,ly,1)[0]

cases=[
 ("(2,2,2,2) t=1",  1, 1, 2),   # a, nrows(M1-t), width(M2)  ; B width=M2
 ("(3,3,3,3) t=2",  1, 1, 3),
 ("(4,4,4,4) t=3",  1, 1, 4),
 ("(4,4,4,4) t=2",  4, 2, 4),   # a=4 (wide cut), 2 spectator rows
 ("(3,3,3,3,3) t=2 [B=prod later]", 1, 1, 3),
]
print("Multiplier M = ∫_Y (g^2+||YB||^2)^{-a/2} dY ;  B singular values [1,..,1,eps].")
print("Scaling vs g (eps=1e-4) and vs eps (g=1e-5): slope 0 => LOG (reduction survives);")
print("slope <0 => POWER loss (joint (S,J) needed).\n")
gs=np.array([1e-1,1e-2,1e-3,1e-4,1e-5])
es=np.array([1e-1,1e-2,1e-3,1e-4,1e-5])
for name,a,nr,w in cases:
    sings=lambda eps,w=w:[1.0]*(w-1)+[eps]
    Mg=[multiplier(a,nr,w,sings(1e-4),g) for g in gs]
    Me=[multiplier(a,nr,w,sings(e),1e-5) for e in es]
    sg=slope(1/gs, Mg); se=slope(1/es, Me)
    print(f"{name}: a={a}, Y={nr}x{w}")
    print(f"    vs 1/g : M={['%.2f'%m for m in Mg]}  slope={sg:+.3f}  {'LOG' if sg<0.25 else 'POWER('+('%.2f'%sg)+')'}")
    print(f"    vs 1/eps: M={['%.2f'%m for m in Me]}  slope={se:+.3f}  {'LOG' if se<0.25 else 'POWER('+('%.2f'%se)+')'}")
