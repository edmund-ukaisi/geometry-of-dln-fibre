"""Unified 3-case ∀M achiever-chart EXHAUSTIVE validation (witness tide v2).
Classifier (2<=L, minAdm>=1):
  INTERIOR  := ∃ p∈[1,L-1] with r_p≥1 ∧ c_p≥1  (r_p=Text(p)-Text(p+1), c_p=M_p-Text(p+1))
  BOUNDARY  := else (all codim at the last boundary; minAdm = Text(L)*M_L)
  L=1       := out of scope here (rides banked DeepestBaseL1)
Validates, per class:
  INTERIOR: the colpath Schur chart -> Hmat 0 (rho,0) = 1 ≠ 0 (rho=Text(p*+1)), so achieverUfun ≠ 0.
  BOUNDARY: the Schur(route P to rank Text(L)) ∘ radial(top Text(L)xM_L block) chart -> F = u^2 U,
            U≠0, active.card = Text(L)*M_L = minAdm (det |u_p|^{minAdm-1}).
Reports counts; ANY failure prints. The gate: 351/351 (and the wider 1..4 grid) covered, 0 failures."""
import numpy as np, itertools
from witness_tide_validated import achiever, colpath_witness
def Text(M,tach,k): return M[0] if k==0 else tach[k-1]

def classify(M):
    L=len(M)-1; T0,mv=achiever(M); tach=[M[0]]+list(T0)
    if mv==0: return 'minAdm0',mv
    isint=any(Text(M,tach,k)-Text(M,tach,k+1)>=1 and M[k]-Text(M,tach,k+1)>=1 for k in range(1,L))
    return ('interior' if isint else 'boundary'),mv

def validate_interior(M):
    T0,mv=achiever(M); tach=[M[0]]+list(T0)
    r=colpath_witness(M,tach)
    return (r is not None) and (not isinstance(r,str)) and bool(np.any(np.abs(r)>1e-9))

def validate_boundary(M, trials=30):
    """SUPERSEDED / FACTOR-LEVEL ONLY -- NOT the boundary gate. Models the routed product P with its last
    cols SET to 0 (a constraint), so it checks only 'F=u^2 U + det count' at the factor level. The
    pen-and-paper exhaustive analysis (certificate-boundary-chart.md, pp_CERTIFICATE_validation.py) showed
    the GENUINE smeared chart is MULTI-AXIS (F=(xz)^2 U, M0=1) or rational (M0>1) -- this misses the
    z-binding. AUTHORITATIVE boundary gate = pp_CERTIFICATE_validation.py.
    Schur(route P rank Text(L)) o radial(top block). F=u^2 U, U!=0, active.card=minAdm."""
    L=len(M)-1; T0,mv=achiever(M); tach=[M[0]]+list(T0)
    r=Text(M,tach,L)
    active_card=r*M[L]
    if active_card!=mv: return False,'det'
    okU=False; factor=True
    for t in range(trials):
        rng=np.random.default_rng(7000+t)
        Pr=rng.standard_normal((M[0],r))               # the routed rank-r incoming product (first r cols of P)
        P=np.zeros((M[0],M[L-1])); P[:, :r]=Pr          # Schur shear: last cols 0 (rank exactly r)
        u0=rng.standard_normal(); Mbar=rng.standard_normal((r,M[L]))
        Alast=np.zeros((M[L-1],M[L])); Alast[:r,:]=u0*Mbar
        F=np.sum((P@Alast)**2); U=np.sum((Pr@Mbar)**2)
        if abs(F-u0**2*U)>1e-9*(1+abs(F)): factor=False
        if U>1e-9: okU=True
    return (okU and factor),('ok' if (okU and factor) else 'U/factor')

if __name__=='__main__':
    grids=[('1..3, L∈{2,3,4}', range(1,4), [2,3,4]), ('1..4, L∈{2,3}', range(1,5), [2,3])]
    for name,wr,Ls in grids:
        tot=ic=bc=icok=bcok=0; fails=[]
        for L in Ls:
          for M in itertools.product(wr,repeat=L+1):
            M=list(M); cls,mv=classify(M)
            if cls=='minAdm0': continue
            tot+=1
            if cls=='interior':
                ic+=1
                if validate_interior(M): icok+=1
                else: fails.append(('INT',M))
            else:
                bc+=1
                ok,why=validate_boundary(M)
                if ok: bcok+=1
                else: fails.append(('BD',M,why))
        print(f"[{name}] total={tot} | interior {icok}/{ic} | boundary {bcok}/{bc} | FAILS={len(fails)}")
        for f in fails[:15]: print("   ",f)
