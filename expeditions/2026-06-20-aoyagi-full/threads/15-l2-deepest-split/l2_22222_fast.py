"""L=4 (2,2,2,2,2) r=1: structure (rank, core entries) symbolically; value numerically."""
import sympy as sp, numpy as np
S=sp.Matrix([[1,0],[0,0]])
ws=[sp.symbols(f'{c}0:4',real=True) for c in 'abcde']
As=[S+sp.Matrix(2,2,w) for w in ws]
P=As[0]
for A in As[1:]: P=(P*A).applyfunc(sp.expand)
E=(P - S**5).applyfunc(sp.expand)
allv=[v for w in ws for v in w]
errs=[E[i,j] for i in range(2) for j in range(2)]
J=sp.Matrix([[sp.diff(e,vv).subs({x:0 for x in allv}) for vv in allv] for e in errs])
print("L=4 error-Jacobian rank at 0 =", J.rank(), " (expect nReg=3)")
print("core entries (zero linear part):",
      [divmod(idx,2) for idx,e in enumerate(errs)
       if sum(sp.diff(e,vv).subs({x:0 for x in allv})*vv for vv in allv)==0])
