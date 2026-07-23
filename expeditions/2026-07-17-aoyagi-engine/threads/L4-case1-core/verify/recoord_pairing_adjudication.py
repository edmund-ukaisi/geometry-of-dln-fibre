"""seat-L4D def-side adjudication of pnp's unpaired-recoord finding (the 12th catch).

Reproduces, exact sympy: (2,2,2,2) ed1 (corner pivot a=b=0).
 - BAKED canonNormalizationOf (branch i interior Schur + branch ii recoord, NO column clear)
 - canonShearOf (branch i only)
 - FULL clear (branch i + ii + column-b clear)
and the UNIPOTENCY of the naive column-clear shear (the fix-obstruction: it breaks hshear).
Run: python3 recoord_pairing_adjudication.py  (exit 0, prints the verdicts).
"""
import sympy as sp

u = lambda l, r, c: sp.Symbol(f'u{l}{r}{c}')
A0 = sp.Matrix([[u(0,0,0), u(0,0,1)], [u(0,1,0), u(0,1,1)]])
A1 = sp.Matrix([[u(1,0,0), u(1,0,1)], [u(1,1,0), u(1,1,1)]])

# BAKED N_p: branch(i) interior (1,1) = -u010*u001; branch(ii) recoord layer1 col0 (pivot row a=0)
A0b = A0.copy(); A0b[1,1] = A0[1,1] - u(0,1,0)*u(0,0,1)
A1b = A1.copy(); A1b[0,0] = A1[0,0] + u(0,1,0)*u(1,0,1); A1b[1,0] = A1[1,0] + u(0,1,0)*u(1,1,1)
A0b[0,0] = 1  # blockBlowupCoordQuot pivot -> 1
baked = sp.expand((A1b*A0b)[0,0])

A0c = A0.copy(); A0c[1,1] = A0[1,1] - u(0,1,0)*u(0,0,1); A0c[0,0] = 1
canonshear = sp.expand((A1*A0c)[0,0])

A0f = A0b.copy(); A0f[1,0] = 0  # FULL: also clear A0's pivot column (row1,col0)
full = sp.expand((A1b*A0f)[0,0])

w100 = sp.Symbol('w100')
sub = {u(1,0,0): w100 - u(0,1,0)*u(1,0,1)}
print('BAKED       :', baked, '  (coeff-2 defect)')
print('canonShearOf:', canonshear, '  (coeff-1)')
print('FULL clear  :', full)
print('baked  w-frame:', sp.expand(baked.subs(sub)), '  (leftover u010*u101)')
print('full   w-frame:', sp.expand(full.subs(sub)), '  (clean)')
assert baked == u(1,0,0) + 2*u(0,1,0)*u(1,0,1)
assert canonshear == u(1,0,0) + u(0,1,0)*u(1,0,1)

# Unipotency (hshear) of the naive column-clear shear: phi(0,1,0) = -u010 (self-read) -> jacDet must be 1.
allv = [u(0,0,0),u(0,0,1),u(0,1,0),u(0,1,1),u(1,0,0),u(1,0,1),u(1,1,0),u(1,1,1)]
img = {v: v for v in allv}
img[u(0,1,1)] = u(0,1,1) - u(0,1,0)*u(0,0,1)          # branch i
img[u(1,0,0)] = u(1,0,0) + u(0,1,0)*u(1,0,1)          # branch ii
img[u(1,1,0)] = u(1,1,0) + u(0,1,0)*u(1,1,1)          # branch ii
img_naive = dict(img); img_naive[u(0,1,0)] = u(0,1,0) + (-u(0,1,0))       # naive column clear
img_ext   = dict(img); img_ext[u(0,1,0)]   = u(0,1,0) + (-u(0,1,0)*u(0,0,0))  # extend branch i to col=b
J  = sp.Matrix([[sp.diff(img_naive[v], w) for w in allv] for v in allv])
Je = sp.Matrix([[sp.diff(img_ext[v], w)   for w in allv] for v in allv])
print('naive col-clear jacDet =', sp.expand(J.det()),  '(hshear needs 1 -> BROKEN)')
print('extend-branch-i jacDet =', sp.expand(Je.det()), '(hshear needs 1 -> BROKEN)')
assert sp.expand(J.det()) == 0
assert sp.expand(Je.det()) == 1 - u(0,0,0)
print('\nVERDICT: coeff-2 defect CONFIRMED; every column-clear-as-shear BREAKS hshear (unipotency).')
