#!/usr/bin/env python3
# LOCALITY PROBE: where does the case-1(2) "inherited divExp(mergeIdx)-1" exponent actually come
# from? The addendum guessed it comes from the case-1(2) node's own intermediate-point substitution.
# This probe shows it does NOT: the case-1(2) node's atom carries ONLY runLen*resCols; the inherited
# part is contributed by the ANCESTOR birth node of mergeIdx (outer to the case-1(2) node), whose atom
# reads the u-corner AFTER the case-1(2) node scaled it. => the regrouping is a NON-LOCAL cocycle.
import sympy as sp

def chart(point, center, pivot):
    piv = point[pivot]
    return {c: (piv if c == pivot else (piv*point[c] if c in center else point[c])) for c in point}

def det_of(path, cells):
    src = {c: sp.Symbol('z_'+c, positive=True) for c in cells}
    pt = dict(src)
    for node in reversed(path):
        pt = chart(pt, node['center'], node['pivot'])
    order = list(cells)
    J = sp.Matrix([[sp.diff(pt[r], src[c]) for c in order] for r in order])
    return sp.factor(J.det()), src

cells = ['A','b','c','d','e']
# (i) SUBTREE rooted at the case-1(2) node alone (A pre-exists as "incoming", not blown up here):
#     just the case-1(2) chart {A,e} pivot e.  A is the u-corner (scaled), e the new pivot.
sub = [ {'center':['A','e'], 'pivot':'e'} ]
det_sub, src = det_of(sub, cells)
zA, ze = src['A'], src['e']
print("case-1(2) node ALONE (A incoming):")
print(f"   |det| = {det_sub}")
print(f"   e-exponent here = {sp.degree(sp.Poly(det_sub, ze))} (= runLen*resCols = 1; NO inheritance)")
print(f"   A-exponent here = {sp.degree(sp.Poly(det_sub, zA))} (= 0; A not blown up in this subtree)")
print()
# (ii) FULL path = ancestor case-2 birth of A (2x2) OUTER + the case-1(2) node INNER:
full = [ {'center':['A','b','c','d'], 'pivot':'A'},   # ancestor births A (divExp 4), OUTER
         {'center':['A','e'], 'pivot':'e'} ]          # case-1(2) splits e off A, INNER
det_full, src2 = det_of(full, cells)
zA2, ze2 = src2['A'], src2['e']
print("FULL path (ancestor case-2 births A, then case-1(2) splits e):")
print(f"   |det| = {det_full}")
print(f"   e-exponent = {sp.degree(sp.Poly(det_full, ze2))} (= divExp(A)-1 + runLen*resCols = 3+1 = 4)")
print(f"   => the extra 3 = divExp(A)-1 appeared ONLY when the ANCESTOR birth of A was included.")
print()
print("CONCLUSION: the case-1(2) inheritance is NON-LOCAL. The case-1(2) node's atom = runLen*resCols;")
print("the divExp(mergeIdx)-1 threads in via the ANCESTOR birth atom reading the u-corner z_A AFTER")
print("the case-1(2) chart scaled it (z_A |-> z_e * z_A). Corrects the addendum's local expectation.")
