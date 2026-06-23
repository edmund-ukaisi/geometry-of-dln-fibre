"""
(3,2,3) r=1 EXPLICIT SPLIT test. Error entries (normalized deepest point):
 regular (linear part): E00,E01,E02,E10,E20  (5 = nReg)
 core (no linear part):  E11,E12,E21,E22      (the (2,1,2) core block)

Strategy mirrors (2,2,2):
 1. unit-pivot triangular solve of the 5 regular entries (each has a unit linear pivot).
 2. det-core change so the core entries become (det-core product) + (regular)*(regular) cross.
 3. completion of squares to absorb the regular*regular cross-terms.
Then F = sum_{i<5} y_i^2 + ||(2,1,2)-core||^2.

We test (1)+(2): after solving the 5 regular pivots and substituting into the 4 core entries,
do the core entries become  Uij * V  +  (regular-coordinate cross terms)/unit  ?
i.e. is the entanglement again of the universal 'det-core product + reg-cross' form?
"""
import sympy as sp
a = sp.symbols('a0:6', real=True)
b = sp.symbols('b0:6', real=True)
a0,a1,a2,a3,a4,a5=a; b0,b1,b2,b3,b4,b5=b
allv=list(a)+list(b)
E00 = a0*b0 + a0 + a1*b3 + b0
E01 = a0*b1 + a1*b4 + b1
E02 = a0*b2 + a1*b5 + b2
E10 = a2*b0 + a2 + a3*b3
E20 = a4*b0 + a4 + a5*b3
E11 = a2*b1 + a3*b4
E12 = a2*b2 + a3*b5
E21 = a4*b1 + a5*b4
E22 = a4*b2 + a5*b5

x = sp.symbols('x0:5', real=True)  # regular coords = the 5 regular entries
# Triangular unit-pivot solve. Identify pivot var for each regular entry (unit coefficient):
# E00 = b0(1+a0) + a0 + a1 b3  -> pivot b0, unit (1+a0)
# E01 = b1(1+a0) + a1 b4       -> pivot b1, unit (1+a0)
# E02 = b2(1+a0) + a1 b5       -> pivot b2, unit (1+a0)
# E10 = a2(1+b0) + a3 b3       -> pivot a2, unit (1+b0)
# E20 = a4(1+b0) + a5 b3       -> pivot a4, unit (1+b0)
# pivots: b0,b1,b2 (from row-0 entries), a2,a4 (from col-0 entries). 5 pivots. Core vars: a0,a1,a3,a5,b3,b4,b5.
# Solve in dependency order: b0,b1,b2 depend on (x,a0,a1,b3,b4,b5); then a2,a4 depend on (x,b0,a3,a5,b3).
b0s = (x[0] - a0 - a1*b3)/(1+a0)
b1s = (x[1] - a1*b4)/(1+a0)
b2s = (x[2] - a1*b5)/(1+a0)
a2s = (x[3] - a3*b3)/(1+b0s)
a4s = (x[4] - a5*b3)/(1+b0s)
sub = {b0:b0s, b1:b1s, b2:b2s, a2:a2s, a4:a4s}

# verify pivots recover x:
for nm,e,xi in [("E00",E00,x[0]),("E01",E01,x[1]),("E02",E02,x[2]),("E10",E10,x[3]),("E20",E20,x[4])]:
    chk = sp.simplify(e.subs(sub)-xi)
    print(f"  {nm} pulls back to x: {nm}-x = {chk}")

# Now the 4 core entries after substitution:
print("\nCore entries after substituting the 5 regular pivots:")
core_subs={}
for nm,e in [("E11",E11),("E12",E12),("E21",E21),("E22",E22)]:
    es = sp.simplify(e.subs(sub))
    core_subs[nm]=es
    print(f"  {nm}_sub =", es)

# On the regular-zero slice x=0:
print("\nCore on {x=0} (pure core slice):")
for nm,es in core_subs.items():
    print(f"  {nm} =", sp.simplify(es.subs({xi:0 for xi in x})))
print("\nExpected (2,1,2) core entries (index>=r blocks): products through width-1 middle:")
print("  C0=(a3,a5)^T (col r=1 of W0 rows>=1), C1=(b4,b5) (row r=1 of W1 cols>=1)? -> a3 b4, a3 b5, a5 b4, a5 b5")
