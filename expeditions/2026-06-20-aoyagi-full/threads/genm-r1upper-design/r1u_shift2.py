import sympy as sp

z, g, h, c, w = sp.symbols('z g h c w', positive=True)

print("1-D exponent-shift core:  J(g,h;c') = ∫_0^∞ (g^2 + z^2 h^2)^{-c'} z^{a-1} dz")
print("Substitute z=(g/h)w  ->  J = (g/h)^a g^{-2c'} · I(a,c'),  I=∫_0^∞(1+w^2)^{-c'}w^{a-1}dw\n")
print(f"{'a=(M0-t)(M1-t)':>16} | {'I(a,c) closed form':<32} | converges iff | tail exponent shift")
print("-"*95)
for aval in [1,2,3,4,6]:
    I = sp.integrate((1+w**2)**(-c) * w**(aval-1), (w, 0, sp.oo))
    I = sp.simplify(I)
    # J scaling in g:
    Jg = sp.simplify((g)**(aval) * g**(-2*c))  # g-power = a - 2c
    print(f"{aval:>16} | {str(I):<32} | c > {sp.Rational(aval,2)}       | g^(a-2c') = g^-2(c'-a/2)")
print()
print("=> per-boundary peel is EXACT: after the z-integral the tail integrand is")
print("   g^{-2 c''} with  c'' = c' - a/2 = c' - (1/2)(M0-t)(M1-t).  Shift is real & exact.")

# concrete: (2,2,2) boundary-0 cut t=1: a=(2-1)(2-1)=1. shift c'' = c' - 1/2.
print("\nConcrete (2,2,2), boundary-0 cut t=1:  a=1, c''=c'-1/2.")
print("  Tail chain (t=1,M2=2) = free 1x2 vector v; ∫_box ||v||^{-2c''} over R^2 finite iff c''<1")
print("  => c'-1/2 < 1  => c' < 3/2 = (1/2)minAdm(2,2,2). EXACT.\n")

# Beta-value spot check numeric
import mpmath as mp
print("Numeric spot-check of the closed form vs direct quad (a=2, c=1.7, g=0.1,h=0.3):")
aval, cval, gval, hval = 2, 1.7, 0.1, 0.3
direct = mp.quad(lambda zz: (gval**2 + zz**2*hval**2)**(-cval) * zz**(aval-1), [0, mp.inf])
closed = (gval/hval)**aval * gval**(-2*cval) * 0.5 * mp.beta(aval/2, cval-aval/2)
print(f"   direct quad = {direct}")
print(f"   closed form = {closed}")
print(f"   ratio       = {direct/closed}")
