import sympy as sp, random

def rrat(lo, hi, rng):
    num = rng.randint(0, 1000)
    return lo + (hi-lo)*sp.Rational(num,1000)

def field_a_check(M0, M1, M2, trials=300, label=""):
    r = M0; s = M1 - M0
    assert s > 0
    delta = sp.Rational(1,1)
    eta = (delta/4 if r==1 else delta/(4*(r-1)))
    maxlam = sp.Rational(0); maxent = sp.Rational(0); fails = 0; dfail=0
    for t in range(trials):
        rng = random.Random(1000+M0*97+M1*13+M2*7+t)
        P1 = sp.zeros(r,r)
        for i in range(r):
            for j in range(r):
                P1[i,j] = rrat(delta/2, delta, rng) if i==j else rrat(-eta, eta, rng)
        P2 = sp.Matrix(r, s, lambda i,j: rrat(-eta,eta,rng))
        Sb = sp.Matrix(s, M2, lambda i,j: rrat(-eta,eta,rng))   # s x c
        d = P1.det()
        if d == 0: dfail+=1; continue
        Lam0 = P1.inv()*P2                # r x s
        lam_inf = max(abs(Lam0[i,j]) for i in range(r) for j in range(s))
        maxlam = max(maxlam, lam_inf)
        LS = Lam0*Sb                      # r x c
        ent = max(abs(delta*1 - LS[i,j]) for i in range(r) for j in range(M2))
        maxent = max(maxent, ent)
        if ent > 2*delta: fails += 1
    bound = (sp.Rational(s, r-1) if r>=2 else sp.nan)
    print(f"{label} M0={M0},M1={M1},M2={M2} r={r},s={s}: eta={eta}, max|Lam0|_inf={maxlam} (pred<=s/(r-1)={bound}), "
          f"max decoded entry={maxent} (need<=2), entry-fails={fails}, detfails={dfail}")

field_a_check(2,3,1, label="(2,3,1) anchor")
field_a_check(2,4,2, label="(2,4,2) smeared non-square M")
field_a_check(3,4,1, label="(3,4,1)")
field_a_check(5,6,2, label="(5,6,2) r=5 (specific delta/8 would fail DD)")
field_a_check(5,8,3, label="(5,8,3) r=5,s=3")
field_a_check(1,3,2, label="(1,3,2) r=1")
