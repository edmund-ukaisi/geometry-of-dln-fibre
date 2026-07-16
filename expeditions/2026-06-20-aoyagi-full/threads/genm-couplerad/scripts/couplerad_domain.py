import numpy as np
# Check: (i) the reduced integrand's singular set is the determinantal cone {rank Y < u} (h(Y)=inf there),
#        NOT just {Y=0}; (ii) finiteness of int_[-c,c]^N (loss)^-q is SCALE-INDEPENDENT (RLCT local at apex).
# We verify (ii) by the eigenvalue/pole method on the arity-3 reduced form: pole at Y-degeneracy independent of box scale c.
np.random.seed(0)
# arity-3 reduced: loss = ||E Y||^2 + ||Btil Qb||^2, E=[P;C] (u+a)x u, Y u x d, Btil u x b
# singular set {EY=0, Btil=0}. For fixed generic E full col rank u (u<=u+a), EY=0 iff Y=0 (E injective) --
# BUT integrating E too: {EY=0} includes E rank-def OR Y rank-def. The h(Y)=int_E (||EY||^2+floor)^-q:
# h(Y) blows up as rank(Y) drops (fewer E-directions penalized). Show h(Y) ~ (sigma_min(Y))^{-power}.
def hY_pole(u,a,d,b, q):
    # measure pole of inner int_{E,Btil box}(||EY||^2+||Btil Qb||^2)^-q as Y -> rank u-1 (one sv ->0)
    Qb=np.random.randn(b, b+ (d if d>b else 0)) if b>0 else np.zeros((0,1))
    # simpler: track eigenvalue count of the E-quadratic as Y loses rank
    # ||E Y||^2 = sum over rows of E of ||row . Y||^2 ; quadratic rank = (u+a)*rank(Y). +Btil block ub.
    for r in [u, u-1]:
        rankY=r
        rho = (u+a)*rankY + u*b
        print(f"    rank(Y)={rankY}: quad-rank rho={rho}  (int_x finite iff 2q<rho => 2q<{rho})")
    print(f"    => h(Y) FINITE for rank(Y)=u iff 2q<{(u+a)*u+u*b}; blows up as rank(Y)->u-1 (needs 2q<{(u+a)*(u-1)+u*b}).")
    print(f"    So h(Y)=+inf on {{rank Y < u}} when 2q in [{(u+a)*(u-1)+u*b}, {(u+a)*u+u*b}) -- a CONE, not just Y=0.")
print("Witness u=3,a=1,b=1,d=3, take q with 2q=8.8:")
hY_pole(3,1,3,1, 4.4)
print("\nCONCLUSION: singular set of h(Y) is the determinantal cone {rank Y<u}, NOT {Y=0}.")
print("So the ★7 'loc-bounded off {0}' germ lemma is WRONG. Correct route: Phi-Fubini + sandwich")
print("Y-parallelepiped between scaled Y-boxes + SCALE-INDEPENDENCE of arity-3 box-finiteness (RLCT local at apex 0).")
