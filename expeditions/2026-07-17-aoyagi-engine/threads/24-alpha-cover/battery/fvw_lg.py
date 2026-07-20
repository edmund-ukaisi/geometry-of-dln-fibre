#!/usr/bin/env python3
# pnp-full (thread 24): Q3 -- is the pivot-column clear (Lg) / pivot-row clear (Rg) realizable as a
# det-1 CHART map (like the div-free interior flatElemShear), or does the corner-division force
# something that is NOT det-1 (a fourth structural atom / a projection)? Compute the EXACT Jacobian
# determinant of each atom's source->result map on a single layer's cells. MC never used.
import sympy as sp

def layer(m, n, tag='a'):
    return {(i, j): sp.Symbol(f'{tag}{i}{j}', real=True) for i in range(m) for j in range(n)}, m, n

def jac_det(before, after, m, n):
    coords = [(i, j) for i in range(m) for j in range(n)]
    vec_after = sp.Matrix([sp.together(after[c]) for c in coords])
    vec_src = [before[c] for c in coords]
    J = vec_after.jacobian(vec_src)
    return sp.factor(sp.simplify(J.det()))

# --- atoms on a single layer, corner c=0 ---
def interior_shear(P, m, n, c=0):
    """div-free flatElemShear form: (i,j) -= (i,c)*(c,j), i,j>c."""
    Q = dict(P)
    for i in range(c + 1, m):
        for j in range(c + 1, n):
            Q[(i, j)] = P[(i, j)] - P[(i, c)] * P[(c, j)]
    return Q

def lg_div(P, m, n, c=0):
    """pivot-column clear, DIVISION form (Gaussian row-reduce): (i,j) -= ((i,c)/(c,c))*(c,j), i>c, j>=c."""
    Q = dict(P); p = P[(c, c)]
    for i in range(c + 1, m):
        f = P[(i, c)] / p
        for j in range(c, n):
            Q[(i, j)] = P[(i, j)] - f * P[(c, j)]
    return Q

def rg_div_inlayer(P, m, n, c=0):
    """pivot-row clear IN-LAYER, DIVISION form: (i,j) -= ((c,j)/(c,c))*(i,c), j>c."""
    Q = dict(P); p = P[(c, c)]
    for j in range(c + 1, n):
        f = P[(c, j)] / p
        for i in range(m):
            Q[(i, j)] = P[(i, j)] - f * P[(i, c)]
    return Q

def lg_shear_productform(P, m, n, c=0):
    """CANDIDATE det-1 realization: clear pivot column by a product-of-cells shear that does NOT
       divide -- (i,c) -= (i,c)*<something>. There is no single cell whose product with (i,c) equals
       (i,c); the honest product-form that does not divide is the interior-only shear, which leaves
       (i,c) UNCHANGED. So this returns interior_shear (the div-free reachable), for contrast."""
    return interior_shear(P, m, n, c)

def beta_first_then_lg_divfree(P, m, n, c=0):
    """Aoyagi order: BLOW UP first (corner->u, others scaled by u), THEN clear pivot col.
       After beta the ratio (i,c)/(c,c) = u*orig(i,c)/u = orig(i,c); but orig(i,c) is NOT a post-beta
       coordinate (post-beta cell is u*orig(i,c)). Model beta as introducing fresh u = corner and
       old(i,j)=u*new(i,j): here we test whether the pivot-col clear on the POST-beta params is div-free.
       Post-beta params: corner stays symbol u (=(c,c)); (i,j)!=corner -> (c,c)*(i,j). Then Lg:
       (i,j) -= ((post(i,c))/(post(c,c)))*post(c,j) = ((c,c)*(i,c)/(c,c))*((c,c)*(c,j)) ... still needs /."""
    Q = dict(P); u = P[(c, c)]
    post = dict(P)
    for i in range(m):
        for j in range(n):
            if (i, j) != (c, c):
                post[(i, j)] = u * P[(i, j)]
    # now clear pivot col on post (division by post corner = u)
    R = dict(post); p = post[(c, c)]
    for i in range(c + 1, m):
        f = post[(i, c)] / p
        for j in range(c, n):
            R[(i, j)] = post[(i, j)] - f * post[(c, j)]
    return R

if __name__ == "__main__":
    for (m, n) in [(2, 2), (3, 3), (3, 4), (4, 3)]:
        P, mm, nn = layer(m, n)
        print("=" * 84)
        print(f"single layer {m}x{n}, corner (0,0)")
        print("=" * 84)
        di = jac_det(P, interior_shear(P, m, n), m, n)
        print(f"  interior shear (div-free flatElemShear)   |det Jac| = {di}   (expect 1)")
        dlg = jac_det(P, lg_div(P, m, n), m, n)
        print(f"  Lg pivot-column clear (DIVISION form)      |det Jac| = {dlg}")
        drg = jac_det(P, rg_div_inlayer(P, m, n), m, n)
        print(f"  Rg pivot-row clear in-layer (DIVISION)     |det Jac| = {drg}")
        # check: does lg_div send the pivot column to 0 (a projection)?
        Q = lg_div(P, m, n)
        zeroed = [(i, 0) for i in range(1, m) if sp.simplify(Q[(i, 0)]) == 0]
        print(f"  Lg sends pivot-column cells to 0 (projection): {zeroed}")
