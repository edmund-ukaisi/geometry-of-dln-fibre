import sympy as sp
print("="*78)
print("CHECK: is K=core homogeneous in the ratio coords z=(u,v,W,B)? (does deepest_le apply to K?)")
print("="*78)
# core = ||Ahat B||^2, Ahat=[[1,u],[v,W]], B=(B0;Bred). The ratio coords are (u,v,W) AND the B-coords.
# Is core homogeneous in z=(u,v,W,B) jointly? Scale z by t: u->tu, v->tv, W->tW, B->tB.
# Ahat(t) = [[1, tu],[tv, tW]]  -- the (0,0)=1 is NOT scaled. So Ahat is NOT homogeneous (the unit pivot).
# => core is NOT jointly homogeneous in (u,v,W,B). deepest_le does NOT apply to K directly.
m,k,n=2,3,2
u=sp.Matrix(1,k-1,lambda i,j:sp.Symbol(f'u{j}'))
v=sp.Matrix(m-1,1,lambda i,j:sp.Symbol(f'v{i}'))
W=sp.Matrix(m-1,k-1,lambda i,j:sp.Symbol(f'W{i}{j}'))
B=sp.Matrix(k,n,lambda i,j:sp.Symbol(f'B{i}{j}'))
Ahat=sp.Matrix(sp.BlockMatrix([[sp.Matrix([[1]]),u],[v,W]]))
core=sum((Ahat*B)[i,j]**2 for i in range(m) for j in range(n))
t=sp.Symbol('t')
subs={**{u[0,j]:t*u[0,j] for j in range(k-1)}, **{v[i,0]:t*v[i,0] for i in range(m-1)},
      **{W[i,j]:t*W[i,j] for i in range(m-1) for j in range(k-1)},
      **{B[i,j]:t*B[i,j] for i in range(k) for j in range(n)}}
core_scaled=core.subs(subs)
ratio=sp.simplify(core_scaled/core)  # if homogeneous deg d, = t^d
print("core(t·z)/core(z) constant power of t?", "NO -- unit pivot breaks it" if not ratio.free_symbols<= {t} else ratio)
print(" (the (0,0)=1 entry of Ahat is not scaled => core not jointly homogeneous in z)")
print()
print("CONSEQUENCE: deepest_le_of_homogeneous_core does NOT apply to K=core in the ratio coords.")
print("So my 'global homogeneity ray covers every v in Vz' shortcut is WRONG for the CHILD box.")
print()
print("CORRECT picture: deepest_le applies to the RAW loss dlnLoss(child) on the CHILD's PARAMETER")
print("space (where it IS homogeneous, degree 2L), giving rlctAtOn(child,0) <= rlctAtOn(child, w)")
print("for w in the child's PARAMETER space. The recursion's hKint is over the child's parameter box")
print("(Bred = child's deeper params; S = child's deepest layer), NOT the ratio coords of THIS node.")
print("So the ordering DOES apply -- but at the CHILD's parameter level, via the recursion, not as a")
print("one-node homogeneity ray on K. The box-collapse is RECURSIVE: each node's hKint is the child's")
print("box-integ, closed by the child's OWN deepest_le at its parameter origin.")
