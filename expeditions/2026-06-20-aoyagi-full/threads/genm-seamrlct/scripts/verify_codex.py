from newton import rlct_monomial, codim_edges
# Codex 2x2 example. ATOMIC Schur coords: K ~ u^2 + (xs)^2+(xz)^2+(tz)^2  (path s-x-z-t) + Morse u.
# vertices: s,x,z,t (indices 0,1,2,3). edges: {s,x}={0,1},{x,z}={1,2},{z,t}={2,3}. path P4.
rl,t0=rlct_monomial([(0,1),(1,2),(2,3)],4); cod=codim_edges([(0,1),(1,2),(2,3)],4)
print(f"ATOMIC path s-x-z-t: rlct(seam)={rl}, codim(seam)={cod}; +u Morse(1/2): total rlct={rl+0.5}, codim/2={(cod+1)/2}")
# RADIALIZED coords: triangle (xy)^2+(xz)^2+(yz)^2 on x,y,z  (UNWEIGHTED, WRONG measure)
rl2,_=rlct_monomial([(0,1),(1,2),(0,2)],3); cod2=codim_edges([(0,1),(1,2),(0,2)],3)
print(f"RADIALIZED triangle x,y,z UNWEIGHTED: rlct(seam)={rl2}, codim(seam)={cod2}; +u: total={rl2+0.5} (SPURIOUS < 3/2)")
# WEIGHTED (Jacobian |y| => w_y=2): weighted fractional cover min{a+2b+c: a+b,a+c,b+c>=1}
from scipy.optimize import linprog
# min w.x=[a,b,c] with weights [1,2,1], constraints a+b>=1,a+c>=1,b+c>=1
res=linprog([1,2,1],A_ub=[[-1,-1,0],[-1,0,-1],[0,-1,-1]],b_ub=[-1,-1,-1],bounds=[(0,None)]*3)
print(f"WEIGHTED cover (w_y=2 from |y| Jacobian): min={res.fun} => rlct(seam)={res.fun/2}; +u: total={res.fun/2+0.5} (= 3/2, RESTORED)")
