#!/usr/bin/env python3
"""
Verify the route-(c) fibration identity exactly:
    dim Σ̄^r  =  δ  +  dim F          (δ = dim Mat^{=r} = r(d_N+d_0−r), F = mult^{-1}(E))
equivalently  codim Σ̄^r = codim F − δ, i.e. C = (C+δ) − δ.  [trivially consistent once we
know dim F = card−C−δ and dim Σ̄^r = card−C; this checks the geometry is internally coherent.]

What this ACTUALLY tests independently: that dim Σ̄^r (computed by Singular as the rank-≤r product
locus) equals δ + dim(fibre over E) (computed by Singular). If both come out matching card−C and
card−C−δ with the engine's C, the fibration identity holds on the nose.

We compute, exactly via Singular:
  dim Σ̄^r  (= dim of {(A_i): rank(A_{N-1}...A_0) ≤ r}), and
  dim F    (= dim of {(A_i): A_{N-1}...A_0 = E}),
and check dim Σ̄^r − dim F == δ, and codim Σ̄^r == C (engine).
Small cases only (Singular cost).
"""
import subprocess, tempfile, os

def singular_dim_sigma_and_fibre(d, r):
    """Return (dim_sigma_bar_r, dim_fibre_E, ambient) via Singular."""
    N=len(d)-1
    # build variable names a{i}_{p}_{q} for factor i, p in d[i+1], q in d[i]
    vs=[]
    for i in range(N):
        for p in range(d[i+1]):
            for q in range(d[i]):
                vs.append(f"x{i}_{p}_{q}")
    ambient=len(vs)
    ring=f"ring R=0,({','.join(vs)}),dp;\n"
    # build matrices and product
    code=ring+'LIB "matrix.lib"; LIB "linalg.lib";\n'
    for i in range(N):
        rows=d[i+1]; cols=d[i]
        entries=",".join(f"x{i}_{p}_{q}" for p in range(rows) for q in range(cols))
        code+=f"matrix M{i}[{rows}][{cols}] = {entries};\n"
    # product P = M_{N-1} * ... * M_0
    prodexpr="M0" if N==1 else "*".join(f"M{i}" for i in range(N-1,-1,-1))
    # careful: matrix mult order M_{N-1}*...*M_0
    prodexpr="*".join(f"M{i}" for i in range(N-1,-1,-1))
    code+=f"matrix P = {prodexpr};\n"
    # Sigma^r : ideal of (r+1)-minors of P
    code+=f"ideal Sig = minor(P, {r+1});\n"
    code+="int dS = dim(std(Sig));\n"
    # Fibre over E = diag(I_r,0) of size d_N x d_0
    code+=f"matrix E[{d[N]}][{d[0]}];\n"
    for j in range(r):
        code+=f"E[{j+1},{j+1}]=1;\n"
    code+="ideal Fib = ideal(P - E);\n"
    code+="int dF = dim(std(Fib));\n"
    code+='print(dS); print(dF);\n$\n'
    with tempfile.NamedTemporaryFile('w',suffix='.sing',delete=False) as f:
        f.write(code); fn=f.name
    try:
        out=subprocess.run(["Singular","-q",fn],capture_output=True,text=True,timeout=300).stdout
    finally:
        os.unlink(fn)
    nums=[int(x) for x in out.split() if x.strip().lstrip('-').isdigit()]
    return nums[0], nums[1], ambient

# engine C values (from ccodim.py)
Cval={("2,2,2",0):3,("2,2,2",1):1,("2,2,2",2):0,("2,2,3",1):1,("3,2,3",1):2,
      ("3,3,3",1):3,("1,2,1",0):1,("1,2,1",1):0,("2,2,2,2",1):1,("2,3,2",1):1}

cases=[([2,2,2],0),([2,2,2],1),([2,2,2],2),([2,2,3],1),([3,2,3],1),
       ([1,2,1],0),([1,2,1],1),([2,2,2,2],1),([2,3,2],1)]
print(f"{'d':<13}{'r':<3}{'dimΣ̄':<7}{'dimF':<6}{'δ':<4}{'dimΣ̄−dimF':<11}{'codimΣ̄':<9}{'C':<4}{'check'}")
allok=True
for d,r in cases:
    N=len(d)-1; card=sum(d[i+1]*d[i] for i in range(N)); dl=r*(d[N]+d[0]-r)
    dS,dF,amb=singular_dim_sigma_and_fibre(d,r)
    C=Cval.get((",".join(map(str,d)),r))
    codimS=amb-dS
    fib_id_ok = (dS-dF==dl)
    codim_ok = (codimS==C) if C is not None else None
    allok = allok and fib_id_ok and (codim_ok is not False)
    print(f"{str(d):<13}{r:<3}{dS:<7}{dF:<6}{dl:<4}{dS-dF:<11}{codimS:<9}{str(C):<4}"
          f"{'OK' if (fib_id_ok and codim_ok) else '**FAIL**'}")
print("ALL:", "OK" if allok else "FAIL")
