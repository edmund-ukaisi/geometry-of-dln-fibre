# Generate a Singular script computing dim mult^{-1}(E) for a given d, r.
import sys

def gen(d, r, name="F"):
    N=len(d)-1
    # variables: a{i}_{rr}_{cc} for factor i (d[i+1] x d[i])
    vars=[]
    for i in range(N):
        for rr in range(d[i+1]):
            for cc in range(d[i]):
                vars.append(f"a{i}_{rr}_{cc}")
    varstr=",".join(vars)
    lines=[f"ring R = 0, ({varstr}), dp;"]
    # build matrices
    for i in range(N):
        entries=[]
        for rr in range(d[i+1]):
            for cc in range(d[i]):
                entries.append(f"a{i}_{rr}_{cc}")
        lines.append(f"matrix A{i}[{d[i+1]}][{d[i]}] = {','.join(entries)};")
    # product M = A_{N-1}*...*A_0
    prod="A"+str(N-1)
    for i in range(N-2,-1,-1):
        prod=f"({prod}*A{i})"
    lines.append(f"matrix M = {prod};")
    # ideal: M[rr,cc] - E[rr,cc], E=diag(I_r,0), size d[N] x d[0]
    gens=[]
    for rr in range(d[N]):
        for cc in range(d[0]):
            e = 1 if (rr==cc and rr<r) else 0
            if e==0:
                gens.append(f"M[{rr+1},{cc+1}]")
            else:
                gens.append(f"M[{rr+1},{cc+1}]-1")
    lines.append(f"ideal I = {','.join(gens)};")
    card=sum(d[i+1]*d[i] for i in range(N))
    lines.append(f'"d={d} r={r} card={card}: fibre dim =", dim(std(I));')
    return "\n".join(lines)

if __name__=="__main__":
    import ast
    d=ast.literal_eval(sys.argv[1]); r=int(sys.argv[2])
    print(gen(d,r))
