import itertools

# Compare candidate SCOPES for whether they imply the FACT (Nat): b <= deepTailMin = min(M[2:]).
# Scopes:
#   S_M2      : a+b <= M2            (task's stated scope)
#   S_brickD  : a+b <= min(M1,Mlast) - j    (Brick D hcvg, involves M_last)
#   S_deep    : a+b <= deepTailMin   (proposed correct scope; = S_M2 for arity 3)
#   S_bdeep   : b   <= deepTailMin   (the FACT itself, as a Nat scope)
# Always: GOOD (deepTailMin<=M1), strict shell 1<=j<r, u=t+j, t>=1, a=M0-u>=0, b=M1-u>=0.

def analyze(max_w, aritymin, aritymax):
    stats = {}
    examples = {}
    for arity in range(aritymin, aritymax+1):
        for M in itertools.product(range(1, max_w+1), repeat=arity):
            M0,M1 = M[0],M[1]
            if arity < 3: continue
            deep = min(M[2:])
            Mlast = M[-1]
            if not (deep <= M1):   # GOOD
                continue
            for t in range(1, min(M0,M1)+1):
                r = min(M0-t, M1-t)
                for j in range(1, r):
                    u = t+j
                    a = M0-u; b = M1-u
                    if a<0 or b<0: continue
                    scopes = {
                        'S_M2':    a+b <= M[2],
                        'S_brickD':a+b <= min(M1, Mlast) - j,
                        'S_deep':  a+b <= deep,
                        'S_bdeep': b <= deep,
                    }
                    fact = (b <= deep)
                    for name,inS in scopes.items():
                        if inS:
                            s = stats.setdefault(name, [0,0])
                            s[0]+=1
                            if not fact:
                                s[1]+=1
                                examples.setdefault(name, []).append((M,t,j,u,a,b,deep,Mlast,M[2]))
    return stats, examples

stats, ex = analyze(6, 3, 5)
print("SCOPE           in-scope-cuts   FACT-FAILS(b>deepTailMin)")
for name in ['S_M2','S_brickD','S_deep','S_bdeep']:
    tot,f = stats.get(name,[0,0])
    print(f"  {name:9s}     {tot:8d}          {f}")
print()
for name in ['S_brickD']:
    print(f"--- sample fails under {name} (a+b<=min(M1,Mlast)-j but b>deepTailMin) ---")
    for e in ex.get(name,[])[:12]:
        M,t,j,u,a,b,deep,Mlast,M2 = e
        print(f"   M={M} t={t} j={j} u={u} a={a} b={b} deepTailMin={deep} Mlast={Mlast} M2={M2}  min(M1,Mlast)-j={min(M[1],Mlast)-j}")
