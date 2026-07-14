import sympy as sp
# General Cayley-Haar density claim: dQ ~ det(I+S)^{-(s-1)} dS.  Verify det(I+S) for s=2,3,4.
def skew(params, s):
    S=sp.zeros(s,s); idx=0
    for i in range(s):
        for j in range(i+1,s):
            S[i,j]=params[idx]; S[j,i]=-params[idx]; idx+=1
    return S
for s in [2,3,4]:
    n=s*(s-1)//2
    ps=sp.symbols(f'p0:{n}')
    S=skew(ps,s)
    d=sp.factor(sp.expand((sp.eye(s)+S).det()))
    print(f"s={s}: det(I+S) =", d, "   density det(I+S)^-(s-1) -> exponent -(s-1)=",-(s-1))
# cross-check my measured factors:
#   s=2: 1/(1+t^2)          = det(I+S)^-1 with det=1+t^2       -> (s-1)=1 OK
#   s=3: -8/(1+a^2+b^2+c^2)^2 = det(I+S)^-2 with det=1+a^2+b^2+c^2 -> (s-1)=2 OK
