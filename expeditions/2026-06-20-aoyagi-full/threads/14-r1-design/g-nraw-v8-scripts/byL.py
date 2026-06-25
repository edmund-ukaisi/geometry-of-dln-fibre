"""Where exactly does the cert-104b V8 formula  min(mk, M_last + minAdm(child)) = minAdm  hold/fail, by L?"""
from itertools import product
from minadm import min_adm

def child(M):
    M=list(M); M[0]-=1; M[1]-=1; return tuple(M)

def v8(M):
    mk=M[0]*M[1]; return min(mk, M[-1]+min_adm(child(M)))

for L in range(1,6):
    tot=ok=under=over=0
    underex=[]; overex=[]
    for widths in product(range(1,6),repeat=L+1):
        M=tuple(widths)
        if M[0]<1 or M[1]<1: continue
        tot+=1
        ma=min_adm(M); f=v8(M)
        if f==ma: ok+=1
        elif f<ma:
            under+=1
            if len(underex)<4: underex.append((M,ma,f))
        else:
            over+=1
            if len(overex)<4: overex.append((M,ma,f))
    print(f"L={L}: {ok}/{tot} hold  under(unsound)={under}  over={over}")
    if underex: print("   undershoot ex:", underex)
    if overex:  print("   overshoot  ex:", overex)
