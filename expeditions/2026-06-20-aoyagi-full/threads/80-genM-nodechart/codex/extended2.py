"""
EXTENDED witness adjudication v2 (uses exact Lean Adm/Mval via exact_achiever).

Build the LIVE-leaf chainOfMt B_det chart on an achiever descent; prefer an achiever with engine
Text(L) >= 1 (a live engine-leaf) when one exists.  Count angular coords, check square + det.

The B_det live-leaf decoder (mirrors B_det3333/B_det222 EXACTLY):
  radial u=x0; per interior boundary k<L: Bmat = LDU-kept; Nblk free; Wblk free.
  Rmat (u-carrier E-block) free couplings; leaf Rfin free with ONE pivot fixed to 1.
  Allocate the free Rmat-E couplings + Rfin to exactly fill flatDim (square by the chartDim=flatDim id).
"""
import sympy as sp
from sympy import symbols, Matrix, eye, zeros
from exact_achiever import achievers, engine_tach, engine_text, minAdm

def chainQ(N,t,c):
    Q=zeros(t,t+c)
    for i in range(t): Q[i,i]=1
    for i in range(t):
        for j in range(c): Q[i,t+j]=N[i,j]
    return Q
def chainA(N,W,C,t,c,mp):
    top=C-N*W; A=zeros(t+c,mp)
    for i in range(t):
        for j in range(mp): A[i,j]=top[i,j]
    for i in range(c):
        for j in range(mp): A[t+i,j]=W[i,j]
    return A
def build(L,M,tach,blocks,u):
    Wext=lambda k:M[k]; Text=lambda k:(M[0] if k==0 else tach[k-1])
    C={}; C[L]=u*blocks[L]['Rfin']
    for k in range(L-1,-1,-1):
        tk1=Text(k+1); ck=Wext(k)-tk1
        C[k]=blocks[k]['B']*chainQ(blocks[k]['N'],tk1,ck)+u*blocks[k]['R']
    A={}
    for k in range(L):
        tk1=Text(k+1); ck=Wext(k)-tk1; mp=Wext(k+1)
        A[k]=chainA(blocks[k]['N'],blocks[k]['W'],C[k+1],tk1,ck,mp)
    return A,C
def ldu_kept(rows,cols,fresh):
    Lm=eye(cols); Um=eye(cols); D=zeros(cols,cols)
    for i in range(cols): D[i,i]=fresh()
    for i in range(cols):
        for j in range(cols):
            if i>j: Lm[i,j]=fresh()
            if i<j: Um[i,j]=fresh()
    K=Lm*D*Um
    if rows==cols: return K
    X=Matrix(rows-cols,cols,lambda i,j:fresh())
    return K.col_join(X*K)

def pick_achiever(M, prefer_live=True):
    L=len(M)-1
    achs=achievers(M)
    scored=[]
    for T in achs:
        tach=engine_tach(M,T); Text=engine_text(M,tach)
        scored.append((Text[L],T,tach,Text))
    if prefer_live:
        live=[s for s in scored if s[0]>=1]
        if live:
            # prefer the live achiever with the LARGEST leaf rank (most leaf angular room)
            return max(live,key=lambda s:s[0])
    return scored[0]

def build_liveleaf(M, prefer_live=True):
    M=tuple(M); L=len(M)-1
    leafrank,T,tach,Text=pick_achiever(M,prefer_live)
    Wext=lambda k:M[k]; Textf=lambda k:(M[0] if k==0 else tach[k-1])
    ctr=[0]; syms=[]
    def fresh():
        s=symbols(f'x{ctr[0]}',real=True); ctr[0]+=1; syms.append(s); return s
    u=fresh()
    slots={'radial':[0],'B':[],'N':[],'W':[],'Rmat_free':[],'Rfin_free':[],'Rfin_fixed':[]}
    blocks={}; flat=sum(M[k]*M[k+1] for k in range(L))
    for k in range(L):
        tk=Textf(k); tk1=Textf(k+1); ck=Wext(k)-tk1; rk=tk-tk1; mp=Wext(k+1)
        s0=ctr[0]
        if tk1==0: B=zeros(tk,0)
        elif tk==tk1 and ck==0: B=eye(tk)
        else: B=ldu_kept(tk,tk1,fresh)
        slots['B']+=list(range(s0,ctr[0]))
        s0=ctr[0]; N=Matrix(tk1,ck,lambda i,j:fresh()) if (tk1>0 and ck>0) else zeros(tk1,ck)
        slots['N']+=list(range(s0,ctr[0]))
        s0=ctr[0]; W=Matrix(ck,mp,lambda i,j:fresh()) if (ck>0 and mp>0) else zeros(ck,mp)
        slots['W']+=list(range(s0,ctr[0]))
        blocks[k]={'B':B,'N':N,'W':W,'_tk':tk,'_tk1':tk1,'_ck':ck,'_rk':rk,'_mp':mp,'_Wk':Wext(k)}
    tL=Textf(L); wL=Wext(L); Rfin=zeros(tL,wL)
    if tL>0 and wL>0:
        first=True
        for i in range(tL):
            for j in range(wL):
                if first: Rfin[i,j]=sp.Integer(1); slots['Rfin_fixed'].append((i,j)); first=False
                else: Rfin[i,j]=fresh(); slots['Rfin_free'].append(ctr[0]-1)
    used=ctr[0]; remaining=flat-used
    # allocate remaining as free E-block couplings (bottom-right r_k x c_k), boundary order
    for k in range(L):
        tk=blocks[k]['_tk']; tk1=blocks[k]['_tk1']; ck=blocks[k]['_ck']; rk=blocks[k]['_rk']; Wk=blocks[k]['_Wk']
        R=zeros(tk,Wk)
        for a in range(rk):
            for b in range(ck):
                if remaining>0:
                    R[tk1+a,tk1+b]=fresh(); slots['Rmat_free'].append(ctr[0]-1); remaining-=1
        blocks[k]['R']=R
    blocks[L]={'Rfin':Rfin}
    return dict(M=M,L=L,tach=tach,T=T,Text=Text,leafrank=leafrank,blocks=blocks,u=u,syms=syms,
                slots=slots,flat=flat,used=ctr[0],remaining=remaining,Wextf=Wext,Textf=Textf)

def div_by_u(g,u):
    g=sp.expand(g)
    if g==0: return True
    P=sp.Poly(g,u); q,r=sp.div(P,sp.Poly(u,u)); return r.as_expr()==0

def adjudicate(M, verbose=True, do_det=True, prefer_live=True):
    d=build_liveleaf(M,prefer_live=prefer_live)
    L=d['L']; u=d['u']; M=d['M']; mA=minAdm(M)
    A,C=build(L,M,d['tach'],d['blocks'],u)
    out=[]
    for k in range(L):
        Ak=A[k]
        for i in range(Ak.rows):
            for j in range(Ak.cols): out.append(sp.expand(Ak[i,j]))
    nout=len(out); ncoords=d['used']
    affine=all((not o.has(u)) or sp.Poly(o,u).degree()<=1 for o in out)
    angular=[];
    for ci in range(ncoords):
        c=symbols(f'x{ci}',real=True)
        if c==u: continue
        cols=[sp.expand(sp.diff(o,c)) for o in out]; nz=[g for g in cols if g!=0]
        if not nz: continue
        if all(div_by_u(g,u) for g in nz): angular.append(ci)
    rep=dict(M=M,tach=d['tach'],T=d['T'],minAdm=mA,flatDim=d['flat'],ncoords=ncoords,nout=nout,
             square=(nout==ncoords and d['remaining']==0),unfilled=d['remaining'],affine=affine,
             leafrank=d['leafrank'],n_angular=len(angular),angular=angular,
             angular_ok=(len(angular)==mA-1),slots=d['slots'])
    if do_det and nout==ncoords and d['remaining']==0:
        J=sp.Matrix(nout,ncoords,lambda i,j: sp.diff(out[i],symbols(f'x{j}',real=True)))
        det=sp.expand(J.det())
        if det==0: rep['det']={'degenerate':True}
        else:
            P=sp.Poly(det,u); lo=min(m[0] for m in P.monoms()); hi=P.degree()
            rep['det']={'factored':str(sp.factor(det))[:120],'u_lo':lo,'u_hi':hi,
                        'single':lo==hi,'front_ok':lo==mA-1}
    else: rep['det']=None
    if verbose:
        print(f"M={M} tach={d['tach']} T={d['T']} minAdm={mA}(−1={mA-1}) leafrank={d['leafrank']}")
        print(f"  flat={d['flat']} ncoords={ncoords} nout={nout} square={rep['square']} unfilled={d['remaining']} affine={affine}")
        print(f"  #angular={len(angular)} ==minAdm-1? {rep['angular_ok']}  angular={angular}")
        print(f"  homes: Rmat_free={d['slots']['Rmat_free']} Rfin_free={d['slots']['Rfin_free']} Rfin_fixed={d['slots']['Rfin_fixed']}")
        if rep['det'] is not None:
            if rep['det'].get('degenerate'): print("  det==0 DEGENERATE")
            else: print(f"  det u-power {rep['det']['u_lo']}..{rep['det']['u_hi']} single={rep['det']['single']} front==minAdm-1? {rep['det']['front_ok']}  det={rep['det']['factored']}")
        else: print("  (det skipped)")
        print()
    return rep

if __name__=='__main__':
    fams=[(3,3,3,3),(2,2,2),(2,1,2),(3,3,4),(2,2,2,2),(4,4,2,2)]
    for M in fams: adjudicate(M)
