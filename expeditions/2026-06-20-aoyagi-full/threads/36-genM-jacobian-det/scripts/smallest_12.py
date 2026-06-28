import sys; sys.path.insert(0,'.')
import pp_smear_GATE as G
cases=G.smeared()
twelve=[(M,T0,L) for M,T0,mv,L in cases if T0[L-2]==1 and M[L]==2]
twelve.sort(key=lambda x: (x[2], sum(x[0][k]*x[0][k+1] for k in range(x[2]))))
print("(1,2) family members (sorted by L then flatDim):")
for M,T0,L in twelve:
    r=T0[L-2]; c=M[L]; m1=M[L-1]; s=m1-r
    N=sum(M[k]*M[k+1] for k in range(L))
    print(f"  M={M}  L={L}  r={r} c={c} s={s} minAdm={r*c}  flatDim={N}")
