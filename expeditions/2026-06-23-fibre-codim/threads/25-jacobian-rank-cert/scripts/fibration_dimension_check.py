# Verify the structural fibration dim count:
#   dim Sigma^r = card - C        [GIVEN/proved by engine]
#   mult|_Sigma^r : Sigma^r -> Mat^{<=r} (rank-<=r matrices, dim = d_N d_0 - (d_N-r)(d_0-r))
#   The rank-EXACTLY-r stratum has dim = delta = r(d_0+d_N-r). (Note: dim Mat^{<=r} = same = delta!
#     because closure of rank-r stratum = Mat^{<=r}, dim = r(d_N+d_0-r) = delta. CHECK.)
#   If mult|Sigma^r is DOMINANT onto Mat^{<=r}, generic fibre dim = dim Sigma^r - dim Mat^{<=r}
#     = (card - C) - delta.  And the fibre over E (E rank r, a generic/smooth pt of Mat^{<=r}) has
#     this generic dimension. => dim F = card - C - delta. QED structurally.
#
# KEY identity to confirm: dim Mat^{<=r}_{m x n} = r(m+n-r) = delta with m=d_N, n=d_0. 
# dim{rank<=r} = r(m+n-r) (standard). delta = r(d_0+d_N-r). SAME. GOOD: delta = dim Mat^{<=r}.
for (m,n,r) in [(2,2,1),(3,2,1),(3,3,2),(2,2,2)]:
    print(f"Mat_{m}x{n} rank<=r={r}: dim = r(m+n-r) = {r*(m+n-r)} ; delta(d_N={m},d_0={n}) = {r*(n+m-r)}")
print()
# Confirm dim Mat^{<=r} = delta exactly, and the fibration count:
# dim F = (card - C) - delta. Check against Singular dims:
import importlib
exec(open('/tmp/cvalue.py').read().split('if __name__')[0])
def card(d): return sum(d[i+1]*d[i] for i in range(len(d)-1))
sing={(("2,2,2"),0):5,(("2,2,2"),1):4,(("2,2,2"),2):4,
      (("2,2,3"),0):6,(("2,2,3"),1):5,(("2,2,3"),2):4,
      (("3,3,3"),1):10,(("3,3,3"),2):9,
      (("1,2,1"),0):3,(("1,2,1"),1):3}
print(f"{'d':<10}{'r':<3}{'card':<6}{'C':<4}{'delta=dimMat<=r':<16}{'(card-C)-delta':<15}{'Singular dimF':<14}{'ok'}")
for (ds,r),dimF in sing.items():
    d=[int(x) for x in ds.split(",")]
    C=C_of(sorted(d),r); de=r*(d[0]+d[-1]-r); pred=(card(d)-C)-de
    print(f"{ds:<10}{r:<3}{card(d):<6}{C:<4}{de:<16}{pred:<15}{dimF:<14}{'OK' if pred==dimF else 'XXX'}")
