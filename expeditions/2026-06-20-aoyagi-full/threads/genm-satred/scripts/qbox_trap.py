"""
P2's qbox-on-pivot-NOT-corank trap (D-cert §3bis; controller: 'most likely to break').
qbox_lintegral_lt_top: ∫ det(gram Q)^{-α/2} < ⊤  iff  (qbox-b <= qbox-q) AND (α < qbox-q - qbox-b + 1).
PIVOT Gram: Q = Qtil (u×n, full row rank u): qbox-b=u, qbox-q=n, α=a => a < n-u+1.
CORANK Gram: Q = Qb (b×n): qbox-b=b, qbox-q=n, α=a => a < n-b+1.
At the EDGE (a+b=ρ+1, the tie), does the CORANK qbox FAIL (a=n-b+1 boundary) while the PIVOT passes?
Scan realizable edge dims. NO MC.
"""
from itertools import product
# edge b=1: a=rho, and the relevant n. Use n=deepTail width; the corank trap is a>=n-b+1.
# The trap flagged: for the CORANK Q_b at edge dims, qbox condition a<n-b+1 is a<a (FALSE) when n-b+1=a+1... 
# i.e. when n = a+b = rho+1 (the edge). Let's check corank vs pivot across (a,b,n).
trap_corank=0; ok_pivot=0; both_checked=0
ex=[]
for a in range(1,6):
  for b in range(1,4):
    for n in range(1,8):
      u=n  # placeholder; the real n is the deep width; test whether corank fails where pivot passes
      pass
# Cleaner: the trap is dimensional. corank qbox needs a < n - b + 1; pivot qbox needs a < n - u + 1.
# Since u (pivot rank) vs b (corank rank): typically u >= b at the relevant cuts, so n-u+1 <= n-b+1,
# meaning PIVOT is HARDER (smaller RHS). Wait -- that means pivot FAILS more?? Re-examine the actual claim.
for a in range(1,6):
  for b in range(1,5):
    for u in range(1,7):
      for n in range(1,9):
        corank_ok = (b<=n) and (a < n-b+1)
        pivot_ok  = (u<=n) and (a < n-u+1)
        both_checked+=1
        # the TRAP: corank qbox is CITED but FAILS while pivot is the right (passing) one
        if (not corank_ok) and pivot_ok:
          trap_corank+=1
        if pivot_ok: ok_pivot+=1
print(f'dim combos: {both_checked}')
print(f'  corank-qbox FAILS but pivot-qbox PASSES (the trap: cite pivot not corank): {trap_corank}')
print(f'  NOTE: pivot passes iff a<n-u+1; corank passes iff a<n-b+1. Since typically u>=b, n-u+1<=n-b+1,')
print(f'  so pivot is the STRICTER (harder) condition -- verify which Gram the descent actually carries.')
