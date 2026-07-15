def minAdm3(M0,M1,s):
    return min((M0-r)*(M1-r)+r*s for r in range(min(M0,M1)+1))
def chargeExp(a,b,s):
    lo = b - s if b > s else 0   # Nat: b-s truncates to 0 if s>b, but Icc(b-s)b with b-s>=0 always
    lo = max(0, b - s)
    vals = []
    for h in range(lo, b+1):
        t = a + b - s - h
        t = t if t > 0 else 0     # Nat truncation
        vals.append(h * t)
    return max(vals) if vals else 0
fails = 0; checks = 0
for M0 in range(1,9):
  for M1 in range(1,9):
    for u in range(0, min(M0,M1)+1):
      a, b = M0-u, M1-u
      for s in range(0, 9):
        lhs = minAdm3(M0,M1,s) + chargeExp(a,b,s)
        rhs = a*b + u*s
        checks += 1
        if lhs > rhs:
            fails += 1
            if fails <= 5: print(f"FAIL M0={M0} M1={M1} u={u} s={s}: {lhs} > {rhs}")
print(f"(II) minAdm3 + chargeExp <= ab+us : {checks} checks, {fails} fails")
# also spot-check chargeExp_zero and chargeExp_eq_zero_of_le
print("chargeExp(3,4,0)=", chargeExp(3,4,0), " expect a*b=12")
print("chargeExp(2,3,6)=", chargeExp(2,3,6), " expect 0 (a+b=5<=6)")
