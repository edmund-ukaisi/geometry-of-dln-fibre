from itertools import product

def deep_tail_min(M):
    # indices >= 2
    return min(M[2:])

def is_waist(M):
    # M[1] < min(M[2:])
    return M[1] < deep_tail_min(M)

def rev(M):
    return tuple(reversed(M))

def is_good(M):
    # deepTailMin M <= M[1]
    return deep_tail_min(M) <= M[1]

# Exhaustive sweep: all width-n chains, widths in 1..R, n in 4..NMAX
# HUNT the obstruction: a >=4-width waist whose reverse is NOT good (i.e. reverse is a waist / not good).
NMAX = 8
R = 6
counter = []
total_waists = 0
for n in range(4, NMAX+1):
    for M in product(range(1, R+1), repeat=n):
        if is_waist(M):
            total_waists += 1
            rM = rev(M)
            if not is_good(rM):
                counter.append((n, M, rM))
print(f"width 4..{NMAX}, widths 1..{R}")
print(f"total >=4-width waists examined: {total_waists}")
print(f"waists whose reverse is NOT good (OBSTRUCTIONS): {len(counter)}")
for c in counter[:20]:
    print("  COUNTEREXAMPLE:", c)

# Also: does any >=4-width waist reverse to a WAIST (both-ends-bad)?
both_bad = []
for n in range(4, NMAX+1):
    for M in product(range(1, R+1), repeat=n):
        if is_waist(M) and is_waist(rev(M)):
            both_bad.append((n, M))
print(f"\n>=4-width waist whose reverse is ALSO a waist (both-bad): {len(both_bad)}")
for c in both_bad[:20]:
    print("  BOTH-BAD:", c)

# Sanity: the 3-width palindrome (3,2,3) is a waist that reverses to itself (waist) -- confirm it's width-3 (handled by mnp, NOT reversal)
M3 = (3,2,3)
print(f"\n3-width (3,2,3): is_waist={is_waist(M3)}, rev={rev(M3)}, rev is_waist={is_waist(rev(M3))}  [handled by mnp base, not reversal]")

# Try to build a >=4-width palindrome that is a waist
pal_waists = []
for n in range(4, NMAX+1):
    for M in product(range(1, R+1), repeat=n):
        if M == rev(M) and is_waist(M):
            pal_waists.append((n,M))
print(f"\n>=4-width PALINDROMES that are waists: {len(pal_waists)}")
for c in pal_waists[:20]:
    print("  PAL-WAIST:", c)
