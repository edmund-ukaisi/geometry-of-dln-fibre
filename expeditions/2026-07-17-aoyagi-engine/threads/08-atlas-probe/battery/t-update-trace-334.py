#!/usr/bin/env python3
# guards: resolution-tree
# provenance: threads/08-atlas-probe (pnp08). Q3 (full-T update-rule trace at (3,3,4)).
#   Rules pinned to PAGE IMAGES: Case-1(1) p.16, Case-1(2) p.17, Case-2 p.20.
"""Q3: trace the full-T update through one Case-1(1) merge + one Case-2 step at M=(3,3,4), L=2.

State per divisor: T (length L=2), exponent Mexp. tilde_t = min(T). Index set {1,2} is FIXED.

Update rules (page-pinned), as pure functions on (T, Mexp):

  case11_merge(T, Mexp; S, J, J1, Msnext):     # p.16 -- mutate the fixed existing record
      tail t^(S..L) := J ; head t^(1..S-1) unchanged
      Mexp' = Mexp + J1*(Msnext - J)           # Msext = M^{(S+1)}

  case2_create(S, J, MS, Msext, widths):       # p.20 -- new record
      head t^(i) := widths[i+1]  (i=1..S-1, i.e. M^{(i+1)}) ; tail t^(S..L) := J
      Mexp  = (MS - J)*(Msext - J)             # codim of the blown-up block; MS = M(S)

  case12_create(parentT; S, J, J1, Msext):     # p.17 -- new record (for completeness)
      head t^(i) := parentT[i]  (i<S, INHERITED) ; tail t^(S..L) := J
      Mexp = parentMexp + J1*(Msext - J)

Terminal read-off (p.22): Mval(t) = (M1-t1)(M2-t1) + (t1-t2)(M3-t2). A record contributes to the
LCT candidate iff tilde_t = 0.  We verify each traced record's exponent == Mval(its T).
"""
import sys

WIDTHS = {1: 3, 2: 3, 3: 4}          # M^{(1)},M^{(2)},M^{(3)} for M=(3,3,4)
L = 2


def Mval(T):
    t1, t2 = T
    return (WIDTHS[1] - t1) * (WIDTHS[2] - t1) + (t1 - t2) * (WIDTHS[3] - t2)


def set_tail(T, S, J):
    T = list(T)
    for j in range(S, L + 1):        # components S..L (1-indexed)
        T[j - 1] = J
    return tuple(T)


def case2_create(S, J, MS):
    Msext = WIDTHS[S + 1]
    T = [0] * L
    for i in range(1, S):            # head i=1..S-1
        T[i - 1] = WIDTHS[i + 1]     # M^{(i+1)}
    T = set_tail(tuple(T), S, J)
    Mexp = (MS - J) * (Msext - J)
    return T, Mexp


def case11_merge(T, Mexp, S, J, J1):
    Msext = WIDTHS[S + 1]
    return set_tail(T, S, J), Mexp + J1 * (Msext - J)


ok = True
print("=== M=(3,3,4), L=2 : Q3 full-T update trace ===\n")

# --- A CASE-2 step: first step, S=1, J=0, M(1)=3. Creates the profile-(0,0) divisor.
S, J, MS = 1, 0, 3
T0, M0 = case2_create(S, J, MS)
print(f"[Case 2] S={S} J={J} M(S)={MS}: create u_(1,1)")
print(f"   head (i<S: none) ; tail t^(1..2):={J}  ->  T={T0}   Mexp=(M(S)-J)(M^(S+1)-J)"
      f"=({MS}-{J})({WIDTHS[S+1]}-{J})={M0}")
print(f"   tilde_t={min(T0)}   Mval{T0}={Mval(T0)}   exponent matches Mval: {M0==Mval(T0)}\n")
ok &= (M0 == Mval(T0) == 9)

# --- Another CASE-2 step: S=2, J=0, M(2)=3.  Head RESET to M^(2)=3.  Profile-(3,0) divisor.
S, J, MS = 2, 0, 3
Tc, Mc = case2_create(S, J, MS)
print(f"[Case 2] S={S} J={J} M(S)={MS}: create u_(2,1)")
print(f"   head t^(1):=M^(2)={WIDTHS[2]} ; tail t^(2):={J}  ->  T={Tc}   "
      f"Mexp=({MS}-{J})({WIDTHS[S+1]}-{J})={Mc}")
print(f"   tilde_t={min(Tc)}   Mval{Tc}={Mval(Tc)}   exponent matches Mval: {Mc==Mval(Tc)}\n")
ok &= (Mc == Mval(Tc) == 12)

# --- A CASE-1(1) merge: the BINDING one. Parent B=(1,1) [born S=1 keep-rank-1, Mexp=Mval(1,1)=4].
#     Node (S,J,J1)=(2,0,1): tilde_t target = J+J1 = 1 = tilde_t(B). Mutate B.
B, MB = (1, 1), Mval((1, 1))
print(f"[Case 1(1)] parent B={B}  Mexp={MB} (=Mval{B}); node S=2 J=0 J1=1 (target tilde_t=1)")
Bp, MBp = case11_merge(B, MB, S=2, J=0, J1=1)
print(f"   tail t^(2):=J=0 ; head t^(1) unchanged  ->  T={Bp}")
print(f"   Mexp' = Mexp + J1*(M^(S+1)-J) = {MB} + 1*({WIDTHS[3]}-0) = {MBp}")
print(f"   tilde_t={min(Bp)}   Mval{Bp}={Mval(Bp)}   exponent matches Mval: {MBp==Mval(Bp)}")
print(f"   -> this is the BINDING divisor: Mexp'={MBp}=minAdm(3,3,4)  (lambda_core = {MBp}/2 = 4)\n")
ok &= (MBp == Mval(Bp) == 8)

print("Every traced record: fixed index set {1,2}, tail-slice write, exponent == Mval(T).")
print("T-update is a CLEAN componentwise rule (no re-indexing / no vector merge)." if ok else "FAILED")
sys.exit(0 if ok else 1)
