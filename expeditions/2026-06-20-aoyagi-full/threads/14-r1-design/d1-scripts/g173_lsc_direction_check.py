# VERIFY the cheaper LB mechanism direction (nbhd-monotonicity, NO homogeneity needed).
# rlctAt(F, p) = sSup A(p), A(p) = {c : |F|^{-c} integrable on SOME U in nbhd(p)}.
#
# Claim (nbhd-monotonicity, general F, no homogeneity): if p_n -> p* and we want rlctAt(p*) <= rlctAt(p_n):
#   take c in A(p*): exists U* nbhd of p* with |F|^{-c} integrable on U*. For p_n close to p*, p_n in U*
#   (U* open nbhd). Then U* is ALSO a nbhd of p_n => |F|^{-c} integrable on U* => c in A(p_n)
#   => c <= rlctAt(p_n). sSup over c in A(p*): rlctAt(p*) <= rlctAt(p_n) for all p_n close enough to p*.
# THIS NEEDS NO HOMOGENEITY. It's pure nbhd-monotonicity: rlctAt(p*) <= rlctAt(p) for ALL p in a nbhd of p*.
print("KEY LEMMA (nbhd-monotonicity of rlctAt, general F, NO homogeneity):")
print("  For ANY p in a nbhd of p*: rlctAt(F,p*) <= rlctAt(F,p).")
print("  Proof: c in A(p*) => admissible U* nbhd of p*; p in U* (U* open) => U* nbhd of p => c in A(p).")
print("  sSup => rlctAt(p*) <= rlctAt(p). [the SAME mechanism as g170/core-P1, but for ANY F, ANY nearby p]")
print()
print("WAIT — is this TOO strong? It would say EVERY point is a local min of rlctAt. That's FALSE in general")
print("(rlctAt is lower-semicontinuous, local minima at singular pts, but not every pt is a local min).")
print()
print("THE BUG in the naive argument: 'p in U* => U* is a nbhd of p' is TRUE, but then 'c in A(p)' requires")
print("|F|^{-c} integrable on U* — which we HAVE. So c in A(p). So the argument seems to give rlctAt(p*)<=rlctAt(p)")
print("for ALL p in U*. Let's TEST it on a known case where it should FAIL:")
print()
# F(x)=x^2 on R. rlctAt(0)=1/2 (|x|^{-2c} integ iff 2c<1 iff c<1/2). rlctAt(p) for p!=0: F smooth nonzero
# near p, |F|^{-c} integrable for ALL c (F bounded away from 0 on small nbhd) => rlctAt(p)=+inf.
# So rlctAt(0)=1/2 <= rlctAt(p)=inf. ✓ consistent (0 is the min). 
print("F=x^2: rlctAt(0)=1/2, rlctAt(p!=0)=+inf. nbhd-monotonicity rlctAt(0)<=rlctAt(p) ✓ (0 is the singular min).")
print()
# Now a case where p* is NOT a local min: F=x^2 again but p*=some p0!=0 (smooth pt). rlctAt(p0)=inf.
# Is rlctAt(p0)=inf <= rlctAt(p) for p near p0? p near p0 also smooth => rlctAt(p)=inf. inf<=inf ✓.
# What about p* where F has a WORSE singularity nearby? F = x^2 * (x-1)^2. p*=1/2 (smooth, rlctAt=inf).
# nbhd of 1/2 NOT containing 0 or 1 => rlctAt(1/2)=inf, and all p near 1/2 smooth => inf. OK.
# The mechanism gives rlctAt(p*) <= rlctAt(p) for p in a SMALL ENOUGH nbhd of p* (U* avoids other singularities).
print("The lemma is CORRECT but LOCAL: rlctAt(p*) <= rlctAt(p) for p in a nbhd of p* SMALL enough that")
print("the admissible U* of p* (which has |F|^{-c} integrable) contains p. If F has a WORSE singularity")
print("arbitrarily close to p*, U* must avoid it, but then p (between p* and the worse sing) is still in U*.")
print()
print("CRUX: the lemma says rlctAt is locally minimized at p*?? NO — it says for p in U*(c) (depends on c).")
print("As c -> rlctAt(p*), U*(c) may SHRINK. So 'p in U* for all c' fails: the nbhd on which c is admissible")
print("shrinks as c grows. So we get rlctAt(p*) <= rlctAt(p) only for p in the c-nbhd, c<rlctAt(p*)... ")
print("=> rlctAt(p*) <= liminf_{p->p*} rlctAt(p). That's LOWER-SEMICONTINUITY, the CORRECT statement.")
