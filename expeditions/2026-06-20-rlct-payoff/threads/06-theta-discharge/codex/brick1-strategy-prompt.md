# Consult: cleanest Lean route for "strict corner-monotonicity of cCodim" (Lean 4 + Mathlib v4.29)

## Setup (combinatorial, no geometry)
Fix N : ℕ and a dimension vector d : Fin (N+1) → ℕ.

A **Kostant partition of d with corner r** is m : Fin(N+1)×Fin(N+1) → ℕ such that
- m vanishes off the upper triangle (m_{ij}=0 when i>j),
- (dimension eqns) for every vertex k: d k = ∑_{i ≤ k ≤ j} m_{ij},
- corner m_{0,N} = r.
The finite set of these is `kostantPartitions d r`.

The quadratic form (corner-blind!) on the ℤ-extension extendℤ m (= m on the box 0≤a≤b≤N, else 0):
  codimForm N m̄ = ∑_{1 ≤ i ≤ u ≤ j ≤ v ≤ N} m̄(i-1,j-1) · m̄(u,v).
Note: it NEVER reads the corner entry m_{0,N}: every first factor has second index j-1 ≤ N-1 < N, every second factor has first index u ≥ 1 > 0. This is PROVED: `codimForm_update_corner`.

`cCodim d r h = inf'_{m ∈ kostantPartitions d r} codimForm N (extendℤ m)`  (h : nonempty).

ALREADY PROVED in the library:
- `cCodim_rankShift`: for r ≤ d k everywhere, cCodim (d−r) 0 = cCodim d r, via the corner-dropping
  bijection `dropCorner m = update m (0,last) 0 : kostantPartitions d r ≃ kostantPartitions (d−r) 0`
  (codimForm-preserving since corner-blind). Same for numTop.
- `dropCorner_mem`, `addCorner_mem`, `kostantPartitions_dminus_eq_image`.

## The TARGET (Brick 1, the (★) certificate, numerically verified 25/25 cases zero failures)
STRICT corner-monotonicity: for s < r (both kostantPartitions nonempty), `cCodim d s > cCodim d r`.
Equivalently the global minimum of codimForm over corner-≤r partitions sits at corner exactly r.

The geometric consumer needs: for every corner-≤r tuple M' (rank(mult M') = s ≤ r),
  (cCodim d r).toNat ≤ codimRepCanonical(orbitRankLocus M').
We have codimRepCanonical(orbitRankLocus M') = codimForm N m' where m' is the Kostant partition of d
with corner s = rank(mult M') (Gabriel normal form, landed). So we need cCodim d r ≤ codimForm N m'
for any Kostant partition m' of corner s ≤ r. Since codimForm m' ≥ cCodim d s, it suffices to show
cCodim d s ≥ cCodim d r for s ≤ r (weak monotonicity is enough for the lower bound; strict is the
"corner exactly r" refinement, only needed if we later want top-dim ⟹ corner=r).

## QUESTION
What is the cleanest Lean proof that **cCodim d s ≥ cCodim d r for s ≤ r** (weak suffices for hLowerBound)?

Candidate construction I'm considering (the "interval-merge"): given a corner-s partition m' (s<r),
build a corner-(s+1) partition m'' of d with codimForm m'' ≤ codimForm m'. The merge: pick a pair of
intervals [0,b] and [a,N] with a ≤ b+1 (adjacent/overlapping) both with positive multiplicity; replace
one copy of each by one copy of [0,N] (corner) and one copy of [a,b] (or [b+1,a-1] if a>b+1... but need
a≤b+1). Then corner rises by 1, dimension eqns preserved, and the codimForm change is ≤ 0.

CONCERNS / what I want your decorrelated read on:
1. Does such a merge ALWAYS exist when s < r and a corner-r partition also exists? (Why must there be a
   [0,b] and an [a,N] with a ≤ b+1 with positive mult?) Give the existence argument or a cleaner one.
2. Is there a SLICKER route avoiding the explicit merge induction entirely — e.g.:
   (a) reduce to corner 0 via rankShift then a monotonicity in d? i.e. cCodim d s = cCodim (d−s) 0 and
       cCodim d r = cCodim (d−r) 0; with s<r, d−r ≤ d−s pointwise; is cCodim e 0 antitone in e? NO —
       smaller dimension vector should give smaller codim, so cCodim (d−r) 0 ≤ cCodim (d−s) 0, giving
       cCodim d r ≤ cCodim d s. Is "cCodim e 0 monotone in e (pointwise ≤)" TRUE and is it easier?
   (b) any generating-function / direct algebraic inequality on codimForm?
3. For the merge's codimForm bookkeeping: codimForm is a fixed bilinear-ish form ∑ m̄(i-1,j-1)·m̄(u,v).
   Replacing intervals changes a few m̄ entries by ±1. Is the net change provably ≤ 0 by a clean
   term-count argument, or does it need case analysis on a vs b?

Please give: (i) the cleanest TRUE statement to induct/transport on, (ii) the construction with its
existence proof, (iii) a rough Lean tactic skeleton (Mathlib v4.29; Finset.inf', Finset.sum), (iv) the
single load-bearing inequality to isolate as a lemma. Flag if weak monotonicity has a much shorter proof
than the strict version (we only need weak for the lower bound).
