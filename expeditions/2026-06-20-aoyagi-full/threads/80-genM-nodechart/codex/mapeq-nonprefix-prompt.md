<task>
Independent algebraic adjudication (pure linear/multilinear algebra; no Lean). Analyze from scratch;
give your own structural conclusion. Do NOT assume any factorization or equality holds.

SETUP. Fix L >= 1, ambient widths W_0..W_L, compressed widths T_0=W_0 and a weakly-decreasing descent
0 < T_{k+1} <= W_k. Per boundary k=0..L-1: free real blocks B_k (T_k x T_{k+1}), N_k (T_{k+1} x c_k),
W_k (c_k x W_{k+1}) with c_k = W_k - T_{k+1}; a u-scaled residual R_k; a scalar radial u; a leaf Rfin.

TELESCOPE chart (the "ground-truth" map phiGen), built by a single backward recursion:
  chainQ(N_k) = [ I_{T_{k+1}} | N_k ]                        (T_{k+1} x W_k)
  C_L = u * Rfin
  C_k = B_k * chainQ(N_k) + u * R_k                          (T_k x W_k), k<L
  A_k = chainA(N_k, W_k, C_{k+1})
      = [[I_{T_{k+1}}, -N_k],[0, I_{c_k}]] @ [ C_{k+1} ; W_k ]   (W_k x W_{k+1})
  phiGen output = flatten(A_0, ..., A_{L-1}).
A_k depends on boundary k's own N_k, W_k AND on C_{k+1} (boundary k+1's B_{k+1},N_{k+1},R_{k+1}).
So output layer k reads input boundaries k and k+1 ("nearest-neighbor coupling").

A SECOND candidate map (call it phi_ach) is a COMPOSITION OF BLOCK SELF-MAPS of the flat coordinate
space V = R^N (no scratch coordinates; the same N coords in and out). Each factor is a "conjugated block
self-map": pick a fixed linear split E_i : V ~= B_i x R_i, apply a nonlinear g_i on the B_i block, identity
on R_i, write back via E_i^{-1}. phi_ach = g_0 . g_1 . ... . g_{m-1} (function composition). Candidate
factors: a radial blow-up; per-boundary Schur frames S(X,K,N,E)=[[K,KN],[XK,XKN+E]]; per-boundary LDU
cores; per-boundary unipotent chain shears [[I,-N_k],[0,I]]. Each factor's |det Dg_i| is a clean monomial.

OBSERVED FACTS (exact sympy at (W)=(2,3,2),T=(2,2,1) and (3,3,3,3),T=(3,3,2,1), both square charts):
- phiGen is ADDITIVELY SEPARABLE across distinct boundary blocks: every monomial of every output entry
  touches at most ONE non-radial boundary block. Concretely A_k = stack(C_{k+1} - N_k W_k ; W_k); the only
  product is N_k*W_k (BOTH boundary k); C_{k+1} (boundary k+1) enters ADDITIVELY. So d2/(dN_i dN_j)=0 and
  d2/(dN_i dB_j)=0 for i != j (distinct boundaries) within any single output entry.
- The per-layer assembly identity chainA(N_k, W_k, C) = shear_k @ [C; W_k] holds for a FRESH FREE symbolic
  C (independent of the prefix), i.e. it is layer-LOCAL.
- A prior refutation ("F1 dead") claimed a composeFold of DISJOINT factors cannot reproduce the chain
  product because of a nonzero cross-boundary mixed partial d2/dn1 dn2; the sympy above shows that specific
  cross partial is in fact ZERO. So the prior refutation's stated mechanism appears not to bite here.

</task>

<questions>
1. Given the additive separability + the layer-LOCAL assembly identity, can the telescope map phiGen be
   written EXACTLY as a finite composition of block self-maps of the SAME flat space V=R^N (no scratch
   coords), i.e. as a phi_ach of the kind above? Give the mechanism (which factors, what order, what each
   reads/writes) OR a precise obstruction.
2. THE KEY SUBTLETY: in such a composition each factor reads the RUNNING OUTPUT of the factors to its
   right, not the original input. The chain-shear factor must compute A_k = C_{k+1} - N_k W_k in the top
   rows. But C_{k+1} = B_{k+1} chainQ(N_{k+1}) + u R_{k+1} must already sit where the shear reads it, and
   the shear's "-N_k W_k" needs N_k and W_k still in their input slots. Does the input-coordinate vs
   output-coordinate distinction (the flat slots get OVERWRITTEN as factors fire) create a genuine
   obstruction to staging phiGen as self-maps over one N-dim space, or can a careful ordering + a
   coordinate identification (output slot of A_k overwrites an input slot) make it telescope cleanly?
   In particular: is the map phiGen even an ENDOMORPHISM-friendly target (input coords B_k,N_k,W_k,R_k,u,
   Rfin vs output coords = entries of A_0..A_{L-1}) — does a natural slot-identification exist that lets a
   self-map composition realize it, or must any honest realization use a CHANGE OF COORDINATES (a fixed
   linear reindex from input-slots to output-slots) wrapping the composition?
3. If phiGen = (linear reindex) o (composition of block self-maps), is the block-self-map composition's
   correctness provable by INDUCTION ON LAYERS (each layer's factor verified locally, the induction
   carrying "the prefix slots already hold C_{k+1}"), WITHOUT any global "prefix-invariance" lemma
   (a lemma asserting a factor's action is unchanged by what earlier factors did to OTHER slots)? Name
   precisely what global fact, if any, an induction would still need. Distinguish: (a) a clean per-layer
   induction exists; (b) it needs a global commutation/disjoint-support fact that is true and provable;
   (c) it is irreducibly global ("prefix-invariance-shaped") and hard.
4. Where would this break? Name the minimal configuration (if any) where the self-map composition cannot
   reproduce phiGen even with reindexing — e.g. a width pattern where the additive separability fails, or
   where two factors contend for the same flat slot.
</questions>

<output_contract>
Answer 1-4 in order, each a tight paragraph. End with a one-line VERDICT: "WITNESS: sound non-prefix
proof structure exists (name it)" OR "OBSTRUCTION: irreducibly prefix-shaped (name the global fact)".
Flag every inference vs. observed-from-the-given-facts claim explicitly.
</output_contract>

<grounding_rules>
- Treat the matrix definitions as exact. Do not assume a factorization; derive it or refute it.
- "Block self-map" = identity outside one block under a fixed linear split; composition reads running output.
- "prefix-invariance" = a global lemma that a later factor's value/derivative is unaffected by earlier
  factors' edits to slots it does not read. Say explicitly whether a per-layer induction avoids needing it.
- Give explicit small matrices / a clean inductive statement where useful. If you must speculate, say so.
</grounding_rules>
