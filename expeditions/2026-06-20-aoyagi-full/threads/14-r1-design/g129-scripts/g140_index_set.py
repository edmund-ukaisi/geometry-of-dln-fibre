import sympy as sp, itertools
# PIN ι — the index set of the Route M chart tree, in the UNIFORM pivotBlowupOn frame.
# fm3's frame: each node = pivotBlowupOn(active, p); branch = pivot CHOICE; Lemma-2 det-1 straightens
# between blow-ups; leaves bottom out at unit≥1. ι = the TREE of (pivot-branch × affine-minor) choices.
#
# RECONCILE the squeeze with the monomial route (NOT competing — same node, two levels):
print("=== Reconcile: squeeze vs monomial route are the SAME node at two levels ===")
print("""
At a node, the operation is:
 (1) unit-pivot chart: normalize a nonzero pivot minor to a unit (post-blow-up hard 1, #127).
 (2) det-1 Schur straighten (Lemma-2): unit-pivot row/col ops, Jacobian 1 (MP), straightens the
     bilinear rank-defect center {r-pq=0} to a COORDINATE subspace {w=0}, w:=r-pq. NO weight.
     [This is where my squeeze F-Φ∈ideal(E) lives — it's the ANALYTIC identity validating that this
      MP straighten preserves the rlct; but it contributes NO monomial weight.]
 (3) pivotBlowupOn(active, p) of the now-coordinate center {y_1=...=y_c=0}, c=Mval(t):
     chart y_i=u, y_j=u·v_j; Jacobian |u|^{c-1}; loss F∘π = u²·F_res (homogeneity/multilinearity).
     ⟹ (k,h)=(1, c-1), ratio c/2. THE MONOMIAL WEIGHT IS HERE.
 (4) recurse on F_res until unit (≥1).
So the squeeze (my #129/#131) and fm3's monomial pivot² are NOT competing: the squeeze is the analytic
content of step (2) (the MP straighten is rlct-preserving), the monomial weight is step (3)'s pivot².
My #138 C1 'regular squares + reduced chain' was the SQUEEZE-LEVEL view; fm3's correction: at the
CONSTRUCTION level the node is uniform pivotBlowupOn, and the 'regular squares' are NOT an additive
nReg/2 — they are absorbed into the recursion (each becomes a unit≥1 leaf factor OR a deeper pivot²).
""")
print("=== ι, pinned (uniform pivotBlowupOn frame) ===")
print("""
ι = the set of ROOT-TO-LEAF PATHS in the blow-up tree. A path is a finite sequence of nodes; each node
is a CHOICE of (active block, pivot p) — i.e. WHICH coordinate is the argmax pivot (the argmaxCell)
AND, for a partial/mixed drop, which rank-r minor survives. Concretely:

  ι = { π = (n_1, n_2, ..., n_d) : each n_s = (active_s, p_s) a valid pivot choice at the s-th node,
        the sequence terminating when the residual is a unit (≥1, all singular directions blown up) }

The TREE structure: at each node, the children are the pivot branches = the cells of argmaxCellOn_cover
(which coordinate attains the max → which affine chart of the blow-up) × the minor choices (which rank-r
survivor block, for a C5/mixed node). The path's (d,k,h):
  d_π = the chart dimension (ambient, the flattened coords after all the path's blow-ups + straightens);
  for each node s on the path: ONE exceptional divisor u_s, (k,h)_s = (1, c_s - 1), c_s = Mval(stratum_s);
  k_π = the per-divisor vanishing (1 at each per-factor blow-up; ≥2 at NC-completion intersection nodes);
  h_π = the per-divisor Jacobian (card_s - 1 = c_s - 1).
""")
# The controller's guess: ι = the squeeze failure mode. Check: is ι determined by WHERE the squeeze
# would-fail-to-be-clean = WHERE a blow-up is needed (the singular/rank-defect directions)?
print("=== Controller's guess: ι = the squeeze failure mode? ===")
print("""
The squeeze c1Φ≤F≤c2Φ holds at EVERY node (the analytic identity, #129/#131). What FAILS to be clean is
the LITERAL u·(ΣE²+G²) factorization — and that failure is EXACTLY at the rank-defect center (where the
pivot is not yet a unit, pre-blow-up). So:
  ι is indexed by the SEQUENCE of rank-defect centers blown up = the sequence of pivot choices resolving
  each layer's rank drop. The 'squeeze failure mode' = the rank-defect locus = the blow-up CENTER. So
  YES, ι is indexed by the rank-defect-resolution choices, which = the pivot-branch tree. The controller's
  guess is right: ι enumerates the ways the squeeze-fails-clean (the rank-defect centers) get resolved by
  pivotBlowupOn — i.e. the pivot/minor choice sequences. ι ↠ Adm M (the (S-min) surjection-to-minimiser).
""")
