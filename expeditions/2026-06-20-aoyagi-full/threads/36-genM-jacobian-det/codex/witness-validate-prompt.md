<task>
INDEPENDENT 3rd-party VERIFICATION of a witness construction; do NOT explore a repo. Work the matrix algebra yourself and CONFIRM or REFUTE.

SETTING. A chained matrix product over widths M=(M_0..M_L). A "chain" produces layers A_0..A_{L-1} with
transitions C_k via: C_L = u*Rfin_L; C_k = Bmat_k*chainQ(N_k) + u*Rmat_k; A_k = chainA(N_k,W_k,C_{k+1}),
where chainA(N,W,C) = the vertical block stack [ C - N*W  (the "kept" top, Text_{k+1} rows) ; W (the "lift"
bottom, c_k rows) ] : Wext_k x Wext_{k+1}, Wext_k = M_k. The telescoped quotient Hmat satisfies:
   Hmat_L = Rfin_L;  Hmat_k = Bmat_k * Hmat_{k+1} + (Rmat_k * A_k) * suffix_{k+1};  suffix_k = A_k*suffix_{k+1}, suffix_L = I.
The product = u * Hmat_0. The GOAL: exhibit a parameter point w where Hmat_0 != 0 (so the unit VvalGen=||Hmat_0||^2 is a nonzero polynomial -> positive a.e.).

The achiever descent ranks are Text_k (Text_0=M_0, strictly decreasing, with Text_L possibly = 0). The
"active" residual blocks: interior boundary k has an E-block of size r_k x c_k (r_k=Text_k-Text_{k+1},
c_k=Wext_k-Text_{k+1}) placed in Rmat_k's bottom-right; the leaf has Rfin_L of size Text_L x Wext_L.

A NAIVE witness ("set all Bmat kept-diagonals = 1, the leaf Rfin_L(0,0) = 1, everything else 0") was found
WRONG by sympy because:
  (#1) injecting the live block at a NON-deepest boundary s: the suffix below s is [0 ; W] with W=0 (dead),
       so A_{s'} for s'>s kills the injected column -> Hmat_0 = 0.
  (#2) when Text_L = 0 (the achiever's penultimate rank dropped to 0), the leaf Rfin_L is ROW-EMPTY (0 x M_L),
       so the live-leaf pivot is INFEASIBLE.

THE CORRECTED CONSTRUCTION (to verify), 2 <= L:
  - q := the deepest index k <= L with Text_k > 0 (the "effective leaf").
  - If q = L (Text_L > 0, live leaf): put the pivot e at Rfin_L(0,0); set the kept-diagonal Bmat entries = 1;
    all N, W, other-E = 0. The kept-diagonal Bmat propagates the leaf pivot UP to Hmat_0(0,0) = e. NO carriers.
  - If q < L (Text_L = 0, dead leaf): put the pivot e at the deepest E-block (boundary q, Rmat_q bottom-right);
    set CARRIER lifts W_q, W_{q+1}, ..., W_{L-1} = 1-entries to propagate the injected column DOWN to the final
    output; kept-diagonal Bmat above q = 1; all else 0. Then Hmat_0(0,0) = e * (product of carrier W entries).

SYMPY RESULTS I obtained (verify them independently):
  (3,3,3,3): Text=[3,3,2,1], q=L=3 (live leaf), NO carriers, Hmat_0(0,0) = e. ✓
  (3,3,4):   Text=[3,3,1],   q=L=2 (live leaf), NO carriers, Hmat_0(0,0) = e. ✓
  (3,3,1,3): Text=[3,2,0,0], q=1 < L=3 (DEAD leaf), carriers W_1,W_2 needed, Hmat_0(0,0) = e*w_1*w_2;
             WITHOUT carriers (W=0): Hmat_0 = 0 (confirms carriers load-bearing). ✓

QUESTIONS:
1. Is the effective-leaf q := deepest k<=L with Text_k > 0 WELL-DEFINED for every achiever path (2<=L)?
   In particular, is Text_q > 0 guaranteed (is the set {k : Text_k > 0} always nonempty)? Text_0 = M_0 >= 1
   for a genuine network, so q >= 0 always — confirm, and confirm q >= 1 (so there's at least one interior or
   leaf block, given minAdm >= 1). Could q = 0 (only the identity boundary positive), and would the
   construction still work?
2. Is the deepest active E-block at boundary q (when q < L) GUARANTEED nonempty (r_q >= 1 and c_q >= 1)?
   r_q = Text_q - Text_{q+1} = Text_q - 0 = Text_q >= 1 (since q is the deepest positive Text); c_q = Wext_q -
   Text_{q+1} = M_q - 0 = M_q >= 1. Confirm both, so the pivot slot exists.
3. The CARRIER propagation (q < L): the injected column at boundary q must reach Hmat_0(0,0) through the
   carriers W_q..W_{L-1}. Verify the mechanism: below q (Text=0, kept rows empty) the layers A_k are ALL lift
   (= W_k), so the suffix product is the carrier W-chain; the E·suffix term at q carries e * (W-chain). Above q
   (Text>0) the kept-diagonal Bmat propagates UP. Is there any boundary where the carrier chain breaks (e.g. a
   width-0 carrier W_k)? Confirm the carrier dims W_k: c_k x Wext_{k+1} are all >= 1x1 in the q<L regime.
4. Any HOLE in the construction? E.g. an achiever path where neither q=L nor a clean q<L carrier chain works;
   or where Hmat_0(0,0) gets an unexpected CANCELLING term from another part of the polynomial. (The witness
   sets all non-essential coords to 0, so other terms vanish — confirm no surviving cancellation.)
5. KILL-FLAG: is this a genuine RESEARCH wall (an achiever path where NO uniform witness exists), or is it
   bounded dependent-width engineering (a uniform construction + a downward induction)? Be sharp.
</task>

<output_contract>
- Q1: well-definedness of q, with the Text_0=M_0>=1 argument; the q>=1 / q=0 edge.
- Q2: the deepest-E-block nonemptiness (r_q,c_q >= 1).
- Q3: the carrier-chain propagation + dims; any break point.
- Q4: a sharp yes/no on holes, with the no-cancellation argument.
- Q5: research wall yes/no.
</output_contract>

<grounding_rules>
- Work the matrix algebra; do NOT explore a repo.
- The chain recursion + the sympy results are FACTS to verify, not assume.
- Be decisive; if there's a hole or a research wall, say so sharply.
</grounding_rules>
