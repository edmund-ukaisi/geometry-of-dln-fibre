<task>
Lean 4 + Mathlib formalization DESIGN review (exact algebra, not numerics). I am proving that the
matrix product of a deep-linear-network weight tuple, after a resolution-of-singularities chart,
equals a DIAGONAL matrix at each leaf of a construction tree — Aoyagi's `Q·prod·P = diag(b)`.

SETUP.
- `prod(A) = A^(1)·A^(2)·…·A^(L)`, a rectangular `M0 × ML` real matrix (product of L layer matrices).
- The resolution is a tree of blow-up charts. `acc : Params → Params` is the accumulated chart fold
  from the root to a construction state `s`. States `s` carry a LEDGER (a count `cleared = J` of
  resolved pivots, a list of divisors with birth-corners, exponents).
- A SCALAR sibling walk is ALREADY DONE: it threads `|det D(acc) w| = ∏_k |z_{divCoord k}(w)|^{e_k−1}`
  down the tree, proven by per-ENTRY read lemmas about each chart B = blow-up:
    * pivot coord: z_pivot(B x) = z_pivot(x)          (free)
    * other center coord i: z_i(B x) = z_pivot(x)·z_i(x)   (scaled by pivot)
    * spectator coord: z_c(B x) = z_c(x)              (fixed)
  plus a det-1 Schur source gauge α (z_{ij} ↦ z_{ij} − z_{ip}·z_{pj}) composed into each chart.
- I now need the VALUE analog: thread `prod(acc w)` itself (the matrix), so the leaf gives
  `prod = diagonal`, which a PROVEN downstream lemma consumes.

CHOSEN ENCODING (entry-wise, to avoid Mathlib matrix-block/HMul/reindex instance friction):
    InvVal(acc, s) := ∀ w i j,
        prod(acc w) i j = if cleared s i then (if i.val = j.val then bmon s w i else 0)
                          else resid s w i j
where `bmon s w i` (cleared diagonal entry) is a clean product of exceptional coords.

THE CRUX = `resid s w i j` (the UN-cleared cells). After a blow-up+Schur step the residual block
looks like `u·[[1,a],[b, a·b+ρ]]` (each entry = a scaling monomial × a ratio-coordinate polynomial);
the det-1 Schur clears the (0,0) corner to leave `diag(u, ρ·u)`, shrinking the residual by one.

Four inductive maintenance cases (per step, innermost-first, `Inv(acc,parent) → Inv(acc∘B, child)`):
  case-2 (fresh block birth), case-1(1) (re-merge, α=id), case-1(2) (split, α clears a column),
  rollover (chartless relabel).

CANDIDATE ENCODINGS for `resid`:
  (A) a CLOSED-FORM monomial×ratio expression per (s,i,j) derived from the ledger;
  (B) `resid` DEFINED by the SAME recursion as the walk (a partial product of the not-yet-resolved
      layers), making InvVal true largely by construction, pushing the real content to proving the
      leaf residual is empty/diagonal;
  (C) restructure: the invariant constrains only CLEARED cells + a support/rank predicate on the
      residual block (no closed form for its entries).
</task>

<output_contract>
1. RANK the three encodings (A/B/C) for a Lean-4 proof that mirrors an existing per-entry read-based
   scalar walk, by (i) per-case maintenance proof burden, (ii) whether it forces matrix-block/HMul
   instance algebra, (iii) leaf-collapse difficulty. One paragraph each, then a single recommendation.
2. State the SHARPEST pitfall: is there any way `resid` fails to be a function of `(s,w)` alone
   (i.e. the intermediate matrix depends on fold history not captured by the state `s`)? If so, name
   the exact InvVal-shape amendment that fixes it.
3. Give the ONE decisive test that discriminates the recommended encoding from the next-best BEFORE
   I commit ~a week of Lean grind.
Keep it under ~700 words. Mark inference vs. established-fact explicitly.
</output_contract>

<grounding_rules>
You do not have the repo. Reason from the structure given. Explicitly label any claim that assumes
a fact about the construction I did not state ("ASSUMES: …"). Do not invent Mathlib lemma names as
if verified; if you cite one, mark it "verify".
</grounding_rules>
