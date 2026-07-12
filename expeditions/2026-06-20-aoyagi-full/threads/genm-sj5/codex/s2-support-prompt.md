<task>
Determine whether a specific accumulated combinatorial quantity is UNIFORM or ANISOTROPIC at the
base of an iterated matrix-resolution recursion. Pure structural/combinatorial reasoning; no code.

## Setup (a resolution of a deep-linear-network loss)

We resolve the RLCT of `frobSq(A_0·A_1···A_{L-1})` (product of matrices A_s : M_s×M_{s+1}, loss at
the origin) by an iterated blow-up that peels the front pair of factors at each step. Each generator
of the loss is tracked as `gen_i = (∏_ℓ |u_ℓ|^{supp(i,ℓ)}) · res_i`, a MONOMIAL prefix in exceptional
coordinates `u` times a LINEAR residual `res_i`. The loss is `Σ_i gen_i²`. `supp(i,ℓ) ∈ ℕ` is the
order to which exceptional divisor `u_ℓ` divides generator `i`. Write `k_ℓ = min_i supp(i,ℓ)` and the
per-generator LEFTOVER `δ(i,ℓ) = supp(i,ℓ) − k_ℓ ≥ 0`.

## The three support-changing operations (exact, from the implementation)

- START (`ofMatrix`): generators are the entries of the raw matrix; `supp ≡ 0` (uniform, all δ=0).
- RADIAL step (once per peel): prepend a fresh exceptional divisor `u_new` dividing EVERY current
  generator to order exactly 1 — `supp ↦ (1,1,…,1) prepended`. This PRESERVES uniformity: if all
  generators shared support row `s` before, all share `(1 ::: s)` after. Contributes NO leftover.
- ROW-MIX (the Schur block-elimination, once per peel): linearly mixes the residuals `res_i` by a
  matrix R and RESETS the support to a target `s'`. It is faithful (the monomial factors cleanly out
  of the mix) ONLY when applied at a CONSTANT-support state and the target is that same constant
  (`gen_rowMix_const`: old support constant `s`, new support `fun _ => s`). Applied faithfully, it
  PRESERVES the constant/uniform support and only mixes residuals. The design comment states this is
  "the ONLY configuration the block-elimination is applied to" (right after a radial step).
- BLOCK SPLIT (once per peel): the generator index set ι is partitioned into a PIVOT block ι_p and a
  CORANK block ι_c; the loss splits additively `Σ_{ι_p} gen² + Σ_{ι_c} gen²`. The split is a
  reindexing; it does not itself change any `supp(i,ℓ)` value.

## The recursion's shape (what happens to the two blocks)

After a peel of the front pair (M_0,M_1) at rank t: the loss becomes `u_new² · [ (pivot part) +
frobSq(Γ · Z_tail) ]`, where Γ is the FREED CORANK block (a·b free parameters, a=M_0−t, b=M_1−t) and
Z_tail = A_2·A_3···A_{L-1} is the DEEPER PRODUCT. The recursion then continues on the ONE-SHORTER
chain (t, M_2, …, M_{L-1}); i.e. the deeper product Z_tail is what gets resolved next (its own front
pair peeled), while the freed corank block Γ multiplies it. At the base (a width-2 chain, a single
matrix, no deeper product: Z_tail is the empty product = identity) no further resolution is needed —
frobSq of a single free matrix is already a nondegenerate sum of squares.

<questions>
Reason independently; state FACT vs JUDGEMENT.
1. As the recursion resolves Z_tail across subsequent peels (each adding a radial divisor shared by
   all current generators), do the CORANK generators (the entries of frobSq(Γ·Z_tail)) receive those
   later radial divisors too, or are they "frozen" at their support-at-freezing while only the pivot
   descendants accumulate more? Key sub-question: since a radial divisor added during Z_tail's
   resolution factors out of the WHOLE frobSq(Γ·Z_tail) (it multiplies every entry), does the corank
   block's support stay in lock-step with the rest, or diverge?
2. Consequently, at the width-2 BASE (all peels done), is the accumulated support UNIFORM across all
   surviving generators (all δ(i,ℓ)=0), or ANISOTROPIC (some generators carry strictly positive
   leftovers δ>0)? If anisotropic, identify WHICH generators carry the leftovers and why.
3. If some generators carry δ>0 at the base, is there nonetheless a SPANNING subset of generators
   with δ≡0 whose residuals span the full free-matrix block (so that dropping the δ>0 generators —
   they are ≥0 — still lower-bounds the loss by commonDivisor² · frobSq(full free block))? Or would
   dropping them lose rank / dimension, so that a clean free-block lower bound is unavailable and an
   anisotropic (coupled-corner) estimate is genuinely required?
4. Net verdict: at the width-2 base, does the loss admit the clean lower bound
   `loss ≥ commonDivisor(u)² · frobSq(free block of dimension M_0·M_1)` (⟹ a fixed-Z=I free-block
   Morse closes it), or is an anisotropic coupled-corner leaf estimate strictly required? State the
   single structural condition on the peel that decides it.
</questions>
</task>

<output_contract>
Four numbered answers, each 3-7 sentences, FACT vs JUDGEMENT tagged. End with "VERDICT:" one line —
either "UNIFORM/SPANNING (clean free-block lower bound suffices), condition = …" or "ANISOTROPIC
(coupled-corner leaf required), because …". Be decisive; if it hinges on one unproven property of
the peel, name that property exactly.
</output_contract>

<grounding_rules>
Ground every step in the operations and recursion shape given. The RLCT fact you may use: for a free
matrix block of dimension N, `∫ frobSq(block)^{−c'} < ∞ ⟺ c' < N/2`. A radial divisor that multiplies
every entry of a matrix block factors out of that block's frobSq as a common scalar squared. Do not
invent operations beyond the four listed.
</grounding_rules>
