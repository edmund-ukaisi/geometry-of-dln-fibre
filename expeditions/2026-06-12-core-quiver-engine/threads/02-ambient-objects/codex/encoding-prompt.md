<task>
I am formalising in Lean 4 (Mathlib v4.29.0) the FOUNDATIONAL ambient objects of a "quiver engine"
for the paper "Geometry of the DLN fibre" (Le Halleur–Rimányi 2024). This is bedrock API: every
downstream theorem stands on it, so I want the encoding right.

THE MATH. Fix a dimension vector d = (d_0, d_1, ..., d_N) of natural numbers. Over a CommRing k:
  Rep_d = ∏_{i=1}^N Mat_{d_i, d_{i-1}}(k)          -- the space of composable matrix tuples (A_1,...,A_N)
  mult : Rep_d → Mat_{d_N, d_0},  (A_1,...,A_N) ↦ A_N A_{N-1} ⋯ A_1   -- ordered product
  Σ^r       = { A ∈ Rep_d | rank(mult A) = r }      -- product-rank locus, a SET
  Σ^{≤r}    = { A ∈ Rep_d | rank(mult A) ≤ r }      -- a SET
  mult⁻¹(B) = { A ∈ Rep_d | mult A = B }            -- the fibre over a target B, a SET

DOWNSTREAM (rungs 2-3, near future, must be reachable cleanly):
  - rank patterns r_{ij} = rank of the COMPOSITE A_j A_{j-1} ⋯ A_{i+1} for 0 ≤ i ≤ j ≤ N
    (so I need every contiguous sub-product, and every intermediate dimension d_k as data);
  - Kostant multiplicities m_{ij} with the constraint d_k = Σ_{i ≤ k ≤ j} m_{ij};
  - Prop 3.1 inclusion-exclusion: m_{ij} = r_{ij} - r_{i,j+1} - r_{i-1,j} + r_{i-1,j+1}, and inverse.
  - Later (next expedition): Ext-codimension formulas keyed on the dimension vector d.

THREE CANDIDATE ENCODINGS, all of which I have ALREADY BUILT GREEN in Lean v4.29:

(i) Fin-vector dimension vector + product space.
    d : Fin (N+1) → ℕ
    Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k
    mult via Fin.induction over j : Fin (N+1), partial products P j : Matrix (Fin (d j)) (Fin (d 0)) k,
      step (fun i prev => A i * prev). COMPUTABLE; concrete N=2 witness closes by `unfold; decide`.
    Σ^r etc. are clean `Set (Tuple d)` for a FIXED d. The Fin.castSucc/Fin.succ transport lives
    INSIDE mult and inside any lemma that recurses on mult (the known v4.29 friction point).

(ii) List ℕ-indexed inductive, indexed by output-dim list (head-first):
    inductive Chain (k) : (inputDim : ℕ) → (outDims : List ℕ) → Type
      | nil (d) : Chain k d []
      | cons (e) (A : Matrix (Fin e) (Fin (outDims.headD inputDim)) k) (rest) : Chain k d (e :: outDims)
    mult : structural recursion, `cons e A rest => A * rest.mult`, DEFINITIONALLY = A * rest.mult.
    Fully computable; rank lemma `(cons e A rest).mult.rank ≤ A.rank` is a ONE-LINER
    (Matrix.rank_mul_le_left A rest.mult), zero Fin transport. Concrete witness `unfold; decide`.
    BUT: the dimension vector is NOT a single fixed index — Σ^r would be a Set over chains whose
    INTERMEDIATE dims float, and the output-dim list is in REVERSE paper order.

(iii) Inductive indexed by the TWO ENDPOINT dims (b = output, a = input), intermediate dims hidden:
    inductive Rep (k) : (b a : ℕ) → Type
      | id (a) : Rep k a a
      | cons (A : Matrix (Fin b) (Fin mid) k) (rest : Rep k mid a) : Rep k b a
    mult : Matrix (Fin b) (Fin a), `cons A rest => A * rest.mult` DEFINITIONALLY. Cleanest mult,
    cleanest rank lemma, computable, `unfold; decide` witness. BUT the intermediate dims AND the
    dimension vector are existential/hidden inside the cons chain — NOT first-class data.

A fourth, the "full dimension list [d_0,...,d_N]" inductive, I tried and it FAILS to build: the
output dim `(d_0::d_1::ds).getLastD 0` is not defeq to `(d_1::ds).getLastD 0` through getLastD,
forcing a transport rewrite inside mult — the friction the project warned me about.

KEY OBSERVATION I want you to pressure-test: the paper takes Σ^r, Σ^{≤r}, mult⁻¹(B) as SETS over
Rep_d FOR A FIXED dimension vector d. That seems to demand the dimension vector be a fixed PARAMETER
and Rep_d be a product space (favouring (i)), because (ii)/(iii) make the dimension data float and
can't naturally express "the set of tuples with THIS d". Against that, (i) carries the
Fin.castSucc/succ transport friction into every lemma that recurses on mult — and rungs 2-3 need
sub-products and intermediate dims, which (i) exposes (d k for k : Fin (N+1)) but (iii) hides.

THE PROJECT'S STANDING STEER (which I am proposing to OVERRIDE) was: "List-indexed inductives avoid
Fin.castSucc/succ transport when defining a fold like mult; weigh (ii) seriously."
</task>

<output_contract>
1. RECOMMENDATION: pick ONE encoding for the ambient Rep_d / mult / Σ^r / fibre layer. One line.
2. THE DECIDING ARGUMENT: the single most important reason, tied to whether Σ^r-as-a-Set-over-fixed-d
   and the rung 2-3 sub-products/intermediate-dims are expressible WITHOUT fighting the type system.
3. Is my "SETS over a fixed d demand a fixed dimension-vector parameter ⟹ product space (i)" inference
   CORRECT, or is there a clean way to take Σ^r as a Set in encoding (ii)/(iii)? Be concrete.
4. The TOP 2 RISKS of your recommendation and the cheapest mitigation for each (e.g. a helper lemma
   that should be proved up-front to tame the mult-recursion friction, or an alternative `mult`
   formulation — Fin.foldr vs Fin.induction vs List.foldl over Matrix — that is easier to reason about).
5. If you'd recommend a HYBRID (e.g. product-space (i) for the Set-level objects, plus a derived
   chain view for sub-products), say so explicitly and name the bridge.
Be concise and decisive. Max ~400 words. This is a one-shot foundational API decision.
</output_contract>

<grounding_rules>
You do not have the Lean files in front of you; reason from the math and the encodings as described.
Flag any claim that depends on a Lean/Mathlib detail you cannot verify as an inference ("I'd expect..."),
not as fact. If you think all three are wrong and there is a materially better fourth encoding, say so,
but only if you can name the concrete construct.
</grounding_rules>
