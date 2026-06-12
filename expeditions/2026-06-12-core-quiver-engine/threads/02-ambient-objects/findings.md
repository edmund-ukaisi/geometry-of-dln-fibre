---
title: "Thread 02 — ambient objects (rung 1)"
status: sorry-free
topics: [setup, ambient-objects, mult, rank-loci, fibre]
created: "2026-06-12"
updated: "2026-06-12"
---

# Thread 02 — Ambient objects of the quiver engine (rung 1)

Module: `lean/DLNFibre/Core/Setup.lean` (namespace `DLNFibre.Core`), network-free
(imports only `Mathlib.Data.Matrix.{Basic,Mul}` and `Mathlib.LinearAlgebra.Matrix.Rank`;
**does not** import `DLNFibre.DLN`).

## What is defined

For a fixed dimension vector `d : Fin (N + 1) -> N` over a `CommRing k`:

| Lean | paper object |
|---|---|
| `Tuple d` (`abbrev`) | `Rep_d = prod_{i=1}^N Mat_{d_i,d_{i-1}}(k)` — composable matrix tuples |
| `multPrefix d A j` | prefix product `A_j ... A_1 : Matrix (Fin d_j) (Fin d_0) k` (recursion handle) |
| `mult d A` | `mult (A_1,...,A_N) = A_N ... A_1 : Matrix (Fin d_N) (Fin d_0) k` |
| `productRankLocus d r` | `Sigma^r = {A | rank (mult A) = r}` |
| `productRankLocusLE d r` | `Sigma^{<=r} = {A | rank (mult A) <= r}` |
| `fibre d B` | `mult^{-1}(B) = {A | mult A = B}` |

Plus the `rfl` API that keeps `mult` from being unfolded downstream:
`multPrefix_zero`, `multPrefix_succ` (both `@[simp]`, both `rfl`); the membership unfoldings
`mem_productRankLocus`, `mem_productRankLocusLE`, `mem_fibre` (all `Iff.rfl`); and
`fibre_eq_preimage : fibre d B = mult d ' {B}` (`rfl`, fidelity to the paper's `mult^{-1}(B)`).

### Def signatures (verbatim)

```lean
abbrev Tuple (d : Fin (N + 1) -> N) : Type u :=
  ForAll i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k

def multPrefix (d : Fin (N + 1) -> N) (A : Tuple (k := k) d) :
    (j : Fin (N + 1)) -> Matrix (Fin (d j)) (Fin (d 0)) k :=
  Fin.induction (1 : Matrix (Fin (d 0)) (Fin (d 0)) k) (fun i prev => A i * prev)

@[simp] theorem multPrefix_zero (d : Fin (N + 1) -> N) (A : Tuple (k := k) d) :
    multPrefix d A 0 = 1 := rfl

@[simp] theorem multPrefix_succ (d : Fin (N + 1) -> N) (A : Tuple (k := k) d) (i : Fin N) :
    multPrefix d A i.succ = A i * multPrefix d A i.castSucc := rfl

def mult (d : Fin (N + 1) -> N) (A : Tuple (k := k) d) :
    Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k :=
  multPrefix d A (Fin.last N)

def productRankLocus (d : Fin (N + 1) -> N) (r : N) : Set (Tuple (k := k) d) :=
  {A | (mult d A).rank = r}

def productRankLocusLE (d : Fin (N + 1) -> N) (r : N) : Set (Tuple (k := k) d) :=
  {A | (mult d A).rank <= r}

def fibre (d : Fin (N + 1) -> N) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    Set (Tuple (k := k) d) :=
  {A | mult d A = B}
```

(Section context: `universe u`, `variable {k : Type u} [CommRing k] {N : N}`.
Notation note: in the verbatim block above `->`/`ForAll`/`'` stand for the Lean arrow / Pi-binder /
preimage glyph; the actual file uses the proper unicode. Read the file for exact glyphs.)

## Encoding decision + rationale

**Decision: encoding (i) — `Fin`-vector dimension vector + product space**, with `mult` built from
prefix products via `Fin.induction`, *not* the `List`-indexed inductive (the brief's standing steer).

**Rationale (one paragraph).** The paper's `Sigma^r`, `Sigma^{<=r}`, `mult^{-1}(B)` are `Set`s over
`Rep_d` *for a fixed dimension vector* `d`. Encoding (i) makes `d : Fin (N+1) -> N` a fixed parameter
and `Rep_d` the product space `Tuple d`, so the loci/fibre are honest `Set (Tuple d)` and every
intermediate dimension `d k` (needed for rungs 2-3: rank patterns `r_{ij} = rank(A_j...A_{i+1})` and
the Kostant constraint `d_k = sum_{i<=k<=j} m_{ij}`) is first-class data over the same `d`. The
`List`-indexed inductives give a *cleaner `mult`* but make the dimension data float — encoding
(ii)/(iii) cannot natively express "the set of tuples with **this** `d`" (they need a reversed-list
re-indexing or a `{R // HasDims d R}` subtype, recovering the data by proof, not by type — the wrong
bedrock for an API the whole engine stands on). The known `Fin.castSucc`/`Fin.succ` transport friction
is real but *local*: it lives inside `multPrefix`, and the two `rfl` step lemmas `multPrefix_zero` /
`multPrefix_succ` export the recursion so downstream lemmas never unfold `Fin.induction` (verified:
`(multPrefix ... i.succ).rank <= (A i).rank` closes by `rw [multPrefix_succ]; exact
Matrix.rank_mul_le_left _ _`, zero transport).

This reverses the brief's "weigh (ii) seriously" steer. The reversal was red-teamed by Codex (xhigh;
prompt+answer at `codex/encoding-{prompt,answer}.md`), which independently recommended (i) for the
public layer for exactly this reason, and supplied the `multPrefix` step-lemma mitigation now in the
module. Codex's further suggestion — make interval sub-products `submult A i j` the primitive and set
`mult := submult A 0 N` — is **deliberately deferred to thread 03** (rungs 2-3 own the `r_{ij}` rank
patterns); pulling it in here would gold-plate past rung 1's scope. The current `multPrefix` is the
`i = 0` slice of that future `submult` and a clean bridge to it.

**Typeclass.** `CommRing k` — the weakest class carrying `Matrix.rank` (defined over a `CommRing` via
`finrank R (range A.mulVecLin)`). A `Field` is *not* required for any of these definitions.

## Non-vacuity witness (in-file)

`N = 2`, `d = (2,2,2)` over `Z`, `A_1 = [[1,2],[0,1]]`, `A_2 = [[1,0],[3,1]]`:
- `example : mult dWitness tupleWitness = !![1, 2; 3, 7]` — closes by `unfold ...; decide` (kernel,
  not `native_decide`). Confirms `mult` computes `A_2 A_1` (ordered product, top factor on the left).
- `example : tupleWitness IN fibre dWitness (!![1, 2; 3, 7])` — the loci and fibre are inhabited.

## Build status

- `cd lean && lake build DLNFibre.Core.Setup` -> **green**, zero warnings.
- `python3 scripts/sorries` -> `Summary: 0 sorry, 0 #exit, 0 native_decide, 0 axiom`.
- `#print axioms mult` (and the loci / fibre / `fibre_eq_preimage`) -> only
  `[propext, Classical.choice, Quot.sound]` — **axiom-clean** (no `sorryAx`, no custom axioms).
- `DLNFibre.Core.Basic` and the aggregator `DLNFibre.lean` untouched; `Core.Basic` still builds.

## Friction / surprises

- The `List` "full dimension list `[d_0,...,d_N]`" inductive (a natural-looking fourth encoding)
  **fails to build**: the output dim `(d_0::d_1::ds).getLastD 0` is not defeq to `(d_1::ds).getLastD 0`
  through `getLastD`, forcing a transport rewrite *inside* `mult` — the exact friction the project
  warned about. The head-first output-dim list (ii) and the two-endpoint inductive (iii) both avoid it
  and build clean, but lose the fixed-`d` Set story (see rationale).
- Surprise (good): with the `multPrefix` step lemmas as `rfl`, encoding (i)'s feared transport friction
  is fully contained — the headline worry against (i) did not materialise at the lemma level.
- `Fin.induction_zero`/`_succ` are `@[simp]` `rfl` lemmas, so the step lemmas are `rfl` directly (no
  `rw`); `unfold multPrefix` eta-expands and breaks a naive `rw [Fin.induction_zero]`, so prefer `rfl`.

## Decisions for the controller

1. **Reversal of the brief's encoding steer** (ii -> i): flagged above, Codex-corroborated. Endorse, or
   raise if there is a downstream reason to keep the dimension vector floating.
2. **`submult` (interval sub-products) deferred to thread 03.** `multPrefix` is the `i=0` slice and the
   clean bridge. If the controller wants `submult` co-located in `Setup.lean` as the primitive (Codex's
   preference), that is a small refactor — but it reaches into rung 2-3's `r_{ij}` territory.
3. **`mult` orientation:** top factor on the **left** (`mult = A_N ... A_1`, output dim `d_N`, input
   `d_0`), matching the paper. Verified by the witness.

---

## Statement card (DRAFT — headline object `mult`)

> **Claim.** For a dimension vector `d = (d_0,...,d_N)` over a `CommRing k`, the multiplication map
> `mult : Rep_d -> Mat_{d_N,d_0}(k)` sends a composable tuple `(A_1,...,A_N)` to the ordered product
> `A_N A_{N-1} ... A_1`; the product-rank loci `Sigma^r`, `Sigma^{<=r}` and the fibre `mult^{-1}(B)`
> are its derived `Set`s.
>
> - **Lean:** `DLNFibre.Core.mult`, `DLNFibre.Core.productRankLocus`,
>   `DLNFibre.Core.productRankLocusLE`, `DLNFibre.Core.fibre`
>   (`lean/DLNFibre/Core/Setup.lean` @ `<commit-sha — controller pins on integration>`)
> - **Gloss.** `mult d A := multPrefix d A (Fin.last N)`, where `multPrefix d A j` is the product of
>   the first `j` factors built by `Fin.induction` with step `A_i * prev` (top factor on the left).
>   `Sigma^r` / `Sigma^{<=r}` / fibre are the set-builder predicates on `(mult d A).rank` resp.
>   `mult d A`; `fibre d B = mult d preimage {B}` by `rfl`.
> - **Proved.** `mult` is a total, computable definition over any `CommRing k`; its `rfl` step lemmas
>   (`multPrefix_zero`, `multPrefix_succ`) and the `Iff.rfl` membership lemmas hold definitionally; the
>   `N=2`, `Z` witness shows `mult = A_2 A_1 = [[1,2],[3,7]]` by kernel `decide` (non-vacuity).
> - **Assumed.** `[CommRing k]` (weakest class carrying `Matrix.rank`); the dimension vector is fixed
>   data `d : Fin (N+1) -> N`.
> - **Cited.** none (`Matrix`, `Matrix.rank`, `Fin.induction` are Mathlib infrastructure, not external
>   results being invoked).
> - **Deferred.** none for rung 1. (Interval sub-products `submult` / the rank patterns `r_{ij}` are
>   thread 03 / rungs 2-3, a *separate* result this card does not claim.)
> - **Status.** sorry-free (awaiting reviewer fidelity audit).
