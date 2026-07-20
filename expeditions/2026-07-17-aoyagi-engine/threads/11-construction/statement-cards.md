# Statement cards — thread 11 (construction spine, A→C)

Seat: `architect`/construction (t01-r2). The IsFullMonomialization spine of the transform-only Aoyagi
engine — the `CanonicalResolution` §1 conjunct of `monomialization_terminates`.

---

> **Claim.** For a width vector `M : Fin (L+1) → ℕ` with `0 < L`, the resolution tree produced by the
> engine's construction (`buildTree` driven by the total oracle `conOracle` from the root state
> `conRoot`) is a **full monomialisation**: at every leaf, each `t̃=0` analytic divisor's accumulated
> exponent equals `Mval` of its rank-pattern and that pattern is admissible, and the analytic side is
> exactly the `t̃=0` sublist of the full ledger.
>
> - **Lean:** `DLNFibre.DLN.RLCT.Engine.isFullMonomialization_buildTree_conRoot`
>   (`lean/DLNFibre/DLN/RLCT/Engine/EngineConstruction.lean` @ `6aead4b00`)
> - **Gloss.** `(M) (hL : 0 < L) : IsFullMonomialization (buildTree M (conOracle M) conRoot)`.
>   `IsFullMonomialization t` (EngineDefs) = for every leaf `l ∈ leaves t`: (1) `∀ k, l.divExp k =
>   (Mval M (l.divProfile k)).toNat ∧ l.divProfile k ∈ Adm M`; (2) each analytic `k` matches a `t̃=0`
>   full divisor; (3) each `t̃=0` full divisor is matched by an analytic `k`. The tree is the GENUINE
>   construction — `conOracle` is the total dispatch (terminal / rollover / case-1(1)+1(2) / case-2),
>   not the trivial `oracleTerminal` fallback.
> - **Proved.** The full statement, unconditionally in `M` except `0 < L`. Axiom footprint
>   `[propext, Classical.choice, Quot.sound]` (clean-three; no `sorryAx`/`native_decide`). Supporting
>   kit, all clean-three: `MvalCoh` (`(divExp k : ℤ) = Mval`), the case-2 telescoping
>   `Mval_setTail_runMinWidth`, the case-1 delta `Mval_setTail_delta`, `BoundaryFlat`, `T0Bound`,
>   `NumDivFlatPos`, and their reachability `MvalBoundaryInv_conOracle_stepChildren`, folded to the
>   leaves by `leaves_isFullMono` (WF-induction on `conRel`).
> - **Assumed.** `0 < L` (the nondegenerate-chain guard: `Adm`'s last-`= 0` clause reads index `L−1`).
>   No positivity of the widths: `T0Bound`/`NumDivFlatPos` keep the statement true even when a later
>   zero-width layer strands an earlier `t̃=0` divisor (`widthMinUpto L = 0` — still admissible, the
>   `flatDim = 0` branch of `leafOfState` carries no `t̃=0` divisor).
> - **Cited.** none (network-free; the `Mval`/`Adm`/`tildeOf`/`runMinWidth`/`flatDim` primitives are
>   local `Foundations`/engine defs).
> - **Deferred.** This is `CanonicalResolution` §1 ONLY. NOT proven here: `ChartBridge` (the coverage
>   lane, T3); the exponent hooks `minAdm ≤ terminalExponents` (tractable) and `minAdm ∈
>   terminalExponents` + live-attainment (the o5 realization, tasks #24/#27); `StepRel`-all and `base`
>   exist pre-spine (`stepRel_all_of_buildTree`, `base_of_buildTree`) and are ready to wire.
> - **Structure & ideas observed.** The B'-coherence tie reduces to two `Mval` identities: the case-2
>   running-min telescoping (head/tail terms vanish, lone survivor = running-min corank product — the
>   FIX-A distinction) and the case-1 tail-write delta `(τ−J)(M^(l+1)−J)`, which is faithful ONLY under
>   the boundary fact `tPrev(T)_layer = τ` (a pending divisor is flat at `layer−1` because it was
>   created at a strictly earlier layer) — encoded as the reachable-state invariant `BoundaryFlat`.
>   Terminal admissibility of `t̃=0` divisors is liveness-free (`T0Bound`: head = `runMinWidth ≤
>   admBound`), so it survives interior-bottleneck stranding. (Codex xhigh corroborated the delta
>   algebra + boundary invariant: `threads/11-construction/codex/case1-mval-delta-answer.md`.)
> - **Route.** SPECIFY→PROVE bottom-up: leaf constructor (t0Indices analytic side) → Mval identities →
>   BoundaryFlat/T0Bound/NumDivFlatPos invariants + reachability → WF-fold → capstone.
> - **NOT a claim of `⊇ Adm`.** pnp-o5 (`threads/12-realization/cert-o5-realization.md`) found the
>   profile-set is a PROPER subset of `Adm` at interior-bottleneck widths; the capstone claims the tree
>   IS a monomialisation (`P ⊆ Adm` direction + coherence), never `P ⊇ Adm`.
> - **Status.** sorry-free (clean-three); reviewer requested (fidelity check pending).
