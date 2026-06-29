**Q1**

Assuming `composeFold [f₁, f₂, …, fₙ] = f₁ ∘ f₂ ∘ … ∘ fₙ`, the proof-level factor list should be shallow-to-deep in the list, so it evaluates deepest-to-shallowest.

For nontrivial boundaries `s = 1, …, L-1`:

```lean
BFactors =
  [ schur_1, chain_1, ldu_1,
    schur_2, chain_2, ldu_2,
    ...
    schur_{L-1}, chain_{L-1}, ldu_{L-1} ]
```

So evaluation is:

```text
ldu_{L-1}
→ chain_{L-1}
→ schur_{L-1}
→ ...
→ ldu_s
→ chain_s
→ schur_s
→ ...
→ ldu_1
→ chain_1
→ schur_1
```

This is the subtle point: within a boundary, I would **not** put `chain_s` after `schur_s` unless raw `N_s` is stored separately and untouched. With the Schur block

```text
(X, K, N, E) ↦ (K, K N, X K, X K N + E)
```

the raw `N` slot is consumed/replaced by `K N`. Since `chain_s` needs raw `N_s` in

```text
(W_s, C_{s+1}) ↦ (W_s, C_{s+1} - N_s W_s),
```

`chain_s` must be evaluated before `schur_s`, but after deeper boundary factors have already built `C_{s+1}`.

So the correct dependency order is:

```text
deep factors first,
then ldu_s,
then chain_s,
then schur_s.
```

`ldu_s` and `chain_s` commute if their slots are genuinely disjoint, but the clean ordered triple is:

```text
[schur_s, chain_s, ldu_s]
```

not `[chain_s, schur_s, ldu_s]`.

`s = 0` should be omitted if it is the identity/no-content boundary.

**Q2**

Use the existing `chartIdxEquiv`-derived coordinatization. Do **not** invent bespoke coordinate equivalences.

But it is not literally one identical CLE for all three factors. It should be one coherent family derived from the same global slot equivalence:

```text
E_schur_s = chartIdxEquiv + boundary frame split + frameSplitEquiv
E_ldu_s   = chartIdxEquiv + same boundary frame split + K-role/LDU split
E_chain_s = chartIdxEquiv + lift slot W_s + next C-slot C_{s+1}
```

The chain CLE is the only one with an index shift: its `C` block is `C_{s+1}`, using the leaf slot when `s = L-1`. That must match the actual decoder slots. Proof-level verdict: chartIdxEquiv-derived CLEs suffice; bespoke E’s would mainly create indexing risk.

**Q3**

No new deep map-equality lemma is needed.

The identity

```lean
phi = B ∘ pivotBlowupOn active p
```

reduces to:

1. the banked Schur block value lemmas

```text
schurFrameProd_block_K
schurFrameProd_block_KN
schurFrameProd_block_XK
schurFrameProd_block_XKNuE
```

2. the slot fact that `pivotBlowupOn` replaces the de-radialized active `E_s` and leaf slots by `u • E_s` and `u • Rfin`.

The useful Lean lemma is only a wrapper/extensionality lemma, with the same grain as the banked block lemmas:

```lean
∀ y,
∀ s, s ∈ nontrivialBoundaries →
  K_block   (phi y) s = K_block   (B (pivotBlowupOn active p y)) s ∧
  KN_block  (phi y) s = KN_block  (B (pivotBlowupOn active p y)) s ∧
  XK_block  (phi y) s = XK_block  (B (pivotBlowupOn active p y)) s ∧
  XKN_block (phi y) s = XKN_block (B (pivotBlowupOn active p y)) s ∧
  lift_block (phi y) s = lift_block (B (pivotBlowupOn active p y)) s
```

plus leaf and pivot-anchor cases.

The only “new lemma” worth adding is a shallow extensional packaging lemma:

```lean
theorem phi_eq_B_comp_pivotBlowupOn :
  ∀ y, phi y = B (pivotBlowupOn active p y)
```

Its proof should be by `ext`/`chartIdxEquiv` cases and per-block rewrites. It is not a new algebraic lemma; it is the same per-boundary, per-block grain as the existing `schurFrameProd_block_*` facts.