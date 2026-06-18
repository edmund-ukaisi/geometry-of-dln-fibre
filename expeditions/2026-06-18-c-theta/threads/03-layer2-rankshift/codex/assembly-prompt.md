<task>
Lean 4 / Mathlib v4.29. I need the cleanest idiom chain to assemble two Finset-bijection conclusions.
I already have the hard parts (membership transport, injectivity, value-preservation); I want the
ASSEMBLY only.

Setup (all in a namespace, `N : ℕ`):
- `KP d r : Finset (Fin (N+1) × Fin (N+1) → ℕ)` — a Finset of functions (DecidableEq holds).
- `dropCorner (m) := Function.update m (0, Fin.last N) (0 : ℕ)`.
- `dminus d r := fun k ↦ d k - r`.
- `val (m) := codimForm N (extendℤ m) : ℤ` — a value function.

I CAN prove (treat as given lemmas, names invented):
  (a) `kp_image : KP (dminus d r) 0 = (KP d r).image dropCorner`  -- set equality
  (b) `drop_inj : Set.InjOn dropCorner (KP d r)`                  -- injective on the set
  (c) `val_drop : ∀ m, val (dropCorner m) = val m`                -- corner-blind (holds for all m)

Definitions:
  `cCodim d r (h : (KP d r).Nonempty) : ℤ := (KP d r).inf' h val`
  `numTop d r (h : (KP d r).Nonempty) : ℕ :=
      ((KP d r).filter (fun m ↦ val m = cCodim d r h)).card`

GOALS to prove (with `hr : ∀ k, r ≤ d k` available, and both nonemptiness hyps in scope as needed):
  (1) `cCodim (dminus d r) 0 h0 = cCodim d r hr'`
  (2) `numTop (dminus d r) 0 h0 = numTop d r hr'`
      (h0 : (KP (dminus d r) 0).Nonempty ; hr' : (KP d r).Nonempty)
</task>

<output_contract>
Two short proof skeletons (Lean 4 tactic mode), one per goal, using PRECISE Mathlib v4.29 lemma names.
For (1): which of `Finset.inf'_image`, `Finset.inf'_congr`, `Finset.inf'_map` — and the exact
signature/orientation. Note `inf'_image` rewrites `(s.image f).inf' hs g = s.inf' _ (g ∘ f)`; I then
need `g ∘ dropCorner = val` to reduce to `(KP d r).inf' _ val` — is `Finset.inf'_congr` the tool to
swap `g ∘ f` for `val` pointwise-on-the-set, and what is its exact statement (does it need the
functions equal ON the finset, and how is the nonemptiness arg discharged given inf' is
proof-irrelevant in it)?
For (2): the chain `filter ∘ image → image ∘ filter` (`Finset.filter_image`? `Finset.image_filter`?
give the exact name + orientation), then `Finset.card_image_of_injOn`. The filter predicate
references `cCodim (dminus d r) 0 h0`; I will first rewrite it to `cCodim d r hr'` using goal (1).
Flag: after `filter_image`, the inner filter predicate becomes `fun m ↦ val (dropCorner m) = …`;
I rewrite with `val_drop` (a `Finset.filter_congr`?). Give the exact congr lemma + signature.
Be concise — lemma names, orientation, and the ~6-10 line skeletons. No prose essays.
</output_contract>

<grounding_rules>
These are Mathlib v4.29 names. If you are unsure a lemma exists at that pin or its exact signature,
SAY SO explicitly and give the most likely name + a fallback (e.g. prove via `le_antisymm` +
`Finset.inf'_le`/`Finset.le_inf'`, or `Finset.card_nbij'`). Mark each lemma name as "confident" vs
"verify". Do not invent a lemma and present it as certain.
</grounding_rules>
