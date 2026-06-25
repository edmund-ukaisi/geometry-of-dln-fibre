**Ring Verdict**

State the localized-chart equivalence and no-drop over `O_eq`.

Decisive reason: a top-dimensional minimal prime `P` of `I_le` with `detΔ ∉ P` actually contains `I_eq`, because `D(detΔ) ∩ V(P) ⊆ Σ^r` is dense in the irreducible component `V(P)`; hence `P/I_eq` is a full-dimensional prime of `O_eq`, and F4 applies directly.

**O_eq Discharge**

Yes, `hsig` can be discharged over `O_eq` without the global density theorem and without `I_eq = I_le`.

Let `S = k[Rep_d]`, `d = detΔ`, and choose a top-dimensional minimal prime `P ⊇ I_le`.

Spec relationship:

- Since `I_le ⊆ I_eq`, there is a surjection `O_le = S/I_le → O_eq = S/I_eq`.
- Thus `Spec(O_eq)` is the closed subset of `Spec(O_le)` consisting of primes containing `I_eq/I_le`.
- A prime `P/I_le ∈ Spec(O_le)` comes from `Spec(O_eq)` iff `I_eq ⊆ P`.
- This is not automatic for arbitrary primes of `O_le`.

For this particular top prime `P`, it works:

- `P` is a top-dimensional minimal prime of `I_le`.
- By F3, `d ∉ P`.
- Since `P ⊇ I_le`, `V(P) ⊆ Σ̄^r`.
- On `D(d)`, product rank is at least `r`; inside `Σ̄^r`, it is at most `r`; hence  
  `D(d) ∩ V(P) ⊆ Σ^r`.
- Since `V(P)` is irreducible and `d ∉ P`, `D(d) ∩ V(P)` is dense in `V(P)`.
- Therefore every function vanishing on `Σ^r` vanishes on `V(P)`, so `I_eq ⊆ P`.

Thus `P/I_eq` is a prime of `O_eq`. It carries full dimension because

`dim(S/P) = dim O_le = dim O_eq`

using F2 and F1. Also `d ∉ P`, so the image of `d` is not in `P/I_eq`. F4 applies over `O_eq`.

**Lemma Chain**

1. Choose a top-dimensional minimal prime `P` of `I_le`. `[cheap]`
2. `P` is prime, `dim(S/P) = dim O_le`, and `V(P)` is the relevant irreducible top component. `[LANDED: F2]`
3. `d ∉ P`. `[LANDED: F3]`
4. Prove `D(d) ∩ V(P) ⊆ Σ^r` from `V(P) ⊆ Σ̄^r` and `d ≠ 0 ⇒ rank ≥ r`. `[cheap]`
5. Since `V(P)` is irreducible and `d ∉ P`, `D(d) ∩ V(P)` is dense in `V(P)`. `[cheap]`
6. Hence `I_eq = vanishingIdeal(Σ^r) ⊆ P`. Equivalently, `P/I_eq ∈ Spec(O_eq)`. `[cheap]`, using F5 or the equivalent dense-open vanishing lemma.
7. `dim(O_eq/(P/I_eq)) = dim(S/P) = dim O_le = dim O_eq`. `[LANDED: F1, F2]`
8. The image of `d` in `O_eq` avoids `P/I_eq`. `[LANDED: F3]`
9. Apply no-drop from a full-dimensional prime avoiding `d`:  
   `ringKrullDim(Localization.Away d O_eq) = ringKrullDim O_eq`. `[LANDED: F4]`

No step uses the global closure identity `closure(Σ^r) = Σ̄^r`.

**Wrapper**

Do not restate the downstream wrapper over `O_le`; keep it over `O_eq`.

**Most Likely Break**

The fragile step is formalizing `I_eq ⊆ P`: you need the local dense-open argument that `D(detΔ) ∩ V(P) ⊆ Σ^r` and is dense in `V(P)`, so functions vanishing on `Σ^r` vanish on `V(P)`. This is not the forbidden global density theorem, but it is the one lemma likely to need careful packaging.