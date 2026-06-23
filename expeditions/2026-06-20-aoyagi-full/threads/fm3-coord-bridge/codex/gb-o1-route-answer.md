**1. ROUTE VERDICT**

Use **RECURSION** for the binding theorem. Given `descentStep`, `chainRel_wf`, and the verified `nReg = minAdm M - minAdm red`, it is lower new work than building `IsRouteMCover` + global `IsResolutionAtlas`. The routes are complementary, not truly duplicate: the atlas route proves a global chart-tree cover plus a pure `⨅` value theorem; the recursion route proves the RLCT value directly by iterating local analytic equalities. For the binding identity, recursion **avoids/subsumes the need for the atlas `(S)` surjectivity/exhaustiveness obligation**. It does not produce the existing atlas `(S)` field unless you later package it that way.

**2. O1 STATEMENT**

O1 should be **(a): an RLCT equality step**, not cover inequalities.

Clean Lean shape:

```lean
theorem dlnLoss_schur_descent
  (D : RouteMNodeDescent M)
  (P : FlatCorePresentation M D) :
  rlctAtOn (dlnLoss M 0) (deepest M)
    =
  ofReal ((D.nReg : ℝ) / 2)
    + rlctAtOn (dlnLoss D.red 0) (deepest D.red)
```

or with `(fun _ => 0)` on the RHS if that is definitionally the reduced deepest point. If not definitionally equal, add a small simp lemma identifying them.

The proof should be just:

```lean
rw [P.rlctAtOn_dlnLoss_eq_flatCore]
exact descentStep D
```

So the right decomposition is:

```lean
O1_of_flatCorePresentation_and_descent
```

then later a producer lemma:

```lean
flatCorePresentation_of_node :
  NonLeaf M → FlatCorePresentation M D
```

Do **not** make O1 a `cover_le / cover_ge_div` statement. That drops below the already-banked `descentStep` abstraction and starts duplicating the `IsRouteMCover` work. A bare `NonLeaf M` hypothesis is only enough if you already have canonical construction of `RouteMNodeDescent M` plus the flatCore transport from it.

Yes: O1 needs the per-node MP transport / presentation

```lean
rlctAtOn (dlnLoss M 0) (deepest M)
  = rlctAtOn flatCore (0,0)
```

as a hypothesis or derived producer. `descentStep` alone only starts after that presentation.

**3. THE TELESCOPE**

The telescope is clean if you formulate the arithmetic as:

```lean
D.nReg + minAdm D.red = minAdm M
```

rather than using Nat subtraction in the main proof. Then the induction step is just:

```lean
nReg/2 + minAdm(red)/2 = minAdm(M)/2
```

The leaf base must be:

```lean
rlctAtOn (dlnLoss M 0) (deepest M) = 0
```

for `Leaf M`, matching `minAdm M = 0`.

If the leaf lemma gives `⊤`, the recursion proof is dead: `nReg/2 + ⊤ = ⊤`. For a degenerate zero-loss leaf, the RLCT threshold should be `0`, not `⊤`. If lemma #70 says `rlctAt(deepest) = nReg/2` at a leaf, it is usable only if that `nReg` is provably `0` or equals `minAdm leaf = 0`.

**4. THE TRAP**

The real risk is the **per-node MP transport from original `dlnLoss M 0` at `deepest M` to `flatCore` at `(0,0)`**, including point/domain matching. That is the piece most likely to contain the same formaliser-weeks coordinate plumbing as the atlas route. But it is still local plumbing, not global chart-tree `(S)` exhaustiveness.

Cheap de-risk: first prove an abstract theorem `binding_from_O1_and_leaf` using only an assumed O1, the leaf value `0`, and the arithmetic step `lambdaCore M = nReg/2 + lambdaCore red`. Separately prove the one-line bridge `O1_of_flatCorePresentation_and_descent`. If both typecheck, the remaining hard work is isolated to the producer `FlatCorePresentation M D`, not the recursion/telescope design.