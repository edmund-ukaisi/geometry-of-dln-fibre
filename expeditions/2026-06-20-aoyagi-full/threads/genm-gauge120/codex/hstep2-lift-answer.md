1. **PROOF**

F1 is correct, assuming the relevant top-left blocks are invertible: `A_11`, `B_11`, and `(AB)_11`.

Write

```text
A = [a b; c d],   B = [e f; g h],
S_A = d - c a⁻¹ b,   S_B = h - g e⁻¹ f,
α = (AB)_11 = ae + bg.
```

Using block LDU decompositions,

```text
A = [I 0; ca⁻¹ I] [a 0; 0 S_A] [I a⁻¹b; 0 I],
B = [I 0; ge⁻¹ I] [e 0; 0 S_B] [I e⁻¹f; 0 I].
```

Left multiplication by a lower block-unit matrix and right multiplication by an upper block-unit matrix do not change the Schur complement. The middle product has blocks

```text
[ α        b S_B
  S_A g    S_A S_B ].
```

Therefore

```text
Schur(AB)
= S_A S_B - S_A g α⁻¹ b S_B
= S_A (I - g α⁻¹ b) S_B.
```

So with `K = B_21 (AB)_11⁻¹ A_12`, F1 is exactly right. No commutativity is being used.

2. **PROOF, conditional on the stated F2/F4/F5**

Yes: once `Psi` is a genuine local smooth diffeomorphism at `0`, the GOAL follows by local-diffeomorphism invariance of RLCT.

The composition identity is

```text
Score = corePhi ∘ Psi
```

and if `Sreg` is fixed by `Psi`, then

```text
Sreg + Score = (Sreg + corePhi) ∘ Psi.
```

Thus

```text
rlctAtOn(Sreg + Score, 0)
= rlctAtOn((Sreg + corePhi) ∘ Psi, 0)
= rlctAtOn(Sreg + corePhi, Psi(0))
= rlctAtOn(Sreg + corePhi, 0).
```

What still must be checked:

- `Psi` is defined on an open neighbourhood of `0`.
- All `(P_k)_11⁻¹` appearing in `K_k` are smooth/analytic there. This follows by shrinking, since `(P_k)_11(0)=I`.
- If the formal coordinates are `(X,Y,Z,S)` rather than `(X,Y,Z,T)`, the Schur-core chart itself must be a local analytic diffeomorphism: `T_s = S_s + Z_s(I+X_s)⁻¹Y_s`.
- `Psi(0)=0`.
- The full derivative, including regular/spectator coordinates, is the identity.
- Then the finite-dimensional inverse function theorem gives a local `C^∞`, indeed analytic, diffeomorphism.
- `Sreg ∘ Psi = Sreg`; this is automatic only if `Sreg` depends solely on coordinates that `Psi` fixes.
- If `rlctAtOn` is over a restricted set rather than the ambient open chart, the set must be carried correctly by `Psi`, or the statement must be localized to an open neighbourhood where the domain issue disappears.

The core-dependence of `K_k` does not threaten local invertibility once smoothness and `dPsi(0)=I` are established.

3. **STRONG-ARGUMENT**

I do not see an obstruction appearing only at `L >= 3`.

The new features are real but not intrinsically new mathematics:

- **Non-commutativity:** harmless. F1 preserves the exact order:
  ```text
  S_0 (I-K_1) S_1 (I-K_2) S_2 ...
  ```
  No reordering is needed.

- **Nested inverses `(P_k)_11⁻¹`:** harmless locally. Each `(P_k)_11(0)=I`, so all inverses are analytic after shrinking the neighbourhood.

- **Core-dependence of `K_k`:** this prevents the explicit L=2-style inverse `S_k ↦ (I-K_k)⁻¹S_k` with `K_k` treated as a fixed regular coefficient. But it does not block the argument. The map has the form
  ```text
  S_k ↦ U_k(q,S) S_k,   U_k(0)=I,
  ```
  so its derivative at `0` is still identity. The inverse function theorem is exactly the right replacement.

So the only genuine difference from `L=2` is proof packaging: for `L >= 3`, use the full inverse function theorem rather than a fibrewise linear inverse depending only on regular variables.

4. **STRONG-ARGUMENT**

Net verdict: **A, bounded structural generalisation**, not a new-mathematics wall.

Concrete sub-lemmas to close it:

1. **Recursive Schur product lemma:** prove F1 generally, then induct to get F2.
2. **Analyticity/domain lemma:** near `0`, all `I+X_s` and `(P_k)_11` are invertible, so all `S_s`, `K_k`, and `Psi` are smooth/analytic.
3. **Derivative lemma for `Psi`:** for `Psi_k = (I-K_k)S_k`, show `Psi(0)=0` and `dPsi(0)=I` on the full coordinate space.
4. **RLCT bridge lemma:** use inverse function theorem plus local-diffeomorphism invariance, with `Sreg` fixed.

The potentially large part is the block-matrix induction and formal bookkeeping around coordinates/inverses. I would not classify it as a mathematical wall.