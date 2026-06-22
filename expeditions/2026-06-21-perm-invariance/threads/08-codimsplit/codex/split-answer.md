**Delta**

Write \(m_{ab}\) for `m (a,b)` as an entry of `Fin (N+2) × Fin (N+2)`, with integer cast understood. The closed form is

\[
\Delta
=
\sum_{a=0}^{N}\sum_{u=a+1}^{N+1} m_{a,N}\,m_{u,N+1}.
\]

Equivalently, in the original `codimForm` indices,

\[
\Delta
=
\sum_{i=1}^{N+1}\sum_{u=i}^{N+1}
m_{i-1,N}\,m_{u,N+1}.
\]

No support/Kostant hypothesis is needed. These are triangular entries automatically: \(a\le N\) and \(u\le N+1\).

**Derivation**

For `codimForm (N+1) (extendℤ m)`, the new bound allows second-factor terms with \(v=N+1\). The first factor can only see columns \(j-1\le N\), so column \(N+1\) of `m` is never read in the first slot. Thus

\[
\operatorname{codimForm}_{N+1}(m)
=
\operatorname{codimForm}_{N}(m_{\le N})
+
\sum_{1\le i\le u\le j\le N+1}
m_{i-1,j-1}m_{u,N+1}.
\]

For `codimForm N (extendℤ (peelPart m))`, the first factor has \(j-1\le N-1\), so it never sees the merged column \(N\). The second factor sees \(v=N\), where peeling gives

\[
m'_{u,N}=m_{u,N}+m_{u,N+1}.
\]

Hence

\[
\operatorname{codimForm}_{N}(m')
=
\operatorname{codimForm}_{N}(m_{\le N})
+
\sum_{1\le i\le u\le j\le N}
m_{i-1,j-1}m_{u,N+1}.
\]

The \(j\le N\) part cancels. The leftover is exactly \(j=N+1\):

\[
\sum_{1\le i\le u\le N+1}m_{i-1,N}m_{u,N+1}
=
\sum_{a=0}^{N}\sum_{u=a+1}^{N+1}m_{a,N}m_{u,N+1}.
\]

**Lean Skeleton**

Introduce three arrays.

```lean
-- lower unmerged part, bound N
let m₀ : Fin (N+1) × Fin (N+1) → ℕ :=
  fun p ↦ m (p.1.castSucc, p.2.castSucc)
let A : ℤ → ℤ → ℤ := extendℤ (N := N) m₀

-- last column of m shifted into column N, for the peeled array
let R : ℤ → ℤ → ℤ := fun α β ↦
  if h : 0 ≤ α ∧ α ≤ (N : ℤ) ∧ β = (N : ℤ) then
    (m (⟨α.toNat, by omega⟩, Fin.last (N+1)) : ℤ)
  else 0

-- true last column of m, in the larger bound N+1
let L : ℤ → ℤ → ℤ := fun α β ↦
  if h : 0 ≤ α ∧ α ≤ ((N+1 : ℕ) : ℤ) ∧ β = ((N+1 : ℕ) : ℤ) then
    (m (⟨α.toNat, by omega⟩, Fin.last (N+1)) : ℤ)
  else 0
```

Then prove on-box identifications using `codimForm_congr_onbox`:

```lean
have hPeel :
  codimForm N (extendℤ (N := N) (peelPart m)) = codimForm N (A + R) :=
  codimForm_congr_onbox (N := N) ?peel_onbox

have hBig :
  codimForm (N+1) (extendℤ (N := N+1) m) = codimForm (N+1) (A + L) :=
  codimForm_congr_onbox (N := N+1) ?big_onbox
```

Expand both with `codimForm_add`.

Small side:

```lean
rw [hPeel, codimForm_add]
```

Then kill:

```lean
codimBil N R A = 0
codimForm N R = 0
```

Reason: in the first slot, `R (i-1) (j-1)` can be nonzero only if `j-1 = N`, i.e. `j = N+1`; but in `codimBil N`, the range has `j ≤ N`.

So

```lean
codimForm N (extendℤ (peelPart m))
  = codimForm N A + codimBil N A R
```

and `codimBil N A R` collapses to

\[
\sum_{1\le i\le u\le j\le N} m_{i-1,j-1}m_{u,N+1}.
\]

Big side:

```lean
rw [hBig, codimForm_add]
```

Kill:

```lean
codimBil (N+1) L A = 0
codimForm (N+1) L = 0
```

Reason: in the first slot, `L (i-1) (j-1)` would require `j-1 = N+1`, i.e. `j = N+2`; but the range has `j ≤ N+1`.

Also prove:

```lean
codimForm (N+1) A = codimForm N A
```

Reason: the only extra `N+1`-bound terms have `v = N+1`, but `A u (N+1) = 0`.

Thus

```lean
codimForm (N+1) (extendℤ m)
  = codimForm N A + codimBil (N+1) A L
```

and `codimBil (N+1) A L` collapses to

\[
\sum_{1\le i\le u\le j\le N+1} m_{i-1,j-1}m_{u,N+1}.
\]

Finally split this last sum into `j ≤ N` plus `j = N+1`. The `j ≤ N` part is exactly `codimBil N A R`; the `j = N+1` part is \(\Delta\).

**Fiddly Lean Step**

The most technical step is `?peel_onbox`: proving

```lean
extendℤ (N := N) (peelPart m) α β = (A + R) α β
```

under `0 ≤ α`, `α ≤ β`, `β ≤ N`.

This is where `Fin.last`, `castSucc`, `Int.toNat`, and the case split `β = N` versus `β < N` meet `peelPart_eq`. The vanish proofs after that are mostly `unfold codimBil`; `sum_eq_zero`; `omega`.

**Status**

The formula and cancellation argument above are a direct derivation from the definitions. The Lean path is a proof skeleton using the stated landed lemmas; I have not checked a full Lean term here, so the exact helper lemma names for the sum-splitting/collapse are inferred implementation details.