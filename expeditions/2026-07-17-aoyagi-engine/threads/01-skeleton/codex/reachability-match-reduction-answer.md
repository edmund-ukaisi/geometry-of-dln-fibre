### Q1

Use a local reduction equation, then rewrite `hc`. In the case-1 branch:

```lean
have hrun : 1 ≤ target - s.cleared := by omega
have helig :
    s.divTilde f = s.cleared + (target - s.cleared) := by
  rw [(chooseMin_spec s target hf).1]
  omega

have horacle :
    conOracle M s =
      case1Decision M s f (target - s.cleared)
        (M ⟨s.layer, by omega⟩ - s.cleared)
        (M ⟨s.layer + 1, by omega⟩ - s.cleared)
        (not_le.mp h1) hrun helig hcap := by
  unfold conOracle
  rw [dif_neg h1, dif_neg h2]
  split <;> simp_all [occ]
  all_goals
    split <;> simp_all [occ]

rw [horacle] at hc
-- hc is now membership in (case1Decision ...).stepChildren
```

The first `split` handles `occ.min?`; the second handles `chooseMin`. For case 2:

```lean
have horacle :
    conOracle M s =
      case2Decision M s
        (M ⟨s.layer, by omega⟩ - s.cleared)
        (M ⟨s.layer + 1, by omega⟩ - s.cleared) hcap := by
  unfold conOracle
  rw [dif_neg h1, dif_neg h2]
  split <;> simp_all [occ]

rw [horacle] at hc
```

Omit `[occ]` if you wrote the filter-map expression directly rather than using a local `occ`.

### Q2

Yes—per-branch reduction equations are the robust approach here.

```lean
have hred :
    conOracle M s =
      case2Decision M s
        (M ⟨s.layer, by omega⟩ - s.cleared)
        (M ⟨s.layer + 1, by omega⟩ - s.cleared) hcap := by
  unfold conOracle
  rw [dif_neg h1, dif_neg h2]
  split <;> simp_all [occ]

rw [hred] at hc
```

Once the outer dites are reduced, `split` can handle `match h : x with` on the equation’s left-hand side. It generates branch equations; `simp_all` removes branches contradicting `hmin`/`hf`, and the selected branch closes definitionally.

Proof irrelevance makes different proofs of `hcap`, `hrun`, etc. definitionally equal. It also makes `⟨s.layer, proof₁⟩` and `⟨s.layer, proof₂⟩` definitionally equal, so the `Fin` arguments match.

### Q3

Yes. A plain nondependent match reduces normally:

```lean
cases hmin : occ.min? with
| none =>
    simp only [conOracle, dif_neg h1, dif_neg h2, hmin] at hc
| some target =>
    have hmem : target ∈ occ := List.min?_mem hmin
    simp only [conOracle, dif_neg h1, dif_neg h2, hmin] at hc
```

However, inside the definition itself, a plain-match branch does not provide `hmin`. Using `cases h : occ.min?` there merely recreates the dependent equation-binding match.

The clean refactor is `isSome/get`:

```lean
if hm : occ.min?.isSome then
  let target := occ.min?.get hm
  have hmin : occ.min? = some target :=
    (Option.some_get hm).symm
  have hmem : target ∈ occ :=
    List.min?_mem hmin
  -- derive htarget from hmem
  ...
else
  have hnone : occ.min? = none :=
    Option.not_isSome_iff_eq_none.mp hm
  ...
```

Repeat the same pattern for `chooseMin`. These are dites, so `dif_pos`/`dif_neg` reduce them reliably.