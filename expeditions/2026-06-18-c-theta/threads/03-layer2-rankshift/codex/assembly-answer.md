All names below are **confident**, verified against local Mathlib `v4.29.0`.

```lean
-- (1)
by
  have himg : ((KP d r).image dropCorner).Nonempty := by
    simpa [← kp_image] using h0
  have h1 :
      ((KP d r).image dropCorner).inf' himg val
        = (KP d r).inf' himg.of_image (val ∘ dropCorner) := by
    exact Finset.inf'_image himg val
  have h2 :
      (KP d r).inf' himg.of_image (val ∘ dropCorner)
        = (KP d r).inf' hr' val := by
    exact Finset.inf'_congr himg.of_image rfl (by
      intro m hm
      exact val_drop m)
  simpa [cCodim, kp_image] using h1.trans h2
```

Relevant signatures:

```lean
Finset.inf'_image :
  (s.image f).inf' hs g = s.inf' hs.of_image (g ∘ f)

Finset.inf'_congr :
  s.inf' H f = t.inf' (h₁ ▸ H) g
```

`inf'_congr` takes the nonempty proof `H` explicitly first:
```lean
Finset.inf'_congr H h₁ (fun x hx => ...)
```

```lean
-- (2), assuming `hc` is goal (1):
-- hc : cCodim (dminus d r) 0 h0 = cCodim d r hr'
by
  unfold numTop
  rw [hc, kp_image, Finset.filter_image]
  rw [Finset.card_image_of_injOn]
  · exact congrArg Finset.card (Finset.filter_congr (by
      intro m hm
      simp [val_drop m]))
  · exact drop_inj.mono (by
      intro m hm
      exact (Finset.mem_filter.mp hm).1)
```

Relevant signatures:

```lean
Finset.filter_image :
  (s.image f).filter p = (s.filter fun a => p (f a)).image f

Finset.filter_congr :
  (∀ x ∈ s, p x ↔ q x) → s.filter p = s.filter q

Finset.card_image_of_injOn :
  Set.InjOn f ↑s → (s.image f).card = s.card
```

`Finset.inf'_map` is not the right tool here unless you package `dropCorner` as an embedding.