# Rockafellar's Page 2 Observation

On page 2 (book page 44) of Rockafellar's "Convex Analysis" Section 6, he makes the following observation:

> Observe that
> cl C ⊆ cl (aff C) = aff C
> for any C. Thus any line through two different points of cl C lies entirely in aff C.

## Status in Mathlib

### Part 1: cl C ⊆ aff C

This is **AVAILABLE** in Mathlib:

```lean
-- From Mathlib.Analysis.Convex.Intrinsic
intrinsicClosure_subset_affineSpan : intrinsicClosure 𝕜 s ⊆ affineSpan 𝕜 s
```

In our context with the subspace topology, `intrinsicClosure ℝ s` is the relative closure (what Rockafellar calls `cl C` when viewing C within its affine hull).

For the **ambient closure**, we need:
```lean
closure s ⊆ affineSpan ℝ s
```

This should follow from:
- `s ⊆ affineSpan ℝ s` (available as `subset_affineSpan`)
- Affine subspaces are closed in finite-dimensional spaces
- `closure_minimal : s ⊆ t → IsClosed t → closure s ⊆ t`

### Part 2: cl (aff C) = aff C (affine subspaces are closed)

This is **AVAILABLE** in Mathlib for finite-dimensional spaces:

```lean
-- From Mathlib.Analysis.Normed.Module.FiniteDimension
AffineSubspace.closed_of_finiteDimensional :
  ∀ {P : Type*} [MetricSpace P] [NormedAddTorsor E P]
    (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction],
  IsClosed (s : Set P)
```

This states that in a finite-dimensional normed space, every finite-dimensional affine subspace is closed.

### Part 3: Lines through two points of cl C lie in aff C

This is **AVAILABLE** in Mathlib:

```lean
-- From Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
AffineMap.lineMap_mem_affineSpan_pair :
  ∀ (r : k) (p₁ p₂ : P), AffineMap.lineMap p₁ p₂ r ∈ line[k, p₁, p₂]
```

Combined with transitivity:
- If p₁, p₂ ∈ closure s, then p₁, p₂ ∈ affineSpan s (by Part 1)
- The line through p₁, p₂ is `line[ℝ, p₁, p₂]` = affineSpan ℝ {p₁, p₂}
- Since p₁, p₂ ∈ affineSpan s, we have affineSpan {p₁, p₂} ⊆ affineSpan s
- Therefore any point on the line lies in affineSpan s

## What Needs to be Added (if anything)

The individual pieces are all in Mathlib. What might be useful is to add **explicit helper lemmas** that package these results for easy use:

```lean
-- Ambient closure is contained in affine span
theorem closure_subset_affineSpan {s : Set E} :
    closure s ⊆ affineSpan ℝ s := by
  apply closure_minimal (subset_affineSpan ℝ s)
  -- Apply AffineSubspace.closed_of_finiteDimensional
  sorry

-- Affine span equals its closure (in finite dimensions)
theorem closure_affineSpan_eq_self {s : Set E} :
    closure (affineSpan ℝ s : Set E) = affineSpan ℝ s := by
  apply IsClosed.closure_eq
  -- Apply AffineSubspace.closed_of_finiteDimensional
  sorry

-- Line through two points in closure lies in affine span
theorem line_through_closure_subset_affineSpan {s : Set E} {x y : E}
    (hx : x ∈ closure s) (hy : y ∈ closure s) (t : ℝ) :
    AffineMap.lineMap x y t ∈ affineSpan ℝ s := by
  -- Combine the above results
  sorry
```

## Recommendation

These lemmas are straightforward consequences of existing Mathlib results. They should be added to `RelativeInterior.lean` if they're needed for the proofs. The key dependency is `AffineSubspace.closed_of_finiteDimensional`, which is already available and applies to our finite-dimensional setting.

## Usage in Rockafellar's Proofs

Rockafellar uses these observations to reason about:
1. Points in the closure staying within the affine hull
2. Convex combinations and line segments preserving the affine structure
3. The relative topology being well-defined

These are foundational for Theorems 6.1-6.4 about relative interiors.
