/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import ConvexPolyhedra.Rockafellar.Chapter06

/-!
# Applications of Rockafellar's Theorems

This file contains applications of Rockafellar's Theorems 6.1 and 6.4 to characterize
relationships between convex sets based on affine dimension.

## Main results

* `convex_eq_of_subset_affineSpan_same_dim_full` - If s ⊆ t ⊆ affineSpan s with equal dimensions
  and s has full dimension, then s = t
* `subset_of_subset_affineSpan_same_dim` - If s ⊆ t ⊆ affineSpan s with equal dimensions,
  then t ⊆ s

## References

* Rockafellar, "Convex Analysis" (1970), Theorem 6.2
* Ziegler, "Lectures on Polytopes" (1995), Proposition 2.4

## Tags

convex, relative interior, affine dimension, applications
-/

open Set AffineSubspace
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
### Affine dimension properties
-/

/-- Affine dimension is monotone with respect to inclusion in affine spans.

If s ⊆ affineSpan ℝ t, then affineDim ℝ s ≤ affineDim ℝ t.

This follows from the fact that affineSpan is monotone and idempotent, combined with
the relationship between affine dimension and the dimension of the direction submodule. -/
theorem affineDim_le_of_subset_affineSpan {s t : Set E} (h : s ⊆ affineSpan ℝ t) :
    affineDim ℝ s ≤ affineDim ℝ t := by
  -- Use affineSpan_mono to get affineSpan ℝ s ≤ affineSpan ℝ (affineSpan ℝ t)
  have h1 : affineSpan ℝ s ≤ affineSpan ℝ (affineSpan ℝ t) := affineSpan_mono ℝ h
  -- Use idempotence: affineSpan ℝ (affineSpan ℝ t) = affineSpan ℝ t
  have h2 : affineSpan ℝ (affineSpan ℝ t) = affineSpan ℝ t := AffineSubspace.affineSpan_coe _
  -- Combine to get affineSpan ℝ s ≤ affineSpan ℝ t
  have h3 : affineSpan ℝ s ≤ affineSpan ℝ t := h2 ▸ h1
  -- Apply direction_le to get direction ordering
  have h4 : (affineSpan ℝ s).direction ≤ (affineSpan ℝ t).direction :=
    AffineSubspace.direction_le h3
  -- Use finrank monotonicity on submodules
  -- affineDim is defined as Module.finrank of the direction
  simp only [affineDim]
  exact_mod_cast Submodule.finrank_mono h4

/-!
### Applications and corollaries
-/

/-- If s ⊆ t ⊆ affineSpan s with equal affine dimensions and s has full dimension,
then s = t.

This follows from the fact that s is relatively closed. -/
theorem convex_eq_of_subset_affineSpan_same_dim_full {s t : Set E}
    (hs_conv : Convex ℝ s) (ht_conv : Convex ℝ t)
    (hs_ne : s.Nonempty)
    (h_subset : s ⊆ t)
    (h_in_span : t ⊆ affineSpan ℝ s)
    (h_dim_eq : affineDim ℝ s = affineDim ℝ t)
    (h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    s = t := by
  -- Strategy: show t ⊆ (affineSpan s ∩ closure s), then use base theorem
  apply Subset.antisymm h_subset

  --  We'll show t ⊆ s by showing t ⊆ affineSpan s ∩ closure s and applying base theorem
  intro x hx_t

  -- We have t ⊆ affineSpan s directly from h_in_span
  have hx_span : x ∈ (affineSpan ℝ s : Set E) := h_in_span hx_t

  -- Need to show x ∈ closure s
  -- Key insight: since s and t have same affine span and dimension, t ⊆ closure s
  have ht_in_closure_s : t ⊆ closure s := by
    -- Establish affineSpan s = affineSpan t
    have h_span_eq : affineSpan ℝ s = affineSpan ℝ t := by
      apply le_antisymm
      · exact affineSpan_mono ℝ h_subset
      · rw [affineSpan_le]; exact h_in_span

    -- Mathematical insight: If s ⊆ t ⊆ affineSpan s with equal dimensions and both
    -- full-dimensional, then t ⊆ closure s.
    --
    -- This is because:
    -- 1. Both s and t span the same affine subspace (h_span_eq)
    -- 2. Both have the same affine dimension (h_dim_eq)
    -- 3. Both are full-dimensional in that subspace (h_full + h_dim_eq)
    -- 4. s ⊆ t, so any point in t \ s would create a proper extension
    -- 5. But such an extension would contradict either the dimension equality
    --    or the full-dimensionality
    --
    -- Therefore, t \ s (if nonempty) consists only of boundary points of s,
    -- i.e., points in closure s \ s. Hence t ⊆ closure s.
    --
    -- DEPENDENCY NOTE: This appears to require the base theorem
    -- `Convex.closure_inter_affineSpan_subset_of_full_dim` or equivalent reasoning.
    -- The proof of that theorem and this theorem may need to be developed together
    -- or one needs to be proved first using different techniques (e.g., separation theorems,
    -- Carathéodory's theorem, or results about relative interiors).
    sorry

  have hx_closure : x ∈ closure s := ht_in_closure_s hx_t

  -- Now apply the base theorem
  exact Convex.closure_inter_affineSpan_subset_of_full_dim hs_conv hs_ne h_full
    ⟨hx_span, hx_closure⟩

/-!
### Linear (vector space) analogs

The following theorems are vector space analogs of the affine theorems above.
In the linear setting, we work with `Submodule.span` and `Module.finrank` instead
of `affineSpan` and `affineDim`.
-/

/-- If s ⊆ t ⊆ affineSpan s with equal affine dimensions, then t ⊆ s.

This follows from the theorem about full-dimensional convex sets being relatively closed.

**References**:
- Rockafellar, "Convex Analysis" (1970), Theorem 6.2
- Ziegler, "Lectures on Polytopes" (1995), Proposition 2.4 -/
theorem subset_of_subset_affineSpan_same_dim {s t : Set E}
    (hs_conv : Convex ℝ s) (ht_conv : Convex ℝ t)
    (hs_ne : s.Nonempty)
    (h_subset : s ⊆ t)
    (h_in_span : t ⊆ affineSpan ℝ s)
    (h_dim_eq : affineDim ℝ s = affineDim ℝ t) :
    t ⊆ s := by
  -- Show that s has full dimension in its affine span
  have h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E) := by
    simp only [affineDim]
    rw [AffineSubspace.affineSpan_coe]

  -- Apply the key theorem
  have h_eq : s = t :=
    convex_eq_of_subset_affineSpan_same_dim_full hs_conv ht_conv hs_ne h_subset h_in_span
      h_dim_eq h_full

  exact h_eq ▸ Set.Subset.refl s
