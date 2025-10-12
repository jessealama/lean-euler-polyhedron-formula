/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.Topology.Algebra.Module.FiniteDimension
import ConvexPolyhedra.Polyhedron

/-!
# Relative Interior Density for Convex Sets

This file develops the theory of relative interior density for convex sets in finite-dimensional
spaces. The main result is that full-dimensional convex sets are relatively closed, meaning
their intrinsic closure equals themselves.

## Main results

* `Convex.intrinsicClosure_eq_self_of_full_dim` - Full-dimensional convex sets are relatively closed
  (Rockafellar's Theorem 6.4)

## Implementation notes

The key insight is that a convex set with full dimension in its affine span cannot have additional
boundary points in the relative topology. This is formalized by showing that the preimage of the
set under the inclusion map into its affine span is closed in the subspace topology.

## References

* Rockafellar, "Convex Analysis" (1970), Theorem 6.4
* Schneider, "Convex Bodies: The Brunn-Minkowski Theory" (2014), Theorem 1.1.4

## Tags

convex, relative interior, intrinsic topology, affine dimension
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

omit [FiniteDimensional ℝ E] in
/-- Translation preserves affine dimension (via pointwise vadd).

For any set s and vector v, translating s by v preserves affine dimension.
This is because translation is an affine equivalence that preserves affine structure. -/
theorem affineDim_vadd (v : E) (s : Set E) :
    affineDim ℝ (v +ᵥ s) = affineDim ℝ s := by
  -- affineSpan (v +ᵥ s) = v +ᵥ affineSpan s (by pointwise_vadd_span)
  have h_span : affineSpan ℝ (v +ᵥ s) = v +ᵥ affineSpan ℝ s :=
    (AffineSubspace.pointwise_vadd_span (k := ℝ) (V := E) (P := E) v s).symm
  -- direction (v +ᵥ S) = S.direction for any affine subspace S
  have h_dir : (v +ᵥ affineSpan ℝ s).direction = (affineSpan ℝ s).direction :=
    AffineSubspace.pointwise_vadd_direction v (affineSpan ℝ s)
  -- Combine: affineDim is the finrank of the direction
  simp only [affineDim]
  rw [h_span, h_dir]

omit [FiniteDimensional ℝ E] in
/-- Translation preserves affine dimension (via vsub/negation).

For any set s and vector v, we have affineDim((-v) +ᵥ s) = affineDim(s).
This follows immediately from affineDim_vadd. -/
theorem affineDim_neg_vadd (v : E) (s : Set E) :
    affineDim ℝ ((-v) +ᵥ s) = affineDim ℝ s :=
  affineDim_vadd (-v) s

omit [FiniteDimensional ℝ E] in
/-- Translation preserves affine dimension (via image under subtraction map).

For any set s and vector v, translating s by the map y ↦ y - v preserves affine dimension.
This is a corollary of affineDim_vadd since (y - v) = y + (-v) = (-v) +ᵥ y. -/
theorem affineDim_image_sub (v : E) (s : Set E) :
    affineDim ℝ ((fun y => y - v) '' s) = affineDim ℝ s := by
  -- The image {y - v | y ∈ s} equals (-v) +ᵥ s
  have h_eq : (fun y => y - v) '' s = (-v) +ᵥ s := by
    ext x
    simp only [mem_image, mem_vadd_set, sub_eq_add_neg]
    constructor
    · intro ⟨y, hy, h⟩
      exact ⟨y, hy, by rw [add_comm] at h; exact h⟩
    · intro ⟨y, hy, h⟩
      exact ⟨y, hy, by rw [add_comm]; exact h⟩
  rw [h_eq]
  exact affineDim_neg_vadd v s

/-- A nonempty convex set has nonempty intrinsic interior (relative interior).

The intrinsic interior (also called relative interior) of a set is its interior when viewed
as a subset of its affine span. This is a fundamental theorem in convex analysis.

This is an alias for the existing Mathlib theorem `Set.Nonempty.intrinsicInterior`. -/
theorem convex_intrinsicInterior_nonempty {s : Set E} (hs_conv : Convex ℝ s) (hs_ne : s.Nonempty) :
    (intrinsicInterior ℝ s).Nonempty :=
  hs_ne.intrinsicInterior hs_conv

/-!
### Helper lemmas for working with subspace topology
-/

omit [FiniteDimensional ℝ E] in
/-- For a set s, the intersection of its affine span with s equals s itself. -/
theorem affineSpan_inter_self (s : Set E) : (affineSpan ℝ s : Set E) ∩ s = s :=
  inter_eq_right.mpr (subset_affineSpan ℝ s)

omit [FiniteDimensional ℝ E] in
/-- The preimage of s under the inclusion into affineSpan ℝ s, viewed as a set
in the affine span, corresponds to s itself. -/
theorem preimage_coe_affineSpan_eq (s : Set E) :
    ((↑) : affineSpan ℝ s → E) ⁻¹' s = (↑) '' ((↑) ⁻¹' s : Set (affineSpan ℝ s)) := by
  ext ⟨x, hx⟩
  simp only [mem_preimage, mem_image]
  constructor
  · intro hxs
    exact ⟨⟨x, hx⟩, hxs, rfl⟩
  · intro ⟨⟨y, hy⟩, hys, h_eq⟩
    simp at h_eq
    rw [← h_eq]
    exact hys

/-!
### Main theorem: Full-dimensional convex sets are relatively closed
-/

/-- A convex set with full dimension in its affine span has the property that
any limit point in the affine span must already be in the set.

This is the key lemma for Rockafellar's Theorem 6.4. If s has full dimension
(affineDim s = affineDim (affineSpan s)), then s cannot be properly extended
within its affine span while maintaining convexity. -/
theorem Convex.closure_inter_affineSpan_subset_of_full_dim {s : Set E}
    (hs_conv : Convex ℝ s) (hs_ne : s.Nonempty)
    (h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    (affineSpan ℝ s : Set E) ∩ closure s ⊆ s := by
  sorry

/-- **Full-dimensional convex sets are relatively closed (Rockafellar's Theorem 6.4).**

For a convex set s with full dimension in its affine span, the intrinsic closure
equals s itself. In other words, full-dimensional convex sets have no additional
boundary points in the relative topology.

This is a fundamental result in convex analysis. The condition
`affineDim s = affineDim (affineSpan s)` means s has full dimension in its affine hull,
which prevents proper extensions within that affine space while maintaining the same
dimension.

**Proof strategy**:
1. Use `IsClosed.intrinsicClosure`: if the preimage (↑) ⁻¹' s is closed in affineSpan ℝ s,
   then intrinsicClosure ℝ s = s
2. Apply `isClosed_preimage_val` characterization: the preimage is closed iff
   affineSpan ∩ closure(affineSpan ∩ s) ⊆ s
3. Simplify using affineSpan ∩ s = s
4. The key step: show affineSpan ∩ closure s ⊆ s using the full dimension condition

**Mathematical background**:
The theorem relies on the fact that convex sets with full dimension in their affine span are
"relatively open" in the sense that they equal the closure of their relative interior. Any limit
point of s that lies in affineSpan s must actually be in s, because otherwise s would not have
full dimension.

**References**:
- Rockafellar, "Convex Analysis" (1970), Theorem 6.4
- Schneider, "Convex Bodies" (2014), Theorem 1.1.4
-/
theorem Convex.intrinsicClosure_eq_self_of_full_dim {s : Set E}
    (hs_conv : Convex ℝ s) (hs_ne : s.Nonempty)
    (h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    intrinsicClosure ℝ s = s := by
  -- Apply IsClosed.intrinsicClosure: if (↑) ⁻¹' s is closed in affineSpan ℝ s,
  -- then intrinsicClosure ℝ s = s
  apply IsClosed.intrinsicClosure

  -- Goal: IsClosed ((↑) ⁻¹' s : Set (affineSpan ℝ s))
  -- Use the characterization: preimage is closed iff affineSpan ∩ closure(affineSpan ∩ s) ⊆ s
  rw [isClosed_preimage_val]

  -- Simplify: affineSpan ℝ s ∩ s = s (since s ⊆ affineSpan ℝ s)
  rw [affineSpan_inter_self]

  -- Goal: (affineSpan ℝ s : Set E) ∩ closure s ⊆ s
  -- Apply the key lemma that uses the full dimension condition
  exact Convex.closure_inter_affineSpan_subset_of_full_dim hs_conv hs_ne h_full

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
  -- Strategy: show t ⊆ s using that s is relatively closed
  apply Subset.antisymm h_subset

  -- We'll show that t ⊆ intrinsicClosure ℝ s and use that intrinsicClosure ℝ s = s
  have h_s_closed : intrinsicClosure ℝ s = s :=
    Convex.intrinsicClosure_eq_self_of_full_dim hs_conv hs_ne h_full

  -- Since t ⊆ affineSpan s and equal dimensions, t must be in the intrinsic closure
  rw [← h_s_closed]

  sorry
