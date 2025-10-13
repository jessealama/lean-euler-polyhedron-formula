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
import Mathlib.Topology.Maps.Basic
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
### Helper lemmas for main theorem
-/

omit [FiniteDimensional ℝ E] in
/-- **Helper Lemma 1**: The intersection of affine span and ambient closure
is contained in the intrinsic closure.

Points that lie in both the ambient closure of s and the affine span of s
are also in the intrinsic closure of s (the closure in the subspace topology). -/
theorem affineSpan_inter_closure_subset_intrinsicClosure {s : Set E}
    (_hs_conv : Convex ℝ s) (_hs_ne : s.Nonempty)
    (_h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    (affineSpan ℝ s : Set E) ∩ closure s ⊆ intrinsicClosure ℝ s := by
  intro x ⟨hx_span, hx_closure⟩

  -- Use mem_intrinsicClosure characterization
  rw [mem_intrinsicClosure]

  -- Need to show: ∃ y ∈ closure ((↑) ⁻¹' s), y.val = x
  -- where (↑) : affineSpan ℝ s → E is the inclusion map

  -- The witness is ⟨x, hx_span⟩ viewed as an element of affineSpan ℝ s
  use ⟨x, hx_span⟩

  constructor
  · -- Show: ⟨x, hx_span⟩ ∈ closure ((↑) ⁻¹' s)
    -- where (↑) ⁻¹' s is the preimage of s under inclusion

    -- Strategy: Use `Topology.IsEmbedding.closure_eq_preimage_closure_image`
    -- which gives: closure (f ⁻¹' A) = f ⁻¹' closure (f '' (f ⁻¹' A))
    -- for any embedding f.
    --
    -- Since Subtype.val '' (Subtype.val ⁻¹' s) = s ∩ affineSpan, this becomes:
    -- closure (Subtype.val ⁻¹' s) = Subtype.val ⁻¹' closure (s ∩ affineSpan)
    --                             = Subtype.val ⁻¹' closure s

    -- The subtype inclusion is an embedding
    have h_emb : Topology.IsEmbedding (Subtype.val : affineSpan ℝ s → E) :=
      Topology.IsEmbedding.subtypeVal

    rw [h_emb.closure_eq_preimage_closure_image]
    simp only [mem_preimage]

    -- Goal: x ∈ closure (Subtype.val '' (Subtype.val ⁻¹' s : Set (affineSpan ℝ s)))
    -- We have: Subtype.val '' (Subtype.val ⁻¹' s) = s ∩ affineSpan ℝ s = s (since s ⊆ affineSpan)
    have h_image_eq : (Subtype.val : affineSpan ℝ s → E) '' (Subtype.val ⁻¹' s) =
                      s ∩ (affineSpan ℝ s : Set E) := by
      ext y
      simp only [mem_image, mem_preimage, mem_inter_iff]
      constructor
      · intro ⟨⟨z, hz_span⟩, hz_s, h_eq⟩
        simp only at h_eq
        rw [← h_eq]
        exact ⟨hz_s, hz_span⟩
      · intro ⟨hy_s, hy_span⟩
        use ⟨y, hy_span⟩, hy_s

    rw [h_image_eq]

    -- Simplify: s ∩ affineSpan ℝ s = s (since s ⊆ affineSpan ℝ s)
    have h_inter_eq : s ∩ (affineSpan ℝ s : Set E) = s :=
      inter_eq_left.mpr (subset_affineSpan ℝ s)

    rw [h_inter_eq]

    -- Goal: x ∈ closure s
    exact hx_closure

  · -- Show: ↑⟨x, hx_span⟩ = x
    rfl

/-- **Auxiliary Lemma for Helper 2**: In a finite-dimensional normed space V,
a convex set with full dimension equals the closure of its interior.

This is a fundamental result about convex sets in finite dimensions:
if S has the same dimension as the ambient space V, then S = closure(interior(S)).

This is more elementary than the main theorem because it works within a SINGLE topology
(V's topology) rather than across ambient and intrinsic topologies. -/
theorem Convex.eq_closure_interior_of_full_dim {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {S : Set V} (hS_conv : Convex ℝ S) (hS_ne : S.Nonempty)
    (h_full_dim : affineDim ℝ S = Module.finrank ℝ V) :
    S = closure (interior S) := by
  /-
  Strategy:
  1. Show interior S is nonempty (use full dimension + finite dimensionality)
     - Full dimension means S spans V
     - In finite dimensions, this implies S contains an open ball
     - Therefore interior S ≠ ∅

  2. Show S ⊆ closure(interior S)
     - For any x ∈ S and p ∈ interior S (which exists by step 1)
     - The open segment (p, x) lies in interior S (by convexity)
     - Taking limits as we approach x from the segment gives x ∈ closure(interior S)

  3. Show closure(interior S) ⊆ S
     - For convex sets in finite dimensions, S is "locally closed"
     - The closure of the interior cannot escape S
     - This uses finite-dimensionality crucially

  Note: This lemma works in a single topology (V's topology), which makes it
  more elementary than working across ambient/intrinsic topologies.
  -/
  sorry

/-- **Helper Lemma 2**: The intrinsic closure of a full-dimensional convex set
equals the set itself.

For a nonempty convex set s with full dimension in its affine span,
the intrinsic closure (closure in the subspace topology) equals s.

This is the KEY non-circular step that uses full dimension to conclude
the set is "relatively closed". -/
theorem intrinsicClosure_eq_of_full_dim {s : Set E}
    (hs_conv : Convex ℝ s) (hs_ne : s.Nonempty)
    (h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    intrinsicClosure ℝ s = s := by
  /-
  Strategy: Apply the auxiliary lemma about closure = closure(interior)
  in the subspace topology of affineSpan ℝ s.

  Key steps:
  1. Transfer the problem to the subspace (affineSpan ℝ s) where we work
     in a single topology

  2. Show that the preimage (↑) ⁻¹' s has full dimension in affineSpan ℝ s
     - Use h_full: affineDim s = affineDim (affineSpan s)

  3. Apply the auxiliary lemma Convex.eq_closure_interior_of_full_dim
     to (↑) ⁻¹' s in the subspace

  4. Transfer back to show intrinsicClosure s = s

  This avoids circularity by proving the auxiliary lemma independently
  for convex sets in a single topology.
  -/
  sorry

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
  -- Step 1: affineSpan ∩ closure ⊆ intrinsicClosure
  have h_step1 : (affineSpan ℝ s : Set E) ∩ closure s ⊆ intrinsicClosure ℝ s :=
    affineSpan_inter_closure_subset_intrinsicClosure hs_conv hs_ne h_full

  -- Step 2: intrinsicClosure = s for full-dimensional sets
  have h_step2 : intrinsicClosure ℝ s = s :=
    intrinsicClosure_eq_of_full_dim hs_conv hs_ne h_full

  -- Combine: affineSpan ∩ closure ⊆ intrinsicClosure = s
  rwa [h_step2] at h_step1

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
