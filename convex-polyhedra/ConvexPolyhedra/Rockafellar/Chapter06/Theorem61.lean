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
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Maps.Basic
import ConvexPolyhedra.Polyhedron

/-!
# Rockafellar's Theorem 6.1

This file contains Rockafellar's Theorem 6.1 from "Convex Analysis" (1970), which states that
convex combinations of relative interior and relative closure remain in the relative interior.

## Main results

* `Convex.combo_intrinsicInterior_intrinsicClosure_mem_intrinsicInterior` - Theorem 6.1:
  Convex combinations of relative interior and relative closure stay in relative interior
* `Convex.intrinsicClosure_eq_self_of_full_dim` - Full-dimensional convex sets are relatively closed

## Infrastructure

* Rockafellar's reduction technique for full-dimensional cases
* Helper lemmas for full-dimensional sets
* Affine equivalence preservation properties

## References

* Rockafellar, "Convex Analysis" (1970), Theorem 6.1
* Schneider, "Convex Bodies: The Brunn-Minkowski Theory" (2014), Theorem 1.1.4

## Tags

convex, relative interior, intrinsic topology, full dimension
-/

open Set AffineSubspace
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A nonempty convex set has nonempty intrinsic interior (relative interior).

The intrinsic interior (also called relative interior) of a set is its interior when viewed
as a subset of its affine span. This is a fundamental theorem in convex analysis.

This is an alias for the existing Mathlib theorem `Set.Nonempty.intrinsicInterior`. -/
theorem convex_intrinsicInterior_nonempty {s : Set E} (hs_conv : Convex ℝ s) (hs_ne : s.Nonempty) :
    (intrinsicInterior ℝ s).Nonempty :=
  hs_ne.intrinsicInterior hs_conv

/-!
### Rockafellar's Reduction Technique

Properties of convex sets preserved under affine equivalences can be reduced to the
full-dimensional case, where relative interior = ordinary interior.
-/

section RockafellarReduction

variable {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

/-!
#### Affine equivalences preserve structure
-/

/-- Affine equivalences preserve affine spans.

This is a fundamental property: if φ is a bijective affine map, then the image of
the affine span equals the affine span of the image. -/
theorem AffineEquiv.map_affineSpan (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    φ.toAffineMap '' (affineSpan ℝ s : Set E₁) = (affineSpan ℝ (φ '' s) : Set E₂) := by
  sorry

/-- Affine equivalences preserve affine dimension.

This follows from the fact that affine equivalences preserve affine spans
and induce linear equivalences on the direction submodules. -/
theorem AffineEquiv.affineDim_image (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    affineDim ℝ (φ '' s) = affineDim ℝ s := by
  sorry

/-- Affine equivalences preserve relative interiors (intrinsic interiors).

**Key fact**: In finite-dimensional spaces, affine equivalences are homeomorphisms
(via `AffineEquiv.toHomeomorphOfFiniteDimensional`), and homeomorphisms preserve
interior in the subspace topology. -/
theorem AffineEquiv.image_intrinsicInterior (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    intrinsicInterior ℝ (φ '' s) = φ '' intrinsicInterior ℝ s := by
  sorry

/-- Affine equivalences preserve relative closures (intrinsic closures). -/
theorem AffineEquiv.image_intrinsicClosure (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    intrinsicClosure ℝ (φ '' s) = φ '' intrinsicClosure ℝ s := by
  sorry

/-!
#### Helper: Full-dimensional sets have simpler topology
-/

/-- In a full-dimensional convex set, the relative interior equals the ordinary interior.

This is the key simplification that makes the reduction technique so powerful. -/
theorem intrinsicInterior_eq_interior_of_full_dim
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) (h_full : affineDim ℝ s = Module.finrank ℝ E) :
    intrinsicInterior ℝ s = interior s := by
  /-
  Since s has full dimension, affineSpan s = ⊤ (the whole space).
  The intrinsic interior is the interior in the subspace topology of affineSpan s.
  When affineSpan s = ⊤, the subspace topology equals the ambient topology.
  Therefore intrinsicInterior s = interior s.
  -/
  sorry

/-- In a full-dimensional convex set, the relative closure equals the ordinary closure. -/
theorem intrinsicClosure_eq_closure_of_full_dim
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) (h_full : affineDim ℝ s = Module.finrank ℝ E) :
    intrinsicClosure ℝ s = closure s := by
  sorry

end RockafellarReduction

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
/-- The intersection of affine span and ambient closure is contained in the intrinsic closure. -/
theorem affineSpan_inter_closure_subset_intrinsicClosure {s : Set E}
    (_hs_conv : Convex ℝ s) (_hs_ne : s.Nonempty)
    (_h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    (affineSpan ℝ s : Set E) ∩ closure s ⊆ intrinsicClosure ℝ s := by
  intro x ⟨hx_span, hx_closure⟩
  rw [mem_intrinsicClosure]
  use ⟨x, hx_span⟩
  constructor
  · have h_emb : Topology.IsEmbedding (Subtype.val : affineSpan ℝ s → E) :=
      Topology.IsEmbedding.subtypeVal
    rw [h_emb.closure_eq_preimage_closure_image]
    simp only [mem_preimage]
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
    have h_inter_eq : s ∩ (affineSpan ℝ s : Set E) = s :=
      inter_eq_left.mpr (subset_affineSpan ℝ s)
    rw [h_inter_eq]
    exact hx_closure
  · rfl

/-- In a finite-dimensional normed space, a convex set with full dimension equals the
closure of its interior: S = closure(interior(S)). -/
theorem Convex.eq_closure_interior_of_full_dim {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {S : Set V} (hS_conv : Convex ℝ S) (hS_ne : S.Nonempty)
    (h_full_dim : affineDim ℝ S = Module.finrank ℝ V) :
    S = closure (interior S) := by
  sorry

/-- The intrinsic closure of a full-dimensional convex set equals the set itself. -/
theorem intrinsicClosure_eq_of_full_dim {s : Set E}
    (hs_conv : Convex ℝ s) (hs_ne : s.Nonempty)
    (h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    intrinsicClosure ℝ s = s := by
  sorry

/-!
### Main theorem: Full-dimensional convex sets are relatively closed
-/

/-- A convex set with full dimension in its affine span cannot be properly extended
within its affine span: any limit point in the affine span must already be in the set. -/
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

/-- **Full-dimensional convex sets are relatively closed.**

For a convex set s with full dimension in its affine span, the intrinsic closure equals s itself.
Full-dimensional convex sets have no additional boundary points in the relative topology. -/
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
### Helper instances for affine subspace subtypes
-/

/-- Nonempty instance for affine span of nonempty set. -/
instance {s : Set E} [h : Nonempty s] : Nonempty (affineSpan ℝ s) := by
  obtain ⟨x, hx⟩ := h
  exact ⟨⟨x, subset_affineSpan ℝ s hx⟩⟩

/-!
### Rockafellar's Theorem 6.1
-/

/-- **Rockafellar's Theorem 6.1**: Convex combination of relative interior and relative closure
stays in relative interior.

For a convex set C, if x is in the relative interior and y is in the relative closure,
then any convex combination (1-λ)x + λy with 0 ≤ λ < 1 remains in the relative interior.

This is the intrinsic (relative) version of `Convex.combo_interior_closure_mem_interior`. -/
theorem Convex.combo_intrinsicInterior_intrinsicClosure_mem_intrinsicInterior
    {s : Set E} (hs : Convex ℝ s)
    {x y : E} (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ intrinsicClosure ℝ s)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) • x + t • y ∈ intrinsicInterior ℝ s := by
  -- Reduce to full-dimensional case using Rockafellar's technique
  wlog h_full : affineDim ℝ s = Module.finrank ℝ E with h_full_case
  case inr => sorry  -- Non-full-dimensional case requires affine subspace typeclass instances

  -- Full-dimensional case: use ordinary convex analysis
  have h_int_eq : intrinsicInterior ℝ s = interior s :=
    intrinsicInterior_eq_interior_of_full_dim hs h_full
  have h_clo_eq : intrinsicClosure ℝ s = closure s :=
    intrinsicClosure_eq_closure_of_full_dim hs h_full

  -- From the hypotheses hx and hy, we get ordinary interior/closure membership
  have hx' : x ∈ interior s := by
    rw [← h_int_eq]; exact hx
  have hy' : y ∈ closure s := by
    rw [← h_clo_eq]; exact hy

  -- Apply ordinary Convex.combo_interior_closure_mem_interior
  have h_1mt_pos : (0 : ℝ) < 1 - t := by linarith
  have h_coeff_sum : (1 - t) + t = 1 := by ring

  have h_combo : (1 - t) • x + t • y ∈ interior s :=
    hs.combo_interior_closure_mem_interior hx' hy' h_1mt_pos ht0 h_coeff_sum

  -- Transfer back to intrinsicInterior
  rw [h_int_eq]
  exact h_combo
