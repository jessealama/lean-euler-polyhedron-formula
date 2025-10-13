/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Rockafellar's Reduction to Full-Dimensional Case

This file formalizes Rockafellar's proof technique from "Convex Analysis" (1970), Section 6,
pages 44-45. The key observation is that properties of convex sets that are preserved under
affine equivalences can be reduced to the case where the set has full dimension in its
ambient space.

## Main results

* `convex_property_by_reduction_to_full_dim` - General reduction theorem
* `AffineEquiv.map_affineSpan` - Affine equivalences preserve affine spans
* `AffineEquiv.image_intrinsicInterior` - Affine equivalences preserve relative interiors
* `AffineEquiv.image_intrinsicClosure` - Affine equivalences preserve relative closures

## References

* Rockafellar, "Convex Analysis" (1970), Section 6, pages 44-45

## Tags

convex, affine equivalence, reduction technique, full dimensional
-/

open Set AffineSubspace

variable {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

/-!
### Affine equivalences preserve structure
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
### Rockafellar's Reduction Technique
-/

/-- **Rockafellar's Reduction to Full-Dimensional Case (Theorem Form)**

This is the formalization of Rockafellar's observation from pages 44-45:

> "It is often possible in this manner to reduce a question about general convex sets
> to the case where the convex set is of full dimension, i.e. has the whole space as
> its affine hull."

The theorem states: **To prove a property P of convex sets, it suffices to:**
1. Show P is preserved under affine equivalences
2. Prove P for all full-dimensional convex sets

**Why this works:**
- For any m-dimensional convex set C in ℝⁿ, there exists an affine equivalence T
  mapping aff(C) to a coordinate subspace L ≅ ℝᵐ
- In L, the set T(C) is full-dimensional
- Apply the full-dimensional case to T(C)
- Transfer back using T⁻¹

**Key insight:** In the full-dimensional case, relative interior = ordinary interior,
which often makes proofs much simpler.

**Usage pattern:** When proving a property of convex sets:
```lean
theorem my_property (C : Set E) (hC : Convex ℝ C) : P C := by
  apply convex_property_by_reduction_to_full_dim
  · -- Show P is preserved under affine equivalences
    intro E₁ E₂ _ _ _ _ _ _ φ s hs
    sorry
  · -- Prove P for full-dimensional case
    intro E _ _ _ s hs h_full
    -- Here we have: affineDim s = Module.finrank ℝ E
    -- So intrinsicInterior s = interior s (much simpler!)
    sorry
```
-/
theorem convex_property_by_reduction_to_full_dim
    {P : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E], Set E → Prop}
    -- (1) P is preserved under affine equivalences
    (h_affine_equiv : ∀ {E₁ E₂ : Type*}
                       [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
                       [FiniteDimensional ℝ E₁]
                       [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
                       [FiniteDimensional ℝ E₂]
                       (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁),
                     P s → P (φ '' s))
    -- (2) P holds for all full-dimensional convex sets
    (h_full_dim : ∀ {E : Type*}
                    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
                    [FiniteDimensional ℝ E] (s : Set E),
                  Convex ℝ s →
                  affineDim ℝ s = Module.finrank ℝ E →
                  P s)
    -- Then P holds for all convex sets
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (C : Set E)
    (hC : Convex ℝ C) :
    P C := by
  /-
  Proof strategy:

  Case 1: C is already full-dimensional
    Apply h_full_dim directly

  Case 2: C has dimension m < n (where n = dim E)
    Step 1: Construct affine equivalence T : E → E such that
            T(aff C) = coordinate subspace L ≅ ℝᵐ
            (This exists by Mathlib's AffineSubspace theory)

    Step 2: Consider T(C) ⊆ L
            Show T(C) is full-dimensional in L

    Step 3: Regard L as a copy of ℝᵐ
            Apply h_full_dim to T(C) in this space

    Step 4: Transfer result back to C using T⁻¹ and h_affine_equiv

  The key technical work is in Step 1 (finding T) and Step 3 (the
  type-theoretic gymnastics of working in the subspace L).
  -/
  sorry

/-!
### Specialized Versions for Common Properties
-/

/-- **Reduction for properties depending on only affine dimension**

Many properties of convex sets depend only on their intrinsic structure
(relative interior, relative closure, affine dimension) rather than the
embedding. For such properties, we can state a cleaner version. -/
theorem convex_property_by_reduction_to_full_dim_intrinsic
    {P : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E], Set E → Prop}
    -- P depends only on intrinsic structure (preserved by affine equivalence)
    (h_intrinsic : ∀ {E₁ E₂ : Type*}
                     [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
                     [FiniteDimensional ℝ E₁]
                     [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
                     [FiniteDimensional ℝ E₂]
                     (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁),
                   P s ↔ P (φ '' s))
    -- P holds for full-dimensional convex sets
    (h_full_dim : ∀ {E : Type*}
                    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
                    [FiniteDimensional ℝ E] (s : Set E),
                  Convex ℝ s →
                  affineDim ℝ s = Module.finrank ℝ E →
                  P s)
    -- Then P holds for all convex sets
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (C : Set E)
    (hC : Convex ℝ C) :
    P C := by
  apply convex_property_by_reduction_to_full_dim
  · intro E₁ E₂ _ _ _ _ _ _ φ s hs
    exact (h_intrinsic φ s).mp hs
  · exact h_full_dim

/-!
### Helper: Full-dimensional sets have simpler topology
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

/-- In a full-dimensional convex set, the relative closure equals the ordinary closure.

This is another key simplification. -/
theorem intrinsicClosure_eq_closure_of_full_dim
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) (h_full : affineDim ℝ s = Module.finrank ℝ E) :
    intrinsicClosure ℝ s = closure s := by
  sorry

/-!
### Example Application: Theorem 6.1

Rockafellar uses this technique in his proof of Theorem 6.1:

> "In view of the preceding remark, we can limit attention to the
> case where C is n-dimensional, so that ri C = int C."

Here's how to formalize this usage:
-/

-- This is a sketch of how Rockafellar's Theorem 6.1 would use the reduction
example (sketch_theorem_6_1 : True) : True := by
  /-
  To prove: For convex C, if x ∈ ri C and y ∈ cl C, then
            (1-λ)x + λy ∈ ri C for all λ ∈ [0, 1)

  Proof by reduction:
  -/
  have h_reduction : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
                       [FiniteDimensional ℝ E] (C : Set E) (hC : Convex ℝ C),
      (∀ x ∈ intrinsicInterior ℝ C, ∀ y ∈ intrinsicClosure ℝ C,
       ∀ λ : ℝ, 0 ≤ λ → λ < 1 → (1 - λ) • x + λ • y ∈ intrinsicInterior ℝ C) := by
    intro E _ _ _ C hC

    -- Apply reduction theorem
    apply convex_property_by_reduction_to_full_dim

    -- (1) Property is preserved under affine equivalences
    · intro E₁ E₂ _ _ _ _ _ _ φ s
      -- This follows from AffineEquiv.image_intrinsicInterior
      sorry

    -- (2) Prove for full-dimensional case
    · intro E _ _ _ s hs h_full
      intro x hx y hy λ hλ0 hλ1

      -- KEY SIMPLIFICATION: Since s is full-dimensional,
      -- intrinsicInterior s = interior s
      -- intrinsicClosure s = closure s
      rw [intrinsicInterior_eq_interior_of_full_dim hs h_full] at hx ⊢
      rw [intrinsicClosure_eq_closure_of_full_dim hs h_full] at hy

      -- Now use the simpler ambient version
      -- (which should already be in Mathlib as Convex.combo_interior_closure_mem_interior)
      sorry

  trivial

/-!
## Notes

This reduction technique is used throughout convex analysis whenever a proof
becomes significantly simpler in the full-dimensional case. The formalization
captures Rockafellar's methodological observation as a reusable theorem.

The key insight is that relative topology (intrinsic interior/closure) becomes
ordinary topology when working in the full-dimensional case, allowing us to
apply simpler theorems about ordinary interiors and closures.
-/
