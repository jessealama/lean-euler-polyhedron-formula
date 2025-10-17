/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import ConvexPolyhedra.Rockafellar.Chapter01.Theorem16

/-!
# Rockafellar's Corollary 1.6.1

This file contains Rockafellar's Corollary 1.6.1 from "Convex Analysis" (1970), which states that
affine sets of the same dimension are related by affine automorphisms of the ambient space.

## Main results

* `affineSubspace_automorphism_of_same_dim` - Rockafellar's Corollary 1.6.1:
  Affine sets of equal dimension can be mapped by an affine automorphism

## References

* Rockafellar, "Convex Analysis" (1970), Corollary 1.6.1

## Tags

affine, affine subspace, affine dimension, affine transformation
-/

open Set AffineSubspace
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Rockafellar's Corollary 1.6.1**: Affine sets of the same dimension are related by
an affine automorphism of the ambient space.

Let M₁ and M₂ be any two affine sets in E of the same dimension. Then there exists
a one-to-one affine transformation T : E → E such that T(M₁) = M₂.

This follows from Theorem 1.6 since any m-dimensional affine set can be expressed as the
affine hull of an affinely independent set of m + 1 points. -/
theorem affineSubspace_automorphism_of_same_dim (A B : AffineSubspace ℝ E)
    [Nonempty A] [Nonempty B]
    (h_dim : Module.finrank ℝ A.direction = Module.finrank ℝ B.direction) :
    ∃ (T : E ≃ᵃ[ℝ] E), T '' (A : Set E) = (B : Set E) := by
  sorry
