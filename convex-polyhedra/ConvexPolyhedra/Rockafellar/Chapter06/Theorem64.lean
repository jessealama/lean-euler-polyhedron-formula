/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import ConvexPolyhedra.Rockafellar.Chapter06.Theorem61

/-!
# Rockafellar's Theorem 6.4

This file contains Rockafellar's Theorem 6.4 from "Convex Analysis" (1970), which characterizes
relative interior points via line segment extensions.

## Main results

* `mem_intrinsicInterior_iff_extension` - Theorem 6.4: Characterization of relative interior
  points via line segment extensions

## Infrastructure

* `affineSubspace_translation_homeomorph` - Translation homeomorphism for affine-to-vector transfer

## References

* Rockafellar, "Convex Analysis" (1970), Theorem 6.4

## Tags

convex, relative interior, line segment extension
-/

open Set AffineSubspace
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
### Infrastructure for affine-to-vector transfer
-/

omit [FiniteDimensional ℝ E] in
/-- Translation homeomorphism for affine subspaces: the map φ(p) = p -ᵥ p₀ is a
homeomorphism from A to A.direction. -/
theorem affineSubspace_translation_homeomorph (A : AffineSubspace ℝ E)
    [Nonempty A]
    (p₀ : A) :
    ∃ (f : A ≃ₜ A.direction), ∀ p : A, f p = (p : E) -ᵥ (p₀ : E) := by
  -- Use Homeomorph.vaddConst which gives v ↦ v +ᵥ p₀ : A.direction → A
  -- Its inverse gives p ↦ p -ᵥ p₀ : A → A.direction, which is what we want
  use (Homeomorph.vaddConst p₀).symm

  intro p
  -- Goal: ↑((Homeomorph.vaddConst p₀).symm p) = ↑p -ᵥ ↑p₀
  -- Use Homeomorph.vaddConst_symm_apply: (vaddConst p₀).symm p' = p' -ᵥ p₀
  rw [Homeomorph.vaddConst_symm_apply]
  -- Now goal is: ↑(p -ᵥ p₀) = ↑p -ᵥ ↑p₀
  -- This is exactly AffineSubspace.coe_vsub (which is rfl)
  rfl

/-- The direction of an affine subspace has AddCommGroup structure.

This is automatic from Mathlib - the direction is a Submodule, which has AddCommGroup.
This is what allows us to apply `Convex.combo_interior_closure_mem_interior` after
transferring to the direction space. -/
instance (A : AffineSubspace ℝ E) : AddCommGroup A.direction :=
  inferInstance

/-!
### Rockafellar's Theorem 6.4
-/

/-- **Rockafellar's Theorem 6.4**: A point z is in the relative interior of a nonempty convex
set C iff every line segment from any x ∈ C to z can be extended slightly beyond z while
remaining in C.

Formally: z ∈ ri C ⟺ (∀ x ∈ C, ∃ μ > 1, (1 - μ)x + μz ∈ C) -/
theorem mem_intrinsicInterior_iff_extension
    {s : Set E} (hs : Convex ℝ s) (hs_ne : s.Nonempty) {z : E} :
    z ∈ intrinsicInterior ℝ s ↔
    ∀ x ∈ s, ∃ (μ : ℝ), μ > 1 ∧ (1 - μ) • x + μ • z ∈ s := by
  constructor

  · -- (⇒) Forward direction: z ∈ ri s → extension property
    intro hz x hx
    rw [mem_intrinsicInterior] at hz
    obtain ⟨⟨z_pt, hz_span⟩, hz_interior, rfl⟩ := hz
    haveI : Nonempty (affineSpan ℝ s) := ⟨⟨z_pt, hz_span⟩⟩
    sorry

  · -- (⇐) Backward direction: extension property → z ∈ ri s
    intro h_ext
    have h_ri_ne : (intrinsicInterior ℝ s).Nonempty := hs_ne.intrinsicInterior hs
    obtain ⟨x, hx⟩ := h_ri_ne
    have hx_in_s : x ∈ s := intrinsicInterior_subset hx
    obtain ⟨μ, ⟨hμ_gt_1, hy⟩⟩ := h_ext x hx_in_s

    -- Express z as a convex combination of x ∈ ri s and a point in s
    have h_z : z = (1 - 1/μ)•x + (1/μ)•((1 - μ)•x + μ•z) := by
      have hμ_ne : μ ≠ 0 := by linarith
      have h1 : (1 : ℝ) / μ * μ = 1 := by field_simp
      calc z
          = (0 : ℝ)•x + z := by rw [zero_smul, zero_add]
        _ = ((1 : ℝ) - 1/μ + (1 - μ)/μ)•x + z := by
            rw [show (0 : ℝ) = (1 : ℝ) - 1/μ + (1 - μ)/μ by field_simp; ring]
        _ = ((1 : ℝ) - 1/μ)•x + ((1 - μ)/μ)•x + z := by rw [add_smul, add_assoc]
        _ = ((1 : ℝ) - 1/μ)•x + (((1 : ℝ)/μ) * (1 - μ))•x + ((1 : ℝ)/μ * μ)•z := by
            rw [show (1 - μ) / μ = ((1 : ℝ) / μ) * (1 - μ) by field_simp]; rw [h1, one_smul]
        _ = ((1 : ℝ) - 1/μ)•x + ((1/μ)•(1 - μ)•x + (1/μ)•μ•z) := by rw [mul_smul, mul_smul]; ac_rfl
        _ = ((1 : ℝ) - 1/μ)•x + (1/μ)•((1 - μ)•x + μ•z) := by rw [← smul_add]

    -- The key insight: We need to show z ∈ intrinsicInterior s
    -- by expressing it as a convex combination of x ∈ intrinsicInterior s
    -- and a point in s (hence in intrinsicClosure s)
    have h_comb : (1 - 1/μ) + (1/μ) = (1 : ℝ) := by
      field_simp; linarith
    have hμ_pos : (0 : ℝ) < μ := by linarith
    have h_nonneg_1m1mu : (0 : ℝ) ≤ (1 : ℝ) - 1/μ := by
      field_simp; linarith
    have h_nonneg_1mu : (0 : ℝ) ≤ 1/μ := by
      exact one_div_nonneg.mpr (le_of_lt hμ_pos)
    have h_lt_1mu : 1/μ < (1 : ℝ) := by
      field_simp; linarith
    -- Now apply Theorem 6.1: since x ∈ intrinsicInterior s and
    -- ((1 - μ)•x + μ•z) ∈ s, we have z ∈ intrinsicInterior s
    have hy_in_closure : (1 - μ) • x + μ • z ∈ intrinsicClosure ℝ s :=
      (subset_intrinsicClosure : s ⊆ intrinsicClosure ℝ s) hy
    rw [h_z]
    exact Convex.combo_intrinsicInterior_intrinsicClosure_mem_intrinsicInterior (t := 1/μ)
      hs hx hy_in_closure h_nonneg_1mu h_lt_1mu
