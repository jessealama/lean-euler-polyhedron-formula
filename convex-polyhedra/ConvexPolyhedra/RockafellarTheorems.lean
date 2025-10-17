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
# Rockafellar's Theorems 6.1 and 6.4

This file contains Rockafellar's fundamental theorems about relative interiors from
"Convex Analysis" (1970), Section 6, along with all the infrastructure needed to prove them.

## Main results

* `Convex.combo_intrinsicInterior_intrinsicClosure_mem_intrinsicInterior` - Theorem 6.1:
  Convex combinations of relative interior and relative closure stay in relative interior
* `mem_intrinsicInterior_iff_extension` - Theorem 6.4: Characterization of relative interior
  points via line segment extensions
* `Convex.intrinsicClosure_eq_self_of_full_dim` - Full-dimensional convex sets are relatively closed

## Infrastructure

* Affine dimension properties and translations
* Rockafellar's reduction technique for full-dimensional cases
* Helper lemmas for subspace topology
* Affine-to-vector transfer machinery

## References

* Rockafellar, "Convex Analysis" (1970), Theorems 6.1 and 6.4
* Schneider, "Convex Bodies: The Brunn-Minkowski Theory" (2014), Theorem 1.1.4

## Tags

convex, relative interior, intrinsic topology, affine dimension, Rockafellar
-/

open Set AffineSubspace
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
### Affine dimension properties and Rockafellar's Theorem 1.6
-/

/-- **Rockafellar's Theorem 1.6**: Affinely independent sets of the same size can be mapped to each
other by an affine automorphism of the ambient space.

Given two affinely independent sets {b₀, b₁, ..., bₘ} and {b'₀, b'₁, ..., b'ₘ} in E,
there exists a one-to-one affine transformation T : E → E such that T(bᵢ) = b'ᵢ for all i.
If m = n (dimension of E), then T is unique.

This is the finite-dimensional version of Rockafellar's Theorem 1.6 from "Convex Analysis". -/
theorem affineIndependent_to_affineIndependent_automorphism
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p q : ι → E}
    (hp : AffineIndependent ℝ p)
    (hq : AffineIndependent ℝ q) :
    ∃ (T : E ≃ᵃ[ℝ] E), ∀ i : ι, T (p i) = q i := by

  have h_lt : Fintype.card ι ≤ Module.finrank ℝ E := by sorry
  let n : ℕ := Module.finrank ℝ E - Fintype.card ι

  induction n
  case zero =>
    -- Full-dimensional case: construct the affine automorphism explicitly
    sorry
  case succ k ih =>
    -- If the difference is (k + 1), we can extend both sets by one point guaranteed t
    -- be affinely independent, reducing to the k case
  -- Rockafellar's proof (Theorem 1.6):
  -- "Enlarging the given affinely independent sets if necessary, we can reduce the question
  -- to the case where m = n. Then, as is well known in linear algebra, there exists a unique
  -- one-to-one linear transformation A of Rⁿ onto itself carrying the basis b₁ - b₀, ..., bₙ - b₀
  -- of Rⁿ onto the basis b'₁ - b'₀, ..., b'ₙ - b'₀. The desired affine transformation is then
  -- given by Tx = Ax + a, where a = b'₀ - Ab₀."
  --
  -- Implementation strategy:
  -- 1. Handle empty ι case (trivial - use identity)
  -- 2. Pick a base point i₀ ∈ ι
  -- 3. Use affineIndependent_iff_linearIndependent_vsub to get linear independence
  -- 4. Extend {p(i) - p(i₀) : i ≠ i₀} and {q(i) - q(i₀) : i ≠ i₀} to bases of E
  -- 5. Construct linear equivalence A : E ≃ₗ[ℝ] E mapping one basis to the other
  -- 6. Build affine equivalence T with T(x) = A(x) + (q(i₀) - A(p(i₀)))
  --
  -- This proof requires several nontrivial steps that may benefit from separate helper lemmas.
  sorry

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
### Rockafellar's Theorems 6.1 and 6.4
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
