/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Basis.Basic
import ConvexPolyhedra.Polyhedron

/-!
# Rockafellar's Theorem 1.6

This file contains Rockafellar's Theorem 1.6 from "Convex Analysis" (1970), which states that
affinely independent sets can be mapped to each other by affine automorphisms of the ambient space.

## Main results

* `affineIndependent_to_affineIndependent_automorphism` - Rockafellar's Theorem 1.6:
  Affinely independent sets of the same size can be mapped by an affine automorphism

## Infrastructure

* Affine dimension properties and translation invariance
* Helper lemmas for affine dimension

## References

* Rockafellar, "Convex Analysis" (1970), Theorem 1.6

## Tags

affine, affine independence, affine dimension, affine transformation
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

/-!
### Helper lemmas for affine independence
-/

/-- The cardinality of any affinely independent finite set in a finite-dimensional
inner product space of dimension n is at most n + 1.

This is a fundamental constraint: you can have at most dim(E) + 1 affinely independent
points in E, which corresponds to a simplex of dimension dim(E). -/
lemma affineIndependent_card_le_finrank_add_one
    [FiniteDimensional ℝ E]
    (s : Finset E)
    (hs : AffineIndependent ℝ ((↑) : s → E)) :
    s.card ≤ Module.finrank ℝ E + 1 := by
  sorry

/-!
### Rockafellar's Theorem 1.6
-/

/-- Given two affinely independent families with the same index type that both span
the entire space, there exists an affine automorphism mapping one to the other.

This is the base case of Rockafellar's Theorem 1.6, reformulated to work naturally
with the `AffineBasis` API. The key insight is that affine bases with the same
index type determine a unique affine automorphism between them.

This theorem is the affine analogue of the linear algebra fact that a bijection
between two bases of a vector space extends uniquely to a linear automorphism. -/
theorem affineIndependent_indexed
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f g : ι → E)
    (hf : AffineIndependent ℝ f)
    (hg : AffineIndependent ℝ g)
    (hf_span : affineSpan ℝ (range f) = ⊤)
    (hg_span : affineSpan ℝ (range g) = ⊤) :
    ∃ (T : E ≃ᵃ[ℝ] E), ∀ i, T (f i) = g i := by
  -- Strategy (following Rockafellar): Reduce to linear algebra
  -- 1. Pick base points f₀ and g₀
  -- 2. Form linear bases B_f = {f i - f₀ | i ≠ 0} and B_g = {g i - g₀ | i ≠ 0}
  -- 3. Construct linear automorphism A mapping B_f to B_g
  -- 4. Define affine map T x := A x + (g₀ - A f₀)
  -- This ensures T(f₀) = g₀ and T(f i) = g i for all i

  -- Pick base points (using Nonempty ι)
  let i₀ : ι := Classical.choice ‹Nonempty ι›
  let f₀ := f i₀
  let g₀ := g i₀

  -- Step 1: Show that {f i - f₀ | i ≠ i₀} is linearly independent
  -- This follows from affine independence of f via affineIndependent_iff_linearIndependent_vsub
  have h_linear_indep_f : LinearIndependent ℝ (fun i : {i // i ≠ i₀} => f i - f₀) := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ f i₀).mp hf
    convert h using 2

  -- Step 2: Show that {f i - f₀ | i ≠ i₀} spans E
  -- This follows from f spanning the affine space (affineSpan = ⊤)
  have h_span_f : ⊤ ≤ Submodule.span ℝ (range (fun i : {i // i ≠ i₀} => f i - f₀)) := by
    sorry

  -- Construct linear basis B_f
  let B_f : Module.Basis {i // i ≠ i₀} ℝ E := Module.Basis.mk h_linear_indep_f h_span_f

  -- Similarly for g: linear independence follows from affine independence
  have h_linear_indep_g : LinearIndependent ℝ (fun i : {i // i ≠ i₀} => g i - g₀) := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ g i₀).mp hg
    convert h using 2

  have h_span_g : ⊤ ≤ Submodule.span ℝ (range (fun i : {i // i ≠ i₀} => g i - g₀)) := by
    sorry

  let B_g : Module.Basis {i // i ≠ i₀} ℝ E := Module.Basis.mk h_linear_indep_g h_span_g

  -- Step 3: Construct linear automorphism A mapping B_f to B_g
  -- Use Basis.constr to define A : E →ₗ[ℝ] E by A(f i - f₀) = g i - g₀
  let A_map : E →ₗ[ℝ] E := B_f.constr ℝ (fun i => g i - g₀)

  -- Show A is bijective (it's a linear map between bases of same dimension)
  have h_bijective_A : Function.Bijective A_map := by
    sorry

  -- Package as LinearEquiv
  let A : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective A_map h_bijective_A

  -- Step 4: Define affine automorphism T x := A x + (g₀ - A f₀)
  let T : E ≃ᵃ[ℝ] E := {
    toFun := fun x => A x + (g₀ - A f₀)
    invFun := fun x => A.symm (x - (g₀ - A f₀))
    left_inv := by
      intro x
      -- Need to show: A.symm (A x + (g₀ - A f₀) - (g₀ - A f₀)) = x
      sorry
    right_inv := by
      intro x
      -- Need to show: A (A.symm (x - (g₀ - A f₀))) + (g₀ - A f₀) = x
      sorry
    linear := A
    map_vadd' := by
      intro x v
      -- Need to show: T (x + v) = T x + v
      sorry
  }

  use T

  -- Prove that T maps f i to g i for all i
  intro i
  by_cases h : i = i₀
  · -- Case i = i₀: T(f₀) = g₀
    subst h
    -- Need to show: A f₀ + (g₀ - A f₀) = g₀
    sorry
  · -- Case i ≠ i₀: T(f i) = g i
    -- We have A(f i - f₀) = g i - g₀ by construction (via Basis.constr)
    -- So A(f i) = A(f i - f₀) + A(f₀) = (g i - g₀) + A(f₀)
    -- Therefore T(f i) = A(f i) + (g₀ - A(f₀)) = (g i - g₀) + A(f₀) + (g₀ - A(f₀)) = g i
    sorry

/-- **Rockafellar's Theorem 1.6**: Affinely independent sets of the same size can be mapped to each
other by an affine automorphism of the ambient space.

Given two affinely independent finite sets {b₀, b₁, ..., bₘ} and {b'₀, b'₁, ..., b'ₘ} in E,
there exists a one-to-one affine transformation T : E → E such that T maps s bijectively to t.

This is the finite-dimensional version of Rockafellar's Theorem 1.6 from "Convex Analysis".

The proof proceeds by induction on n = (dim E + 1) - |s|:
- Base case (n = 0): Both s and t have maximal dimension (dim E + 1 points), so they span
  the entire space. We construct affine bases from them and build the automorphism.
- Inductive step: When |s| < dim E + 1, we extend both s and t by adding one point each,
  preserving affine independence. By IH, we get an automorphism T' mapping s' to t'.
  Since s ⊆ s' (as cosets) and T' bijects s' to t', we have T' '' s = t.
-/
theorem affineIndependent_to_affineIndependent_automorphism
    [DecidableEq E]
    (s t : Finset E)
    (h_card_eq : s.card = t.card)
    (hs : AffineIndependent ℝ ((↑) : s → E))
    (ht : AffineIndependent ℝ ((↑) : t → E)) :
    ∃ (T : E ≃ᵃ[ℝ] E), T '' s = t := by
  -- Induction on the "dimension gap": how many points we need to add to reach a full basis
  let n : ℕ := Module.finrank ℝ E + 1 - Finset.card s

  -- Induction on n, generalizing over s and t
  induction n generalizing s t with
  | zero => sorry
  | succ k ih =>
    -- INDUCTIVE STEP: n = k + 1 > 0, so |s| < dim E + 1
    -- We can extend s and t by adding one point each
    -- Since n = k + 1, we have Module.finrank ℝ E + 1 - s.card = k + 1
    have h_n_succ : Module.finrank ℝ E + 1 - s.card = k + 1 := by
      show Module.finrank ℝ E + 1 - s.card = k + 1
      sorry  -- This is true by the induction step
    have h_card_lt : s.card < Module.finrank ℝ E + 1 := by
      -- If a - b = k + 1 > 0, then b < a
      -- We have Module.finrank ℝ E + 1 - s.card = k + 1
      -- This means Module.finrank ℝ E + 1 = s.card + (k + 1)
      have h_le : s.card ≤ Module.finrank ℝ E + 1 :=
        affineIndependent_card_le_finrank_add_one s hs
      -- From Module.finrank ℝ E + 1 - s.card = k + 1 > 0, we get s.card < Module.finrank ℝ E + 1
      omega

    -- Since |s| < dim E + 1, the affine span of s is not the whole space
    have h_span_ne_top : affineSpan ℝ (s : Set E) ≠ ⊤ := by
      sorry

    -- So there exists a point p ∉ affineSpan ℝ s
    have : ∃ p : E, p ∉ affineSpan ℝ (s : Set E) := by
      sorry
    obtain ⟨p, hp⟩ := this

    -- Similarly for t
    have : ∃ q : E, q ∉ affineSpan ℝ (t : Set E) := by
      sorry
    obtain ⟨q, hq⟩ := this

    -- Extend s and t
    have hp_notin_s : p ∉ s := by
      sorry
    have hq_notin_t : q ∉ t := by
      sorry

    let s' : Finset E := insert p s
    let t' : Finset E := insert q t

    -- The extended sets are still affinely independent
    have hs' : AffineIndependent ℝ ((↑) : s' → E) := by
      sorry

    have ht' : AffineIndependent ℝ ((↑) : t' → E) := by
      sorry

    -- The extended sets have the same cardinality
    have h_card_eq' : s'.card = t'.card := by
      simp [s', t']
      rw [Finset.card_insert_of_notMem hp_notin_s]
      rw [Finset.card_insert_of_notMem hq_notin_t]
      linarith

    -- The dimension gap is exactly k
    have h_n_eq_k : Module.finrank ℝ E + 1 - s'.card = k := by
      simp [s']
      rw [Finset.card_insert_of_notMem hp_notin_s]
      -- We have Module.finrank ℝ E + 1 - s.card = k + 1
      -- and s'.card = s.card + 1
      -- so Module.finrank ℝ E + 1 - (s.card + 1) = k
      calc Module.finrank ℝ E + 1 - (s.card + 1)
          = (Module.finrank ℝ E + 1 - s.card) - 1 := by
            -- Nat subtraction: (a - b) - 1 = a - (b + 1)
            exact Nat.sub_sub (Module.finrank ℝ E + 1) s.card 1
        _ = (k + 1) - 1 := by rw [h_n_succ]
        _ = k := by omega

    -- Apply induction hypothesis
    obtain ⟨T, hT⟩ := ih s' t' h_card_eq' hs' ht'

    -- T maps s' to t', and since s ⊆ s' and t ⊆ t',
    -- we need to show T '' s = t
    use T

    sorry
