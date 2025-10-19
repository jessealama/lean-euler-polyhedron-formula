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

This file proves Rockafellar's Theorem 1.6 from "Convex Analysis" (1970): affinely independent
families of the same size can be mapped to each other by affine automorphisms.

The file is organized into two sections:
1. **General Results**: Theorems that hold for any affine space (no finite-dimensionality required)
2. **Finite-Dimensional Results**: Theorems specific to finite-dimensional spaces

## Main results

### General (any dimension)
* `AffineMap.eq_of_eq_on_spanning`: Affine maps uniquely determined by values on spanning sets
* `AffineEquiv.eq_of_eq_on_spanning`: Affine automorphisms uniquely determined on spanning sets
* `affineIndependent_option_extend`: Extending affinely independent families preserves independence

### Finite-dimensional
* `affineIndependent_indexed`: Two affinely independent families that span the entire space
  can be mapped by an affine automorphism (Rockafellar's Theorem 1.6)

## References

* Rockafellar, "Convex Analysis" (1970), Theorem 1.6

## Tags

affine independence, affine automorphism, affine dimension
-/

open Set AffineSubspace
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
## General Results

These theorems hold for affine spaces of any dimension (including infinite-dimensional spaces).
-/

section General

/-!
### Translation invariance of affine dimension
-/

/-- Translation preserves affine dimension: `affineDim ℝ (v +ᵥ s) = affineDim ℝ s`. -/
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

/-- Translation preserves affine dimension: `affineDim ℝ ((-v) +ᵥ s) = affineDim ℝ s`. -/
theorem affineDim_neg_vadd (v : E) (s : Set E) :
    affineDim ℝ ((-v) +ᵥ s) = affineDim ℝ s :=
  affineDim_vadd (-v) s

/-- Translation preserves affine dimension: `affineDim ℝ ((y ↦ y - v) '' s) = affineDim ℝ s`. -/
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

/-- A proper affine subspace does not contain all points. -/
lemma exists_point_not_mem_of_affineSubspace_ne_top
    (S : AffineSubspace ℝ E) (h : S ≠ ⊤) :
    ∃ p : E, p ∉ S := by
  -- Convert to set reasoning: S ≠ ⊤ as affine subspaces means (S : Set E) ≠ Set.univ
  have h_ne_univ : (S : Set E) ≠ Set.univ := by
    intro h_eq
    have h_top : S = ⊤ := SetLike.coe_injective h_eq
    exact h h_top
  -- Use the fact that a set ≠ univ iff there exists an element not in it
  exact (Set.ne_univ_iff_exists_notMem (S : Set E)).mp h_ne_univ

/-!
### Uniqueness of affine maps on spanning sets
-/

/-- **Uniqueness of affine maps on spanning sets**: If two affine maps agree on a set that
spans the entire space, then they are equal.

This is a fundamental principle: affine maps are uniquely determined by their values on any
spanning set. Affine independence is not required for uniqueness, only spanning. -/
theorem AffineMap.eq_of_eq_on_spanning
    {ι : Type*} [Fintype ι]
    {P₁ P₂ : Type*} [NormedAddCommGroup P₁] [InnerProductSpace ℝ P₁]
    [NormedAddCommGroup P₂] [InnerProductSpace ℝ P₂]
    (p : ι → P₁)
    (h_span : affineSpan ℝ (range p) = ⊤)
    (f g : P₁ →ᵃ[ℝ] P₂)
    (h_agree : ∀ i, f (p i) = g (p i)) :
    f = g := by
  -- Use AffineMap.ext: it suffices to show f and g agree on all points
  ext x
  -- Since p spans the entire space, x is in the affine span of range p
  have hx : x ∈ affineSpan ℝ (range p) := by
    rw [h_span]
    exact AffineSubspace.mem_top ℝ P₁ x
  -- By membership in affine span, x can be written as an affine combination
  obtain ⟨w, hw_sum, hw_eq⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
  -- Rewrite x using the affine combination
  rw [hw_eq]
  -- Both f and g preserve affine combinations
  rw [Finset.map_affineCombination Finset.univ p w hw_sum f,
      Finset.map_affineCombination Finset.univ p w hw_sum g]
  -- The compositions f ∘ p and g ∘ p are equal
  have : (f ∘ p : ι → P₂) = (g ∘ p : ι → P₂) := funext h_agree
  rw [this]

/-- **Uniqueness of affine automorphisms on spanning sets**: If two affine automorphisms
agree on a set that spans the entire space, then they are equal.

This specializes the general uniqueness principle to affine automorphisms. -/
theorem AffineEquiv.eq_of_eq_on_spanning
    {ι : Type*} [Fintype ι]
    (p : ι → E)
    (h_span : affineSpan ℝ (range p) = ⊤)
    (T₁ T₂ : E ≃ᵃ[ℝ] E)
    (h_agree : ∀ i, T₁ (p i) = T₂ (p i)) :
    T₁ = T₂ := by
  -- Use AffineEquiv.toAffineMap_inj: affine equivalences are equal iff their affine maps are equal
  rw [← AffineEquiv.toAffineMap_inj]
  -- Apply the general theorem for affine maps
  exact AffineMap.eq_of_eq_on_spanning p h_span T₁.toAffineMap T₂.toAffineMap h_agree

/-!
### Extending affinely independent families
-/

/-- Extending an affinely independent family with a point outside its affine span preserves
affine independence. -/
lemma affineIndependent_option_extend
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {f : ι → E} (hf : AffineIndependent ℝ f)
    {p : E} (hp : p ∉ affineSpan ℝ (range f))
    (f' : Option ι → E)
    (h_some : ∀ i : ι, f' (some i) = f i)
    (h_none : f' none = p) :
    AffineIndependent ℝ f' := by
  -- Show the subfamily excluding `none` is affinely independent
  have h_sub : AffineIndependent ℝ (fun x : {y : Option ι // y ≠ none} => f' x) := by
    -- The restricted function equals f composed with Option.get
    have : (fun x : {y : Option ι // y ≠ none} => f' x) =
           f ∘ (fun x => Option.get x.val (Option.ne_none_iff_isSome.mp x.prop)) := by
      ext ⟨x, hx⟩
      cases x with
      | some i => exact h_some i
      | none => exact absurd rfl hx

    rw [this]

    -- Construct the embedding {y : Option ι // y ≠ none} ↪ ι
    let e : {y : Option ι // y ≠ none} ↪ ι :=
      ⟨fun x => Option.get x.val (Option.ne_none_iff_isSome.mp x.prop),
       fun ⟨x, hx⟩ ⟨y, hy⟩ h_eq => by
         simp only [Subtype.mk.injEq]
         cases x with
         | some i =>
           cases y with
           | some j => simp_all
           | none => exact absurd rfl hy
         | none => exact absurd rfl hx⟩

    exact hf.comp_embedding e

  -- Show f' none ∉ affineSpan ℝ (f' '' {x | x ≠ none})
  have h_not_mem : f' none ∉ affineSpan ℝ (f' '' {x : Option ι | x ≠ none}) := by
    -- The image equals range f
    have h_image_eq : f' '' {x : Option ι | x ≠ none} = range f := by
      ext y
      simp only [mem_image, Set.mem_setOf_eq, mem_range]
      constructor
      · intro ⟨x, hx_ne, hx_eq⟩
        cases x with
        | none => contradiction
        | some i => use i; rw [← h_some]; exact hx_eq
      · intro ⟨i, hi⟩
        use some i
        exact ⟨Option.some_ne_none i, h_some i ▸ hi⟩
    rw [h_image_eq, h_none]
    exact hp

  -- Apply the main theorem
  exact AffineIndependent.affineIndependent_of_notMem_span h_sub h_not_mem

end General

/-!
## Finite-Dimensional Results

These theorems require the affine space to be finite-dimensional.
-/

variable [FiniteDimensional ℝ E]

section FiniteDimensional

/-!
### Affine dimension properties
-/

/-- Affine dimension is monotone: if `s ⊆ affineSpan ℝ t`, then `affineDim ℝ s ≤ affineDim ℝ t`. -/
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
### Rockafellar's Theorem 1.6
-/

/-- Two affinely independent families with the same index type that both span the entire
space can be mapped to each other by an affine automorphism. -/
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

  -- Define the difference families (cleaner than repeating the bulky lambda)
  let f_diff : {i // i ≠ i₀} → E := fun i => f i - f₀
  let g_diff : {i // i ≠ i₀} → E := fun i => g i - g₀

  -- Step 1: Show that f_diff is linearly independent
  -- This follows from affine independence of f via affineIndependent_iff_linearIndependent_vsub
  have h_linear_indep_f : LinearIndependent ℝ f_diff := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ f i₀).mp hf
    convert h using 2

  -- Step 2: Show that f_diff spans E
  -- Strategy: A linearly independent family with cardinality = finrank spans the space
  have h_span_f : ⊤ ≤ Submodule.span ℝ (range f_diff) := by
    -- First, show that Fintype.card {i // i ≠ i₀} = Module.finrank ℝ E
    -- Since affineSpan f = ⊤ and f is affinely independent,
    -- by AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one,
    -- we have Fintype.card ι = Module.finrank ℝ E + 1
    have h_card_ι : Fintype.card ι = Module.finrank ℝ E + 1 :=
      hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hf_span

    -- The cardinality of {i // i ≠ i₀} is one less than the cardinality of ι
    have h_card : Fintype.card {i // i ≠ i₀} = Module.finrank ℝ E := by
      -- Fintype.card {i // i ≠ i₀} = Fintype.card ι - 1
      -- Use Set.card_ne_eq from Mathlib.Data.Set.Finite.Basic
      have h_sub : Fintype.card {i // i ≠ i₀} = Fintype.card ι - 1 :=
        Set.card_ne_eq i₀
      rw [h_sub, h_card_ι]
      omega

    -- By linearIndependent_iff_card_eq_finrank_span:
    -- LinearIndependent implies card = finrank(span)
    have h_finrank_span : Fintype.card {i // i ≠ i₀} = (range f_diff).finrank ℝ :=
      (linearIndependent_iff_card_eq_finrank_span.mp h_linear_indep_f)

    -- Since card = Module.finrank E and card = finrank(span),
    -- we have finrank(span) = Module.finrank E
    have h_span_full : (range f_diff).finrank ℝ = Module.finrank ℝ E :=
      h_finrank_span.symm.trans h_card

    -- A submodule with finrank equal to the ambient space must be the whole space
    -- Use Submodule.eq_top_of_finrank_eq from Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean
    have h_span_eq_top : Submodule.span ℝ (range f_diff) = ⊤ :=
      Submodule.eq_top_of_finrank_eq h_span_full

    exact h_span_eq_top.ge

  -- Construct linear basis B_f
  let B_f : Module.Basis {i // i ≠ i₀} ℝ E := Module.Basis.mk h_linear_indep_f h_span_f

  -- Similarly for g: linear independence follows from affine independence
  have h_linear_indep_g : LinearIndependent ℝ g_diff := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ g i₀).mp hg
    convert h using 2

  -- And g_diff also spans E (by the same cardinality argument)
  have h_span_g : ⊤ ≤ Submodule.span ℝ (range g_diff) := by
    -- Same cardinality argument as for f
    have h_card_ι : Fintype.card ι = Module.finrank ℝ E + 1 :=
      hg.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hg_span
    have h_card : Fintype.card {i // i ≠ i₀} = Module.finrank ℝ E := by
      have h_sub : Fintype.card {i // i ≠ i₀} = Fintype.card ι - 1 :=
        Set.card_ne_eq i₀
      rw [h_sub, h_card_ι]
      omega
    have h_finrank_span : Fintype.card {i // i ≠ i₀} = (range g_diff).finrank ℝ :=
      (linearIndependent_iff_card_eq_finrank_span.mp h_linear_indep_g)
    have h_span_full : (range g_diff).finrank ℝ = Module.finrank ℝ E :=
      h_finrank_span.symm.trans h_card
    have h_span_eq_top : Submodule.span ℝ (range g_diff) = ⊤ :=
      Submodule.eq_top_of_finrank_eq h_span_full
    exact h_span_eq_top.ge

  let B_g : Module.Basis {i // i ≠ i₀} ℝ E := Module.Basis.mk h_linear_indep_g h_span_g

  -- Step 3: Construct linear automorphism A mapping B_f to B_g
  -- Use Basis.equiv to construct a linear equivalence that maps B_f i to B_g i
  -- This is automatically bijective since it's a LinearEquiv
  let A : E ≃ₗ[ℝ] E := B_f.equiv B_g (Equiv.refl _)

  -- Step 4: Define affine automorphism T x := A x + (g₀ - A f₀)
  let T : E ≃ᵃ[ℝ] E := {
    toFun := fun x => A x + (g₀ - A f₀)
    invFun := fun x => A.symm (x - (g₀ - A f₀))
    left_inv := by
      intro x
      -- Need to show: A.symm (A x + (g₀ - A f₀) - (g₀ - A f₀)) = x
      simp only [add_sub_cancel_right]
      exact A.left_inv x
    right_inv := by
      intro x
      -- Need to show: A (A.symm (x - (g₀ - A f₀))) + (g₀ - A f₀) = x
      simp only [LinearEquiv.apply_symm_apply]
      exact sub_add_cancel x (g₀ - A f₀)
    linear := A
    map_vadd' := by
      intro x v
      -- For an affine map, we need: toFun (p +ᵥ v) = toFun p +ᵥ linear v
      -- The affine structure requires: (A (x + v) + (g₀ - A f₀)) = (A x + (g₀ - A f₀)) + A v
      simp only [vadd_eq_add]
      -- Unfold the toFun application and expand using linearity of A
      change A (v + x) + (g₀ - A f₀) = A v + (A x + (g₀ - A f₀))
      rw [A.map_add]
      -- This is just associativity of addition
      ac_rfl
  }

  use T

  -- Prove that T maps f i to g i for all i
  intro i
  by_cases h : i = i₀
  · -- Case i = i₀: T(f₀) = g₀
    subst h
    -- Need to show: A f₀ + (g₀ - A f₀) = g₀
    change A f₀ + (g₀ - A f₀) = g₀
    simp [sub_eq_add_neg, add_left_comm]
  · -- Case i ≠ i₀: T(f i) = g i
    -- Key: A maps basis B_f to basis B_g, so A(f i - f₀) = g i - g₀
    -- By definition of Basis.equiv, we have A (B_f j) = B_g j for all j
    -- Since B_f ⟨i, h⟩ = f i - f₀ and B_g ⟨i, h⟩ = g i - g₀,
    -- we get A(f i - f₀) = g i - g₀

    -- Basis.equiv maps basis elements to corresponding basis elements
    have h_basis_map : A (f i - f₀) = g i - g₀ := by
      -- A = B_f.equiv B_g (Equiv.refl _)
      -- By definition, A (B_f j) = B_g ((Equiv.refl _) j) = B_g j
      -- B_f and B_g are constructed from f_diff and g_diff via Basis.mk
      -- So B_f ⟨i, h⟩ = f_diff ⟨i, h⟩ = f i - f₀
      have h1 : A (B_f ⟨i, h⟩) = B_g ⟨i, h⟩ := by
        -- Use Basis.equiv_apply or try grind
        grind [Module.Basis.equiv_apply]
      -- B_f ⟨i, h⟩ = f_diff ⟨i, h⟩ = f i - f₀ (by construction via Basis.mk)
      -- Use Basis.mk_apply or Basis.coe_mk to relate B_f to f_diff
      have h2 : B_f ⟨i, h⟩ = f_diff ⟨i, h⟩ := Module.Basis.mk_apply h_linear_indep_f h_span_f ⟨i, h⟩
      have h3 : B_g ⟨i, h⟩ = g_diff ⟨i, h⟩ := Module.Basis.mk_apply h_linear_indep_g h_span_g ⟨i, h⟩
      simp only [f_diff, g_diff] at h2 h3
      rw [← h2, ← h3]
      exact h1

    -- Now prove T (f i) = g i using the mapping property
    calc T (f i)
        = A (f i) + (g₀ - A f₀)           := rfl
      _ = A ((f i - f₀) + f₀) + (g₀ - A f₀)  := by rw [sub_add_cancel]
      _ = A (f i - f₀) + A f₀ + (g₀ - A f₀) := by rw [LinearEquiv.map_add]
      _ = (g i - g₀) + A f₀ + (g₀ - A f₀)   := by rw [h_basis_map]
      _ = g i                               := by abel

/-- **Rockafellar's Theorem 1.6**: Affinely independent families of the same size can be
mapped to each other by an affine automorphism.

Given two affinely independent families `f, g : ι → E` with the same finite index type,
there exists an affine automorphism `T : E ≃ᵃ[ℝ] E` such that `T (f i) = g i` for all `i`. -/
-- Helper lemma for the induction
private theorem affineIndependent_to_affineIndependent_automorphism_aux
    (n : ℕ)
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f g : ι → E)
    (hf : AffineIndependent ℝ f)
    (hg : AffineIndependent ℝ g)
    (hn : n = Module.finrank ℝ E + 1 - Fintype.card ι)
    (h_card : Fintype.card ι ≤ Module.finrank ℝ E + 1) :
    ∃ (T : E ≃ᵃ[ℝ] E), ∀ i, T (f i) = g i := by
  -- Induction on n
  induction n generalizing ι f g with
  | zero =>
    -- Base case: n = 0, so card ι = finrank E + 1
    -- This means both families span the entire space
    have h_card_eq : Fintype.card ι = Module.finrank ℝ E + 1 := by
      omega

    -- By affineSpan_eq_top_iff_card_eq_finrank_add_one, this implies affineSpan = ⊤
    have h_span_f : affineSpan ℝ (range f) = ⊤ := by
      exact hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h_card_eq

    have h_span_g : affineSpan ℝ (range g) = ⊤ := by
      exact hg.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h_card_eq

    -- Apply affineIndependent_indexed
    exact affineIndependent_indexed f g hf hg h_span_f h_span_g

  | succ n ih =>
    -- Inductive case: n > 0
      -- This means card ι < finrank E + 1
      -- So the affine spans are proper subspaces
      have h_card_lt : Fintype.card ι < Module.finrank ℝ E + 1 := by
        omega

      -- Since card < finrank + 1, the affine span cannot be the whole space
      have h_span_f_ne_top : affineSpan ℝ (range f) ≠ ⊤ := by
        intro h_top
        have h_card_eq := hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp h_top
        omega

      have h_span_g_ne_top : affineSpan ℝ (range g) ≠ ⊤ := by
        intro h_top
        have h_card_eq := hg.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp h_top
        omega

      -- Find points outside the affine spans
      -- Since affineSpan (range f) is a proper affine subspace, there exists a point not in it
      have h_exists_f : ∃ p_f : E, p_f ∉ affineSpan ℝ (range f) :=
        exists_point_not_mem_of_affineSubspace_ne_top _ h_span_f_ne_top

      obtain ⟨p_f, hp_f⟩ := h_exists_f

      have h_exists_g : ∃ p_g : E, p_g ∉ affineSpan ℝ (range g) :=
        exists_point_not_mem_of_affineSubspace_ne_top _ h_span_g_ne_top

      obtain ⟨p_g, hp_g⟩ := h_exists_g

      -- Extend f and g to Option ι
      let f' : Option ι → E := fun o => match o with
        | none => p_f
        | some i => f i

      let g' : Option ι → E := fun o => match o with
        | none => p_g
        | some i => g i

      -- Show that f' and g' are affinely independent using the helper lemma
      have hf' : AffineIndependent ℝ f' :=
        affineIndependent_option_extend hf hp_f f' (fun i => rfl) rfl

      have hg' : AffineIndependent ℝ g' :=
        affineIndependent_option_extend hg hp_g g' (fun i => rfl) rfl

      -- The dimension gap for Option ι is n - 1
      have h_card_option : Fintype.card (Option ι) = Fintype.card ι + 1 := by
        exact Fintype.card_option

      -- The dimension gap for Option ι is exactly n (since we added 1 to the card)
      have h_gap : n = Module.finrank ℝ E + 1 - Fintype.card (Option ι) := by
        omega

      have h_card_option_bound : Fintype.card (Option ι) ≤ Module.finrank ℝ E + 1 := by
        omega

      -- Apply IH to f' and g'
      have h_ih := @ih (Option ι) _ _ _ f' g' hf' hg' h_gap h_card_option_bound

      -- Extract the automorphism
      obtain ⟨T, hT⟩ := h_ih

      -- T already maps f i to g i for all i (because T (f' (some i)) = g' (some i))
      use T
      intro i
      exact hT (some i)

end FiniteDimensional
