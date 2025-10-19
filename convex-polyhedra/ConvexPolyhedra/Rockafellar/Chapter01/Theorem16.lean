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
* `nonempty_of_affineSpan_eq_top`: If affine span equals the entire space, index type is nonempty
* `AffineMap.eq_of_eq_on_spanning`: Affine maps uniquely determined by values on spanning sets
* `AffineEquiv.eq_of_eq_on_spanning`: Affine automorphisms uniquely determined on spanning sets
* `affineIndependent_option_extend`: Extending affinely independent families preserves independence

### Finite-dimensional
* `affineDim_le_of_subset_affineSpan`: Affine dimension is monotone with respect to affine span
* `linearBasis_of_affineIndependent_spanning`: Construct linear basis from affinely independent
  spanning family via the difference map
* `affineIndependent_indexed`: Two affinely independent families that span the entire space
  can be mapped by an affine automorphism (base case of Rockafellar's Theorem 1.6)
* `affineIndependent_to_affineIndependent_automorphism`: Rockafellar's Theorem 1.6 -
  affinely independent families of the same size can be mapped by affine automorphisms

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

/-- If the affine span of the range of a function equals the entire space, then the index type
must be nonempty. -/
lemma nonempty_of_affineSpan_eq_top {ι : Type*} (f : ι → E)
    (h : affineSpan ℝ (range f) = ⊤) : Nonempty ι := by
  -- Proof by contradiction
  by_contra h_empty
  -- Convert ¬Nonempty ι to IsEmpty ι
  rw [not_nonempty_iff] at h_empty
  -- If ι is empty, then range f is empty
  have h_range_empty : range f = ∅ := range_eq_empty_iff.mpr h_empty
  -- The affine span of the empty set is ⊥
  have h_span_empty : affineSpan ℝ (range f) = ⊥ := by
    rw [h_range_empty]
    exact span_empty ℝ E E
  -- But h says it equals ⊤
  rw [h_span_empty] at h
  -- This gives us ⊥ = ⊤, which contradicts bot_ne_top
  exact absurd h (bot_ne_top (α := AffineSubspace ℝ E))

/-!
### Uniqueness of affine maps on spanning sets
-/

/-- **Uniqueness of affine maps on spanning sets**: If two affine maps agree on a set that
spans the entire space, then they are equal.

Affine maps are uniquely determined by their values on any spanning set. Affine independence
is not required for uniqueness, only spanning. -/
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

Specialization of `AffineMap.eq_of_eq_on_spanning` to affine automorphisms. -/
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

/-- Given an affinely independent family that spans the entire space, the differences from any
base point form a linear basis of the ambient space.

This is a key construction in the proof of Rockafellar's Theorem 1.6: affine bases
correspond to linear bases via the difference map. -/
lemma linearBasis_of_affineIndependent_spanning
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → E)
    (hf : AffineIndependent ℝ f)
    (hf_span : affineSpan ℝ (range f) = ⊤)
    (i₀ : ι) :
    ∃ (B : Module.Basis {i // i ≠ i₀} ℝ E), ∀ i : {i // i ≠ i₀}, B i = f i - f i₀ := by
  -- Define the difference family
  let f_diff : {i // i ≠ i₀} → E := fun i => f i - f i₀

  -- Show that f_diff is linearly independent
  have h_linear_indep : LinearIndependent ℝ f_diff := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ f i₀).mp hf
    convert h using 2

  -- Show that f_diff spans E
  have h_span : ⊤ ≤ Submodule.span ℝ (range f_diff) := by
    -- Since affineSpan f = ⊤ and f is affinely independent,
    -- we have Fintype.card ι = Module.finrank ℝ E + 1
    have h_card_ι : Fintype.card ι = Module.finrank ℝ E + 1 :=
      hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hf_span

    -- The cardinality of {i // i ≠ i₀} is one less
    have h_card : Fintype.card {i // i ≠ i₀} = Module.finrank ℝ E := by
      have h_sub : Fintype.card {i // i ≠ i₀} = Fintype.card ι - 1 := Set.card_ne_eq i₀
      rw [h_sub, h_card_ι]
      omega

    -- Linear independence implies card = finrank(span)
    have h_finrank_span : Fintype.card {i // i ≠ i₀} = (range f_diff).finrank ℝ :=
      linearIndependent_iff_card_eq_finrank_span.mp h_linear_indep

    -- Therefore finrank(span) = Module.finrank E
    have h_span_full : (range f_diff).finrank ℝ = Module.finrank ℝ E :=
      h_finrank_span.symm.trans h_card

    -- A submodule with full rank must be the whole space
    have h_span_eq_top : Submodule.span ℝ (range f_diff) = ⊤ :=
      Submodule.eq_top_of_finrank_eq h_span_full

    exact h_span_eq_top.ge

  -- Construct the basis
  let B : Module.Basis {i // i ≠ i₀} ℝ E := Module.Basis.mk h_linear_indep h_span

  -- Verify that B i = f i - f i₀
  use B
  intro i
  exact Module.Basis.mk_apply h_linear_indep h_span i

/-- Two affinely independent families with the same index type that both span the entire
space can be mapped to each other by an affine automorphism. -/
theorem affineIndependent_indexed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
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

  -- Pick base points (ι is nonempty since the span equals ⊤)
  let i₀ : ι := Classical.choice (nonempty_of_affineSpan_eq_top f hf_span)
  let f₀ := f i₀
  let g₀ := g i₀

  -- Construct linear bases from the affine bases using the helper lemma
  obtain ⟨B_f, hB_f⟩ := linearBasis_of_affineIndependent_spanning f hf hf_span i₀
  obtain ⟨B_g, hB_g⟩ := linearBasis_of_affineIndependent_spanning g hg hg_span i₀

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
      have h1 : A (B_f ⟨i, h⟩) = B_g ⟨i, h⟩ := by
        grind [Module.Basis.equiv_apply]
      -- Use the helper lemma results: B_f ⟨i, h⟩ = f i - f i₀ and B_g ⟨i, h⟩ = g i - g i₀
      rw [← hB_f ⟨i, h⟩, ← hB_g ⟨i, h⟩]
      exact h1

    -- Now prove T (f i) = g i using the mapping property
    calc T (f i)
        = A (f i) + (g₀ - A f₀)           := rfl
      _ = A ((f i - f₀) + f₀) + (g₀ - A f₀)  := by rw [sub_add_cancel]
      _ = A (f i - f₀) + A f₀ + (g₀ - A f₀) := by rw [LinearEquiv.map_add]
      _ = (g i - g₀) + A f₀ + (g₀ - A f₀)   := by rw [h_basis_map]
      _ = g i                               := by abel

/-- An affinely independent family in a finite-dimensional space has cardinality at most
`finrank + 1`. -/
lemma AffineIndependent.card_le_finrank_add_one
    {ι : Type*} [Fintype ι] {f : ι → E} (hf : AffineIndependent ℝ f) :
    Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
  calc Fintype.card ι
      ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range f)) + 1 := hf.card_le_finrank_succ
    _ ≤ Module.finrank ℝ E + 1 := by
        apply Nat.add_le_add_right
        exact Submodule.finrank_le _

/-- **Rockafellar's Theorem 1.6**: Affinely independent families of the same size can be
mapped to each other by an affine automorphism.

Given two affinely independent families `f, g : ι → E` with the same finite index type,
there exists an affine automorphism `T : E ≃ᵃ[ℝ] E` such that `T (f i) = g i` for all `i`. -/
theorem affineIndependent_to_affineIndependent_automorphism
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (f g : ι → E)
    (hf : AffineIndependent ℝ f)
    (hg : AffineIndependent ℝ g) :
    ∃ (T : E ≃ᵃ[ℝ] E), ∀ i, T (f i) = g i := by
  have h_card_bound : Fintype.card ι ≤ Module.finrank ℝ E + 1 := hf.card_le_finrank_add_one
  -- Induction on the dimension gap
  induction h : Module.finrank ℝ E + 1 - Fintype.card ι generalizing ι f g with
  | zero =>
    -- Base case: dimension gap = 0, so card ι = finrank E + 1
    -- h : Module.finrank ℝ E + 1 - Fintype.card ι = 0
    have h_lower : Module.finrank ℝ E + 1 ≤ Fintype.card ι := by
      exact Nat.sub_eq_zero_iff_le.mp h
    -- Case split on whether ι is empty
    by_cases h_empty : IsEmpty ι
    · -- If ι is empty, the conclusion is vacuous
      use AffineEquiv.refl ℝ E
      intro i
      exact IsEmpty.elim h_empty i
    · -- If ι is nonempty, both families span the entire space
      rw [not_isEmpty_iff] at h_empty
      have h_card_eq : Fintype.card ι = Module.finrank ℝ E + 1 := by omega

      -- By affineSpan_eq_top_iff_card_eq_finrank_add_one, this implies affineSpan = ⊤
      have h_span_f : affineSpan ℝ (range f) = ⊤ := by
        exact hf.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h_card_eq

      have h_span_g : affineSpan ℝ (range g) = ⊤ := by
        exact hg.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr h_card_eq

      -- Apply affineIndependent_indexed
      exact affineIndependent_indexed f g hf hg h_span_f h_span_g

  | succ n ih =>
    -- Inductive case: dimension gap = n + 1 > 0
    -- h : Module.finrank ℝ E + 1 - Fintype.card ι = n + 1
    have h_gap : 0 < Module.finrank ℝ E + 1 - Fintype.card ι := by
      rw [h]
      omega
    -- Case split on whether ι is empty
    by_cases h_empty : IsEmpty ι
    · -- If ι is empty, the conclusion is vacuous
      use AffineEquiv.refl ℝ E
      intro i
      exact IsEmpty.elim h_empty i
    · -- If ι is nonempty, proceed with the inductive step
      rw [not_isEmpty_iff] at h_empty
      -- This means card ι < finrank E + 1
      -- So the affine spans are proper subspaces
      have h_card_lt : Fintype.card ι < Module.finrank ℝ E + 1 := by omega

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

      -- The dimension gap for Option ι
      have h_card_option : Fintype.card (Option ι) = Fintype.card ι + 1 := by
        exact Fintype.card_option

      have h_card_option_bound : Fintype.card (Option ι) ≤ Module.finrank ℝ E + 1 := by omega

      -- Compute the gap for Option ι
      have h_gap_option : Module.finrank ℝ E + 1 - Fintype.card (Option ι) = n := by
        rw [h_card_option]
        omega

      -- Apply IH to f' and g'
      obtain ⟨T, hT⟩ := @ih (Option ι) _ _ f' g' hf' hg' h_card_option_bound h_gap_option

      -- T already maps f i to g i for all i
      use T
      intro i
      exact hT (some i)

end FiniteDimensional
