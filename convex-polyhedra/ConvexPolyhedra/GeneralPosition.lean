/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import ConvexPolyhedra.Basic
import ConvexPolyhedra.Face
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# General Position for Polyhedra

This file defines what it means for an H-polyhedron to be in general position.
This is a crucial hypothesis for many combinatorial properties of polyhedra,
including the Diamond Property.

## Main definitions

* `HPolyhedron.InGeneralPosition` - The general position condition
* `HPolyhedron.HasDiamondProperty` - The Diamond Property

## Main results

* `general_position_implies_diamond` - General position implies the Diamond Property

-/

open scoped RealInnerProductSpace
open Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace HPolyhedron

variable (P : HPolyhedron E)

/-- The set of halfspaces where a point x lies on the boundary (satisfies with equality) -/
noncomputable def tightHalfSpaces (x : E) : Finset (HalfSpace E) :=
  -- Using Classical since equality in ℝ is not decidable
  @Finset.filter _ (fun h => ⟪h.normal, x⟫ = h.bound)
    (Classical.decPred _) P.halfSpaces

/-- The vertices of a face (0-dimensional subfaces contained in F) -/
def Face.vertices (F : Set E) (hF : IsFace P F) : Set E :=
  {v ∈ F | IsVertex P {v}}

/-- General Position: A polyhedron is in general position if
    the vertices of each face are affinely independent and span exactly
    the face's affine hull -/
def InGeneralPosition [FiniteDimensional ℝ E] : Prop :=
  ∀ F : Set E, ∀ hF : IsFace P F,
    -- The vertices of F are affinely independent
    (∃ (ι : Type*) (v : ι → E) (hv : Set.range v = Face.vertices P F hF),
      AffineIndependent ℝ v) ∧
    -- The affine span of the vertices equals the affine span of F
    affineSpan ℝ (Face.vertices P F hF) = affineSpan ℝ F ∧
    -- The dimension equals the number of vertices minus 1
    faceDim P F hF + 1 = (Face.vertices P F hF).ncard

/-- The set of halfspaces that are tight on a face F -/
noncomputable def tightOnFace (F : Set E) (_ : IsFace P F) : Finset (HalfSpace E) :=
  -- Using Classical since the predicate involves a universal quantifier over a set
  @Finset.filter _ (fun h => ∀ x ∈ F, ⟪h.normal, x⟫ = h.bound)
    (Classical.decPred _) P.halfSpaces

/-- A Diamond configuration: two faces with codimension 2 and their intermediate faces -/
structure Diamond (P : HPolyhedron E) [FiniteDimensional ℝ E] where
  /-- The larger face -/
  F : Set E
  /-- The smaller face with codimension 2 -/
  H : Set E
  /-- The first intermediate face -/
  G₁ : Set E
  /-- The second intermediate face -/
  G₂ : Set E
  /-- F is a face of P -/
  hF : IsFace P F
  /-- H is a face of P -/
  hH : IsFace P H
  /-- G₁ is a face of P -/
  hG₁ : IsFace P G₁
  /-- G₂ is a face of P -/
  hG₂ : IsFace P G₂
  /-- H is contained in F -/
  h_sub : H ⊆ F
  /-- H has codimension 2 in F -/
  h_codim : faceDim P H hH + 2 = faceDim P F hF
  /-- The intermediate faces are distinct -/
  h_distinct : G₁ ≠ G₂
  /-- G₁ is between H and F -/
  h_between₁ : H ⊆ G₁ ∧ G₁ ⊆ F
  /-- G₂ is between H and F -/
  h_between₂ : H ⊆ G₂ ∧ G₂ ⊆ F
  /-- G₁ has the right dimension -/
  h_dim₁ : faceDim P G₁ hG₁ = faceDim P H hH + 1
  /-- G₂ has the right dimension -/
  h_dim₂ : faceDim P G₂ hG₂ = faceDim P H hH + 1

/-- The Diamond Property: Every pair of faces F, H with H ⊆ F and dim(H) = dim(F) - 2
    has exactly 2 intermediate faces G with H ⊆ G ⊆ F and dim(G) = dim(F) - 1 -/
def HasDiamondProperty : Prop :=
  ∀ (F H : Set E) (hF : IsFace P F) (hH : IsFace P H),
    H ⊆ F → faceDim P H hH + 2 = faceDim P F hF →
    ∃ (d : Diamond P), d.F = F ∧ d.H = H

/-- Extract the intermediate faces from a Diamond as a pair -/
def Diamond.intermediatePair (d : Diamond P) : Set E × Set E := (d.G₁, d.G₂)

/-- Extract the intermediate faces as a Finset (requires Classical for DecidableEq) -/
noncomputable def Diamond.intermediateFinset (d : Diamond P) : Finset (Set E) :=
  by classical exact {d.G₁, d.G₂}

/-- The cardinality of intermediate faces is always 2 -/
lemma Diamond.intermediate_card (d : Diamond P) :
    d.intermediateFinset.card = 2 := by
  unfold intermediateFinset
  classical exact Finset.card_pair d.h_distinct

section HelperLemmas

/-- The face determined by a set of halfspaces
    (all points in P satisfying all halfspaces with equality) -/
noncomputable def faceFromHalfspaces (hs : Finset (HalfSpace E)) : Set E :=
  P.toSet ∩ { x : E | ∀ h ∈ hs, ⟪h.normal, x⟫ = h.bound }

/-- If the halfspaces come from tightOnFace of an existing face,
    then faceFromHalfspaces is nonempty -/
lemma faceFromHalfspaces_nonempty (F : Set E) (hF : IsFace P F)
    (hs : Finset (HalfSpace E)) (h_subset : hs ⊆ tightOnFace P F hF) :
    (faceFromHalfspaces P hs).Nonempty := by
  -- Since F is a face and hs are halfspaces tight on F,
  -- any point in F satisfies all constraints in hs
  -- Therefore F ⊆ faceFromHalfspaces P hs
  -- Since F is a face, it's nonempty, so faceFromHalfspaces P hs is also nonempty
  sorry

/-- If all halfspaces are tight on some common point in P, then faceFromHalfspaces is nonempty -/
lemma faceFromHalfspaces_nonempty_of_common_point (hs : Finset (HalfSpace E))
    (x : E) (hx : x ∈ P.toSet) (h_tight : ∀ h ∈ hs, ⟪h.normal, x⟫ = h.bound) :
    (faceFromHalfspaces P hs).Nonempty := by
  use x
  simp [faceFromHalfspaces]
  exact ⟨hx, h_tight⟩

/-- If all halfspaces in a set are from P's halfspace collection and tight on some existing face,
    then faceFromHalfspaces produces a valid face -/
lemma faceFromHalfspaces_is_face (hs : Finset (HalfSpace E))
    (h_subset : hs ⊆ P.halfSpaces)
    (h_nonempty : (faceFromHalfspaces P hs).Nonempty) :
    IsFace P (faceFromHalfspaces P hs) := by
  sorry -- This needs to be proved using the definition of IsFace
  -- The key is to show that faceFromHalfspaces P hs is the intersection of P with
  -- the boundaries of supporting halfspaces

/-- DEPRECATED: In general position, the dimension of a face obtained from halfspaces is
    the ambient dimension minus the number of halfspaces.

    This lemma has been replaced by the more direct tightOnFace_card_eq, which avoids
    circular dependencies and proves the dimension reduction for the specific case we need.

    If needed, this can be derived from tightOnFace_card_eq by showing that hs equals
    tightOnFace for the appropriate face. -/
lemma faceFromHalfspaces_dim (hs : Finset (HalfSpace E))
    (h_subset : hs ⊆ P.halfSpaces)
    (h_nonempty : (faceFromHalfspaces P hs).Nonempty)
    (h_gp : P.InGeneralPosition) :
    faceDim P (faceFromHalfspaces P hs) (faceFromHalfspaces_is_face P hs h_subset h_nonempty) =
    finrank ℝ E - hs.card := by
  -- This can be derived from tightOnFace_card_eq if needed, but we don't currently use it
  sorry
  --
  -- Mathematical outline:
  -- 1. Each halfspace boundary is a hyperplane with codimension 1
  -- 2. In general position, hyperplanes intersect transversely
  -- 3. For transverse intersection of k hyperplanes in n-dimensional space,
  --    the intersection has dimension n - k
  --
  -- Lean approach:
  -- - Use induction on hs.card
  -- - Base case (hs = ∅): faceFromHalfspaces P ∅ = P.toSet,
  --   so faceDim = finrank E - 0
  -- - Inductive step: Given h ∈ hs', show that adding one more halfspace
  --   reduces dimension by 1 using:
  --   * The general position hypothesis implies transversality
  --   * Submodule.finrank_add_inf_finrank_orthogonal' for orthogonal decomposition
  --   * AffineIndependent.finrank_vectorSpan for affine independence
  --
  -- Key lemmas needed:
  -- - Connection between halfspace boundaries and hyperplanes as affine subspaces
  -- - Dimension formula for affine subspace intersections
  -- - General position implies generic (transverse) intersection

/-- Face dimensions are bounded by the ambient space dimension -/
lemma face_dim_le_finrank (F : Set E) (hF : IsFace P F) :
    faceDim P F hF ≤ finrank ℝ E := by
  -- faceDim is defined as finrank ℝ (affineSpan ℝ F).direction
  -- The direction of an affine subspace is a linear subspace of E
  -- So its dimension is bounded by finrank ℝ E
  unfold faceDim
  -- Need: finrank ℝ (affineSpan ℝ F).direction ≤ finrank ℝ E
  -- The direction is a submodule of E, so we can use finrank bounds for submodules
  exact Submodule.finrank_le (affineSpan ℝ F).direction

/-- If hs₁ ⊆ hs₂, then faceFromHalfspaces hs₂ ⊆ faceFromHalfspaces hs₁
    (more constraints means smaller face) -/
lemma faceFromHalfspaces_antimono (hs₁ hs₂ : Finset (HalfSpace E))
    (h_sub : hs₁ ⊆ hs₂) :
    faceFromHalfspaces P hs₂ ⊆ faceFromHalfspaces P hs₁ := by
  intro x hx
  simp only [faceFromHalfspaces, Set.mem_inter_iff, Set.mem_setOf_eq] at hx ⊢
  exact ⟨hx.1, fun h hh => hx.2 h (h_sub hh)⟩

/-- If hs are tight on face F, then F ⊆ faceFromHalfspaces P hs -/
lemma face_subset_faceFromHalfspaces (F : Set E) (hF : IsFace P F)
    (hs : Finset (HalfSpace E)) (h_subset : hs ⊆ tightOnFace P F hF) :
    F ⊆ faceFromHalfspaces P hs := by
  intro x hx
  simp only [faceFromHalfspaces, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · -- x ∈ P.toSet
    -- By definition, F = P.toSet ∩ h.boundary for some supporting h
    obtain ⟨h, _, rfl⟩ := hF
    exact hx.1
  · -- ∀ h ∈ hs, ⟪h.normal, x⟫ = h.bound
    intro h hh
    -- h ∈ hs ⊆ tightOnFace P F hF
    have h_tight : h ∈ tightOnFace P F hF := h_subset hh
    simp only [tightOnFace, Finset.mem_filter] at h_tight
    exact h_tight.2 x hx

/-- If H ⊆ F are faces, then any halfspace tight on F is also tight on H -/
lemma tight_on_face_subset (F H : Set E) (_hF : IsFace P F) (_hH : IsFace P H)
    (h_sub : H ⊆ F) (h : HalfSpace E) (_h_in : h ∈ P.halfSpaces) :
    (∀ x ∈ F, ⟪h.normal, x⟫ = h.bound) → (∀ x ∈ H, ⟪h.normal, x⟫ = h.bound) := by
  intros h_tight x hx
  exact h_tight x (h_sub hx)

/-- In general position, a face equals the set of points where its tight halfspaces are tight -/
lemma face_eq_faceFromTightHalfspaces (h_gp : P.InGeneralPosition)
    (F : Set E) (hF : IsFace P F) :
    F = faceFromHalfspaces P (tightOnFace P F hF) := by
  sorry
  -- This is the key property of general position:
  -- A face is exactly characterized by the set of halfspaces tight on it.
  --
  -- Proof sketch:
  -- (⊆) F ⊆ faceFromHalfspaces P (tightOnFace P F hF) by face_subset_faceFromHalfspaces
  -- (⊇) Need to show points satisfying all tight halfspaces with equality are in F
  --     This requires:
  --     1. The tight halfspaces are exactly those needed to "cut out" F
  --     2. No redundant constraints exist (this is what general position ensures)
  --     3. The affine independence of vertices implies dimension counting
  --        which implies the tight halfspaces are minimal/non-redundant

/-- In general position, the tight halfspaces determine the face uniquely -/
lemma face_determined_by_tight (h_gp : P.InGeneralPosition)
    (F G : Set E) (hF : IsFace P F) (hG : IsFace P G) :
    tightOnFace P F hF = tightOnFace P G hG → F = G := by
  intro h_eq
  rw [face_eq_faceFromTightHalfspaces P h_gp F hF]
  rw [face_eq_faceFromTightHalfspaces P h_gp G hG]
  rw [h_eq]

/-- In general position, if two faces from halfspaces are equal,
    then their defining halfspace sets must be equal -/
lemma faceFromHalfspaces_injective (h_gp : P.InGeneralPosition)
    (hs₁ hs₂ : Finset (HalfSpace E))
    (h₁_sub : hs₁ ⊆ P.halfSpaces) (h₂_sub : hs₂ ⊆ P.halfSpaces)
    (h₁_nonempty : (faceFromHalfspaces P hs₁).Nonempty)
    (h₂_nonempty : (faceFromHalfspaces P hs₂).Nonempty) :
    faceFromHalfspaces P hs₁ = faceFromHalfspaces P hs₂ → hs₁ = hs₂ := by
  sorry
  -- Proof sketch:
  -- 1. Let F₁ = faceFromHalfspaces P hs₁ and F₂ = faceFromHalfspaces P hs₂
  -- 2. Assume F₁ = F₂
  -- 3. In general position, tightOnFace P F₁ = hs₁ and tightOnFace P F₂ = hs₂
  --    (this is essentially the converse of face_eq_faceFromTightHalfspaces)
  -- 4. Since F₁ = F₂, we have tightOnFace P F₁ = tightOnFace P F₂
  -- 5. Therefore hs₁ = hs₂

/-- In general position, the number of tight halfspaces on a non-empty face
    is bounded by the ambient dimension.

    This is the fundamental bound that we prove first. -/
lemma tightOnFace_card_le (h_gp : P.InGeneralPosition)
    (F : Set E) (hF : IsFace P F) :
    (tightOnFace P F hF).card ≤ finrank ℝ E := by
  -- PROOF STRATEGY:
  -- Connect the combinatorial structure (halfspaces/faces) to linear algebra
  -- (normal vectors, linear independence, matrix ranks).
  --
  -- Key bridge: Each halfspace h has a normal vector h.normal : E
  -- In general position, the normal vectors of tight halfspaces should be
  -- linearly independent (or have bounded rank).
  --
  -- Approach:
  -- 1. Extract the normal vectors: {h.normal | h ∈ tightOnFace P F hF}
  -- 2. Show these vectors are linearly independent (from general position)
  -- 3. By linear algebra: a linearly independent set in E has size ≤ finrank ℝ E
  -- 4. Therefore: card ≤ finrank
  --
  -- Alternative approach using matrix ranks:
  -- - Form a matrix where rows are the normal vectors
  -- - In general position, this matrix should have full rank
  -- - The rank is bounded by min(card, finrank)
  -- - For a nonempty intersection, we need rank ≤ finrank
  -- - Therefore: card ≤ finrank
  --
  -- This requires connecting:
  -- - Halfspace normals to linear independence
  -- - General position to linear independence of normals
  -- - Cardinality of linearly independent sets to finrank
  sorry

/-- In general position, the number of tight halfspaces on a face equals
    the ambient dimension minus the face dimension. -/
lemma tightOnFace_card_eq (h_gp : P.InGeneralPosition)
    (F : Set E) (hF : IsFace P F) :
    (tightOnFace P F hF).card = finrank ℝ E - faceDim P F hF := by
  -- PROOF STRATEGY:
  -- Use tightOnFace_card_le to establish the bound, then prove the exact equality.
  --
  -- Key ideas:
  -- 1. From tightOnFace_card_le: card ≤ finrank
  -- 2. From face_dim_le_finrank: faceDim F ≤ finrank
  -- 3. In general position, each tight hyperplane reduces dimension by exactly 1
  -- 4. F = faceFromHalfspaces P (tightOnFace P F hF) (by face_eq_faceFromTightHalfspaces)
  -- 5. Starting from finrank ℝ E, after card reductions of 1 each:
  --    faceDim F = finrank ℝ E - card
  --    Therefore: card = finrank ℝ E - faceDim F
  --
  -- The proof requires showing that each tight hyperplane reduces dimension by
  -- exactly 1 (the dimension reduction formula), which is the key property of
  -- general position.
  sorry

/-- For faces H ⊆ F, the tight halfspaces on H contain those tight on F -/
lemma tight_halfspaces_monotone (F H : Set E) (hF : IsFace P F) (hH : IsFace P H)
    (h_sub : H ⊆ F) :
    tightOnFace P F hF ⊆ tightOnFace P H hH := by
  intro h
  simp only [tightOnFace, Finset.mem_filter]
  intro ⟨h_in, h_tight_F⟩
  constructor
  · exact h_in
  · exact tight_on_face_subset P F H hF hH h_sub h h_in h_tight_F

end HelperLemmas

section MainTheorems

variable [DecidableEq (HalfSpace E)]

/-- Helper lemma: dimension of intermediate face in a diamond configuration -/
lemma intermediate_face_dim (h_gp : P.InGeneralPosition)
    (F H : Set E) (hF : IsFace P F) (hH : IsFace P H)
    (_h_subset : H ⊆ F) (h_codim2 : faceDim P H hH + 2 = faceDim P F hF)
    (h_extra : HalfSpace E) (h_extra_in : h_extra ∈ tightOnFace P H hH \ tightOnFace P F hF)
    (G_halfspaces : Finset (HalfSpace E))
    (hG_def : G_halfspaces = tightOnFace P F hF ∪ {h_extra})
    (G : Set E) (hG : G = faceFromHalfspaces P G_halfspaces)
    (hG_face : IsFace P G) :
    faceDim P G hG_face = faceDim P H hH + 1 := by
  -- Step 1: Count the halfspaces in G_halfspaces
  have card_G : G_halfspaces.card = (tightOnFace P F hF).card + 1 := by
    rw [hG_def]
    have h_not_in_F : h_extra ∉ tightOnFace P F hF := (Finset.mem_sdiff.mp h_extra_in).2
    rw [Finset.union_comm, Finset.singleton_union]
    exact Finset.card_insert_of_notMem h_not_in_F

  -- Step 2: Use faceFromHalfspaces_dim (requires general position)
  -- The full calculation would be:
  calc P.faceDim G hG_face
      = finrank ℝ E - G_halfspaces.card := by
          -- We need to show G_halfspaces = tightOnFace P G hG_face
          -- Then we can apply tightOnFace_card_eq
          have G_tight : G_halfspaces = P.tightOnFace G hG_face := by
            -- In general position, G = faceFromHalfspaces (tightOnFace G)
            have G_from_tight : G = P.faceFromHalfspaces (P.tightOnFace G hG_face) :=
              face_eq_faceFromTightHalfspaces P h_gp G hG_face
            -- We also have G = faceFromHalfspaces G_halfspaces (from hG)
            -- So faceFromHalfspaces G_halfspaces = faceFromHalfspaces (tightOnFace G)
            have faces_eq : P.faceFromHalfspaces G_halfspaces =
                P.faceFromHalfspaces (P.tightOnFace G hG_face) := by
              calc P.faceFromHalfspaces G_halfspaces
                  = G := hG.symm
                _ = P.faceFromHalfspaces (P.tightOnFace G hG_face) := G_from_tight
            -- By injectivity of faceFromHalfspaces in general position,
            -- G_halfspaces = tightOnFace G
            apply faceFromHalfspaces_injective P h_gp
            · -- G_halfspaces ⊆ P.halfSpaces
              rw [hG_def]
              intro h hh
              rw [Finset.mem_union, Finset.mem_singleton] at hh
              cases hh with
              | inl h_in_F =>
                simp only [tightOnFace, Finset.mem_filter] at h_in_F
                exact h_in_F.1
              | inr h_eq =>
                rw [h_eq]
                have : h_extra ∈ P.tightOnFace H hH := (Finset.mem_sdiff.mp h_extra_in).1
                simp only [tightOnFace, Finset.mem_filter] at this
                exact this.1
            · -- tightOnFace P G hG_face ⊆ P.halfSpaces
              intro h hh
              simp only [tightOnFace, Finset.mem_filter] at hh
              exact hh.1
            · -- faceFromHalfspaces G_halfspaces is nonempty
              obtain ⟨h, h_supp, rfl⟩ := hG_face
              rw [← hG]
              exact h_supp.2
            · -- faceFromHalfspaces (tightOnFace G) is nonempty
              obtain ⟨h, h_supp, rfl⟩ := hG_face
              rw [← G_from_tight]
              exact h_supp.2
            · exact faces_eq
          rw [G_tight, tightOnFace_card_eq P h_gp G hG_face]
          have dim_le : P.faceDim G hG_face ≤ finrank ℝ E := face_dim_le_finrank P G hG_face
          omega
    _ = finrank ℝ E - ((P.tightOnFace F hF).card + 1) := by
          rw [card_G]
    _ = finrank ℝ E - ((finrank ℝ E - P.faceDim F hF) + 1) := by
          rw [tightOnFace_card_eq P h_gp F hF]
    _ = P.faceDim F hF - 1 := by
          have dim_le : P.faceDim F hF ≤ finrank ℝ E := face_dim_le_finrank P F hF
          omega
    _ = (P.faceDim H hH + 2) - 1 := by
          rw [← h_codim2]
    _ = P.faceDim H hH + 1 := by
          omega

/-- The key counting lemma: In general position, if H has codimension 2 in F,
    then there are exactly 2 halfspaces tight on H but not on F -/
lemma codim_two_halfspace_count (h_gp : P.InGeneralPosition)
    (F H : Set E) (hF : IsFace P F) (hH : IsFace P H)
    (h_sub : H ⊆ F) (h_codim2 : faceDim P H hH + 2 = faceDim P F hF) :
    (tightOnFace P H hH \ tightOnFace P F hF).card = 2 := by
  -- Strategy: Use the dimension formula to compute the count
  -- We know that dim(H) + count = dim(F) from tightOnFace_card_eq
  -- Rearranging gives us the count

  have h_H_card : (tightOnFace P H hH).card = finrank ℝ E - faceDim P H hH :=
    tightOnFace_card_eq P h_gp H hH
  have h_F_card : (tightOnFace P F hF).card = finrank ℝ E - faceDim P F hF :=
    tightOnFace_card_eq P h_gp F hF

  -- The halfspaces tight on H but not F can be computed as a difference
  have h_subset_tight : tightOnFace P F hF ⊆ tightOnFace P H hH :=
    tight_halfspaces_monotone P F H hF hH h_sub

  calc (tightOnFace P H hH \ tightOnFace P F hF).card
      = (tightOnFace P H hH).card - (tightOnFace P F hF).card := by
          exact Finset.card_sdiff_of_subset h_subset_tight
    _ = (finrank ℝ E - faceDim P H hH) - (finrank ℝ E - faceDim P F hF) := by
          rw [h_H_card, h_F_card]
    _ = faceDim P F hF - faceDim P H hH := by
          have h_F_le : P.faceDim F hF ≤ finrank ℝ E := face_dim_le_finrank P F hF
          have h_H_le : P.faceDim H hH ≤ finrank ℝ E := face_dim_le_finrank P H hH
          omega
    _ = (faceDim P H hH + 2) - faceDim P H hH := by
          rw [← h_codim2]
    _ = 2 := by omega

/-- General position implies the Diamond Property - this is the crucial theorem
    for proving boundary ∘ boundary = 0 -/
theorem general_position_implies_diamond (h_gp : P.InGeneralPosition) :
    P.HasDiamondProperty := by
  intros F H hF hH h_subset h_codim2

  -- The intermediate faces G are exactly those determined by:
  -- 1. All halfspaces tight on F (these ensure G ⊆ F)
  -- 2. All but one of the halfspaces tight on H but not F

  -- By codim_two_halfspace_count, there are exactly 2 such "extra" halfspaces
  have h_two : (tightOnFace P H hH \ tightOnFace P F hF).card = 2 :=
    codim_two_halfspace_count P h_gp F H hF hH h_subset h_codim2

  -- Each choice of leaving out one of these 2 halfspaces gives an intermediate face
  -- Therefore, there are exactly 2 intermediate faces

  -- Get the two extra halfspaces as a finite set of size 2
  let extra_halfspaces := tightOnFace P H hH \ tightOnFace P F hF

  -- By h_two, we know extra_halfspaces has exactly 2 elements
  obtain ⟨h₁, h₂, h_ne, h_set⟩ := Finset.card_eq_two.mp h_two

  -- Define the two intermediate faces G₁ and G₂
  -- G₁ uses all halfspaces tight on F plus h₁ (but not h₂)
  -- G₂ uses all halfspaces tight on F plus h₂ (but not h₁)
  let G₁_halfspaces := tightOnFace P F hF ∪ {h₁}
  let G₂_halfspaces := tightOnFace P F hF ∪ {h₂}

  -- The actual intermediate faces
  let G₁ := faceFromHalfspaces P G₁_halfspaces
  let G₂ := faceFromHalfspaces P G₂_halfspaces

  -- For the diamond property, we claim that the two intermediate faces are G₁ and G₂
  -- We'll prove existence first, then uniqueness

  -- First, establish the key facts about G₁ and G₂
  have hG₁_face : IsFace P G₁ := by
    apply faceFromHalfspaces_is_face
    · -- G₁_halfspaces ⊆ P.halfSpaces
      intro h hh
      rw [Finset.mem_union, Finset.mem_singleton] at hh
      cases hh with
      | inl h_in_F =>
        -- h ∈ tightOnFace P F hF, and tightOnFace P F hF ⊆ P.halfSpaces
        simp only [tightOnFace, Finset.mem_filter] at h_in_F
        exact h_in_F.1
      | inr h_eq =>
        rw [h_eq]
        -- h₁ ∈ tightOnFace P H hH \ tightOnFace P F hF
        have h₁_in : h₁ ∈ extra_halfspaces := by
          have : extra_halfspaces = {h₁, h₂} := h_set
          rw [this]
          exact Finset.mem_insert_self h₁ {h₂}
        have : h₁ ∈ tightOnFace P H hH := (Finset.mem_sdiff.mp h₁_in).1
        simp only [tightOnFace, Finset.mem_filter] at this
        exact this.1
    · -- G₁ is nonempty
      -- G₁_halfspaces = tightOnFace P F hF ∪ {h₁}
      -- We need to show there exists a point in P satisfying all these halfspaces with equality
      -- Key: tightOnFace P F hF ⊆ tightOnFace P H hH (by tight_halfspaces_monotone)
      -- And h₁ ∈ tightOnFace P H hH (shown above)
      -- So G₁_halfspaces ⊆ tightOnFace P H hH
      have G₁_sub : G₁_halfspaces ⊆ tightOnFace P H hH := by
        intro h hh
        rw [Finset.mem_union, Finset.mem_singleton] at hh
        cases hh with
        | inl h_in_F =>
          -- h ∈ tightOnFace P F hF, use monotonicity
          exact tight_halfspaces_monotone P F H hF hH h_subset h_in_F
        | inr h_eq =>
          -- h = h₁
          rw [h_eq]
          have h₁_in : h₁ ∈ extra_halfspaces := by
            have : extra_halfspaces = {h₁, h₂} := h_set
            rw [this]
            exact Finset.mem_insert_self h₁ {h₂}
          exact (Finset.mem_sdiff.mp h₁_in).1
      exact faceFromHalfspaces_nonempty P H hH G₁_halfspaces G₁_sub

  have hG₂_face : IsFace P G₂ := by
    apply faceFromHalfspaces_is_face
    · -- G₂_halfspaces ⊆ P.halfSpaces
      intro h hh
      rw [Finset.mem_union, Finset.mem_singleton] at hh
      cases hh with
      | inl h_in_F =>
        -- h ∈ tightOnFace P F hF, and tightOnFace P F hF ⊆ P.halfSpaces
        simp only [tightOnFace, Finset.mem_filter] at h_in_F
        exact h_in_F.1
      | inr h_eq =>
        rw [h_eq]
        -- h₂ ∈ tightOnFace P H hH \ tightOnFace P F hF
        have h₂_in : h₂ ∈ extra_halfspaces := by
          have : extra_halfspaces = {h₁, h₂} := h_set
          rw [this, Finset.mem_insert, Finset.mem_singleton]
          right; rfl
        have : h₂ ∈ tightOnFace P H hH := (Finset.mem_sdiff.mp h₂_in).1
        simp only [tightOnFace, Finset.mem_filter] at this
        exact this.1
    · -- G₂ is nonempty
      -- G₂_halfspaces = tightOnFace P F hF ∪ {h₂}
      -- Same reasoning as for G₁
      have G₂_sub : G₂_halfspaces ⊆ tightOnFace P H hH := by
        intro h hh
        rw [Finset.mem_union, Finset.mem_singleton] at hh
        cases hh with
        | inl h_in_F =>
          -- h ∈ tightOnFace P F hF, use monotonicity
          exact tight_halfspaces_monotone P F H hF hH h_subset h_in_F
        | inr h_eq =>
          -- h = h₂
          rw [h_eq]
          have h₂_in : h₂ ∈ extra_halfspaces := by
            have : extra_halfspaces = {h₁, h₂} := h_set
            rw [this, Finset.mem_insert, Finset.mem_singleton]
            right; rfl
          exact (Finset.mem_sdiff.mp h₂_in).1
      exact faceFromHalfspaces_nonempty P H hH G₂_halfspaces G₂_sub

  have hG₁_between : H ⊆ G₁ ∧ G₁ ⊆ F := by
    constructor
    · -- H ⊆ G₁
      -- Since G₁_halfspaces ⊆ tightOnFace P H hH, we have H ⊆ faceFromHalfspaces P G₁_halfspaces
      have G₁_sub : G₁_halfspaces ⊆ tightOnFace P H hH := by
        intro h hh
        rw [Finset.mem_union, Finset.mem_singleton] at hh
        cases hh with
        | inl h_in_F =>
          -- h ∈ tightOnFace P F hF, use monotonicity
          exact tight_halfspaces_monotone P F H hF hH h_subset h_in_F
        | inr h_eq =>
          -- h = h₁
          rw [h_eq]
          have h₁_in : h₁ ∈ extra_halfspaces := by
            have : extra_halfspaces = {h₁, h₂} := h_set
            rw [this]
            exact Finset.mem_insert_self h₁ {h₂}
          exact (Finset.mem_sdiff.mp h₁_in).1
      exact face_subset_faceFromHalfspaces P H hH G₁_halfspaces G₁_sub
    · -- G₁ ⊆ F
      -- In general position, F = faceFromHalfspaces P (tightOnFace P F hF)
      -- Since G₁ = faceFromHalfspaces P (tightOnFace P F hF ∪ {h₁}),
      -- and tightOnFace P F hF ⊆ tightOnFace P F hF ∪ {h₁},
      -- we have G₁ ⊆ faceFromHalfspaces P (tightOnFace P F hF) = F
      have F_eq : F = faceFromHalfspaces P (tightOnFace P F hF) :=
        face_eq_faceFromTightHalfspaces P h_gp F hF
      have F_sub : tightOnFace P F hF ⊆ G₁_halfspaces := Finset.subset_union_left
      rw [F_eq]
      exact faceFromHalfspaces_antimono P _ _ F_sub

  have hG₂_between : H ⊆ G₂ ∧ G₂ ⊆ F := by
    constructor
    · -- H ⊆ G₂
      -- Since G₂_halfspaces ⊆ tightOnFace P H hH, we have H ⊆ faceFromHalfspaces P G₂_halfspaces
      have G₂_sub : G₂_halfspaces ⊆ tightOnFace P H hH := by
        intro h hh
        rw [Finset.mem_union, Finset.mem_singleton] at hh
        cases hh with
        | inl h_in_F =>
          -- h ∈ tightOnFace P F hF, use monotonicity
          exact tight_halfspaces_monotone P F H hF hH h_subset h_in_F
        | inr h_eq =>
          -- h = h₂
          rw [h_eq]
          have h₂_in : h₂ ∈ extra_halfspaces := by
            have : extra_halfspaces = {h₁, h₂} := h_set
            rw [this, Finset.mem_insert, Finset.mem_singleton]
            right; rfl
          exact (Finset.mem_sdiff.mp h₂_in).1
      exact face_subset_faceFromHalfspaces P H hH G₂_halfspaces G₂_sub
    · -- G₂ ⊆ F
      -- Same reasoning as for G₁
      have F_eq : F = faceFromHalfspaces P (tightOnFace P F hF) :=
        face_eq_faceFromTightHalfspaces P h_gp F hF
      have F_sub : tightOnFace P F hF ⊆ G₂_halfspaces := Finset.subset_union_left
      rw [F_eq]
      exact faceFromHalfspaces_antimono P _ _ F_sub

  have hG₁_dim : faceDim P G₁ hG₁_face = faceDim P H hH + 1 := by
    have h₁_in : h₁ ∈ extra_halfspaces := by
      have : extra_halfspaces = {h₁, h₂} := h_set
      rw [this]
      exact Finset.mem_insert_self h₁ {h₂}
    exact intermediate_face_dim P h_gp F H hF hH h_subset h_codim2 h₁ h₁_in
      G₁_halfspaces rfl G₁ rfl hG₁_face

  have hG₂_dim : faceDim P G₂ hG₂_face = faceDim P H hH + 1 := by
    have h₂_in : h₂ ∈ extra_halfspaces := by
      have : extra_halfspaces = {h₁, h₂} := h_set
      rw [this, Finset.mem_insert, Finset.mem_singleton]
      right; rfl
    exact intermediate_face_dim P h_gp F H hF hH h_subset h_codim2 h₂ h₂_in
      G₂_halfspaces rfl G₂ rfl hG₂_face

  have hG₁_ne_G₂ : G₁ ≠ G₂ := by
    -- Proof by contradiction: if G₁ = G₂, then by faceFromHalfspaces_injective,
    -- G₁_halfspaces = G₂_halfspaces, which implies h₁ = h₂
    intro h_eq

    -- Apply faceFromHalfspaces_injective to conclude G₁_halfspaces = G₂_halfspaces
    have hs_eq : G₁_halfspaces = G₂_halfspaces := by
      apply faceFromHalfspaces_injective P h_gp G₁_halfspaces G₂_halfspaces
      · -- G₁_halfspaces ⊆ P.halfSpaces
        intro h hh
        rw [Finset.mem_union, Finset.mem_singleton] at hh
        cases hh with
        | inl h_in_F =>
          simp only [tightOnFace, Finset.mem_filter] at h_in_F
          exact h_in_F.1
        | inr h_eq =>
          rw [h_eq]
          have h₁_in : h₁ ∈ extra_halfspaces := by
            have : extra_halfspaces = {h₁, h₂} := h_set
            rw [this]; exact Finset.mem_insert_self h₁ {h₂}
          have : h₁ ∈ tightOnFace P H hH := (Finset.mem_sdiff.mp h₁_in).1
          simp only [tightOnFace, Finset.mem_filter] at this
          exact this.1
      · -- G₂_halfspaces ⊆ P.halfSpaces (similar)
        intro h hh
        rw [Finset.mem_union, Finset.mem_singleton] at hh
        cases hh with
        | inl h_in_F =>
          simp only [tightOnFace, Finset.mem_filter] at h_in_F
          exact h_in_F.1
        | inr h_eq =>
          rw [h_eq]
          have h₂_in : h₂ ∈ extra_halfspaces := by
            have : extra_halfspaces = {h₁, h₂} := h_set
            rw [this, Finset.mem_insert, Finset.mem_singleton]; right; rfl
          have : h₂ ∈ tightOnFace P H hH := (Finset.mem_sdiff.mp h₂_in).1
          simp only [tightOnFace, Finset.mem_filter] at this
          exact this.1
      · -- G₁ nonempty (H ⊆ G₁ from hG₁_between, and H is a face so nonempty)
        -- H is a face, so H = P.toSet ∩ h.boundary for some supporting h
        -- IsSupporting guarantees (P.toSet ∩ h.boundary).Nonempty
        obtain ⟨h, h_supp, rfl⟩ := hH
        obtain ⟨x, hx⟩ := h_supp.2
        exact ⟨x, hG₁_between.1 hx⟩
      · -- G₂ nonempty (similar)
        obtain ⟨h, h_supp, rfl⟩ := hH
        obtain ⟨x, hx⟩ := h_supp.2
        exact ⟨x, hG₂_between.1 hx⟩
      · exact h_eq

    -- Now G₁_halfspaces = tightOnFace P F hF ∪ {h₁}
    -- and G₂_halfspaces = tightOnFace P F hF ∪ {h₂}
    -- So tightOnFace P F hF ∪ {h₁} = tightOnFace P F hF ∪ {h₂}
    -- This implies {h₁} = {h₂}, hence h₁ = h₂
    have : ({h₁} : Finset (HalfSpace E)) = {h₂} := by
      have h₁_in : h₁ ∈ G₂_halfspaces := by
        rw [← hs_eq]; exact Finset.mem_union_right _ (Finset.mem_singleton_self h₁)
      have h₂_in : h₂ ∈ G₁_halfspaces := by
        rw [hs_eq]; exact Finset.mem_union_right _ (Finset.mem_singleton_self h₂)
      rw [Finset.mem_union, Finset.mem_singleton] at h₁_in h₂_in
      cases h₁_in with
      | inl h₁_in_F =>
        -- h₁ ∈ tightOnFace P F hF, but h₁ ∈ extra_halfspaces = ... \ tightOnFace P F hF
        have h₁_in_extra : h₁ ∈ extra_halfspaces := by
          have : extra_halfspaces = {h₁, h₂} := h_set
          rw [this]; exact Finset.mem_insert_self h₁ {h₂}
        have : h₁ ∉ tightOnFace P F hF := (Finset.mem_sdiff.mp h₁_in_extra).2
        contradiction
      | inr h₁_eq_h₂ =>
        cases h₂_in with
        | inl h₂_in_F =>
          have h₂_in_extra : h₂ ∈ extra_halfspaces := by
            have : extra_halfspaces = {h₁, h₂} := h_set
            rw [this, Finset.mem_insert, Finset.mem_singleton]; right; rfl
          have : h₂ ∉ tightOnFace P F hF := (Finset.mem_sdiff.mp h₂_in_extra).2
          contradiction
        | inr h₂_eq_h₁ =>
          -- h₁ = h₂ (from h₁_eq_h₂) and h₂ = h₁ (from h₂_eq_h₁)
          -- So {h₁} = {h₂}
          simp [h₁_eq_h₂]

    -- From {h₁} = {h₂}, we get h₁ = h₂
    have : h₁ = h₂ := Finset.singleton_inj.mp this
    exact h_ne this

  -- We can now construct the Diamond structure directly
  refine ⟨{
    F := F
    H := H
    G₁ := G₁
    G₂ := G₂
    hF := hF
    hH := hH
    hG₁ := hG₁_face
    hG₂ := hG₂_face
    h_sub := h_subset
    h_codim := h_codim2
    h_distinct := hG₁_ne_G₂
    h_between₁ := hG₁_between
    h_between₂ := hG₂_between
    h_dim₁ := hG₁_dim
    h_dim₂ := hG₂_dim
  }, rfl, rfl⟩

end MainTheorems

end HPolyhedron
