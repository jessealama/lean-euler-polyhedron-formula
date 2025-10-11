/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import ConvexPolyhedra.Polyhedron
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Grade
import Mathlib.Order.RelSeries
import Mathlib.Order.Cover

/-!
# Faces of Convex Polyhedra

This file defines faces of convex polyhedra using the V-representation.
A face is an exposed face: a subset obtained by maximizing a linear functional.

## Main definitions

* `ConvexPolyhedron.Face` - A face structure with supporting functional
* `ConvexPolyhedron.Face.toSet` - The underlying set of a face
* `ConvexPolyhedron.Face.dim` - Affine dimension of a face
* `ConvexPolyhedron.faces` - Faces of a given dimension
* `ConvexPolyhedron.incident` - Incidence relation between faces

## Main results

* `faces_finite` - Finitely many faces in each dimension (to be proven)
* Incidence properties: irreflexive, asymmetric

## Implementation notes

For V-representation, a face is characterized by a supporting hyperplane that achieves
its maximum on the polyhedron exactly at that face.

-/

open Set Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace ConvexPolyhedron

section Faces

/-- A face of a polyhedron is an exposed face: a subset obtained by maximizing a linear functional.

For V-representation, a face is characterized by a supporting hyperplane that achieves
its maximum on the polyhedron exactly at that face. -/
structure Face (P : ConvexPolyhedron E) where
  /-- The supporting linear functional defining this face -/
  support : E →L[ℝ] ℝ
  /-- The vertices of the polyhedron that maximize the supporting functional -/
  vertices : Finset E
  /-- These vertices are a subset of the polyhedron's vertices -/
  subset : vertices ⊆ P.vertices
  /-- These are exactly the vertices where the maximum is attained -/
  is_maximal : ∀ v ∈ P.vertices, v ∈ vertices ↔
    (∀ w ∈ P.vertices, support v ≥ support w)

namespace Face

variable {P : ConvexPolyhedron E}

/-- The underlying set of a face (convex hull of its vertices) -/
def toSet (F : Face P) : Set E :=
  convexHull ℝ (F.vertices : Set E)

/-- A face is convex -/
theorem convex (F : Face P) : Convex ℝ F.toSet :=
  convex_convexHull ℝ _

/-- A face is contained in the polyhedron -/
theorem subset_polyhedron (F : Face P) : F.toSet ⊆ (P : Set E) :=
  convexHull_mono (by exact_mod_cast F.subset)

/-- All vertices in a face achieve the same value under the supporting functional.
This is a direct consequence of is_maximal: each vertex in F.vertices maximizes
F.support over all of P.vertices, so they all achieve the maximum value. -/
theorem support_const_on_face_vertices (F : Face P) :
    ∀ v ∈ F.vertices, ∀ v' ∈ F.vertices, F.support v = F.support v' := by
  intro v hv v' hv'
  -- Both v and v' maximize F.support over P.vertices (by is_maximal)
  have hv_max : ∀ w ∈ P.vertices, F.support w ≤ F.support v := by
    intro w hw
    exact (F.is_maximal v (F.subset hv)).mp hv w hw
  have hv'_max : ∀ w ∈ P.vertices, F.support w ≤ F.support v' := by
    intro w hw
    exact (F.is_maximal v' (F.subset hv')).mp hv' w hw
  -- In particular, F.support v ≤ F.support v' and F.support v' ≤ F.support v
  have h1 : F.support v ≤ F.support v' := hv'_max v (F.subset hv)
  have h2 : F.support v' ≤ F.support v := hv_max v' (F.subset hv')
  exact le_antisymm h1 h2

/-- The supporting functional is constant on the face.
Since all vertices achieve the same value M, and the functional is linear,
all points in the convex hull also achieve M. -/
theorem support_const_on_face (F : Face P) (hne : F.vertices.Nonempty) :
    ∀ x ∈ F.toSet, ∀ v ∈ F.vertices, F.support x = F.support v := by
  intro x hx v hv
  -- Strategy: Use LinearMap.image_convexHull
  -- Since F.support is constant on F.vertices, F.support '' F.vertices = {M}
  -- So F.support '' convexHull F.vertices = convexHull {M} = {M}

  -- Get the constant value M that all vertices achieve
  obtain ⟨v₀, hv₀⟩ := hne

  -- All vertices achieve the same value as v₀
  have h_const : ∀ w ∈ F.vertices, F.support w = F.support v₀ :=
    fun w hw => F.support_const_on_face_vertices w hw v₀ hv₀

  -- Therefore (F.support : E → ℝ) '' F.vertices = {F.support v₀}
  have h_image : (F.support : E → ℝ) '' (F.vertices : Set E) = {F.support v₀} := by
    ext y
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact h_const w hw
    · intro hy
      use v₀, hv₀
      exact hy.symm

  -- Apply LinearMap.image_convexHull to get the image of the convex hull
  have h_hull : (F.support : E → ℝ) '' F.toSet = convexHull ℝ {F.support v₀} := by
    calc (F.support : E → ℝ) '' F.toSet
        = (F.support : E → ℝ) '' convexHull ℝ (F.vertices : Set E) := rfl
      _ = F.support.toLinearMap '' convexHull ℝ (F.vertices : Set E) := rfl
      _ = convexHull ℝ (F.support.toLinearMap '' (F.vertices : Set E)) :=
            F.support.toLinearMap.image_convexHull _
      _ = convexHull ℝ ((F.support : E → ℝ) '' (F.vertices : Set E)) := rfl
      _ = convexHull ℝ {F.support v₀} := by rw [h_image]

  -- convexHull of singleton is the singleton
  rw [convexHull_singleton] at h_hull

  -- Since x ∈ F.toSet, F.support x ∈ {F.support v₀}
  have hx_eq : F.support x = F.support v₀ := by
    -- F.support x ∈ (F.support : E → ℝ) '' F.toSet = {F.support v₀}
    have mem : F.support x ∈ (F.support : E → ℝ) '' F.toSet :=
      Set.mem_image_of_mem (F.support : E → ℝ) hx
    rw [h_hull] at mem
    -- Now mem : F.support x ∈ {F.support v₀}
    exact Set.mem_singleton_iff.mp mem

  -- And F.support v = F.support v₀ (since all vertices achieve the same value)
  calc F.support x
      = F.support v₀ := hx_eq
    _ = F.support v := (h_const v hv).symm

/-- Weighted average lemma: If a weighted sum of values equals an upper bound M,
and all values are ≤ M, then all values with positive weight must equal M.

This is a key technical lemma for proving the reverse direction of isExposed. -/
lemma weighted_sum_eq_max_of_le {ι : Type*} (s : Finset ι) (w : ι → ℝ) (a : ι → ℝ) (M : ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : ∑ i ∈ s, w i = 1)
    (ha_le : ∀ i ∈ s, a i ≤ M)
    (h_sum_eq : ∑ i ∈ s, w i * a i = M) :
    ∀ i ∈ s, w i > 0 → a i = M := by
  intro i hi hwi_pos
  -- Proof by contradiction
  by_contra h_ne
  -- If a i < M (since a i ≤ M and a i ≠ M)
  have hai_lt : a i < M := by
    exact lt_of_le_of_ne (ha_le i hi) h_ne
  -- Then the weighted sum is strictly less than M
  have : ∑ j ∈  s, w j * a j < M := by
    calc ∑ j ∈  s, w j * a j
        < ∑ j ∈  s, w j * M := by
            -- Apply strict inequality for the sum
            apply Finset.sum_lt_sum
            · -- All terms ≤ bound
              intro j hj
              exact mul_le_mul_of_nonneg_left (ha_le j hj) (hw_nonneg j hj)
            · -- Strict inequality for at least one term
              use i, hi
              exact mul_lt_mul_of_pos_left hai_lt hwi_pos
      _ = (∑ j ∈  s, w j) * M := by rw [← Finset.sum_mul]
      _ = 1 * M := by rw [hw_sum]
      _ = M := one_mul M
  -- But this contradicts h_sum_eq
  linarith

/-- Every face of a polytope is an exposed face.

This connects our `Face` structure to Mathlib's `IsExposed` predicate from
`Analysis.Convex.Exposed`. Our Face structure is defined to be exposed by
construction (via the supporting functional), but this theorem makes the
connection explicit.

The key insight: For polytopes (convex hull of finitely many points), every
face is exposed. This is a fundamental theorem in polytope theory that
distinguishes polytopes from general convex sets, where faces may exist that
are not exposed.

This theorem is crucial for leveraging Mathlib's exposed face theory in our
proofs. -/
theorem isExposed (F : Face P) : IsExposed ℝ (P : Set E) F.toSet := by
  -- IsExposed requires: B.Nonempty → ∃ l, B = {x | x ∈ A ∧ ∀ y ∈ A, l y ≤ l x}
  intro h_nonempty
  use F.support
  -- Need to show: F.toSet = {x | x ∈ P ∧ ∀ y ∈ P, F.support y ≤ F.support x}
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · -- Forward direction: x ∈ F.toSet → x ∈ P ∧ x maximizes F.support
    intro hx
    constructor
    · -- x ∈ P follows from F.toSet ⊆ P
      exact F.subset_polyhedron hx
    · -- x maximizes F.support over P
      intro y hy
      -- KEY INSIGHT: By analyzing the Face definition, we discovered that is_maximal
      -- implies all vertices in F.vertices achieve the SAME value M.
      -- This dramatically simplifies the proof!

      -- Get nonemptiness of F.vertices from h_nonempty
      have hF_nonempty : F.vertices.Nonempty := by
        -- If F.vertices were empty, then F.toSet = convexHull ∅ = ∅
        by_contra hempty
        simp only [Finset.not_nonempty_iff_eq_empty] at hempty
        have : F.toSet = ∅ := by
          rw [Face.toSet, hempty]
          simp only [Finset.coe_empty, convexHull_empty]
        rw [this] at h_nonempty
        exact Set.not_nonempty_empty h_nonempty

      -- Get a vertex to establish the maximum value M
      obtain ⟨v, hv⟩ := hF_nonempty

      -- By support_const_on_face, F.support x = F.support v = M
      have hx_eq : F.support x = F.support v :=
        F.support_const_on_face ⟨v, hv⟩ x hx v hv

      -- By is_maximal, v maximizes over P.vertices
      have hv_max : ∀ w ∈ P.vertices, F.support w ≤ F.support v := by
        exact (F.is_maximal v (F.subset hv)).mp hv

      -- The key: linear functionals on convex hulls are bounded by max on vertices
      -- Since y ∈ convexHull P.vertices and v maximizes over P.vertices,
      -- we have F.support y ≤ F.support v = F.support x
      calc F.support y
          ≤ F.support v := by
              -- KEY: Linear maps are convex functions, so the max on convexHull
              -- equals max on vertices. Use ConvexOn.le_sup_of_mem_convexHull to
              -- show F.support y ≤ sup (F.support on P.vertices)

              -- y ∈ P means y ∈ convexHull P.vertices (by the SetLike instance)
              have hy_hull : y ∈ convexHull ℝ (P.vertices : Set E) := hy

              -- Linear maps are convex on any convex set
              have h_convex : ConvexOn ℝ Set.univ F.support.toLinearMap :=
                F.support.toLinearMap.convexOn convex_univ

              -- Apply ConvexOn.le_sup_of_mem_convexHull
              have h_le_sup := h_convex.le_sup_of_mem_convexHull
                (Set.subset_univ _) hy_hull

              -- P.vertices is nonempty (from P.nonempty)
              have hP_nonempty : P.vertices.Nonempty := P.nonempty

              calc F.support y
                  ≤ P.vertices.sup' hP_nonempty F.support.toLinearMap := h_le_sup
                _ = F.support v := by
                    -- Show equality by antisymmetry
                    apply le_antisymm
                    · -- sup' ≤ F.support v: all vertices ≤ F.support v
                      apply Finset.sup'_le
                      intro w hw
                      exact hv_max w hw
                    · -- F.support v ≤ sup': v is one of the vertices
                      apply Finset.le_sup'
                      exact F.subset hv
        _ = F.support x := hx_eq.symm
  · -- Reverse direction: x ∈ P and x maximizes F.support → x ∈ F.toSet
    intro ⟨hx_in_P, hx_max⟩
    -- KEY INSIGHT: Combined with support_const_on_face_vertices, the maximality
    -- condition forces x to be in convexHull F.vertices.

    -- DETAILED PROOF STRATEGY:
    --
    -- Goal: Show x ∈ convexHull ℝ (F.vertices : Set E)
    --
    -- What we have:
    -- - x ∈ P, so x ∈ convexHull ℝ (P.vertices : Set E)
    -- - hx_max : ∀ y ∈ P, F.support y ≤ F.support x  (x maximizes F.support)
    --
    -- Step 1: Express x as convex combination of P.vertices
    --   Use: mem_convexHull or convexHull_eq to write
    --        x = Σᵢ λᵢ vᵢ where vᵢ ∈ P.vertices, λᵢ ≥ 0, Σᵢ λᵢ = 1
    --
    -- Step 2: Apply linearity of F.support
    --   F.support x = F.support (Σᵢ λᵢ vᵢ)
    --               = Σᵢ λᵢ (F.support vᵢ)  (ContinuousLinearMap.map_sum)
    --
    -- Step 3: Each vertex satisfies F.support vᵢ ≤ F.support x
    --   Since vᵢ ∈ P.vertices ⊆ P, we have F.support vᵢ ≤ F.support x (by hx_max)
    --
    -- Step 4: If weighted average equals upper bound, all terms must equal bound
    --   KEY LEMMA NEEDED: If aᵢ ≤ M for all i, λᵢ ≥ 0, Σᵢ λᵢ = 1,
    --   and Σᵢ λᵢ aᵢ = M, then aᵢ = M whenever λᵢ > 0
    --
    --   Apply this with aᵢ = F.support vᵢ, M = F.support x:
    --   For all i with λᵢ > 0, we have F.support vᵢ = F.support x
    --
    -- Step 5: Maximizing vertices are exactly F.vertices
    --   If F.support vᵢ = F.support x, then vᵢ maximizes F.support over P.vertices
    --   By is_maximal (reverse direction), vᵢ ∈ F.vertices
    --
    -- Step 6: x is convex combination of F.vertices
    --   Filter the sum to only include vertices with λᵢ > 0
    --   All such vertices are in F.vertices (from Step 5)
    --   Therefore x ∈ convexHull ℝ (F.vertices : Set E)
    --
    -- MATHLIB LEMMAS TO SEARCH FOR:
    -- - mem_convexHull or finsum characterization
    -- - Weighted average lemma (Step 4) - may need to prove ourselves
    -- - F.support.map_sum for linearity over finite sums
    --
    -- POTENTIAL CHALLENGES:
    -- - The weighted average lemma (Step 4) is the key technical piece
    -- - May need to work with Finsupp or explicit finite sums

    -- Step 1: Express x as convex combination of P.vertices
    have hx_hull : x ∈ convexHull ℝ (P.vertices : Set E) := hx_in_P
    rw [Finset.mem_convexHull'] at hx_hull
    obtain ⟨w, hw_nonneg, hw_sum, hx_eq⟩ := hx_hull

    -- Step 2: Apply linearity of F.support
    have h_linear : F.support x = ∑ v ∈ P.vertices, w v * F.support v := by
      calc F.support x
          = F.support (∑ v ∈ P.vertices, w v • v) := by rw [hx_eq]
        _ = ∑ v ∈ P.vertices, F.support (w v • v) := by rw [map_sum]
        _ = ∑ v ∈ P.vertices, w v * F.support v := by
            congr 1
            ext v
            rw [F.support.map_smul]
            rfl

    -- Step 3: Each vertex satisfies F.support v ≤ F.support x
    have hv_le : ∀ v ∈ P.vertices, F.support v ≤ F.support x := by
      intro v hv
      have : v ∈ (P : Set E) := subset_convexHull ℝ _ hv
      exact hx_max v this

    -- Step 4: Apply weighted average lemma
    have hv_eq : ∀ v ∈ P.vertices, w v > 0 → F.support v = F.support x := by
      intro v hv hwv_pos
      exact weighted_sum_eq_max_of_le P.vertices w (fun v => F.support v) (F.support x)
        hw_nonneg hw_sum hv_le h_linear.symm v hv hwv_pos

    -- Step 5: Maximizing vertices are in F.vertices
    have hv_in_F : ∀ v ∈ P.vertices, w v > 0 → v ∈ F.vertices := by
      intro v hv hwv_pos
      have hv_max : ∀ u ∈ P.vertices, F.support u ≤ F.support v := by
        intro u hu
        calc F.support u
            ≤ F.support x := hv_le u hu
          _ = F.support v := (hv_eq v hv hwv_pos).symm
      exact (F.is_maximal v hv).mpr hv_max

    -- Step 6: x is convex combination of F.vertices
    rw [Face.toSet, Finset.mem_convexHull']
    use w
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      exact hw_nonneg v (F.subset hv)
    · -- Sum of weights on F.vertices equals 1
      have h_sum : ∑ y ∈ F.vertices, w y = ∑ y ∈ P.vertices, w y := by
        apply Finset.sum_subset F.subset
        intro v hv_P hv_not_F
        have : ¬(w v > 0) := fun h_pos => hv_not_F (hv_in_F v hv_P h_pos)
        push_neg at this
        exact le_antisymm this (hw_nonneg v hv_P)
      rw [h_sum, hw_sum]
    · -- Sum of weighted points on F.vertices equals x
      have h_sum : ∑ y ∈ F.vertices, w y • y = ∑ y ∈ P.vertices, w y • y := by
        apply Finset.sum_subset F.subset
        intro v hv_P hv_not_F
        have : ¬(w v > 0) := fun h_pos => hv_not_F (hv_in_F v hv_P h_pos)
        push_neg at this
        have : w v = 0 := le_antisymm this (hw_nonneg v hv_P)
        simp [this]
      rw [h_sum, hx_eq]

/-- The affine dimension of a face -/
noncomputable def dim (F : Face P) : ℤ :=
  affineDim ℝ F.toSet

/-- Two faces are incident if one is contained in the other -/
def incident (F G : Face P) : Prop :=
  F.toSet ⊆ G.toSet ∨ G.toSet ⊆ F.toSet

end Face

/-- Faces of a given dimension -/
def faces (P : ConvexPolyhedron E) (k : ℕ) : Set (Face P) :=
  {F : Face P | F.dim = k}

/-- Simplified incidence relation: F is incident to G if F is a facet of G.
This is the relation we use in the boundary map: for each k-face G, we sum over
all (k-1)-faces F that are incident to it.

Note: This is directional - F is incident to G means F ⊆ G and dim F = dim G - 1. -/
noncomputable def incident (P : ConvexPolyhedron E) (F G : Face P) : Bool :=
  -- Check if F is a proper face of G with dimension exactly one less
  (F.dim + 1 == G.dim) && @decide (F.toSet ⊆ G.toSet) (Classical.dec _)

/-- Incidence is true iff the dimension condition holds and F ⊆ G -/
theorem incident_iff (P : ConvexPolyhedron E) (F G : Face P) :
    P.incident F G ↔ (F.dim + 1 = G.dim ∧ F.toSet ⊆ G.toSet) := by
  unfold incident
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1, @of_decide_eq_true (F.toSet ⊆ G.toSet) (Classical.dec _) h2⟩
  · intro ⟨h1, h2⟩
    exact ⟨h1, @decide_eq_true (F.toSet ⊆ G.toSet) (Classical.dec _) h2⟩

/-- If F is incident to G, then F ⊆ G -/
theorem incident_subset (P : ConvexPolyhedron E) {F G : Face P} (h : P.incident F G) :
    F.toSet ⊆ G.toSet := by
  rw [incident_iff] at h
  exact h.2

/-- If F is incident to G, then dim F = dim G - 1 -/
theorem incident_dim (P : ConvexPolyhedron E) {F G : Face P} (h : P.incident F G) :
    F.dim + 1 = G.dim := by
  rw [incident_iff] at h
  exact h.1

/-- Incidence is irreflexive: a face is not incident to itself -/
theorem incident_irrefl (P : ConvexPolyhedron E) (F : Face P) :
    ¬P.incident F F := by
  intro h
  have := incident_dim P h
  omega

/-- Incidence is asymmetric: if F is incident to G, then G is not incident to F -/
theorem incident_asymm (P : ConvexPolyhedron E) {F G : Face P}
    (h : P.incident F G) : ¬P.incident G F := by
  intro h'
  have hFG := incident_dim P h
  have hGF := incident_dim P h'
  omega

/-- The k-dimensional faces form a finite set (key theorem).

## Proof Strategy

Each face is determined by which subset of vertices maximizes a linear functional.
Since P.vertices is finite, there are only finitely many possible vertex subsets.

## What's Needed for Complete Proof

1. **Face lattice theory**: Faces of a convex polytope form a finite lattice
2. **Counting argument**: For each dimension k, only finitely many vertex subsets
   can form k-dimensional faces (bounded by affine independence constraints)
3. **Exposed face finiteness**: Mathlib may have results about finite face structures
   for polytopes (see `Mathlib.Analysis.Convex.Exposed`)

## Current Status

This is left as sorry for now. The geometric fact is standard: a polytope defined as
the convex hull of finitely many points has finitely many faces of each dimension.
The full formalization would benefit from:
- Connecting to Mathlib's exposed face theory
- Developing face lattice structure
- Using combinatorial bounds on faces (e.g., upper bound theorem) -/
theorem faces_finite (P : ConvexPolyhedron E) (k : ℕ) : (P.faces k).Finite := by
  sorry

/-- Incidence relation: a (k-1)-face is on the boundary of a k-face -/
def incidentFaces (P : ConvexPolyhedron E) (k : ℕ) (F : Face P) (G : Face P) : Prop :=
  F.dim = k - 1 ∧ G.dim = k ∧ F.toSet ⊆ G.toSet

/-- Decidable instance for face incidence (for computation).
This requires checking dimension equality and set containment.
For now, we use Classical.dec since the full decidability proof is complex. -/
noncomputable instance (P : ConvexPolyhedron E) (k : ℕ) (F G : Face P) :
    Decidable (incidentFaces P k F G) :=
  Classical.dec _

end Faces

end ConvexPolyhedron
