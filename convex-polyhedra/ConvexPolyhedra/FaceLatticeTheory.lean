/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import ConvexPolyhedra.VRepresentation

/-!
# Face Lattice Theory for Convex Polyhedra

This file develops the theory of face lattices for convex polyhedra, proving that:
1. Faces form a lattice under the subset relation
2. The lattice is graded by affine dimension
3. Intermediate faces exist between any two faces with a dimension gap

## Main theorems

* `exists_intermediate_exposed_face` - Between any two exposed faces with dimension gap ≥ 2,
  there exists an intermediate exposed face
* `face_lattice_is_graded` - The face lattice is graded by dimension
* `exists_incident_face_below` - Every proper face has an incident face one dimension higher

## References

* Ziegler, "Lectures on Polytopes", Chapter 2
* Grünbaum, "Convex Polytopes"
-/

open Set Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace ConvexPolyhedron

/-!
### Key Helper Lemmas

These are the fundamental results we need about exposed faces and dimension.
-/

/-- If A and B are exposed faces of a convex set P with A ⊂ B and a dimension gap ≥ 2,
then there exists an intermediate exposed face C with A ⊂ C ⊆ B and dim C = dim A + 1.

This is a fundamental theorem about the structure of face lattices of polytopes.
It says that you can always "step up" one dimension at a time through exposed faces. -/
theorem exists_intermediate_exposed_face {P : ConvexPolyhedron E}
    {A B : Set E}
    (hA_exposed : IsExposed ℝ (P : Set E) A)
    (hB_exposed : IsExposed ℝ (P : Set E) B)
    (hAB_proper : A ⊂ B)
    (hdim_gap : affineDim ℝ A + 2 ≤ affineDim ℝ B) :
    ∃ C : Set E,
      IsExposed ℝ (P : Set E) C ∧
      A ⊂ C ∧
      C ⊆ B ∧
      affineDim ℝ C = affineDim ℝ A + 1 := by
  sorry

/-- Two faces are equal if they have the same underlying set.
This is fundamental for showing the face structure is determined by geometry. -/
theorem Face.eq_of_toSet_eq {P : ConvexPolyhedron E} {F G : Face P}
    (h : F.toSet = G.toSet) : F = G := by
  sorry

/-- If F ≤ G (F.toSet ⊆ G.toSet), then F.vertices ⊆ G.vertices.
This connects the partial order on faces to vertex inclusion. -/
theorem vertices_subset_of_face_subset {P : ConvexPolyhedron E} {F G : Face P}
    (h : F ≤ G) : F.vertices ⊆ G.vertices := by
  intro v hv
  -- v ∈ F.vertices, need to show v ∈ G.vertices
  -- Key idea: v is an extreme point of P, and v ∈ G.toSet
  -- Since G.toSet = convexHull ℝ G.vertices and G.vertices are extreme points,
  -- v must be in G.vertices

  -- v is in F.toSet
  have hv_in_F : v ∈ F.toSet := by
    show v ∈ convexHull ℝ (F.vertices : Set E)
    exact subset_convexHull ℝ _ hv

  -- F.toSet ⊆ G.toSet, so v ∈ G.toSet
  have hv_in_G : v ∈ G.toSet := h hv_in_F

  -- v ∈ P.vertices (since F.vertices ⊆ P.vertices)
  have hv_in_P : v ∈ P.vertices := F.subset hv

  -- v is an extreme point of P
  have hv_extreme : v ∈ P.extremePointsSet := by
    rw [ConvexPolyhedron.extremePoints_eq_vertices]
    exact hv_in_P

  -- G.toSet = convexHull ℝ G.vertices
  have hG_hull : G.toSet = convexHull ℝ (G.vertices : Set E) := rfl

  -- v ∈ convexHull ℝ G.vertices
  rw [hG_hull] at hv_in_G

  -- Now we use: if v is extreme in P and v ∈ convexHull G.vertices,
  -- where G.vertices ⊆ P.vertices are also extreme in P,
  -- then v ∈ G.vertices

  -- This requires showing that extreme points in convex hulls of extreme points
  -- are in the generating set
  sorry

/-- If F.vertices ⊆ G.vertices, then F ≤ G (F.toSet ⊆ G.toSet).
Converse of vertices_subset_of_face_subset. -/
theorem face_subset_of_vertices_subset {P : ConvexPolyhedron E} {F G : Face P}
    (h : F.vertices ⊆ G.vertices) : F ≤ G := by
  -- The convex hull of a subset is contained in the convex hull of the superset
  exact convexHull_mono (by exact_mod_cast h)

/-- Given a vertex v in a face G but not in the affine span of face F,
there exists a face H containing F and v with dimension exactly dim F + 1. -/
theorem exists_face_extending_by_vertex {P : ConvexPolyhedron E} {F G : Face P}
    (hFG : F < G)
    (v : E) (hv_in_G : v ∈ G.vertices)
    (hv_not_in_F : v ∉ affineSpan ℝ (F.vertices : Set E)) :
    ∃ H : Face P,
      F < H ∧
      H ≤ G ∧
      v ∈ H.vertices ∧
      affineDim ℝ (convexHull ℝ (H.vertices : Set E)) = affineDim ℝ (convexHull ℝ (F.vertices : Set E)) + 1 := by
  sorry

/-- If F and G are faces with F ⊂ G and dim F < dim G, then there exists
a vertex v ∈ G.vertices such that v ∉ affineSpan F.vertices. -/
theorem exists_vertex_not_in_affineSpan {P : ConvexPolyhedron E} {F G : Face P}
    (hFG : F < G) (hdim : F.dim < G.dim) :
    ∃ v ∈ G.vertices, v ∉ affineSpan ℝ (F.vertices : Set E) := by
  sorry

end ConvexPolyhedron
