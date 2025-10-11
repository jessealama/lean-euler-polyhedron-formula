/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import ConvexPolyhedra.Face

/-!
# Face Lattice Theory for Convex Polyhedra

This file develops the theory of face lattices for convex polyhedra, proving that:
1. Geometric faces form a lattice under the subset relation
2. The lattice is graded by affine dimension
3. Intermediate faces exist between any two faces with a dimension gap

## Main theorems

* `exists_intermediate_exposed_face` - Between any two exposed faces with dimension gap ≥ 2,
  there exists an intermediate exposed face
* `face_lattice_is_graded` - The face lattice is graded by dimension
* `exists_incident_face_below` - Every proper face has an incident face one dimension higher

## Implementation notes

We work with `GeometricFace P` rather than `Face P` to avoid non-uniqueness issues.
The `Face` structure includes a supporting functional field, allowing infinitely many
Face values to represent the same geometric face. `GeometricFace` quotients out this
choice, giving canonical representatives.

For example, a square's top edge can be represented by Face structures with functionals
φ₁(x,y) = y or φ₂(x,y) = 2y, but there is only one GeometricFace for this edge.

## References

* Ziegler, "Lectures on Polytopes", Chapter 2
* Grünbaum, "Convex Polytopes"
-/

open Set Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace ConvexPolyhedron

/-!
### Lattice Structure Theorems

These theorems establish that geometric faces form a graded lattice.
-/

/-- If A and B are geometric faces of a convex polyhedron with A ⊂ B and a dimension gap ≥ 2,
then there exists an intermediate geometric face C with A ⊂ C ⊆ B and dim C = dim A + 1.

This is a fundamental theorem about the structure of face lattices of polytopes.
It says that you can always "step up" one dimension at a time through exposed faces.

Note: This theorem is now well-defined because GeometricFace has canonical representatives.
The old version using Face P was ill-defined due to non-unique supporting functionals. -/
theorem exists_intermediate_geometric_face {P : ConvexPolyhedron E}
    {A B : GeometricFace P}
    (hAB_proper : A < B)
    (hdim_gap : A.dim + 2 ≤ B.dim) :
    ∃ C : GeometricFace P,
      A < C ∧
      C ≤ B ∧
      C.dim = A.dim + 1 := by
  sorry

/-- If F and G are geometric faces with F ⊂ G and dim F < dim G, then there exists
a vertex v in G that is not in the affine span of F.

This is a key lemma for constructing intermediate faces. -/
theorem exists_vertex_not_in_affineSpan {P : ConvexPolyhedron E}
    {F G : GeometricFace P}
    (hFG : F < G)
    (hdim : F.dim < G.dim) :
    ∃ v ∈ G.toSet ∩ (P.vertices : Set E), v ∉ affineSpan ℝ F.toSet := by
  sorry

/-- Given a vertex v in geometric face G but not in the affine span of face F,
there exists a geometric face H containing F and v with dimension exactly dim F + 1.

Note: This is now well-defined because it returns a GeometricFace, not a Face.
The old version was problematic because the choice of supporting functional for H
was not canonical. -/
theorem exists_geometric_face_extending_by_vertex {P : ConvexPolyhedron E}
    {F G : GeometricFace P}
    (hFG : F < G)
    (v : E)
    (hv_in_G : v ∈ G.toSet)
    (hv_vertex : v ∈ (P.vertices : Set E))
    (hv_not_in_F : v ∉ affineSpan ℝ F.toSet) :
    ∃ H : GeometricFace P,
      F < H ∧
      H ≤ G ∧
      v ∈ H.toSet ∧
      H.dim = F.dim + 1 := by
  sorry

/-!
### Finiteness and Computability

Geometric faces are finite in each dimension.
-/

/-- The set of geometric k-dimensional faces is finite.

This uses the fact that geometric faces correspond bijectively to subsets of vertices,
and the powerset of P.vertices is finite. -/
theorem geometric_k_faces_finite (P : ConvexPolyhedron E) (k : ℤ) :
    {F : GeometricFace P | F.dim = k}.Finite := by
  -- Use the fact that the underlying sets are finite
  have h_sets_finite := geometric_faces_finite P k
  -- We need to show that {F : GeometricFace P | F.dim = k} is finite
  -- This set injects into {s : Set E | ∃ F : Face P, F.dim = k ∧ s = F.toSet}
  -- via the map F ↦ F.toSet
  sorry

/-!
### Incidence Relations

Incidence between geometric faces is well-defined and matches geometric intuition.
-/

/-- Two geometric faces are incident if one is a facet of the other.
This means F ⊆ G and dim F = dim G - 1. -/
def geometricIncident (P : ConvexPolyhedron E) (F G : GeometricFace P) : Prop :=
  F < G ∧ F.dim + 1 = G.dim

omit [FiniteDimensional ℝ E] in
/-- Incidence is irreflexive -/
theorem geometric_incident_irrefl (P : ConvexPolyhedron E) (F : GeometricFace P) :
    ¬geometricIncident P F F := by
  intro ⟨h_lt, _⟩
  exact lt_irrefl _ h_lt

omit [FiniteDimensional ℝ E] in
/-- Incidence is asymmetric -/
theorem geometric_incident_asymm (P : ConvexPolyhedron E) {F G : GeometricFace P}
    (h : geometricIncident P F G) : ¬geometricIncident P G F := by
  intro ⟨_, h_dim⟩
  have := h.2
  omega

/-!
### Diamond Property

The diamond property states that in a graded poset, if F covers G (is one dimension higher),
then there is a unique way to "connect" them through the lattice.

For geometric faces, this is well-defined because GeometricFace has canonical representatives.
The old Face-based approach was problematic because Face.eq_of_toSet_eq was false.
-/

omit [FiniteDimensional ℝ E] in
/-- If F and G are geometric faces with F < G and dim F + 1 = dim G,
then F is a facet of G (this is just the definition of geometric incidence). -/
theorem facet_characterization {P : ConvexPolyhedron E} {F G : GeometricFace P}
    (h_strict : F < G) (h_dim : F.dim + 1 = G.dim) :
    geometricIncident P F G :=
  ⟨h_strict, h_dim⟩

/-!
### Bridge Lemmas Between Face and GeometricFace

These lemmas connect the witness structure (Face) to the canonical geometric objects.
-/

omit [FiniteDimensional ℝ E] in
/-- If F ≤ G as geometric faces, and we have Face witnesses F' and G',
then F'.toSet ⊆ G'.toSet. -/
theorem face_witnesses_preserve_order {P : ConvexPolyhedron E}
    {F G : GeometricFace P}
    (hFG : F ≤ G)
    (F' : Face P) (hF' : F'.toSet = F.toSet)
    (G' : Face P) (hG' : G'.toSet = G.toSet) :
    F'.toSet ⊆ G'.toSet := by
  rw [hF', hG']
  exact hFG

end ConvexPolyhedron
