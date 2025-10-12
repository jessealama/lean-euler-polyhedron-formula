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

This file develops the minimal theory needed for the diamond property of geometric faces.

## Main theorem

* `geometric_diamond_property` - Between any two geometric faces F < G with
  dim(G) = dim(F) + 2, there are exactly 2 intermediate geometric faces
  (needed for ∂² = 0 in chain complex)

## Supporting lemmas

* `geometric_dim_lt_of_ssubset` - Strict containment implies strict dimension increase
* `exists_intermediate_geometric_face` - Existence of intermediate geometric faces

## Implementation notes

We work with `GeometricFace P` rather than `Face P` to avoid non-uniqueness issues.
The `Face` structure includes a supporting functional field, allowing infinitely many
Face values to represent the same geometric face. `GeometricFace` quotients out this
choice, giving canonical representatives.

For example, a square's top edge can be represented by Face structures with functionals
φ₁(x,y) = y or φ₂(x,y) = 2y, but there is only one GeometricFace for this edge.

This canonical representation is essential for the diamond property: we need to count
intermediate faces, which requires meaningful equality.

## References

* Ziegler, "Lectures on Polytopes", Chapter 2
* Grünbaum, "Convex Polytopes"
-/

open Set Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace ConvexPolyhedron

/-!
### Lattice Structure

Geometric faces form a partial order (and later a lattice) under set inclusion.
-/

/-- Partial order on geometric faces by set inclusion.

This is well-defined because GeometricFace provides canonical representatives:
two geometric faces are equal iff their underlying sets are equal. -/
instance {P : ConvexPolyhedron E} : PartialOrder (GeometricFace P) where
  le F G := F.toSet ⊆ G.toSet
  le_refl F := Set.Subset.rfl
  le_trans F G H := Set.Subset.trans
  le_antisymm F G hFG hGF := by
    have : F.val = G.val := Set.Subset.antisymm hFG hGF
    exact Subtype.ext this

/-!
### Basic Dimension Properties

These establish that dimension is monotone with respect to face containment.
-/

/-- If F ⊂ G (strict containment), then dim F < dim G -/
theorem geometric_dim_lt_of_ssubset {P : ConvexPolyhedron E} {F G : GeometricFace P}
    (h : F < G) : F.dim < G.dim := by
  sorry

/-!
### Intermediate Face Existence

The key geometric construction showing that we can find faces of intermediate dimension.
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

/-- If F and G are geometric faces with F ⊂ G and dim F < dim G, then there exists
a vertex v in G that is not in the affine span of F.

This is a key lemma for constructing intermediate faces. -/
theorem exists_vertex_not_in_affineSpan {P : ConvexPolyhedron E}
    {F G : GeometricFace P}
    (_hFG : F < G)
    (hdim : F.dim < G.dim) :
    ∃ v ∈ G.toSet ∩ (P.vertices : Set E), v ∉ affineSpan ℝ F.toSet := by
  -- Proof by contradiction
  by_contra h
  push_neg at h
  -- h : ∀ v ∈ G.toSet ∩ P.vertices, v ∈ affineSpan ℝ F.toSet

  -- Key claim: G.toSet ⊆ affineSpan ℝ F.toSet
  have h_subset : G.toSet ⊆ affineSpan ℝ F.toSet := by
    -- Get a Face witness for G
    obtain ⟨G_face, hG_face⟩ := GeometricFace.exists_face_witness G
    -- G.toSet is the convex hull of G_face.vertices
    have hG_conv : G.toSet = convexHull ℝ (G_face.vertices : Set E) := by
      rw [← hG_face, Face.toSet]
    -- All vertices of G_face are in G.toSet ∩ P.vertices
    have hG_verts_in : (G_face.vertices : Set E) ⊆ G.toSet ∩ (P.vertices : Set E) := by
      intro v hv
      constructor
      · rw [hG_conv]
        exact subset_convexHull ℝ _ hv
      · exact G_face.subset hv
    -- By hypothesis h, all these vertices are in affineSpan ℝ F.toSet
    have hG_verts_span : (G_face.vertices : Set E) ⊆ affineSpan ℝ F.toSet := by
      intro v hv
      exact h v (hG_verts_in hv)
    -- convexHull of vertices ⊆ affineSpan of vertices ⊆ affineSpan of F
    calc G.toSet
        = convexHull ℝ (G_face.vertices : Set E) := hG_conv
      _ ⊆ affineSpan ℝ (G_face.vertices : Set E) := convexHull_subset_affineSpan _
      _ ⊆ affineSpan ℝ F.toSet := by
          -- Use affineSpan_le: if s ⊆ affine subspace S, then affineSpan s ≤ S
          exact (affineSpan_le.mpr hG_verts_span : _)

  -- F.toSet ⊆ affineSpan ℝ F.toSet (basic property)
  have hF_span : F.toSet ⊆ affineSpan ℝ F.toSet := subset_affineSpan ℝ F.toSet

  -- Since G.toSet ⊆ affineSpan ℝ F.toSet, we get dimension constraint
  have h_dim_le : G.dim ≤ F.dim := affineDim_le_of_subset_affineSpan h_subset

  -- Contradiction with hdim : F.dim < G.dim
  omega

/-- Given a vertex v in geometric face G but not in the affine span of face F,
there exists a geometric face H containing F and v with dimension exactly dim F + 1.

Note: This is well-defined because it returns a GeometricFace, not a Face.
The Face structure construction is handled separately in FaceLattice.lean. -/
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

/-- If A and B are geometric faces with A ⊂ B and a dimension gap ≥ 2,
then there exists an intermediate geometric face C with A ⊂ C ⊆ B and dim C = dim A + 1. -/
theorem exists_intermediate_geometric_face {P : ConvexPolyhedron E}
    {A B : GeometricFace P}
    (hAB_proper : A < B)
    (hdim_gap : A.dim + 2 ≤ B.dim) :
    ∃ C : GeometricFace P,
      A < C ∧
      C ≤ B ∧
      C.dim = A.dim + 1 := by
  sorry

/-!
### Finiteness

Geometric faces are finite in each dimension (needed for counting).
-/

/-- The set of geometric k-dimensional faces is finite.

Proof strategy: The map F ↦ F.toSet injects {F : GeometricFace P | F.dim = k}
into the finite set {s : Set E | ∃ F : Face P, F.dim = k ∧ s = F.toSet}. -/
theorem geometric_k_faces_finite (P : ConvexPolyhedron E) (k : ℤ) :
    {F : GeometricFace P | F.dim = k}.Finite := by
  have h_sets_finite := geometric_faces_finite P k

  -- Step 1: toSet is injective on GeometricFace by subtype equality
  have h_inj : Set.InjOn GeometricFace.toSet {F : GeometricFace P | F.dim = k} := by
    intros F _hF G _hG hFG
    -- Two GeometricFaces are equal iff their underlying sets are equal
    exact Subtype.ext hFG

  -- Step 2: Image lands in the finite set from geometric_faces_finite
  have h_image_subset : (GeometricFace.toSet '' {F : GeometricFace P | F.dim = k}) ⊆
      {s : Set E | ∃ F : Face P, F.dim = k ∧ s = F.toSet} := by
    intro s hs
    obtain ⟨F, hF, rfl⟩ := hs
    -- Use exists_face_witness to get a Face with the same underlying set
    obtain ⟨F', hF'_eq⟩ := GeometricFace.exists_face_witness F
    use F'
    constructor
    · -- F'.dim = affineDim ℝ F'.toSet = affineDim ℝ F.toSet = F.dim = k
      show F'.dim = k
      calc F'.dim
          = affineDim ℝ F'.toSet := rfl
        _ = affineDim ℝ F.toSet := by rw [hF'_eq]
        _ = F.dim := rfl
        _ = k := hF
    · exact hF'_eq.symm

  -- Step 3: Apply finiteness via the injection
  exact (h_sets_finite.subset h_image_subset).of_finite_image h_inj

/-!
### Diamond Property

The main theorem: intervals of height 2 contain exactly 2 elements.
-/

/-- The open interval (F, G) in the geometric face lattice -/
def geometricFaceInterval (P : ConvexPolyhedron E) (F G : GeometricFace P) :
    Set (GeometricFace P) :=
  Set.Ioo F G

/-- The open interval in the geometric face lattice is finite.

Proof: The interval is a subset of ⋃_{k ∈ (F.dim, G.dim)} {H | H.dim = k},
and each of those sets is finite by geometric_k_faces_finite. -/
theorem geometricFaceInterval_finite (P : ConvexPolyhedron E) (F G : GeometricFace P) :
    (P.geometricFaceInterval F G).Finite := by
  -- The interval is a subset of the union of k-faces for k ∈ (F.dim, G.dim)
  have h_subset : P.geometricFaceInterval F G ⊆
      ⋃ k ∈ Set.Ioo F.dim G.dim, {H : GeometricFace P | H.dim = k} := by
    intro H ⟨hFH, hHG⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Ioo]
    use H.dim
    refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact geometric_dim_lt_of_ssubset hFH
    · exact geometric_dim_lt_of_ssubset hHG

  -- Apply finiteness: finite union of finite sets
  apply Set.Finite.subset _ h_subset
  apply Set.Finite.biUnion (Set.finite_Ioo F.dim G.dim)
  intro k _
  exact geometric_k_faces_finite P k

/-- Instance: The open interval in the geometric face lattice has a Finite instance. -/
instance geometricFaceInterval_instFinite (P : ConvexPolyhedron E) (F G : GeometricFace P) :
    Finite (P.geometricFaceInterval F G) :=
  (geometricFaceInterval_finite P F G).to_subtype

/-- Intermediate geometric faces of codimension 1 between F and G -/
def geometricIntermediateFaces (P : ConvexPolyhedron E) (F G : GeometricFace P) :
    Set (GeometricFace P) :=
  {H ∈ P.geometricFaceInterval F G | H.dim = F.dim + 1}

/-- In a graded poset, intervals of height 2 consist only of elements at the
intermediate dimension -/
theorem geometricFaceInterval_eq_intermediateFaces {P : ConvexPolyhedron E}
    {F G : GeometricFace P}
    (_hlt : F < G) (hcodim2 : G.dim = F.dim + 2) :
    P.geometricFaceInterval F G = P.geometricIntermediateFaces F G := by
  ext H
  simp only [geometricFaceInterval, geometricIntermediateFaces, Set.Ioo, Set.mem_setOf_eq]
  constructor
  · intro ⟨hFH, hHG⟩
    constructor
    · exact ⟨hFH, hHG⟩
    · -- If F < H < G and dim(G) = dim(F) + 2, then dim(H) = dim(F) + 1
      have h1 : F.dim < H.dim := geometric_dim_lt_of_ssubset hFH
      have h2 : H.dim < G.dim := geometric_dim_lt_of_ssubset hHG
      omega
  · intro ⟨⟨hFH, hHG⟩, _⟩
    exact ⟨hFH, hHG⟩

/-- Diamond property: Between any two geometric faces F < G with dim(G) = dim(F) + 2,
there are exactly 2 intermediate geometric faces.

This is the key combinatorial property needed to prove ∂² = 0 in the chain complex. -/
theorem geometric_diamond_property (P : ConvexPolyhedron E) (F G : GeometricFace P)
    (h : F < G) (h_codim : G.dim = F.dim + 2) :
    (P.geometricFaceInterval F G).ncard = 2 := by
  rw [geometricFaceInterval_eq_intermediateFaces h h_codim]
  sorry  -- Deep geometric result about polytope face structure

omit [FiniteDimensional ℝ E] in
/-- If F ⊆ G and dim F + 2 = dim G, then by the diamond property,
there are exactly 2 intermediate geometric faces. In ZMod 2, this is 0. -/
theorem geometric_intermediate_count_eq_zero_mod_two (P : ConvexPolyhedron E)
    (F G : GeometricFace P)
    (_h_lt : F < G) (_h_dim : G.dim = F.dim + 2) :
    (2 : ZMod 2) = 0 := by
  decide

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
