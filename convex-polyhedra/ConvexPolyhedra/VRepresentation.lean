/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
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

/-!
# V-Representation of Convex Polyhedra

This file defines convex polyhedra using the vertex (V-) representation:
a polyhedron is the convex hull of a finite set of points.

## Main definitions

* `ConvexPolyhedron E` - A convex polyhedron as convex hull of finitely many vertices
* `ConvexPolyhedron.vertices` - The vertices of the polyhedron
* `ConvexPolyhedron.extremePoints` - Extreme points (subset of vertices)
* `ConvexPolyhedron.dim` - Affine dimension of the polyhedron
* `ConvexPolyhedron.Face` - A face as an exposed subset
* `ConvexPolyhedron.faceChainComplex` - Chain complex from face lattice

## Main results

* `ConvexPolyhedron.compact` - Every polyhedron is compact
* `ConvexPolyhedron.convex` - Every polyhedron is convex
* `ConvexPolyhedron.bounded` - Every polyhedron is bounded
* `ConvexPolyhedron.extremePoints_eq_vertices` - Extreme points are exactly vertices (by definition)
* `ConvexPolyhedron.faces_finite` - Finitely many faces in each dimension
* `ConvexPolyhedron.boundary_comp_boundary` - ∂² = 0 (chain complex property)
* `ConvexPolyhedron3D.isHomologicalSphere` - 3D polyhedra have sphere homology
* `ConvexPolyhedron3D.euler_formula` - V - E + F = 2

## Strategy for Euler's Formula

The proof follows this path:
1. Build a chain complex from the face lattice of the polyhedron (over ZMod 2)
2. Define boundary maps ∂ₖ: Cₖ → Cₖ₋₁ from face incidence relations
3. Prove ∂² = 0 (boundary of boundary is zero)
4. Compute homology groups Hₖ = ker(∂ₖ) / im(∂ₖ₊₁)
5. Show that convex polyhedra in ℝ³ are homological spheres: H₀ ≅ ZMod 2, H₁ ≅ 0, H₂ ≅ ZMod 2
6. Apply Euler-Poincaré formula: χ = Σ(-1)ᵏ dim Hₖ = 1 - 0 + 1 = 2
7. Also χ = Σ(-1)ᵏ (# of k-faces) = V - E + F
8. Therefore V - E + F = 2

Note: We work over ZMod 2 to avoid orientation issues in the boundary maps. The chain
groups are indexed by all integers k ∈ ℤ (with trivial groups for k < 0).

## Implementation notes

This is the primary representation for Euler's polyhedron formula because:
1. Vertices, edges, and faces arise naturally from the face lattice
2. All polyhedra in this representation are automatically bounded
3. The Mathlib theory of extreme points and exposed faces applies directly
4. The convex hull is well-studied in Mathlib with many useful lemmas

We work in general finite-dimensional inner product spaces, specializing to ℝ³
when needed.

## References

* Minkowski-Weyl theorem: https://people.inf.ethz.ch/fukudak/polyfaq/node14.html
* Mathlib.Analysis.Convex.Hull
* Mathlib.Analysis.Convex.Extreme
* Mathlib.Algebra.Homology.ChainComplex

-/

open Set Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The affine dimension of a set is the dimension of its affine span.

For a set in an affine space, this is the rank of the direction (vector space) of the
affine span. An affine space of dimension d requires d+1 affinely independent points.

Examples:
- A single point has affine dimension 0
- A line segment has affine dimension 1
- A triangle has affine dimension 2
- A tetrahedron has affine dimension 3
-/
noncomputable def affineDim (𝕜 : Type*) {V : Type*} {P : Type*}
    [DivisionRing 𝕜] [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]
    (s : Set P) : ℤ :=
  Module.finrank 𝕜 (affineSpan 𝕜 s).direction

/-- A convex polyhedron as the convex hull of finitely many points (V-representation).

This is the primary definition for formalizing Euler's polyhedron formula. The polyhedron
is represented as a finite set of vertices that are exactly the extreme points of their
convex hull (irredundancy condition). The polyhedron itself is the convex hull of these
vertices.

The `vertices_are_extreme` field ensures that:
- No vertex can be expressed as a convex combination of other vertices
- The vertex set is minimal (removing any vertex changes the polyhedron)
- Two polyhedra with the same convex hull have the same vertices

Note: This representation automatically ensures boundedness and compactness. -/
structure ConvexPolyhedron (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The finite set of vertices defining the polyhedron -/
  vertices : Finset E
  /-- The vertex set must be nonempty -/
  nonempty : vertices.Nonempty
  /-- The vertices are exactly the extreme points of their convex hull (irredundancy condition) -/
  vertices_are_extreme : (vertices : Set E) = (convexHull ℝ (vertices : Set E)).extremePoints ℝ

namespace ConvexPolyhedron

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The underlying set of points in the polyhedron (the convex hull of vertices) -/
def toSet (P : ConvexPolyhedron E) : Set E :=
  convexHull ℝ (P.vertices : Set E)

instance : SetLike (ConvexPolyhedron E) E where
  coe := toSet
  coe_injective' := by
    intro ⟨v₁, h₁, he₁⟩ ⟨v₂, h₂, he₂⟩ h
    -- The key idea: vertices_are_extreme makes vertices canonical
    -- If two polyhedra have the same convex hull, they must have the same vertices
    -- because vertices are uniquely determined as the extreme points of the hull
    congr
    ext x
    -- Use vertices_are_extreme (he₁ and he₂) to show v₁ = v₂
    -- First, extract the convex hull equality from h
    have hull_eq : convexHull ℝ (v₁ : Set E) = convexHull ℝ (v₂ : Set E) := by
      simpa [toSet] using h
    have key : (v₁ : Set E) = (v₂ : Set E) := by
      calc (v₁ : Set E)
          = (convexHull ℝ (v₁ : Set E)).extremePoints ℝ := he₁  -- vertices_are_extreme for P₁
        _ = (convexHull ℝ (v₂ : Set E)).extremePoints ℝ := by rw [hull_eq]  -- equal convex hulls
        _ = (v₂ : Set E) := he₂.symm  -- vertices_are_extreme for P₂
    exact Set.ext_iff.mp key x

/-- A polyhedron is convex (immediate from convexity of convex hull) -/
theorem convex (P : ConvexPolyhedron E) : Convex ℝ (P : Set E) :=
  convex_convexHull ℝ _

/-- A polyhedron is compact (finite sets have compact convex hulls) -/
theorem compact (P : ConvexPolyhedron E) : IsCompact (P : Set E) :=
  P.vertices.finite_toSet.isCompact_convexHull

/-- A polyhedron is closed in Hausdorff spaces -/
theorem closed [T2Space E] (P : ConvexPolyhedron E) : IsClosed (P : Set E) :=
  P.compact.isClosed

/-- A polyhedron is bounded -/
theorem bounded (P : ConvexPolyhedron E) : Bornology.IsBounded (P : Set E) :=
  isBounded_convexHull.mpr P.vertices.finite_toSet.isBounded

/-- The vertices are contained in the polyhedron -/
theorem vertices_subset (P : ConvexPolyhedron E) : (P.vertices : Set E) ⊆ (P : Set E) :=
  subset_convexHull ℝ _

/-- The set of extreme points of the polyhedron -/
def extremePointsSet (P : ConvexPolyhedron E) : Set E :=
  (P : Set E).extremePoints ℝ

/-- Extreme points of a polyhedron are contained in the vertex set -/
theorem extremePoints_subset_vertices (P : ConvexPolyhedron E) :
    P.extremePointsSet ⊆ (P.vertices : Set E) :=
  extremePoints_convexHull_subset

/-- The extreme points are exactly the vertices (by definition) -/
theorem extremePoints_eq_vertices (P : ConvexPolyhedron E) :
    P.extremePointsSet = (P.vertices : Set E) :=
  P.vertices_are_extreme.symm

/-- The affine dimension of the polyhedron -/
noncomputable def dim (P : ConvexPolyhedron E) : ℤ :=
  affineDim ℝ (P : Set E)

/-- A polyhedron is full-dimensional if its affine dimension equals the space dimension -/
def isFullDimensional (P : ConvexPolyhedron E) : Prop :=
  P.dim = Module.finrank ℝ E

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

section ChainComplex

/-- Helper to get the index set for k-faces. Returns subtype of faces with dimension k. -/
def facesIndexSet (P : ConvexPolyhedron E) (k : ℤ) : Type _ :=
  if 0 ≤ k then { F : Face P // F.dim = k } else PUnit

/-- The k-faces form a finite type (assuming faces_finite) -/
noncomputable instance (P : ConvexPolyhedron E) (k : ℤ) : Fintype (P.facesIndexSet k) := by
  unfold facesIndexSet
  split
  · -- k ≥ 0: Use faces_finite to get Fintype
    -- Convert ℤ to ℕ (we know k ≥ 0)
    have hk : 0 ≤ k := by assumption
    let k_nat : ℕ := Int.toNat k
    have hk_eq : (k_nat : ℤ) = k := Int.toNat_of_nonneg hk
    -- We need Fintype for {F : Face P // F.dim = k}
    -- This would follow from faces_finite, but that theorem is currently sorry
    sorry
  · -- k < 0: PUnit is finite
    infer_instance

/-- The chain group of k-dimensional faces (functions from k-faces to ZMod 2).

We work over ZMod 2 to avoid orientation issues. Each face either appears (1) or
doesn't appear (0) in a boundary, and we only care about parity.

The chain groups are indexed by all integers k ∈ ℤ. For k < 0, the index set is
PUnit (trivial type), making this the trivial module.

Using functions (rather than Finsupp) simplifies the type class instances
and makes the boundary map definition much cleaner. -/
def chainGroup (P : ConvexPolyhedron E) (k : ℤ) : Type _ :=
  P.facesIndexSet k → ZMod 2

/-- The chain group is an AddCommGroup via the Pi structure -/
instance (P : ConvexPolyhedron E) (k : ℤ) : AddCommGroup (P.chainGroup k) :=
  Pi.addCommGroup

/-- The chain group is a Module over ZMod 2 via the Pi structure -/
instance (P : ConvexPolyhedron E) (k : ℤ) : Module (ZMod 2) (P.chainGroup k) :=
  Pi.module _ _ _

/-- Boundary map: sends a k-face to the formal sum of its (k-1)-faces.

For a k-face G, ∂(G) = Σ F where F ranges over (k-1)-faces on the boundary of G.
Working over ZMod 2 means we don't need orientation signs - we just sum all incident
(k-1)-faces modulo 2.

The map extends linearly to the entire chain group by:
∂(Σᵢ aᵢ·Gᵢ) = Σᵢ aᵢ·∂(Gᵢ)

For k ≤ 0, the boundary map is the zero map (source is trivial).

This follows the pattern from Polyhedron.lean, using functions instead of Finsupp
for simpler type class inference. -/
noncomputable def boundaryMap (P : ConvexPolyhedron E) (k : ℤ) :
    P.chainGroup k →ₗ[ZMod 2] P.chainGroup (k - 1) := by
  -- When k ≤ 0 or k-1 < 0, at least one side is the trivial module (functions from PUnit)
  -- In those cases, we can just return the zero map
  by_cases hk : 0 < k
  · by_cases hk' : 0 ≤ k - 1
    · -- Both k and k-1 are non-negative
      -- For now, use the zero map until we complete the full implementation
      -- TODO: Implement the proper boundary map following Polyhedron.lean pattern
      sorry
    · -- k > 0 but k - 1 < 0: zero map (target is trivial)
      exact 0
  · -- k ≤ 0: zero map (source is trivial)
    exact 0

/-- The boundary of a boundary is zero: ∂² = 0.

This is the key algebraic property that makes the face lattice into a chain complex.

The proof relies on a fundamental combinatorial fact: each (k-2)-face H appears in
∂²(G) exactly as many times as there are k-1 faces F containing H that are themselves
contained in the k-face G. In the boundary of a face, this count is always even
(it equals the number of ways to choose 2 facets of a simplex-like structure).

Working over ZMod 2, any even count becomes 0, so ∂²(G) = 0 for each k-face G.
By linearity, ∂² = 0 on the entire chain group. -/
theorem boundary_comp_boundary (P : ConvexPolyhedron E) (k : ℤ) :
    (P.boundaryMap (k - 1)).comp (P.boundaryMap k) = 0 := by
  -- Strategy: Show that for any k-face G, (∂ ∘ ∂)(G) = 0
  -- Each (k-2)-face H appears in ∂(∂(G)) an even number of times (over ZMod 2, this is 0)

  ext x
  simp [LinearMap.comp_apply]

  -- The composition ∂_{k-1} ∘ ∂_k is the zero map
  -- This follows from the fact that in the face lattice, each (k-2)-face H is incident
  -- to an even number of pairs (F, G) where H ⊆ F ⊆ G, F is a (k-1)-face, and G is a k-face
  sorry

-- TODO: Define faceChainComplex (P : ConvexPolyhedron E) : ChainComplex (ZMod 2) ℤ
-- This requires CategoryTheory infrastructure for chain complexes indexed by ℤ.
-- The chain complex will be built from chainGroup, boundaryMap, and boundary_comp_boundary.

/-- The k-th homology group of the polyhedron.

Hₖ(P) = ker(∂ₖ) / im(∂ₖ₊₁) measures "k-dimensional holes" in the polyhedron. -/
noncomputable def homologyGroup (P : ConvexPolyhedron E) (k : ℕ) : Type _ := by
  sorry

end ChainComplex

section ThreeDimensional

/-- Convex polyhedra in ℝ³ -/
abbrev ConvexPolyhedron3D := ConvexPolyhedron (EuclideanSpace ℝ (Fin 3))

variable (P : ConvexPolyhedron3D)

/-- 0-dimensional faces (vertices) -/
def vertices0D := P.faces 0

/-- 1-dimensional faces (edges) -/
def edges := P.faces 1

/-- 2-dimensional faces (faces in the geometric sense) -/
def faces2D := P.faces 2

/-- Count of vertices -/
noncomputable def numVertices (P : ConvexPolyhedron3D) : ℕ := (P.faces_finite 0).toFinset.card

/-- Count of edges -/
noncomputable def numEdges (P : ConvexPolyhedron3D) : ℕ := (P.faces_finite 1).toFinset.card

/-- Count of 2-faces -/
noncomputable def numFaces (P : ConvexPolyhedron3D) : ℕ := (P.faces_finite 2).toFinset.card

/-- The Euler characteristic V - E + F (combinatorial definition) -/
noncomputable def eulerCharacteristicCombinatorial (P : ConvexPolyhedron3D) : ℤ :=
  (numVertices P : ℤ) - (numEdges P : ℤ) + (numFaces P : ℤ)

/-- The Euler characteristic as alternating sum of Betti numbers (homological definition).

For a space with homology groups H₀, H₁, H₂, the Euler characteristic is:
χ = dim H₀ - dim H₁ + dim H₂

This is the connection to the Euler-Poincaré formula. -/
noncomputable def eulerCharacteristicHomological (P : ConvexPolyhedron3D) : ℤ := by
  sorry  -- Σ(-1)ᵏ · rank(Hₖ(P))

/-- A convex polyhedron in ℝ³ is a homological 2-sphere.

Working over ZMod 2, this means:
- H₀(P) ≅ ZMod 2 (connected, one component)
- H₁(P) ≅ 0 (no "1-dimensional holes")
- H₂(P) ≅ ZMod 2 (encloses a 3D region, one "2-dimensional cavity")

This is the key topological property that makes the Euler formula work. -/
theorem isHomologicalSphere (P : ConvexPolyhedron3D) :
    -- H₀(P) ≅ ZMod 2 ∧ H₁(P) ≅ 0 ∧ H₂(P) ≅ ZMod 2
    True := by  -- Placeholder, need proper statement
  sorry

/-- The two definitions of Euler characteristic coincide.

This follows from the Euler-Poincaré formula, which states that for any chain complex:
χ = Σ(-1)ᵏ · rank(Hₖ) = Σ(-1)ᵏ · rank(Cₖ)

where Cₖ is the k-th chain group (generated by k-faces). -/
theorem eulerCharacteristic_eq (P : ConvexPolyhedron3D) :
    eulerCharacteristicCombinatorial P = eulerCharacteristicHomological P := by
  sorry

/-- Euler's Polyhedron Formula: V - E + F = 2.

This is the main theorem! It follows from:
1. isHomologicalSphere: H₀ ≅ ℤ, H₁ ≅ 0, H₂ ≅ ℤ
2. Therefore χ = dim H₀ - dim H₁ + dim H₂ = 1 - 0 + 1 = 2
3. By eulerCharacteristic_eq: V - E + F = χ = 2 -/
theorem euler_formula (P : ConvexPolyhedron3D) :
    (numVertices P : ℤ) - (numEdges P : ℤ) + (numFaces P : ℤ) = 2 := by
  sorry

end ThreeDimensional

end ConvexPolyhedron
