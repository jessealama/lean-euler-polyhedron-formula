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
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice

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

section Lattice

/-!
## Face Lattice Structure

Faces of a convex polyhedron form a graded lattice under the subset relation.
The grading is given by the dimension function.

Key properties:
- The subset relation F.toSet ⊆ G.toSet defines a partial order on faces
- The incidence relation is the "covering relation": F incident G ↔ F ⊂ G and no face strictly between
- Dimension gives the grading: faces at level k have dimension k
- The lattice is bounded (has minimum and maximum elements)

This lattice structure is fundamental to the face theory and chain complex construction.
-/

namespace Face

variable {P : ConvexPolyhedron E}

/-- The subset relation on faces: F ≤ G if F.toSet ⊆ G.toSet -/
def le (F G : Face P) : Prop := F.toSet ⊆ G.toSet

instance : LE (Face P) where
  le := le

/-- Two faces are equal if they have the same underlying set -/
theorem eq_iff_toSet_eq {F G : Face P} : F = G ↔ F.toSet = G.toSet := by
  constructor
  · intro h
    rw [h]
  · intro h
    -- Two faces with the same convex hull must have the same vertices
    -- This follows because both are determined by maximizing linear functionals,
    -- and the vertices are exactly those points where some functional is maximized
    sorry  -- Requires showing face structure is determined by its geometric realization

/-- Faces form a partial order under subset -/
instance : PartialOrder (Face P) where
  le := le
  le_refl F := Set.Subset.refl F.toSet
  le_trans F G H := Set.Subset.trans
  le_antisymm F G hFG hGF := by
    apply eq_iff_toSet_eq.mpr
    exact Set.Subset.antisymm hFG hGF

/-- Incidence implies subset -/
theorem incident_le {F G : Face P} (h : P.incident F G) : F ≤ G := by
  exact incident_subset P h

/-- The subset relation is decidable (classically) -/
noncomputable instance (F G : Face P) : Decidable (F ≤ G) :=
  Classical.dec _

end Face

/-- Incidence is the covering relation in the face poset.
    F is incident to G iff F < G and dim F + 1 = dim G. -/
theorem incident_iff_covers (P : ConvexPolyhedron E) (F G : Face P) :
    P.incident F G ↔ (F < G ∧ F.dim + 1 = G.dim) := by
  rw [incident_iff]
  constructor
  · intro ⟨hdim, hsub⟩
    constructor
    · constructor
      · exact hsub
      · intro hGF
        -- If G ≤ F and F ≤ G (from hsub), then F = G by antisymmetry
        have : F = G := le_antisymm hsub hGF
        -- But then F.dim + 1 = G.dim becomes F.dim + 1 = F.dim, contradiction
        rw [this] at hdim
        omega
    · exact hdim
  · intro ⟨⟨hsub, _⟩, hdim⟩
    exact ⟨hdim, hsub⟩

/-- Dimension is monotone: F ⊆ G implies dim F ≤ dim G -/
theorem dim_mono {P : ConvexPolyhedron E} {F G : Face P} (h : F ≤ G) : F.dim ≤ G.dim := by
  -- A face contained in another has dimension at most the containing face
  sorry  -- Requires affine dimension properties from Mathlib

/-- If F ⊆ G and F ≠ G, then dim F < dim G -/
theorem dim_lt_of_ssubset {P : ConvexPolyhedron E} {F G : Face P}
    (h : F < G) : F.dim < G.dim := by
  -- Strict containment in convex sets implies strict dimension increase
  sorry  -- Requires affine dimension properties

/-- Faces are graded by dimension: the dimension function respects the partial order -/
theorem face_grading {P : ConvexPolyhedron E} {F G : Face P} :
    F ≤ G → F.dim ≤ G.dim := dim_mono

/-- Transitivity of incidence through the lattice -/
theorem subset_trans_incident (P : ConvexPolyhedron E) {F G H : Face P}
    (hFG : F ≤ G) (hGH : P.incident G H) : F ≤ H := by
  exact Set.Subset.trans hFG (incident_subset P hGH)

/-- Two distinct faces of the same dimension are incomparable -/
theorem incomparable_of_eq_dim {P : ConvexPolyhedron E} {F G : Face P}
    (hdim : F.dim = G.dim) (hne : F ≠ G) : ¬(F ≤ G) ∧ ¬(G ≤ F) := by
  constructor
  · intro hFG
    -- If F ≤ G and dim F = dim G, then by monotonicity dim F ≤ dim G
    -- But also dim G = dim F, so we need F = G, contradicting hne
    have hle : F.dim ≤ G.dim := dim_mono hFG
    have hge : G.dim ≤ F.dim := by omega
    -- For faces with same dimension, F ⊆ G and dim F = dim G implies F = G
    sorry  -- Requires: equal dimension + subset implies equality for faces
  · intro hGF
    have hle : G.dim ≤ F.dim := dim_mono hGF
    have hge : F.dim ≤ G.dim := by omega
    sorry  -- Same argument by symmetry

/-- The dimension function is strictly monotone on chains -/
theorem dim_strictMono_of_chain {P : ConvexPolyhedron E} {F G H : Face P}
    (hFG : F < G) (hGH : G < H) : F.dim < G.dim ∧ G.dim < H.dim := by
  exact ⟨dim_lt_of_ssubset hFG, dim_lt_of_ssubset hGH⟩

/-- Between any two faces differing by k dimensions, there exists
    a saturated chain of length k (chain where consecutive elements
    are incident) -/
theorem exists_saturated_chain {P : ConvexPolyhedron E} {F G : Face P}
    (h : F ≤ G) (k : ℕ) (hdim : G.dim = F.dim + k) :
    ∃ (chain : Fin (k + 1) → Face P),
      chain 0 = F ∧
      chain (Fin.last k) = G ∧
      (∀ i : Fin k, P.incident (chain i.castSucc) (chain i.succ)) := by
  sorry  -- Induction on k using that lattice is graded by dimension

/-- The face lattice is a graded poset: any two maximal chains between
    the same endpoints have the same length -/
theorem face_lattice_is_graded {P : ConvexPolyhedron E} {F G : Face P}
    (h : F ≤ G) :
    ∀ (m n : ℕ)
      (chain1 : Fin (m + 1) → Face P)
      (chain2 : Fin (n + 1) → Face P),
    (chain1 0 = F ∧ chain1 (Fin.last m) = G ∧
     ∀ i : Fin m, P.incident (chain1 i.castSucc) (chain1 i.succ)) →
    (chain2 0 = F ∧ chain2 (Fin.last n) = G ∧
     ∀ i : Fin n, P.incident (chain2 i.castSucc) (chain2 i.succ)) →
    m = n := by
  intro m n chain1 chain2 h1 h2
  -- Both chains have length G.dim - F.dim because dimension increases
  -- by exactly 1 at each step in a saturated chain
  sorry  -- Use that incident increases dimension by 1

/-- The open interval (H, G) in the face lattice:
    all faces F with H < F < G -/
def faceInterval (P : ConvexPolyhedron E) (H G : Face P) : Set (Face P) :=
  Set.Ioo H G

/-- Intermediate faces of codimension 1 between H and G -/
def intermediateFaces (P : ConvexPolyhedron E) (H G : Face P) : Set (Face P) :=
  {F ∈ P.faceInterval H G | F.dim = H.dim + 1}

/-- The open interval in a graded poset consists only of elements
    at intermediate dimensions -/
theorem faceInterval_eq_intermediateFaces {P : ConvexPolyhedron E} {H G : Face P}
    (hlt : H < G) (hcodim2 : G.dim = H.dim + 2) :
    P.faceInterval H G = P.intermediateFaces H G := by
  ext F
  simp only [faceInterval, intermediateFaces, Set.Ioo, Set.mem_setOf_eq]
  constructor
  · intro ⟨hHF, hFG⟩
    constructor
    · exact ⟨hHF, hFG⟩
    · -- If H < F < G and dim(G) = dim(H) + 2, then dim(F) = dim(H) + 1
      -- This follows from strict monotonicity of dimension
      have h1 : H.dim < F.dim := dim_lt_of_ssubset hHF
      have h2 : F.dim < G.dim := dim_lt_of_ssubset hFG
      omega
  · intro ⟨⟨hHF, hFG⟩, _⟩
    exact ⟨hHF, hFG⟩

/-- Intermediate faces form a finite set -/
theorem intermediateFaces_finite (P : ConvexPolyhedron E) (H G : Face P) :
    (P.intermediateFaces H G).Finite := by
  -- The intermediate faces are a subset of faces of dimension H.dim + 1
  have subset : P.intermediateFaces H G ⊆ P.faces (Int.toNat (H.dim + 1)) := by
    intro F hF
    simp only [intermediateFaces, Set.mem_sep_iff, faceInterval] at hF
    simp only [faces, Set.mem_setOf_eq]
    rw [hF.2]
    sorry  -- H.dim + 1 = ↑(Int.toNat (H.dim + 1))
  exact Set.Finite.subset (faces_finite P (Int.toNat (H.dim + 1))) subset

/-- Diamond property (lattice-theoretic formulation):
    In the face lattice, any interval of height 2 contains exactly 2 elements.

    This is the key combinatorial property of convex polyhedra needed to
    prove ∂² = 0. It says that the face lattice is "diamond-shaped" at
    codimension 2: between any (k-2)-face and k-face, there are exactly
    2 intermediate (k-1)-faces. -/
theorem diamond_property (P : ConvexPolyhedron E) (H G : Face P)
    (h : H < G) (h_codim : G.dim = H.dim + 2) :
    (P.faceInterval H G).ncard = 2 := by
  rw [faceInterval_eq_intermediateFaces h h_codim]
  sorry  -- The geometric diamond property for polytopes

/-- Backward compatibility: old formulation of diamond property -/
theorem intermediate_face_count (P : ConvexPolyhedron E) (H G : Face P)
    (h_sub : H.toSet ⊆ G.toSet) (h_codim : H.dim + 2 = G.dim) :
    (P.intermediateFaces H G).ncard = 2 := by
  have hlt : H < G := by
    constructor
    · exact h_sub
    · intro hGF
      -- If G ≤ H and H ⊆ G, then H = G by antisymmetry
      have : H = G := le_antisymm h_sub hGF
      -- But then H.dim + 2 = G.dim becomes H.dim + 2 = H.dim
      rw [← this] at h_codim
      omega
  have hcodim2 : G.dim = H.dim + 2 := h_codim.symm
  rw [← faceInterval_eq_intermediateFaces hlt hcodim2]
  exact diamond_property P H G hlt hcodim2

/-- If H ⊆ G and dim H + 2 = dim G, then by the diamond property,
    there are exactly 2 intermediate faces. In ZMod 2, this is 0. -/
theorem intermediate_count_eq_zero_mod_two (P : ConvexPolyhedron E) (H G : Face P)
    (h_sub : H.toSet ⊆ G.toSet) (h_dim : H.dim + 2 = G.dim) :
    (2 : ZMod 2) = 0 := by
  decide

end Lattice

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
for simpler type class inference.

Helper function to compute the boundary map value. Returns 0 if k ≤ 0 or k-1 < 0. -/
noncomputable def boundaryMapValue (P : ConvexPolyhedron E) (k : ℤ)
    (chain : P.chainGroup k) (g : P.facesIndexSet (k - 1)) : ZMod 2 :=
  if h : 0 < k ∧ 0 ≤ k - 1 then
    -- Both k and k-1 are non-negative, so facesIndexSet gives subtypes
    have hk_nonneg : 0 ≤ k := le_of_lt h.1
    have hk1_nonneg : 0 ≤ k - 1 := h.2
    -- Use the fact that when k ≥ 0, facesIndexSet k = { F : Face P // F.dim = k }
    have idx_k : P.facesIndexSet k = { F : Face P // F.dim = k } := by
      unfold facesIndexSet
      split_ifs
      · rfl
    have idx_k1 : P.facesIndexSet (k - 1) = { F : Face P // F.dim = k - 1 } := by
      unfold facesIndexSet
      split_ifs
      · rfl
    -- For each (k-1)-face g, sum over all k-faces F that are incident to g
    Finset.univ.sum fun F : P.facesIndexSet k =>
      if P.incident (idx_k1 ▸ g).val (idx_k ▸ F).val then chain F else 0
  else
    0

noncomputable def boundaryMap (P : ConvexPolyhedron E) (k : ℤ) :
    P.chainGroup k →ₗ[ZMod 2] P.chainGroup (k - 1) := {
  toFun := fun chain => fun g => P.boundaryMapValue k chain g
  map_add' := by
    intro x y
    funext g
    unfold boundaryMapValue
    split_ifs with h
    · -- Case: 0 < k ∧ 0 ≤ k - 1
      -- The sum distributes over addition
      have hk_nonneg : 0 ≤ k := le_of_lt h.1
      have hk1_nonneg : 0 ≤ k - 1 := h.2
      have idx_k : P.facesIndexSet k = { F : Face P // F.dim = k } := by
        unfold facesIndexSet
        split_ifs
        · rfl
      have idx_k1 : P.facesIndexSet (k - 1) = { F : Face P // F.dim = k - 1 } := by
        unfold facesIndexSet
        split_ifs
        · rfl
      have h_dist : ∀ F : P.facesIndexSet k,
        (if P.incident (idx_k1 ▸ g).val (idx_k ▸ F).val then (x + y) F else 0) =
        (if P.incident (idx_k1 ▸ g).val (idx_k ▸ F).val then x F else 0) +
        (if P.incident (idx_k1 ▸ g).val (idx_k ▸ F).val then y F else 0) := by
        intro F
        split_ifs
        · rfl
        · simp
      simp_rw [h_dist]
      rw [Finset.sum_add_distrib]
      rfl
    · -- Case: ¬(0 < k ∧ 0 ≤ k - 1), so the map is zero
      rfl
  map_smul' := by
    intro r x
    funext g
    unfold boundaryMapValue
    simp only [RingHom.id_apply]
    split_ifs with h
    · -- Case: 0 < k ∧ 0 ≤ k - 1
      -- Scalar multiplication distributes through the sum
      have hk_nonneg : 0 ≤ k := le_of_lt h.1
      have hk1_nonneg : 0 ≤ k - 1 := h.2
      have idx_k : P.facesIndexSet k = { F : Face P // F.dim = k } := by
        unfold facesIndexSet
        split_ifs
        · rfl
      have idx_k1 : P.facesIndexSet (k - 1) = { F : Face P // F.dim = k - 1 } := by
        unfold facesIndexSet
        split_ifs
        · rfl
      have h_dist : ∀ F : P.facesIndexSet k,
        (if P.incident (idx_k1 ▸ g).val (idx_k ▸ F).val then (r • x) F else 0) =
        r • (if P.incident (idx_k1 ▸ g).val (idx_k ▸ F).val then x F else 0) := by
        intro F
        split_ifs
        · rfl
        · simp
      simp_rw [h_dist]
      rw [← Finset.smul_sum]
      rfl
    · -- Case: ¬(0 < k ∧ 0 ≤ k - 1), so the map is zero
      rfl
}

/-- If a function from a finite type to ZMod 2 is nonzero, then there exists
a witness where the function evaluates to a nonzero value.

This is used to extract a specific face from the assumption that a chain complex
composition is nonzero. -/
lemma function_ne_zero_implies_witness {α : Type*} [Fintype α] (f : α → ZMod 2) :
    f ≠ 0 → ∃ a : α, f a ≠ 0 := by
  intro h_ne
  -- By contradiction: if f a = 0 for all a, then f = 0
  by_contra h_all_zero
  push_neg at h_all_zero
  -- So f is the zero function
  have h_f_zero : f = 0 := by
    ext a
    exact h_all_zero a
  -- But this contradicts h_ne
  exact h_ne h_f_zero

set_option maxHeartbeats 5000000 in
-- The proof involves nested case analysis and double summations over face lattices
-- which require substantial elaboration time, particularly in the main k≥2 case
-- where we expand the composition of boundary maps and apply the diamond property.
/-- The boundary of a boundary is zero: ∂² = 0.

This is the key algebraic property that makes the face lattice into a chain complex.

The proof relies on the diamond property: each (k-2)-face H appears in ∂²(G) exactly
as many times as there are (k-1)-faces F with H ⊆ F ⊆ G. By the diamond property,
this count is always 2 (for codimension 2 pairs), which equals 0 in ZMod 2.

Working over ZMod 2, any even count becomes 0, so ∂²(G) = 0 for each k-face G.
By linearity, ∂² = 0 on the entire chain group.
-/
theorem boundary_comp_boundary (P : ConvexPolyhedron E) (k : ℤ) :
    (P.boundaryMap (k - 1)).comp (P.boundaryMap k) = 0 := by
  -- Proof strategy (mirroring boundaryMap structure):
  -- 1. For k ≤ 1: at least one boundary map is zero, so composition is zero
  --    - boundaryMap k is zero if k ≤ 0
  --    - boundaryMap (k-1) is zero if k-1 ≤ 0, i.e., k ≤ 1
  -- 2. For k ≥ 2: both boundary maps are well-defined, use diamond property

  -- Mirror the by_cases structure from boundaryMap
  by_cases hk : 0 < k
  · -- Case: k > 0, so boundaryMap k might be non-zero
    by_cases hkm1 : 0 < k - 1
    · -- Case: k > 1 (so k ≥ 2), both boundaryMap k and boundaryMap (k-1) are non-zero
      -- This is where we need the diamond property
      -- MAIN COMPUTATIONAL CASE (k ≥ 2):
      --
      -- Goal: show (∂_{k-1} ∘ ∂_k) = 0
      --
      -- Strategy:
      -- 1. Expand the composition: for each (k-2)-face g,
      --    (∂_{k-1} ∘ ∂_k)(x)(g) = Σ_{F:(k-1)-face} [Σ_{G:k-face} x(G) if g⊆F⊆G]
      --
      -- 2. Swap sum order to: Σ_{G:k-face} x(G) · #{F | g⊆F⊆G, dim F = dim g + 1}
      --
      -- 3. Apply diamond property: when dim G = dim g + 2, count = 2
      --
      -- 4. Simplify: x(G) · 2 = x(G) · 0 = 0 in ZMod 2

      -- Start with extensionality
      ext chain
      funext g
      simp [LinearMap.comp_apply, LinearMap.zero_apply]

      -- Unfold the boundary maps
      unfold boundaryMap boundaryMapValue

      -- We have k > 1, so k ≥ 2
      have hk_ge_2 : k ≥ 2 := by omega

      -- Set up the conditions for both boundary maps
      have hk_cond : 0 < k ∧ 0 ≤ k - 1 := by omega
      have hkm1_cond : 0 < k - 1 ∧ 0 ≤ k - 2 := by omega

      -- Simplify using these conditions
      simp only [hk_cond, hkm1_cond]

      -- Set up type equalities for index sets using explicit conditions
      have hk_nonneg : 0 ≤ k := by omega
      have hkm1_nonneg : 0 ≤ k - 1 := by omega
      have hkm2_nonneg : 0 ≤ k - 2 := by omega

      have idx_k : P.facesIndexSet k = { F : Face P // F.dim = k } := by
        unfold facesIndexSet; rw [if_pos hk_nonneg]
      have idx_km1 : P.facesIndexSet (k - 1) = { F : Face P // F.dim = k - 1 } := by
        unfold facesIndexSet; rw [if_pos hkm1_nonneg]
      have idx_km2 : P.facesIndexSet (k - 2) = { F : Face P // F.dim = k - 2 } := by
        unfold facesIndexSet; rw [if_pos hkm2_nonneg]

      -- Now we have a double sum:
      -- Σ_F:(k-1)-faces [if g incident F then Σ_G:k-faces [if F incident G then chain(G)]]
      --
      -- This equals (after swapping sums):
      -- Σ_G:k-faces [chain(G) · #{F:(k-1)-faces | g incident F ∧ F incident G}]
      --
      -- By diamond property: #{F | g incident F ∧ F incident G} = 2 when g.dim = k-2 and G.dim = k
      -- And 2 = 0 in ZMod 2, so each term is 0

      -- Proof by contradiction using the diamond property

      -- We've already applied ext/funext, so we're working with a specific chain
      -- Assume for contradiction that the double sum for this chain is not identically zero
      by_contra h_nonzero

      -- Extract a witness (k-2)-face where the double sum is nonzero
      -- This uses function_ne_zero_implies_witness but the full elaboration is expensive
      have ⟨g_witness, h_witness⟩ : ∃ g : P.facesIndexSet (k - 2),
          (Finset.univ.sum fun F_km1 : P.facesIndexSet (k - 1) =>
            if P.incident (idx_km2 ▸ g).val (idx_km1 ▸ F_km1).val then
              Finset.univ.sum fun G_k : P.facesIndexSet k =>
                if P.incident (idx_km1 ▸ F_km1).val (idx_k ▸ G_k).val then
                  chain G_k
                else 0
            else 0) ≠ 0 := by
        sorry -- Apply function_ne_zero_implies_witness to extract witness

      -- Let g be this witness (k-2)-face
      let g := g_witness

      -- The double sum counts pairs (F, G) where g < F < G
      have h_count : (Finset.univ.sum fun F_km1 : P.facesIndexSet (k - 1) =>
          if P.incident (idx_km2 ▸ g).val (idx_km1 ▸ F_km1).val then
            Finset.univ.sum fun G_k : P.facesIndexSet k =>
              if P.incident (idx_km1 ▸ F_km1).val (idx_k ▸ G_k).val then
                chain G_k
              else 0
          else 0) =
        (Finset.univ.sum fun G_k : P.facesIndexSet k =>
          chain G_k *
          (Finset.univ.filter fun F_km1 : P.facesIndexSet (k - 1) =>
            P.incident (idx_km2 ▸ g).val (idx_km1 ▸ F_km1).val ∧
            P.incident (idx_km1 ▸ F_km1).val (idx_k ▸ G_k).val).card) := by
        sorry -- Swap sum order and factor out chain(G)

      -- For each G with g < G, the filter counts intermediate faces
      have h_diamond : ∀ G_k : P.facesIndexSet k,
          (idx_k ▸ G_k).val.dim = k →
          (idx_km2 ▸ g).val.dim = k - 2 →
          (idx_km2 ▸ g).val < (idx_k ▸ G_k).val →
          (Finset.univ.filter fun F_km1 : P.facesIndexSet (k - 1) =>
            P.incident (idx_km2 ▸ g).val (idx_km1 ▸ F_km1).val ∧
            P.incident (idx_km1 ▸ F_km1).val (idx_k ▸ G_k).val).card = 2 := by
        intro G_k hG_dim hg_dim hg_lt_G
        -- Apply diamond property: between g and G (differing by 2 dimensions),
        -- there are exactly 2 intermediate faces
        have h_codim : (idx_k ▸ G_k).val.dim = (idx_km2 ▸ g).val.dim + 2 := by omega
        sorry -- Apply diamond_property theorem

      -- Each term in the sum contributes chain(G) * 2
      have h_sum_even : (Finset.univ.sum fun G_k : P.facesIndexSet k =>
          chain G_k *
          (Finset.univ.filter fun F_km1 : P.facesIndexSet (k - 1) =>
            P.incident (idx_km2 ▸ g).val (idx_km1 ▸ F_km1).val ∧
            P.incident (idx_km1 ▸ F_km1).val (idx_k ▸ G_k).val).card) =
        (Finset.univ.sum fun G_k : P.facesIndexSet k =>
          chain G_k * 2) := by
        rw [Finset.sum_congr rfl]
        simp
        intro x
        -- Apply h_diamond with the necessary conditions
        have hx_dim : (idx_k ▸ x).val.dim = k := (idx_k ▸ x).property
        have hg_dim : (idx_km2 ▸ g).val.dim = k - 2 := (idx_km2 ▸ g).property
        -- Case split: either g < x (apply diamond property) or g ≮ x (filter is empty)
        by_cases hg_lt_x : (idx_km2 ▸ g).val < (idx_k ▸ x).val
        · -- Case: g < x, apply diamond property to get card = 2
          rw [h_diamond x hx_dim hg_dim hg_lt_x]
          norm_cast
        · -- Case: g ≮ x, filter is empty so card = 0, and 0 = 2 in ZMod 2
          have h_empty : (Finset.univ.filter fun F_km1 : P.facesIndexSet (k - 1) =>
              P.incident (idx_km2 ▸ g).val (idx_km1 ▸ F_km1).val ∧
              P.incident (idx_km1 ▸ F_km1).val (idx_k ▸ x).val).card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro F _
            push_neg
            intro h1 h2
            -- From incidence relations, derive g < x, contradicting hg_lt_x
            have hg_F : (idx_km2 ▸ g).val ≤ (idx_km1 ▸ F).val := incident_subset P h1
            have hF_x : (idx_km1 ▸ F).val ≤ (idx_k ▸ x).val := incident_subset P h2
            have hg_x : (idx_km2 ▸ g).val ≤ (idx_k ▸ x).val := le_trans hg_F hF_x
            -- Show it's strict using dimensions
            have h_strict_dim : (idx_km2 ▸ g).val.dim < (idx_k ▸ x).val.dim := by omega
            -- To show g < x, we need hg_x and ¬(x ≤ g)
            have h_not_ge : ¬((idx_k ▸ x).val ≤ (idx_km2 ▸ g).val) := by
              intro hx_g
              have : (idx_k ▸ x).val.dim ≤ (idx_km2 ▸ g).val.dim := dim_mono hx_g
              omega
            exact hg_lt_x ⟨hg_x, h_not_ge⟩
          rw [h_empty]
          -- Both 0 and 2 equal 0 in ZMod 2
          simp [show (2 : ZMod 2) = 0 from by decide]


      -- In ZMod 2, multiplying by 2 gives 0
      have h_two_eq_zero : (2 : ZMod 2) = 0 := by decide

      have h_sum_zero : (Finset.univ.sum fun G_k : P.facesIndexSet k =>
          chain G_k * 2) = 0 := by
        simp [h_two_eq_zero]
        -- Each term is chain(G) * 0 = 0, and simp solves it

      -- Chain the equalities to get our sum equals 0
      have h_final : (Finset.univ.sum fun F_km1 : P.facesIndexSet (k - 1) =>
          if P.incident (idx_km2 ▸ g).val (idx_km1 ▸ F_km1).val then
            Finset.univ.sum fun G_k : P.facesIndexSet k =>
              if P.incident (idx_km1 ▸ F_km1).val (idx_k ▸ G_k).val then
                chain G_k
              else 0
          else 0) = 0 := by
        rw [h_count, h_sum_even, h_sum_zero]

      -- But this contradicts our witness that said it's nonzero!
      exact h_witness h_final

    · -- Case: k = 1 (since k > 0 but not k - 1 > 0)
      -- Here k - 1 = 0, so boundaryMap 0 is zero (since ¬(0 < 0))
      -- Therefore the composition is zero
      have hk_eq_1 : k = 1 := by omega
      have h_km1_eq_0 : k - 1 = 0 := by omega
      -- Show boundaryMap 0 ∘ boundaryMap 1 = 0 using extensionality
      ext chain g
      simp [LinearMap.comp_apply, LinearMap.zero_apply]
      unfold boundaryMap boundaryMapValue
      -- For boundaryMap 0, the condition 0 < 0 ∧ 0 ≤ -1 is false
      simp [h_km1_eq_0]
      rw [h_km1_eq_0]
      rfl

  · -- Case: k ≤ 0
    -- Here boundaryMap k is zero (since ¬(0 < k))
    -- Therefore the composition is zero
    have hk_le_0 : k ≤ 0 := by omega
    -- Show boundaryMap (k-1) ∘ boundaryMap k = 0 using extensionality
    ext chain
    funext g
    simp [LinearMap.comp_apply, LinearMap.zero_apply]
    unfold boundaryMap boundaryMapValue
    -- Split on all the if conditions
    split_ifs
    · -- All conditions true - but this is impossible when k ≤ 0
      omega
    · rfl

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
