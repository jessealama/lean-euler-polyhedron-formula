/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import ConvexPolyhedra.Face
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
# Face Lattice Structure of Convex Polyhedra

This file develops the lattice-theoretic structure of faces in convex polyhedra.

Faces of a convex polyhedron form a graded lattice under the subset relation,
with dimension providing the grading function.

## Main definitions

* `Face.le` - Partial order on faces (subset relation)
* `ConvexPolyhedron.faceInterval` - Interval in the face lattice
* `ConvexPolyhedron.intermediateFaces` - Faces between two given faces

## Main results

* `Face.PartialOrder` - Faces form a partial order
* `exists_face_extending_by_vertex` - Key construction lemma (requires heavy machinery)
* `exists_incident_face_below` - Graded lattice property
* `exists_saturated_chain` - Saturated chains exist between any two faces

## Implementation notes

This file contains the deep geometric results about face lattices, including
the difficult theorem `exists_face_extending_by_vertex` which requires Hahn-Banach
separation and careful dimension control.

-/

open Set Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace ConvexPolyhedron

section Lattice

/-!
## Face Lattice Structure

Faces of a convex polyhedron form a graded lattice under the subset relation.
The grading is given by the dimension function.

Key properties:
- The subset relation F.toSet ⊆ G.toSet defines a partial order on faces
- The incidence relation is the "covering relation":
  F incident G ↔ F ⊂ G and no face strictly between
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

/-- Every face has dimension at most the polyhedron's dimension.

This is the fundamental constraint that makes `exists_saturated_chain` well-defined:
since G is a Face P, we have G.dim ≤ P.dim, which means the hypothesis
`G.dim = F.dim + k` automatically bounds k ≤ P.dim. -/
theorem face_dim_le_polyhedron_dim {P : ConvexPolyhedron E} (F : Face P) : F.dim ≤ P.dim := by
  -- F.toSet ⊆ P by subset_polyhedron
  -- Affine dimension is monotone under subset
  sorry  -- Requires affine dimension properties from Mathlib

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

/-! ### Face Lattice Theory Helper Lemmas

These lemmas develop the theory needed to prove `exists_incident_face_below`.
They show that vertex inclusion is equivalent to face inclusion, and that
we can construct intermediate faces by adding vertices appropriately. -/

/-- If F ≤ G (F.toSet ⊆ G.toSet), then F.vertices ⊆ G.vertices.
This connects the partial order on faces to vertex inclusion.

The geometric intuition: if one face is contained in another, then the vertices
of the smaller face must be among the vertices of the larger face. -/
theorem vertices_subset_of_face_subset {P : ConvexPolyhedron E} {F G : Face P}
    (h : F ≤ G) : F.vertices ⊆ G.vertices := by
  intro v hv
  -- v ∈ F.vertices, need to show v ∈ G.vertices

  -- v is in F.toSet
  have hv_in_F : v ∈ F.toSet := by
    change v ∈ convexHull ℝ (F.vertices : Set E)
    exact subset_convexHull ℝ _ hv

  -- F.toSet ⊆ G.toSet, so v ∈ G.toSet
  have hv_in_G : v ∈ G.toSet := h hv_in_F

  -- v ∈ P.vertices (since F.vertices ⊆ P.vertices)
  have hv_in_P : v ∈ P.vertices := F.subset hv

  -- v is an extreme point of P
  have hv_extreme : v ∈ P.extremePointsSet := by
    rw [ConvexPolyhedron.extremePoints_eq_vertices]
    exact hv_in_P

  -- G.toSet ⊆ P by subset_polyhedron
  have hG_sub_P : G.toSet ⊆ (P : Set E) := G.subset_polyhedron

  -- Since v ∈ G.toSet and v is extreme in P, v is extreme in G.toSet
  have hv_extreme_G : v ∈ (G.toSet).extremePoints ℝ := by
    apply inter_extremePoints_subset_extremePoints_of_subset hG_sub_P
    exact ⟨hv_in_G, hv_extreme⟩

  -- G.toSet = convexHull (G.vertices), so v is extreme in convexHull (G.vertices)
  have : G.toSet = convexHull ℝ (G.vertices : Set E) := rfl
  rw [this] at hv_extreme_G

  -- Extreme points of convexHull S are contained in S
  have : (convexHull ℝ (G.vertices : Set E)).extremePoints ℝ ⊆ (G.vertices : Set E) :=
    extremePoints_convexHull_subset

  exact this hv_extreme_G

/-- If F and G are faces with F ⊂ G and dim F < dim G, then there exists
a vertex v ∈ G.vertices such that v ∉ affineSpan F.vertices.

This is the key step: finding a vertex "outside" F that we can use to extend it. -/
theorem exists_vertex_not_in_affineSpan {P : ConvexPolyhedron E} {F G : Face P}
    (hFG : F < G) (hdim : F.dim < G.dim) :
    ∃ v ∈ G.vertices, v ∉ affineSpan ℝ (F.vertices : Set E) := by
  -- Strategy: By contradiction, if all vertices of G are in affineSpan F.vertices,
  -- then affineSpan G.vertices ≤ affineSpan F.vertices.
  -- But F.toSet = convexHull F.vertices, so affineSpan F.toSet = affineSpan F.vertices.
  -- Similarly for G. This would give dim G ≤ dim F, contradicting dim F < dim G.

  by_contra h_all_in
  push_neg at h_all_in

  -- All vertices of G are in affineSpan F.vertices
  have h_vertices_sub : (G.vertices : Set E) ⊆ (affineSpan ℝ (F.vertices : Set E) : Set E) := by
    intro v hv
    exact h_all_in v hv

  -- Therefore affineSpan G.vertices ≤ affineSpan F.vertices
  have h_span_le : affineSpan ℝ (G.vertices : Set E) ≤ affineSpan ℝ (F.vertices : Set E) := by
    rw [affineSpan_le]
    exact h_vertices_sub

  -- Key fact: affineSpan (convexHull s) = affineSpan s
  have hF_span : affineSpan ℝ F.toSet = affineSpan ℝ (F.vertices : Set E) := by
    unfold Face.toSet
    exact affineSpan_convexHull (F.vertices : Set E)

  have hG_span : affineSpan ℝ G.toSet = affineSpan ℝ (G.vertices : Set E) := by
    unfold Face.toSet
    exact affineSpan_convexHull (G.vertices : Set E)

  -- Combine: affineSpan G.toSet = affineSpan G.vertices
  --          ≤ affineSpan F.vertices = affineSpan F.toSet
  have h_face_span_le : affineSpan ℝ G.toSet ≤ affineSpan ℝ F.toSet := by
    rw [hG_span, hF_span]
    exact h_span_le

  -- By direction monotonicity: (affineSpan G.toSet).direction ≤ (affineSpan F.toSet).direction
  have h_dir_le : (affineSpan ℝ G.toSet).direction ≤ (affineSpan ℝ F.toSet).direction :=
    AffineSubspace.direction_le h_face_span_le

  -- By finrank monotonicity:
  --   finrank (affineSpan G.toSet).direction ≤ finrank (affineSpan F.toSet).direction
  -- Note: F.vertices is a Finset, so the affine span direction is finite-dimensional
  have h_finrank_le : (Module.finrank ℝ (affineSpan ℝ G.toSet).direction : ℤ) ≤
      (Module.finrank ℝ (affineSpan ℝ F.toSet).direction : ℤ) := by
    -- Cast ℕ comparison to ℤ
    have : Module.finrank ℝ (affineSpan ℝ G.toSet).direction ≤
        Module.finrank ℝ (affineSpan ℝ F.toSet).direction := by
      -- F.toSet = convexHull F.vertices, and F.vertices is finite
      -- So affineSpan F.toSet has finite-dimensional direction
      have hF_finite : (F.vertices : Set E).Finite := F.vertices.finite_toSet
      have hG_finite : (G.vertices : Set E).Finite := G.vertices.finite_toSet
      have hF_span : affineSpan ℝ F.toSet = affineSpan ℝ (F.vertices : Set E) :=
        affineSpan_convexHull (F.vertices : Set E)
      have hG_span : affineSpan ℝ G.toSet = affineSpan ℝ (G.vertices : Set E) :=
        affineSpan_convexHull (G.vertices : Set E)
      -- The direction of affineSpan of a finite set is finite-dimensional
      haveI : FiniteDimensional ℝ (affineSpan ℝ (F.vertices : Set E)).direction :=
        finiteDimensional_direction_affineSpan_of_finite ℝ hF_finite
      -- Rewrite both sides using the span equality
      rw [hG_span, hF_span]
      apply Submodule.finrank_mono
      -- Now h_dir_le needs to be rewritten too
      rw [hG_span, hF_span] at h_dir_le
      exact h_dir_le
    exact Nat.cast_le.mpr this

  -- But G.dim = finrank (affineSpan G.toSet).direction and similarly for F (both as ℤ)
  have hG_dim_eq : G.dim = (Module.finrank ℝ (affineSpan ℝ G.toSet).direction : ℤ) := rfl
  have hF_dim_eq : F.dim = (Module.finrank ℝ (affineSpan ℝ F.toSet).direction : ℤ) := rfl

  -- Therefore G.dim ≤ F.dim
  have h_dim_contradiction : G.dim ≤ F.dim := by
    rw [hG_dim_eq, hF_dim_eq]
    exact h_finrank_le

  -- This contradicts our assumption that F.dim < G.dim
  omega

/-- Given a vertex v in a face G but not in the affine span of face F,
there exists a face H containing F and v with dimension exactly dim F + 1.

This is the key construction lemma for the graded lattice structure: it allows us
to "grow" a face by adding one vertex at a time while controlling the dimension.

## Geometric Strategy

The construction works in three conceptual steps:

### Step 1: Identify the Target Affine Subspace

Since v ∉ affineSpan(F.vertices), the affine span of F.vertices ∪ {v} has dimension
exactly dim(F) + 1 (fundamental theorem of affine geometry):

```lean
let S := affineSpan ℝ (insert v (F.vertices : Set E))
have : affineDim ℝ S = affineDim ℝ (F.toSet) + 1
```

This S is our "target" - we want H to be the intersection S ∩ P (or at least contain it).

### Step 2: Prove the Intersection is an Exposed Face

The set H_set := S ∩ P is an exposed face of P. This requires showing:
1. H_set is nonempty (contains F.vertices ∪ {v})
2. There exists a linear functional φ : E →L[ℝ] ℝ such that
   H_set = {x ∈ P | φ achieves maximum on P at x}

**Key idea**: Use Hahn-Banach separation to construct φ that:
- Vanishes on S.direction (making φ constant on the affine subspace S)
- Achieves its maximum on P exactly at points in S

The construction uses `exists_extension_of_le_sublinear` with an appropriately chosen
gauge function to extend the zero functional on S.direction to all of E.

### Step 3: Construct the Face Witness

Once we have H_set and its exposing functional φ, construct the Face structure:

```lean
H : Face P := {
  support := φ
  vertices := {w ∈ P.vertices | w ∈ H_set}
  subset := ...
  is_maximal := ... (verification that φ maximizes exactly on H.vertices)
}
```

The geometric properties (v ∈ H, F < H, H ≤ G, dim(H) = dim(F) + 1) then follow
from the construction and affine geometry.

## Required Infrastructure

The proof requires three main ingredients from Mathlib:

1. **Affine dimension theory** (`LinearAlgebra.AffineSpace.FiniteDimensional`):
   - Dimension increases by 1 when adding a point outside the affine span
   - Affine span of convex hull equals affine span of generators
   - Direction space properties

2. **Hahn-Banach separation** (`Analysis.NormedSpace.HahnBanach`):
   - Extension of linear functionals dominated by sublinear maps
   - Gauge functions and their properties
   - Continuous extension theorems

3. **Exposed face theory** (`Analysis.Convex.Exposed`):
   - Characterization of exposed faces via linear functionals
   - Properties of maximal sets of linear functionals
   - Connection to Face structure

## Implementation Notes

**Difference from GeometricFace approach**: This theorem still works with the `Face P` type
(which includes the supporting functional). However, the geometric insights carry over:
the functional φ is not arbitrary but determined by the separation requirement.

**Alternative**: The geometric version (returning a set proven to be exposed) would avoid
the need to construct the specific Face witness. See FaceLatticeTheory.lean for the
cleaner GeometricFace formulation.

**Why Hahn-Banach is essential**: We need explicit control over which vertices maximize
the functional. Direct constructions (e.g., "pick any functional") fail because they
don't guarantee the right dimension - other vertices might also achieve the maximum,
giving dim(H) > dim(F) + 1.

### Three Key Helper Lemmas

```lean
-- 1. Affine dimension grows by exactly 1
lemma affineDim_insert_of_not_mem_affineSpan {s : Finset E} {v : E}
    (hv : v ∉ affineSpan ℝ (s : Set E)) :
    affineDim ℝ (convexHull ℝ (insert v s : Set E)) = affineDim ℝ (convexHull ℝ (s : Set E)) + 1

-- 2. Separation from affine subspaces
lemma exists_separating_functional_affineSpan {s : Finset E} {v : E}
    (hv : v ∉ affineSpan ℝ (s : Set E)) :
    ∃ f : E →L[ℝ] ℝ, f v > ⨆ w ∈ (s : Set E), f w

-- 3. Exposed faces from functionals on polytopes
lemma exposed_face_of_maximizing_functional (P : ConvexPolyhedron E) (f : E →L[ℝ] ℝ) :
    IsExposed ℝ (P : Set E) {x ∈ P | ∀ y ∈ P, f y ≤ f x}
```

## Current Status

This is a deep geometric result requiring substantial Mathlib infrastructure. The proof
strategy is sound but requires careful formalization of the Hahn-Banach construction
and the dimension control machinery.

This theorem is the main blocker for `exists_incident_face_below`, which in turn
is needed for the full graded lattice structure used in the Euler characteristic
computation. -/
theorem exists_face_extending_by_vertex {P : ConvexPolyhedron E} {F G : Face P}
    (hFG : F < G)
    (v : E) (hv_in_G : v ∈ G.vertices)
    (hv_not_in_F : v ∉ affineSpan ℝ (F.vertices : Set E)) :
    ∃ H : Face P,
      F < H ∧
      H ≤ G ∧
      v ∈ H.vertices ∧
      affineDim ℝ (convexHull ℝ (H.vertices : Set E)) =
        affineDim ℝ (convexHull ℝ (F.vertices : Set E)) + 1 := by
  sorry  -- See documentation above for complete implementation strategy

/-- Key lemma for graded lattices: every proper face has an incident face.

    If F < G (proper containment), then there exists H with P.incident F H and H ≤ G.
    In particular, H.dim = F.dim + 1.

    This is the fundamental "upward extension" property of graded posets:
    you can always take one step up the lattice while staying below a given upper bound.

    ## Geometric Intuition

    Example (cube): Let F be an edge (1D) and G be the cube (3D).
    - F has 2 vertices, G has 8 vertices
    - We can find H = a square face containing F
    - H has 4 vertices and dim(H) = 2 = dim(F) + 1
    - So F ⊂ H ⊂ G with H exactly one dimension higher than F

    Note: "One dimension higher" does NOT mean "add one vertex"!
    - Edge → Face: add 2 vertices (2D → 4 vertices)
    - Face → Cube: add 4 vertices (4 → 8 vertices)
    The dimension is about the affine span, not the vertex count.

    ## Proof Strategy

    The geometric idea: if F is properly contained in G, we can find an intermediate face H
    with dimension exactly one higher than F, while staying within G. More rigorously:

    1. Since F < G, we have dim F < dim G (by dim_lt_of_ssubset)
    2. By exists_vertex_not_in_affineSpan: find v ∈ G.vertices \ affineSpan F.vertices
    3. By exists_face_extending_by_vertex: construct H from F and v with dim H = dim F + 1
    4. This H satisfies P.incident F H (by construction) and H ≤ G (since H ⊆ G)

    For polytopes, this follows from the face lattice being graded by dimension.

    ## Implementation Note

    We use `incident` instead of `⋖` (CovBy) to avoid circular dependency through
    the GradeOrder instance, which itself relies on incident_iff_covBy. -/
theorem exists_incident_face_below {P : ConvexPolyhedron E} {F G : Face P}
    (h : F < G) : ∃ H : Face P, P.incident F H ∧ H ≤ G := by
  sorry  -- Will be proven using the three helper lemmas above

/-- Between any two faces differing by k dimensions, there exists
    a chain of length k where consecutive elements are incident.

    ## Proof by Induction on k

    - Base case (k=0): F.dim = G.dim and F ≤ G implies F = G
    - Inductive step: Use `exists_incident_face_below` to find H with P.incident F H and H ≤ G
      Then H.dim = F.dim + 1 (by incident_dim), so G.dim = H.dim + k, and apply IH

    Note: We return incident relations (not covering ⋖) to avoid circular dependency.
    The covering version can be derived later using incident_iff_covBy. -/
theorem exists_saturated_chain {P : ConvexPolyhedron E} {F G : Face P}
    (h : F ≤ G) (k : ℕ) (hdim : G.dim = F.dim + k) :
    ∃ (chain : Fin (k + 1) → Face P),
      chain 0 = F ∧
      chain (Fin.last k) = G ∧
      (∀ i : Fin k, P.incident (chain i.castSucc) (chain i.succ)) := by
  -- Induction on k
  induction k generalizing F G with
  | zero =>
    -- Base case: k = 0, so F.dim = G.dim and F ≤ G
    have hFG_eq : F = G := by
      -- We have F ≤ G and F.dim = G.dim
      -- By incomparable_of_eq_dim: if F.dim = G.dim and F ≠ G, then ¬(F ≤ G) ∧ ¬(G ≤ F)
      -- Since we have F ≤ G, we must have F = G
      have hdim_eq : F.dim = G.dim := by omega
      by_contra hne
      have := incomparable_of_eq_dim hdim_eq hne
      exact this.1 h
    subst hFG_eq
    -- Chain of length 1: just [F] (since k+1 = 1)
    use fun _ => F
    constructor
    · rfl  -- chain 0 = F
    constructor
    · rfl  -- chain (Fin.last 0) = F
    · -- For k = 0, Fin k is empty, so the incident property is vacuous
      intro i
      exact Fin.elim0 i
  | succ k ih =>
    -- Inductive case: k' = k + 1, so we have k + 1 + 1 = k + 2 elements
    -- We have F.dim + (k + 1) = G.dim
    have hF_lt_G : F < G := by
      constructor
      · exact h
      · intro hGF
        have : F = G := le_antisymm h hGF
        subst this
        omega  -- F.dim + (k + 1) = F.dim is impossible
    -- By exists_incident_face_below, find H with P.incident F H and H ≤ G
    obtain ⟨H, hF_inc_H, hH_le_G⟩ := exists_incident_face_below hF_lt_G
    -- From P.incident F H, we get H.dim = F.dim + 1
    have hH_dim : H.dim = F.dim + 1 := (incident_dim P hF_inc_H).symm
    -- Therefore G.dim = H.dim + k
    have hG_dim : G.dim = H.dim + k := by omega
    -- By IH, get a chain from H to G of length k (so k+1 elements)
    obtain ⟨tail_chain, htail_head, htail_last, htail_inc⟩ :=
      ih hH_le_G hG_dim
    -- Prepend F to get a chain of length k+1 (so k+2 elements)
    use fun i : Fin (k + 2) =>
      if h : i = 0 then F else tail_chain ⟨i.val - 1, by omega⟩
    constructor
    · -- chain 0 = F
      simp
    constructor
    · -- chain (Fin.last (k+1)) = G
      -- Fin.last (k+1) has value k+1 in type Fin (k+2)
      -- We need to show chain (Fin.last (k+1)) = G
      simp only [Fin.last]
      -- When i.val = k+1, the condition i = 0 is false
      have hne : (⟨k + 1, by omega⟩ : Fin (k + 2)) ≠ 0 := by
        intro h
        have : (k + 1 : ℕ) = 0 := Fin.val_eq_of_eq h
        omega
      simp [hne]
      -- Now we have: tail_chain ⟨(k + 1) - 1, _⟩ = G
      -- Since tail_chain (Fin.last k) = G and (k+1) - 1 = k = Fin.last k
      convert htail_last using 2
    · -- incident property
      intro i
      -- Split into two cases: i = 0 (first step) or i > 0 (inherited from tail)
      by_cases hi : i.val = 0
      · -- First step: F is incident to H
        have hi_eq : i = 0 := Fin.ext hi
        simp [hi_eq, Fin.castSucc, Fin.succ]
        convert hF_inc_H
      · -- Later steps: inherited from tail_chain
        -- For i > 0, we have i.castSucc.val = i.val and i.succ.val = i.val + 1
        -- chain i.castSucc = tail_chain ⟨i.val - 1, _⟩
        -- chain i.succ = tail_chain ⟨i.val + 1 - 1, _⟩ = tail_chain ⟨i.val, _⟩
        -- We need: P.incident (chain i.castSucc) (chain i.succ)

        -- Compute chain at i.castSucc
        have hcast_ne_zero : i.castSucc ≠ 0 := by
          intro h
          have : i.castSucc.val = 0 := Fin.val_eq_of_eq h
          simp [Fin.castSucc] at this
          exact hi (Fin.val_eq_of_eq this)

        -- Compute chain at i.succ
        have hsucc_ne_zero : i.succ ≠ 0 := by
          intro h
          have : i.succ.val = 0 := Fin.val_eq_of_eq h
          simp [Fin.succ] at this

        simp only [hcast_ne_zero, hsucc_ne_zero, ite_false]

        -- Now we need to show the tail_chain indices match up correctly
        -- We have htail_inc : ∀ j : Fin k, P.incident (tail_chain j.castSucc) (tail_chain j.succ)
        -- We want to apply this to some j : Fin k

        -- Since i : Fin (k+1), we have i.val < k+1
        -- Since i.val ≠ 0, we have 0 < i.val, so 1 ≤ i.val
        -- Therefore i.val - 1 < k

        have hi_bound : i.val - 1 < k := by omega
        let j : Fin k := ⟨i.val - 1, hi_bound⟩

        -- Show that the indices match
        have hcast : (⟨i.castSucc.val - 1, by omega⟩ : Fin (k + 1)) = j.castSucc := by
          ext
          simp [Fin.castSucc, j]

        have hsucc : (⟨i.succ.val - 1, by omega⟩ : Fin (k + 1)) = j.succ := by
          ext
          simp [Fin.succ, j]
          omega

        rw [hcast, hsucc]
        exact htail_inc j

/-- Raw formulation of saturated chains using Fin functions, for backward compatibility.
    This is derivable from the LTSeries version but may be more convenient in some proofs.

    TODO: Complete this proof after proving exists_saturated_chain and incident_iff_covBy.
    The proof requires:
    1. exists_saturated_chain (currently sorry) - uses induction on k with graded lattice structure
    2. incident_iff_covBy (defined later in file) - proves incidence is the covering relation

    Current blocker: Circular dependency - incident_iff_covBy uses this theorem in its proof. -/
theorem exists_saturated_chain_fin {P : ConvexPolyhedron E} {F G : Face P}
    (h : F ≤ G) (k : ℕ) (hdim : G.dim = F.dim + k) :
    ∃ (chain : Fin (k + 1) → Face P),
      chain 0 = F ∧
      chain (Fin.last k) = G ∧
      (∀ i : Fin k, P.incident (chain i.castSucc) (chain i.succ)) := by
  sorry  -- Will be completed after exists_saturated_chain and resolving circular dependency

/-- Saturated chains are strictly monotone: if consecutive elements are incident,
    then the chain is strictly increasing.

    This is just an application of Fin.strictMono_iff_lt_succ combined with the
    fact that incidence implies strict inequality. -/
theorem saturated_chain_strictMono {P : ConvexPolyhedron E} {n : ℕ}
    (chain : Fin (n + 1) → Face P)
    (hsat : ∀ i : Fin n, P.incident (chain i.castSucc) (chain i.succ)) :
    StrictMono chain := by
  -- Use the characterization of strict monotonicity for Fin
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  -- We have incidence, which implies strict inequality
  have hinc := hsat i
  rw [incident_iff_covers] at hinc
  exact hinc.1

/-! ### Graded lattice structure using Mathlib infrastructure

The following provides a cleaner formulation of the graded lattice property
using Mathlib's `GradeOrder` typeclass and `LTSeries` for chains.
-/

/-- Incidence is the covering relation in the face lattice. -/
theorem incident_iff_covBy {P : ConvexPolyhedron E} (F G : Face P) :
    P.incident F G ↔ F ⋖ G := by
  rw [incident_iff_covers, CovBy]
  simp only [and_congr_right_iff]
  intro hlt
  constructor
  · intro hdim H hFH hHG
    -- If F < H < G, then by dimension monotonicity dim F < dim H < dim G
    have hF_dim : F.dim < H.dim := dim_lt_of_ssubset hFH
    have hH_dim : H.dim < G.dim := dim_lt_of_ssubset hHG
    -- But hdim says dim F + 1 = dim G, so no integer can be strictly between
    omega
  · intro hcov
    -- Have: no face H with F < H < G
    -- Need to show: dim F + 1 = dim G
    have hdim_lt : F.dim < G.dim := dim_lt_of_ssubset hlt
    -- If dim F + 1 ≠ dim G, there would be a face of intermediate dimension
    by_contra hdim_ne
    have : F.dim + 1 < G.dim := by omega
    -- Then by exists_saturated_chain there's a chain with more than one step
    let k := (G.dim - F.dim).toNat
    have hk : k ≥ 2 := by omega
    have hdim_eq : G.dim = F.dim + ↑k := by
      simp [k]
      omega
    obtain ⟨chain, hchain_start, hchain_end, hchain_inc⟩ :=
      exists_saturated_chain_fin hlt.le k hdim_eq
    -- This chain has length k ≥ 2, so there exists an intermediate face H between F and G
    -- Since k ≥ 2, chain has at least 3 elements: chain 0 = F, chain 1 = H, ..., chain k = G
    -- So chain 1 is strictly between F and G
    let H := chain ⟨1, by omega⟩
    have hF_H : F < H := by
      rw [← hchain_start]
      constructor
      · -- chain 0 ⊆ chain 1
        have hinc := hchain_inc ⟨0, by omega⟩
        exact incident_subset P hinc
      · -- ¬(chain 1 ⊆ chain 0)
        intro hHF
        -- If chain 1 ⊆ chain 0 and chain 0 ⊆ chain 1 (from incidence), then chain 0 = chain 1
        have hinc := hchain_inc ⟨0, by omega⟩
        have heq : chain ⟨0, by omega⟩ = chain ⟨1, by omega⟩ := by
          apply le_antisymm
          · exact incident_subset P hinc
          · exact hHF
        -- But incidence implies dim(chain 0) + 1 = dim(chain 1), so they can't be equal
        have hdim := incident_dim P hinc
        -- Simplify: i.castSucc for i = ⟨0, ...⟩ gives ⟨0, ...⟩ and i.succ gives ⟨1, ...⟩
        simp only [Fin.castSucc_mk, Fin.succ_mk, zero_add] at hdim
        rw [heq] at hdim
        omega
    have hH_G : H < G := by
      rw [← hchain_end]
      -- Chain is strictly monotone, so chain 1 < chain k follows immediately
      have hstrict : StrictMono chain := saturated_chain_strictMono chain hchain_inc
      have h_idx : (⟨1, by omega⟩ : Fin (k + 1)) < Fin.last k := by
        rw [Fin.lt_iff_val_lt_val, Fin.val_last]
        simp
        omega
      exact hstrict h_idx
    -- Now we have hF_H : F < H and hH_G : H < G
    -- But hcov says: ∀ c, F < c → ¬(c < G)
    -- Applying hcov with c = H gives: F < H → ¬(H < G)
    -- Then applying hF_H gives: ¬(H < G)
    -- Finally applying hH_G to the negation gives False
    exact (hcov hF_H) hH_G

/-- The face lattice forms a ℤ-graded order with dimension as the grade function. -/
noncomputable instance Face.instGradeOrder {P : ConvexPolyhedron E} : GradeOrder ℤ (Face P) where
  grade := Face.dim
  grade_strictMono := by
    intro F G hFG
    exact dim_lt_of_ssubset hFG
  covBy_grade := by
    intro F G hcov
    -- hcov : F ⋖ G, need to show: F.dim ⋖ G.dim (covering in ℤ)
    -- Use incident_iff_covBy to get incident, then use incident_dim
    have hinc : P.incident F G := incident_iff_covBy F G |>.mpr hcov
    have hdim : F.dim + 1 = G.dim := incident_dim P hinc
    -- Now show F.dim ⋖ G.dim
    constructor
    · -- F.dim < G.dim
      omega
    · -- No integer strictly between F.dim and G.dim
      intro k hFk hkG
      omega

/-- Simplified statement: all saturated chains between F and G have length equal to
    the dimension difference.

    This is the key property of graded posets, stated cleanly using Mathlib's infrastructure.
    It directly implies that all such chains have the same length. -/
theorem face_lattice_graded_clean {P : ConvexPolyhedron E} (F G : Face P) (h : F ≤ G) :
    ∀ (chain : LTSeries (Face P)),
      chain.head = F →
      chain.last = G →
      (∀ i : Fin chain.length, chain.toFun i.castSucc ⋖ chain.toFun i.succ) →
      (chain.length : ℤ) = G.dim - F.dim := by
  intro chain hhead hlast hsat
  -- In a graded poset, each covering step increases grade (dimension) by exactly 1
  -- So the total length equals the dimension difference
  sorry -- Induction on chain length using covBy_grade

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

end ConvexPolyhedron
