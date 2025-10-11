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
import Mathlib.Order.Grade
import Mathlib.Order.RelSeries
import Mathlib.Order.Cover

/-!
# Convex Polyhedron - Basic Structure

This file defines the basic structure of a convex polyhedron using V-representation
(vertex representation) as the convex hull of a finite set of points.

## Main definitions

* `ConvexPolyhedron E` - A convex polyhedron as convex hull of finitely many vertices
* `ConvexPolyhedron.vertices` - The vertices of the polyhedron
* `ConvexPolyhedron.dim` - Affine dimension of the polyhedron
* `affineDim` - Helper for computing affine dimension

## Main results

* `ConvexPolyhedron.compact` - Every polyhedron is compact
* `ConvexPolyhedron.convex` - Every polyhedron is convex
* `ConvexPolyhedron.bounded` - Every polyhedron is bounded
* `ConvexPolyhedron.extremePoints_eq_vertices` - Extreme points are exactly vertices

## Implementation notes

This is the foundation for the Euler polyhedron formula formalization. The polyhedron
is represented as a finite set of vertices that are exactly the extreme points of their
convex hull (irredundancy condition).

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

end ConvexPolyhedron
