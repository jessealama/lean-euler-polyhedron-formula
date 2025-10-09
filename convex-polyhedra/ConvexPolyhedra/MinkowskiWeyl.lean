/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import ConvexPolyhedra.Basic
import ConvexPolyhedra.VRepresentation

/-!
# Minkowski-Weyl Theorem

This file states the Minkowski-Weyl theorem, which establishes the equivalence between
the H-representation (intersection of half-spaces) and V-representation (convex hull of
vertices) for bounded polyhedra.

## Main definitions

* `HPolyhedron.toConvexPolyhedron` - Convert bounded H-polyhedron to V-polyhedron
* `ConvexPolyhedron.toHPolyhedron` - Convert V-polyhedron to H-polyhedron

## Main results

* `minkowski_weyl` - The two representations define the same geometric object
* `hpoly_iff_vpoly` - Characterization: bounded H-polyhedra ↔ V-polyhedra

## Implementation notes

For now, all proofs are `sorry`. The full Minkowski-Weyl theorem is a deep result
requiring:
1. Extreme points of bounded H-polyhedra are finite (Minkowski's theorem)
2. Every V-polyhedron has a supporting hyperplane description
3. The two constructions are inverse up to equality of underlying sets

This is a substantial theorem that we defer for later development. For Euler's formula,
we work primarily with the V-representation and don't need the full equivalence.

## References

* Minkowski-Weyl theorem: https://people.inf.ethz.ch/fukudak/polyfaq/node14.html
* Characterization (a): H-representation as `{x : Ax ≤ b}`
* Characterization (b): V-representation as `conv(v₁,...,vₙ)` (for bounded case)

-/

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace HPolyhedron

/-- Extract the set of extreme points from a bounded H-polyhedron.

This is the key step in converting from H to V representation. The extreme points
of a bounded polyhedron form a finite set, and these become the vertices of the
V-representation.

Proof sketch:
1. Show extreme points exist (compactness + Krein-Milman)
2. Show they are finite (bounded polyhedra have finitely many exposed faces)
3. Each extreme point is an intersection of d hyperplanes (dimension d)
-/
noncomputable def extremePointsFinset (P : HPolyhedron E) (hb : P.isBounded) : Finset E := by
  sorry

/-- The extreme points form a nonempty set (bounded polyhedra are nonempty) -/
theorem extremePointsFinset_nonempty (P : HPolyhedron E) (hb : P.isBounded) :
    (P.extremePointsFinset hb).Nonempty := by
  sorry

/-- The extreme points are exactly the extreme points of the polyhedron -/
theorem extremePointsFinset_eq (P : HPolyhedron E) (hb : P.isBounded) :
    (P.extremePointsFinset hb : Set E) = P.toSet.extremePoints ℝ := by
  sorry

/-- Convert a bounded H-polyhedron to a V-polyhedron.

This is one direction of the Minkowski-Weyl theorem: every bounded intersection of
half-spaces can be expressed as a convex hull of finitely many points.

The construction:
1. Find all extreme points (vertices)
2. Show these points generate the same set via convex hull
-/
noncomputable def toConvexPolyhedron (P : HPolyhedron E) (hb : P.isBounded) :
    ConvexPolyhedron E := {
  vertices := P.extremePointsFinset hb
  nonempty := P.extremePointsFinset_nonempty hb
  vertices_are_extreme := by sorry
}

/-- The V-polyhedron has the same underlying set as the H-polyhedron -/
theorem toConvexPolyhedron_toSet_eq (P : HPolyhedron E) (hb : P.isBounded) :
    (P.toConvexPolyhedron hb).toSet = P.toSet := by
  sorry

end HPolyhedron

namespace ConvexPolyhedron

/-- Find a supporting hyperplane for a face of the polyhedron.

For each face F of the V-polyhedron, there exists a half-space whose intersection
with the polyhedron is exactly F. The collection of these half-spaces gives the
H-representation.

Proof sketch:
1. Use separation theorem: for any point outside the face, there's a separating hyperplane
2. The supporting hyperplane achieves maximum at face vertices
3. Finitely many faces → finitely many half-spaces
-/
noncomputable def supportingHalfSpace (P : ConvexPolyhedron E) (F : P.Face) : HalfSpace E := by
  sorry

/-- The collection of all supporting half-spaces -/
noncomputable def supportingHalfSpaces (P : ConvexPolyhedron E) : Finset (HalfSpace E) := by
  sorry

/-- The supporting half-spaces are nonempty -/
theorem supportingHalfSpaces_nonempty (P : ConvexPolyhedron E) :
    P.supportingHalfSpaces.Nonempty := by
  sorry

/-- Convert a V-polyhedron to an H-polyhedron.

This is the other direction of Minkowski-Weyl: every convex hull of finitely many
points can be described as an intersection of finitely many half-spaces.

The construction:
1. For each face, find a supporting hyperplane
2. Take the intersection of all corresponding half-spaces
-/
noncomputable def toHPolyhedron (P : ConvexPolyhedron E) : HPolyhedron E := {
  halfSpaces := P.supportingHalfSpaces
  nonempty := P.supportingHalfSpaces_nonempty
}

/-- The H-polyhedron has the same underlying set as the V-polyhedron -/
theorem toHPolyhedron_toSet_eq (P : ConvexPolyhedron E) :
    (P.toHPolyhedron).toSet = P.toSet := by
  sorry

/-- V-polyhedra are automatically bounded -/
theorem toHPolyhedron_isBounded (P : ConvexPolyhedron E) :
    (P.toHPolyhedron).isBounded := by
  sorry

end ConvexPolyhedron

section MinkowskiWeyl

/-- The Minkowski-Weyl Theorem: H ↔ V equivalence for bounded polyhedra.

This theorem states that bounded H-polyhedra and V-polyhedra represent the same
class of geometric objects. Specifically:

(a) Every bounded H-polyhedron can be expressed as a convex hull of vertices
(b) Every V-polyhedron can be expressed as an intersection of half-spaces
(c) These operations are inverse (up to set equality)

This is a fundamental result in polyhedral theory and computational geometry.

For the unbounded case, the V-representation needs to include rays (recession cone),
but for Euler's formula we only need the bounded case.
-/
theorem minkowski_weyl_forward (P : HPolyhedron E) (hb : P.isBounded) :
    (P.toConvexPolyhedron hb).toSet = P.toSet :=
  P.toConvexPolyhedron_toSet_eq hb

theorem minkowski_weyl_backward (P : ConvexPolyhedron E) :
    (P.toHPolyhedron).toSet = P.toSet :=
  P.toHPolyhedron_toSet_eq

/-- Bounded H-polyhedra and V-polyhedra define the same sets -/
theorem minkowski_weyl (P : HPolyhedron E) (hb : P.isBounded) :
    ∃ Q : ConvexPolyhedron E, Q.toSet = P.toSet ∧
    ∃ P' : HPolyhedron E, P'.toSet = Q.toSet ∧ P'.toSet = P.toSet := by
  use P.toConvexPolyhedron hb
  constructor
  · exact minkowski_weyl_forward P hb
  · use (P.toConvexPolyhedron hb).toHPolyhedron
    constructor
    · exact minkowski_weyl_backward _
    · rw [minkowski_weyl_backward, minkowski_weyl_forward]

/-- Characterization: A set is a bounded H-polyhedron iff it's a V-polyhedron.

More precisely: For bounded sets, the H-representation and V-representation
generate the same class of sets. -/
theorem hpoly_iff_vpoly (S : Set E) :
    (∃ P : HPolyhedron E, P.isBounded ∧ P.toSet = S) ↔
    (∃ Q : ConvexPolyhedron E, Q.toSet = S) := by
  constructor
  · intro ⟨P, hb, hS⟩
    use P.toConvexPolyhedron hb
    rw [minkowski_weyl_forward P hb, hS]
  · intro ⟨Q, hQ⟩
    use Q.toHPolyhedron
    constructor
    · exact Q.toHPolyhedron_isBounded
    · rw [minkowski_weyl_backward, hQ]

/-- The operations are inverse: H → V → H preserves the set -/
theorem toHPolyhedron_toConvexPolyhedron (P : HPolyhedron E) (hb : P.isBounded) :
    ((P.toConvexPolyhedron hb).toHPolyhedron).toSet = P.toSet := by
  rw [minkowski_weyl_backward, minkowski_weyl_forward]

/-- The operations are inverse: V → H → V preserves the set -/
theorem toConvexPolyhedron_toHPolyhedron (Q : ConvexPolyhedron E) :
    ((Q.toHPolyhedron).toConvexPolyhedron Q.toHPolyhedron_isBounded).toSet = Q.toSet := by
  rw [minkowski_weyl_forward, minkowski_weyl_backward]

end MinkowskiWeyl

/-!
## Notes on the proof strategy

The full proof of Minkowski-Weyl requires several deep results:

### H → V direction (bounded H-polyhedra have finite extreme points)

1. **Extreme points exist**: By Krein-Milman theorem, compact convex sets are the
   closed convex hull of their extreme points. Bounded H-polyhedra are compact.

2. **Extreme points are finite**: Each extreme point is the unique solution to d
   linearly independent equations from the half-space constraints (where d is the
   dimension). Since there are finitely many constraints, there are finitely many
   such solutions.

3. **Extreme points generate the set**: The polyhedron equals the convex hull of
   its extreme points (this is the key part of Krein-Milman for polytopes).

### V → H direction (convex hulls have supporting hyperplane descriptions)

1. **Supporting hyperplanes exist**: For each face of the polytope, there exists a
   supporting hyperplane (by the separating hyperplane theorem).

2. **Faces correspond to constraints**: Each facet (maximal proper face) corresponds
   to exactly one inequality in the minimal H-representation.

3. **Intersection equals convex hull**: The intersection of all supporting half-spaces
   equals the original polytope.

### For Euler's formula

We primarily work with the V-representation, so we don't need the full Minkowski-Weyl
theorem. We can state it here for completeness and prove it later if needed.

The key property we need is that V-polyhedra have well-defined face lattices, which
we can use to construct chain complexes.
-/
