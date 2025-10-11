/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import ConvexPolyhedra.Polyhedron
import ConvexPolyhedra.Face
import ConvexPolyhedra.FaceLattice
import ConvexPolyhedra.ChainComplex
import ConvexPolyhedra.Euler3D

/-!
# Convex Polyhedra - V-Representation and Euler's Formula

This module imports all the modular components for formalizing Euler's polyhedron formula
using the V-representation (vertex representation) of convex polyhedra.

## Module Structure

* `ConvexPolyhedra.Polyhedron` - Basic polyhedron structure and properties
* `ConvexPolyhedra.Face` - Face structure and incidence relations
* `ConvexPolyhedra.FaceLattice` - Face lattice theory and graded structure
* `ConvexPolyhedra.ChainComplex` - Chain complex construction from faces
* `ConvexPolyhedra.Euler3D` - Euler's formula for 3D polyhedra (V - E + F = 2)

-/
