/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import ConvexPolyhedra.Rockafellar.Chapter06.Theorem61
import ConvexPolyhedra.Rockafellar.Chapter06.Theorem64

/-!
# Rockafellar Chapter 6: Relative Interiors

This file aggregates results from Chapter 6 of Rockafellar's "Convex Analysis" (1970).

## Main results

From `Theorem61.lean`:
* `Convex.combo_intrinsicInterior_intrinsicClosure_mem_intrinsicInterior` - Theorem 6.1
* `Convex.intrinsicClosure_eq_self_of_full_dim` - Full-dimensional sets are relatively closed
* Rockafellar's reduction technique infrastructure
* Affine equivalence preservation properties

From `Theorem64.lean`:
* `mem_intrinsicInterior_iff_extension` - Theorem 6.4
* `affineSubspace_translation_homeomorph` - Affine-to-vector transfer

## Tags

convex, relative interior, intrinsic topology
-/
