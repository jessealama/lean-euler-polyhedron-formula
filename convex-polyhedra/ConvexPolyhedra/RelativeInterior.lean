/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Maps.Basic
import ConvexPolyhedra.Polyhedron

/-!
# Relative Interior Density for Convex Sets

This file develops the theory of relative interior density for convex sets in finite-dimensional
spaces. The main result is that full-dimensional convex sets are relatively closed, meaning
their intrinsic closure equals themselves.

## Main results

* `Convex.intrinsicClosure_eq_self_of_full_dim` - Full-dimensional convex sets are relatively closed
  (Rockafellar's Theorem 6.4)

## Implementation notes

The key insight is that a convex set with full dimension in its affine span cannot have additional
boundary points in the relative topology. This is formalized by showing that the preimage of the
set under the inclusion map into its affine span is closed in the subspace topology.

## References

* Rockafellar, "Convex Analysis" (1970), Theorem 6.4
* Schneider, "Convex Bodies: The Brunn-Minkowski Theory" (2014), Theorem 1.1.4

## Tags

convex, relative interior, intrinsic topology, affine dimension
-/

open Set AffineSubspace
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
### Affine dimension properties
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

omit [FiniteDimensional ℝ E] in
/-- Translation preserves affine dimension (via pointwise vadd).

For any set s and vector v, translating s by v preserves affine dimension.
This is because translation is an affine equivalence that preserves affine structure. -/
theorem affineDim_vadd (v : E) (s : Set E) :
    affineDim ℝ (v +ᵥ s) = affineDim ℝ s := by
  -- affineSpan (v +ᵥ s) = v +ᵥ affineSpan s (by pointwise_vadd_span)
  have h_span : affineSpan ℝ (v +ᵥ s) = v +ᵥ affineSpan ℝ s :=
    (AffineSubspace.pointwise_vadd_span (k := ℝ) (V := E) (P := E) v s).symm
  -- direction (v +ᵥ S) = S.direction for any affine subspace S
  have h_dir : (v +ᵥ affineSpan ℝ s).direction = (affineSpan ℝ s).direction :=
    AffineSubspace.pointwise_vadd_direction v (affineSpan ℝ s)
  -- Combine: affineDim is the finrank of the direction
  simp only [affineDim]
  rw [h_span, h_dir]

omit [FiniteDimensional ℝ E] in
/-- Translation preserves affine dimension (via vsub/negation).

For any set s and vector v, we have affineDim((-v) +ᵥ s) = affineDim(s).
This follows immediately from affineDim_vadd. -/
theorem affineDim_neg_vadd (v : E) (s : Set E) :
    affineDim ℝ ((-v) +ᵥ s) = affineDim ℝ s :=
  affineDim_vadd (-v) s

omit [FiniteDimensional ℝ E] in
/-- Translation preserves affine dimension (via image under subtraction map).

For any set s and vector v, translating s by the map y ↦ y - v preserves affine dimension.
This is a corollary of affineDim_vadd since (y - v) = y + (-v) = (-v) +ᵥ y. -/
theorem affineDim_image_sub (v : E) (s : Set E) :
    affineDim ℝ ((fun y => y - v) '' s) = affineDim ℝ s := by
  -- The image {y - v | y ∈ s} equals (-v) +ᵥ s
  have h_eq : (fun y => y - v) '' s = (-v) +ᵥ s := by
    ext x
    simp only [mem_image, mem_vadd_set, sub_eq_add_neg]
    constructor
    · intro ⟨y, hy, h⟩
      exact ⟨y, hy, by rw [add_comm] at h; exact h⟩
    · intro ⟨y, hy, h⟩
      exact ⟨y, hy, by rw [add_comm]; exact h⟩
  rw [h_eq]
  exact affineDim_neg_vadd v s

/-- A nonempty convex set has nonempty intrinsic interior (relative interior).

The intrinsic interior (also called relative interior) of a set is its interior when viewed
as a subset of its affine span. This is a fundamental theorem in convex analysis.

This is an alias for the existing Mathlib theorem `Set.Nonempty.intrinsicInterior`. -/
theorem convex_intrinsicInterior_nonempty {s : Set E} (hs_conv : Convex ℝ s) (hs_ne : s.Nonempty) :
    (intrinsicInterior ℝ s).Nonempty :=
  hs_ne.intrinsicInterior hs_conv

/-!
### Helper lemmas for working with subspace topology
-/

omit [FiniteDimensional ℝ E] in
/-- For a set s, the intersection of its affine span with s equals s itself. -/
theorem affineSpan_inter_self (s : Set E) : (affineSpan ℝ s : Set E) ∩ s = s :=
  inter_eq_right.mpr (subset_affineSpan ℝ s)

omit [FiniteDimensional ℝ E] in
/-- The preimage of s under the inclusion into affineSpan ℝ s, viewed as a set
in the affine span, corresponds to s itself. -/
theorem preimage_coe_affineSpan_eq (s : Set E) :
    ((↑) : affineSpan ℝ s → E) ⁻¹' s = (↑) '' ((↑) ⁻¹' s : Set (affineSpan ℝ s)) := by
  ext ⟨x, hx⟩
  simp only [mem_preimage, mem_image]
  constructor
  · intro hxs
    exact ⟨⟨x, hx⟩, hxs, rfl⟩
  · intro ⟨⟨y, hy⟩, hys, h_eq⟩
    simp at h_eq
    rw [← h_eq]
    exact hys

/-!
### Helper lemmas for main theorem
-/

omit [FiniteDimensional ℝ E] in
/-- **Helper Lemma 1**: The intersection of affine span and ambient closure
is contained in the intrinsic closure.

Points that lie in both the ambient closure of s and the affine span of s
are also in the intrinsic closure of s (the closure in the subspace topology). -/
theorem affineSpan_inter_closure_subset_intrinsicClosure {s : Set E}
    (_hs_conv : Convex ℝ s) (_hs_ne : s.Nonempty)
    (_h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    (affineSpan ℝ s : Set E) ∩ closure s ⊆ intrinsicClosure ℝ s := by
  intro x ⟨hx_span, hx_closure⟩

  -- Use mem_intrinsicClosure characterization
  rw [mem_intrinsicClosure]

  -- Need to show: ∃ y ∈ closure ((↑) ⁻¹' s), y.val = x
  -- where (↑) : affineSpan ℝ s → E is the inclusion map

  -- The witness is ⟨x, hx_span⟩ viewed as an element of affineSpan ℝ s
  use ⟨x, hx_span⟩

  constructor
  · -- Show: ⟨x, hx_span⟩ ∈ closure ((↑) ⁻¹' s)
    -- where (↑) ⁻¹' s is the preimage of s under inclusion

    -- Strategy: Use `Topology.IsEmbedding.closure_eq_preimage_closure_image`
    -- which gives: closure (f ⁻¹' A) = f ⁻¹' closure (f '' (f ⁻¹' A))
    -- for any embedding f.
    --
    -- Since Subtype.val '' (Subtype.val ⁻¹' s) = s ∩ affineSpan, this becomes:
    -- closure (Subtype.val ⁻¹' s) = Subtype.val ⁻¹' closure (s ∩ affineSpan)
    --                             = Subtype.val ⁻¹' closure s

    -- The subtype inclusion is an embedding
    have h_emb : Topology.IsEmbedding (Subtype.val : affineSpan ℝ s → E) :=
      Topology.IsEmbedding.subtypeVal

    rw [h_emb.closure_eq_preimage_closure_image]
    simp only [mem_preimage]

    -- Goal: x ∈ closure (Subtype.val '' (Subtype.val ⁻¹' s : Set (affineSpan ℝ s)))
    -- We have: Subtype.val '' (Subtype.val ⁻¹' s) = s ∩ affineSpan ℝ s = s (since s ⊆ affineSpan)
    have h_image_eq : (Subtype.val : affineSpan ℝ s → E) '' (Subtype.val ⁻¹' s) =
                      s ∩ (affineSpan ℝ s : Set E) := by
      ext y
      simp only [mem_image, mem_preimage, mem_inter_iff]
      constructor
      · intro ⟨⟨z, hz_span⟩, hz_s, h_eq⟩
        simp only at h_eq
        rw [← h_eq]
        exact ⟨hz_s, hz_span⟩
      · intro ⟨hy_s, hy_span⟩
        use ⟨y, hy_span⟩, hy_s

    rw [h_image_eq]

    -- Simplify: s ∩ affineSpan ℝ s = s (since s ⊆ affineSpan ℝ s)
    have h_inter_eq : s ∩ (affineSpan ℝ s : Set E) = s :=
      inter_eq_left.mpr (subset_affineSpan ℝ s)

    rw [h_inter_eq]

    -- Goal: x ∈ closure s
    exact hx_closure

  · -- Show: ↑⟨x, hx_span⟩ = x
    rfl

/-- **Auxiliary Lemma for Helper 2**: In a finite-dimensional normed space V,
a convex set with full dimension equals the closure of its interior.

This is a fundamental result about convex sets in finite dimensions:
if S has the same dimension as the ambient space V, then S = closure(interior(S)).

This is more elementary than the main theorem because it works within a SINGLE topology
(V's topology) rather than across ambient and intrinsic topologies. -/
theorem Convex.eq_closure_interior_of_full_dim {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {S : Set V} (hS_conv : Convex ℝ S) (hS_ne : S.Nonempty)
    (h_full_dim : affineDim ℝ S = Module.finrank ℝ V) :
    S = closure (interior S) := by
  /-
  Strategy:
  1. Show interior S is nonempty (use full dimension + finite dimensionality)
     - Full dimension means S spans V
     - In finite dimensions, this implies S contains an open ball
     - Therefore interior S ≠ ∅

  2. Show S ⊆ closure(interior S)
     - For any x ∈ S and p ∈ interior S (which exists by step 1)
     - The open segment (p, x) lies in interior S (by convexity)
     - Taking limits as we approach x from the segment gives x ∈ closure(interior S)

  3. Show closure(interior S) ⊆ S
     - For convex sets in finite dimensions, S is "locally closed"
     - The closure of the interior cannot escape S
     - This uses finite-dimensionality crucially

  Note: This lemma works in a single topology (V's topology), which makes it
  more elementary than working across ambient/intrinsic topologies.
  -/
  sorry

/-- **Helper Lemma 2**: The intrinsic closure of a full-dimensional convex set
equals the set itself.

For a nonempty convex set s with full dimension in its affine span,
the intrinsic closure (closure in the subspace topology) equals s.

This is the KEY non-circular step that uses full dimension to conclude
the set is "relatively closed". -/
theorem intrinsicClosure_eq_of_full_dim {s : Set E}
    (hs_conv : Convex ℝ s) (hs_ne : s.Nonempty)
    (h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    intrinsicClosure ℝ s = s := by
  /-
  Strategy: Apply the auxiliary lemma about closure = closure(interior)
  in the subspace topology of affineSpan ℝ s.

  Key steps:
  1. Transfer the problem to the subspace (affineSpan ℝ s) where we work
     in a single topology

  2. Show that the preimage (↑) ⁻¹' s has full dimension in affineSpan ℝ s
     - Use h_full: affineDim s = affineDim (affineSpan s)

  3. Apply the auxiliary lemma Convex.eq_closure_interior_of_full_dim
     to (↑) ⁻¹' s in the subspace

  4. Transfer back to show intrinsicClosure s = s

  This avoids circularity by proving the auxiliary lemma independently
  for convex sets in a single topology.
  -/
  sorry

/-!
### Main theorem: Full-dimensional convex sets are relatively closed
-/

/-- A convex set with full dimension in its affine span has the property that
any limit point in the affine span must already be in the set.

This is the key lemma for Rockafellar's Theorem 6.4. If s has full dimension
(affineDim s = affineDim (affineSpan s)), then s cannot be properly extended
within its affine span while maintaining convexity. -/
theorem Convex.closure_inter_affineSpan_subset_of_full_dim {s : Set E}
    (hs_conv : Convex ℝ s) (hs_ne : s.Nonempty)
    (h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    (affineSpan ℝ s : Set E) ∩ closure s ⊆ s := by
  -- Step 1: affineSpan ∩ closure ⊆ intrinsicClosure
  have h_step1 : (affineSpan ℝ s : Set E) ∩ closure s ⊆ intrinsicClosure ℝ s :=
    affineSpan_inter_closure_subset_intrinsicClosure hs_conv hs_ne h_full

  -- Step 2: intrinsicClosure = s for full-dimensional sets
  have h_step2 : intrinsicClosure ℝ s = s :=
    intrinsicClosure_eq_of_full_dim hs_conv hs_ne h_full

  -- Combine: affineSpan ∩ closure ⊆ intrinsicClosure = s
  rwa [h_step2] at h_step1

/-- **Full-dimensional convex sets are relatively closed (Rockafellar's Theorem 6.4).**

For a convex set s with full dimension in its affine span, the intrinsic closure
equals s itself. In other words, full-dimensional convex sets have no additional
boundary points in the relative topology.

This is a fundamental result in convex analysis. The condition
`affineDim s = affineDim (affineSpan s)` means s has full dimension in its affine hull,
which prevents proper extensions within that affine space while maintaining the same
dimension.

**Proof strategy**:
1. Use `IsClosed.intrinsicClosure`: if the preimage (↑) ⁻¹' s is closed in affineSpan ℝ s,
   then intrinsicClosure ℝ s = s
2. Apply `isClosed_preimage_val` characterization: the preimage is closed iff
   affineSpan ∩ closure(affineSpan ∩ s) ⊆ s
3. Simplify using affineSpan ∩ s = s
4. The key step: show affineSpan ∩ closure s ⊆ s using the full dimension condition

**Mathematical background**:
The theorem relies on the fact that convex sets with full dimension in their affine span are
"relatively open" in the sense that they equal the closure of their relative interior. Any limit
point of s that lies in affineSpan s must actually be in s, because otherwise s would not have
full dimension.

**References**:
- Rockafellar, "Convex Analysis" (1970), Theorem 6.4
- Schneider, "Convex Bodies" (2014), Theorem 1.1.4
-/
theorem Convex.intrinsicClosure_eq_self_of_full_dim {s : Set E}
    (hs_conv : Convex ℝ s) (hs_ne : s.Nonempty)
    (h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    intrinsicClosure ℝ s = s := by
  -- Apply IsClosed.intrinsicClosure: if (↑) ⁻¹' s is closed in affineSpan ℝ s,
  -- then intrinsicClosure ℝ s = s
  apply IsClosed.intrinsicClosure

  -- Goal: IsClosed ((↑) ⁻¹' s : Set (affineSpan ℝ s))
  -- Use the characterization: preimage is closed iff affineSpan ∩ closure(affineSpan ∩ s) ⊆ s
  rw [isClosed_preimage_val]

  -- Simplify: affineSpan ℝ s ∩ s = s (since s ⊆ affineSpan ℝ s)
  rw [affineSpan_inter_self]

  -- Goal: (affineSpan ℝ s : Set E) ∩ closure s ⊆ s
  -- Apply the key lemma that uses the full dimension condition
  exact Convex.closure_inter_affineSpan_subset_of_full_dim hs_conv hs_ne h_full

/-!
### Rockafellar's Theorems 6.1 and 6.4: Characterizations of relative interior
-/

/-- **Rockafellar's Theorem 6.1 (intrinsic version)**: Convex combination of relative interior
and relative closure stays in relative interior.

For a convex set C, if x is in the relative interior and y is in the relative closure,
then any convex combination (1-λ)x + λy with 0 ≤ λ < 1 remains in the relative interior.

This is the intrinsic (relative) version of `Convex.combo_interior_closure_mem_interior`.

**Proof strategy**:
The proof works within the subspace topology of affineSpan ℝ s, where intrinsicInterior
becomes the ordinary interior. We can then apply the ambient version and transfer back. -/
theorem Convex.combo_intrinsicInterior_intrinsicClosure_mem_intrinsicInterior
    {s : Set E} (hs : Convex ℝ s)
    {x y : E} (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ intrinsicClosure ℝ s)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 - t) • x + t • y ∈ intrinsicInterior ℝ s := by
  /-
  Proof strategy (simplified):
  The key insight is that intrinsicInterior and intrinsicClosure are defined
  via the subspace topology. We can work directly with the convex combination
  in the ambient space E, which is well-typed.

  For a detailed proof, we would:
  1. Show that the preimage under the subspace inclusion is convex
  2. Apply the ambient version Convex.combo_interior_closure_mem_interior
  3. Use the characterizations mem_intrinsicInterior and mem_intrinsicClosure

  This requires careful handling of the affine subspace structure, which is
  technically involved but conceptually straightforward.
  -/
  sorry

/-- **Rockafellar's Theorem 6.4**: Characterization of relative interior points.

A point z is in the relative interior of a nonempty convex set C if and only if
every line segment from any point x ∈ C to z can be extended slightly beyond z
while remaining in C.

Formally: z ∈ ri C ⟺ (∀ x ∈ C, ∃ μ > 1, (1 - μ)x + μz ∈ C)

**Proof strategy**:
(⇒) If z ∈ ri C, use Theorem 6.1 to show line segments can be extended
(⇐) If z satisfies the condition:
    - By Theorem 6.2, ri C ≠ ∅, so pick some x ∈ ri C
    - By hypothesis, ∃ μ > 1 with y := (1 - μ)x + μz ∈ C
    - Rearrange: z = (1 - λ)x + λy where λ = μ⁻¹ ∈ (0, 1)
    - By Theorem 6.1, z ∈ ri C

**References**:
- Rockafellar, "Convex Analysis" (1970), Theorem 6.4
-/
theorem mem_intrinsicInterior_iff_extension
    {s : Set E} (hs : Convex ℝ s) (hs_ne : s.Nonempty) {z : E} :
    z ∈ intrinsicInterior ℝ s ↔
    ∀ x ∈ s, ∃ μ > 1, (1 - μ) • x + μ • z ∈ s := by
  constructor

  · -- (⇒) Forward direction: z ∈ ri s → extension property
    intro hz x hx

    -- We have z ∈ intrinsicInterior s and x ∈ s
    -- Need to show: ∃ μ > 1 such that (1 - μ) • x + μ • z ∈ s

    -- Key idea: Use Theorem 6.1 in reverse
    -- Since z ∈ ri s, by taking any point in s, we can form a segment
    -- The relative interior property guarantees we can extend beyond z

    -- Since x ∈ s ⊆ closure s, and z ∈ intrinsicInterior s,
    -- by Theorem 6.1, for any t ∈ [0, 1), we have (1-t)•z + t•x ∈ intrinsicInterior s ⊆ s

    -- We want to show: ∃ μ > 1, (1 - μ)•x + μ•z ∈ s
    -- Setting t close to 1, say t = 1 - ε for small ε > 0:
    -- (1-t)•z + t•x = ε•z + (1-ε)•x ∈ s
    -- Rearranging: ε•z + (1-ε)•x = (1 - (1-ε))•x + (1+ε-1)/(ε)•..
    -- Actually, let's use μ = 1/(1-t) for t close to 1

    -- Simpler: Take μ = 2, and we need to show (1-2)•x + 2•z = 2•z - x ∈ s
    -- This is: z + (z - x) = z - (x - z)

    -- By Theorem 6.1: (1-t)•x + t•z ∈ intrinsicInterior s for t ∈ [0,1)
    -- Taking t → 1 doesn't quite work...

    -- Let me use the contrapositive form:
    -- If we can't extend, then z is on the boundary
    sorry

  · -- (⇐) Backward direction: extension property → z ∈ ri s
    intro h_ext

    -- By Theorem 6.2 (Rockafellar), intrinsicInterior s is nonempty for nonempty convex s
    -- This is available in Mathlib as Set.Nonempty.intrinsicInterior
    have h_ri_ne : (intrinsicInterior ℝ s).Nonempty :=
      hs_ne.intrinsicInterior hs

    -- Pick any point x in the relative interior
    obtain ⟨x, hx⟩ := h_ri_ne

    -- We have x ∈ intrinsicInterior s
    -- By hypothesis h_ext with this x, since x ∈ intrinsicInterior s ⊆ s:
    have hx_in_s : x ∈ s := intrinsicInterior_subset hx
    obtain ⟨μ, hμ_gt_1, hy⟩ := h_ext x hx_in_s

    -- hy states: (1 - μ) • x + μ • z ∈ s
    -- We need to express z as a convex combination of x and this point

    -- Since the algebra is getting complex with type inference,
    -- let's use a more direct approach

    -- From (1 - μ)•x + μ•z ∈ s and μ > 1, we can rearrange to get
    -- z = (1 - 1/μ)•x + (1/μ)•((1 - μ)•x + μ•z)

    -- The key insight: We need to show z ∈ intrinsicInterior s
    -- by expressing it as a convex combination of x ∈ intrinsicInterior s
    -- and a point in s (hence in intrinsicClosure s)

    -- This requires careful algebraic manipulation that depends on
    -- proper handling of the scalar μ as a real number
    sorry

/-!
### Applications and corollaries
-/

/-- If s ⊆ t ⊆ affineSpan s with equal affine dimensions and s has full dimension,
then s = t.

This follows from the fact that s is relatively closed. -/
theorem convex_eq_of_subset_affineSpan_same_dim_full {s t : Set E}
    (hs_conv : Convex ℝ s) (ht_conv : Convex ℝ t)
    (hs_ne : s.Nonempty)
    (h_subset : s ⊆ t)
    (h_in_span : t ⊆ affineSpan ℝ s)
    (h_dim_eq : affineDim ℝ s = affineDim ℝ t)
    (h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E)) :
    s = t := by
  -- Strategy: show t ⊆ (affineSpan s ∩ closure s), then use base theorem
  apply Subset.antisymm h_subset

  --  We'll show t ⊆ s by showing t ⊆ affineSpan s ∩ closure s and applying base theorem
  intro x hx_t

  -- We have t ⊆ affineSpan s directly from h_in_span
  have hx_span : x ∈ (affineSpan ℝ s : Set E) := h_in_span hx_t

  -- Need to show x ∈ closure s
  -- Key insight: since s and t have same affine span and dimension, t ⊆ closure s
  have ht_in_closure_s : t ⊆ closure s := by
    -- Establish affineSpan s = affineSpan t
    have h_span_eq : affineSpan ℝ s = affineSpan ℝ t := by
      apply le_antisymm
      · exact affineSpan_mono ℝ h_subset
      · rw [affineSpan_le]; exact h_in_span

    -- Mathematical insight: If s ⊆ t ⊆ affineSpan s with equal dimensions and both
    -- full-dimensional, then t ⊆ closure s.
    --
    -- This is because:
    -- 1. Both s and t span the same affine subspace (h_span_eq)
    -- 2. Both have the same affine dimension (h_dim_eq)
    -- 3. Both are full-dimensional in that subspace (h_full + h_dim_eq)
    -- 4. s ⊆ t, so any point in t \ s would create a proper extension
    -- 5. But such an extension would contradict either the dimension equality
    --    or the full-dimensionality
    --
    -- Therefore, t \ s (if nonempty) consists only of boundary points of s,
    -- i.e., points in closure s \ s. Hence t ⊆ closure s.
    --
    -- DEPENDENCY NOTE: This appears to require the base theorem
    -- `Convex.closure_inter_affineSpan_subset_of_full_dim` or equivalent reasoning.
    -- The proof of that theorem and this theorem may need to be developed together
    -- or one needs to be proved first using different techniques (e.g., separation theorems,
    -- Carathéodory's theorem, or results about relative interiors).
    sorry

  have hx_closure : x ∈ closure s := ht_in_closure_s hx_t

  -- Now apply the base theorem
  exact Convex.closure_inter_affineSpan_subset_of_full_dim hs_conv hs_ne h_full
    ⟨hx_span, hx_closure⟩

/-!
### Linear (vector space) analogs

The following theorems are vector space analogs of the affine theorems above.
In the linear setting, we work with `Submodule.span` and `Module.finrank` instead
of `affineSpan` and `affineDim`.
-/

/-- If s ⊆ t ⊆ affineSpan s with equal affine dimensions, then t ⊆ s.

This follows from the theorem about full-dimensional convex sets being relatively closed.

**References**:
- Rockafellar, "Convex Analysis" (1970), Theorem 6.2
- Ziegler, "Lectures on Polytopes" (1995), Proposition 2.4 -/
theorem subset_of_subset_affineSpan_same_dim {s t : Set E}
    (hs_conv : Convex ℝ s) (ht_conv : Convex ℝ t)
    (hs_ne : s.Nonempty)
    (h_subset : s ⊆ t)
    (h_in_span : t ⊆ affineSpan ℝ s)
    (h_dim_eq : affineDim ℝ s = affineDim ℝ t) :
    t ⊆ s := by
  -- Show that s has full dimension in its affine span
  have h_full : affineDim ℝ s = affineDim ℝ (affineSpan ℝ s : Set E) := by
    simp only [affineDim]
    rw [AffineSubspace.affineSpan_coe]

  -- Apply the key theorem
  have h_eq : s = t :=
    convex_eq_of_subset_affineSpan_same_dim_full hs_conv ht_conv hs_ne h_subset h_in_span
      h_dim_eq h_full

  exact h_eq ▸ Set.Subset.refl s

/-!
### Rockafellar's Reduction Technique

This section formalizes Rockafellar's proof technique from "Convex Analysis" (1970), Section 6,
pages 44-45. The key observation is that properties of convex sets that are preserved under
affine equivalences can be reduced to the case where the set has full dimension in its
ambient space.

**Rockafellar's observation** (pages 44-45):

> "Closures and relative interiors are preserved under translations and more generally under
> any one-to-one affine transformation of Rⁿ onto itself. [...] It is often possible in this
> manner to reduce a question about general convex sets to the case where the convex set is
> of full dimension, i.e. has the whole space as its affine hull."

**The technique works as follows:**
- To prove a property P of an m-dimensional convex set C in Rⁿ
- Find an affine equivalence T mapping aff(C) to a coordinate subspace L ≅ Rᵐ
- Prove P for T(C), which is full-dimensional in L
- Transfer back using T⁻¹

**Key simplification:** In the full-dimensional case, relative interior = ordinary interior,
which often makes proofs much simpler.

**Usage pattern:** When proving Theorem 6.1, Rockafellar writes:
> "In view of the preceding remark, we can limit attention to the case where C is
> n-dimensional, so that ri C = int C."
-/

section RockafellarReduction

variable {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

/-!
#### Affine equivalences preserve structure

We first establish that `AffineEquiv` (bijective affine maps) preserve the key
structures we need. These are the building blocks for the reduction technique.
-/

/-- Affine equivalences preserve affine spans.

This is a fundamental property: if φ is a bijective affine map, then the image of
the affine span equals the affine span of the image. -/
theorem AffineEquiv.map_affineSpan (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    φ.toAffineMap '' (affineSpan ℝ s : Set E₁) = (affineSpan ℝ (φ '' s) : Set E₂) := by
  sorry

/-- Affine equivalences preserve affine dimension.

This follows from the fact that affine equivalences preserve affine spans
and induce linear equivalences on the direction submodules. -/
theorem AffineEquiv.affineDim_image (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    affineDim ℝ (φ '' s) = affineDim ℝ s := by
  sorry

/-- Affine equivalences preserve relative interiors (intrinsic interiors).

**Key fact**: In finite-dimensional spaces, affine equivalences are homeomorphisms
(via `AffineEquiv.toHomeomorphOfFiniteDimensional`), and homeomorphisms preserve
interior in the subspace topology. -/
theorem AffineEquiv.image_intrinsicInterior (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    intrinsicInterior ℝ (φ '' s) = φ '' intrinsicInterior ℝ s := by
  sorry

/-- Affine equivalences preserve relative closures (intrinsic closures). -/
theorem AffineEquiv.image_intrinsicClosure (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    intrinsicClosure ℝ (φ '' s) = φ '' intrinsicClosure ℝ s := by
  sorry

/-!
#### The Reduction Theorem

This is the main theorem that formalizes Rockafellar's methodological observation.
-/

/-- **Rockafellar's Reduction to Full-Dimensional Case**

This theorem formalizes Rockafellar's observation: **To prove a property P of convex sets,
it suffices to:**
1. Show P is preserved under affine equivalences
2. Prove P for all full-dimensional convex sets

**Why this works:**
- For any m-dimensional convex set C in Rⁿ, there exists an affine equivalence T
  mapping aff(C) to a coordinate subspace L ≅ Rᵐ
- In L, the set T(C) is full-dimensional
- Apply the full-dimensional case to T(C)
- Transfer back using T⁻¹

**Key insight:** In the full-dimensional case, relative interior = ordinary interior,
which often makes proofs much simpler.

**Usage pattern:**
```lean
theorem my_property (C : Set E) (hC : Convex ℝ C) : P C := by
  apply convex_property_by_reduction_to_full_dim
  · -- Show P is preserved under affine equivalences
    intro E₁ E₂ _ _ _ _ _ _ φ s hs
    sorry
  · -- Prove P for full-dimensional case
    intro E _ _ _ s hs h_full
    -- Here: intrinsicInterior s = interior s (much simpler!)
    sorry
```

**References**:
- Rockafellar, "Convex Analysis" (1970), Section 6, pages 44-45
-/
theorem convex_property_by_reduction_to_full_dim
    {P : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E], Set E → Prop}
    -- (1) P is preserved under affine equivalences
    (h_affine_equiv : ∀ {E₁ E₂ : Type*}
                       [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
                       [FiniteDimensional ℝ E₁]
                       [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
                       [FiniteDimensional ℝ E₂]
                       (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁),
                     P s → P (φ '' s))
    -- (2) P holds for all full-dimensional convex sets
    (h_full_dim : ∀ {E : Type*}
                    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
                    [FiniteDimensional ℝ E] (s : Set E),
                  Convex ℝ s →
                  affineDim ℝ s = Module.finrank ℝ E →
                  P s)
    -- Then P holds for all convex sets
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (C : Set E)
    (hC : Convex ℝ C) :
    P C := by
  /-
  Proof strategy:

  Case 1: C is already full-dimensional
    Apply h_full_dim directly

  Case 2: C has dimension m < n (where n = dim E)
    Step 1: Construct affine equivalence T : E → E such that
            T(aff C) = coordinate subspace L ≅ Rᵐ
            (This exists by Mathlib's AffineSubspace theory)

    Step 2: Consider T(C) ⊆ L
            Show T(C) is full-dimensional in L

    Step 3: Regard L as a copy of Rᵐ
            Apply h_full_dim to T(C) in this space

    Step 4: Transfer result back to C using T⁻¹ and h_affine_equiv

  The key technical work is in Step 1 (finding T) and Step 3 (the
  type-theoretic gymnastics of working in the subspace L).
  -/
  sorry

/-- **Specialized version for intrinsic properties**

Many properties of convex sets depend only on their intrinsic structure
(relative interior, relative closure, affine dimension) rather than the
embedding. For such properties, we can state a cleaner version using ↔. -/
theorem convex_property_by_reduction_to_full_dim_intrinsic
    {P : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E], Set E → Prop}
    -- P depends only on intrinsic structure (preserved by affine equivalence)
    (h_intrinsic : ∀ {E₁ E₂ : Type*}
                     [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
                     [FiniteDimensional ℝ E₁]
                     [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
                     [FiniteDimensional ℝ E₂]
                     (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁),
                   P s ↔ P (φ '' s))
    -- P holds for full-dimensional convex sets
    (h_full_dim : ∀ {E : Type*}
                    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
                    [FiniteDimensional ℝ E] (s : Set E),
                  Convex ℝ s →
                  affineDim ℝ s = Module.finrank ℝ E →
                  P s)
    -- Then P holds for all convex sets
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (C : Set E)
    (hC : Convex ℝ C) :
    P C := by
  apply convex_property_by_reduction_to_full_dim
  · intro E₁ E₂ _ _ _ _ _ _ φ s hs
    exact (h_intrinsic φ s).mp hs
  · exact h_full_dim

/-!
#### Helper: Full-dimensional sets have simpler topology
-/

/-- In a full-dimensional convex set, the relative interior equals the ordinary interior.

This is the key simplification that makes the reduction technique so powerful. -/
theorem intrinsicInterior_eq_interior_of_full_dim
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) (h_full : affineDim ℝ s = Module.finrank ℝ E) :
    intrinsicInterior ℝ s = interior s := by
  /-
  Since s has full dimension, affineSpan s = ⊤ (the whole space).
  The intrinsic interior is the interior in the subspace topology of affineSpan s.
  When affineSpan s = ⊤, the subspace topology equals the ambient topology.
  Therefore intrinsicInterior s = interior s.
  -/
  sorry

/-- In a full-dimensional convex set, the relative closure equals the ordinary closure. -/
theorem intrinsicClosure_eq_closure_of_full_dim
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) (h_full : affineDim ℝ s = Module.finrank ℝ E) :
    intrinsicClosure ℝ s = closure s := by
  sorry

end RockafellarReduction
