# Rockafellar's Reduction to Full-Dimensional Case

## The Observation (Pages 2-3, PDF)

Rockafellar makes a crucial methodological observation about simplifying proofs:

> Closures and relative interiors are preserved under translations and more
> generally under any one-to-one affine transformation of Rⁿ onto itself.
> Indeed, such a transformation preserves affine hulls and is continuous in
> both directions (since the components of the image of a vector x under an
> affine transformation are linear or affine functions of the components ξᵢ
> of x). One should keep this in mind as a useful device for simplifying
> proofs. For example, if C is an m-dimensional convex set in Rⁿ, there exists
> by Corollary 1.6.1 a one-to-one affine transformation T of Rⁿ onto itself
> which carries aff C onto the subspace
> L = {x = (ξ₁, ... , ξₘ, ξₘ₊₁, ... , ξₙ) | ξₘ₊₁ = 0, ... , ξₙ = 0}.
> This L can be regarded as a copy of Rᵐ. It is often possible in this manner
> to reduce a question about general convex sets to the case where the
> convex set is of full dimension, i.e. has the whole space as its affine hull.

## What This Means

The key insight is: **To prove a property P of a convex set C, we can:**

1. Find an affine equivalence T : Rⁿ → Rⁿ that maps aff(C) to a coordinate subspace L ≅ Rᵐ
2. Prove P for T(C), which is now a full-dimensional convex set in L ≅ Rᵐ
3. Transfer the result back to C using the inverse transformation T⁻¹

This is valid because affine equivalences preserve:
- Convexity
- Affine hulls
- Relative interiors
- Closures
- Affine dimension

## Status in Mathlib

### ✅ Available: Preservation under Affine Isometries

**Affine isometries** (distance-preserving affine maps) preserve relative topology:

```lean
-- From Mathlib.Analysis.Convex.Intrinsic
AffineIsometry.image_intrinsicInterior :
  ∀ (φ : P →ᵃⁱ[𝕜] Q) (s : Set P),
    intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s

AffineIsometry.image_intrinsicClosure :
  ∀ (φ : P →ᵃⁱ[𝕜] Q) (s : Set P),
    intrinsicClosure 𝕜 (φ '' s) = φ '' intrinsicClosure 𝕜 s
```

These are exactly what we need, **but** they only work for isometries (preserving distances).

### ⚠️ Problem: Not All Affine Equivalences Are Isometries

Rockafellar's technique uses **arbitrary affine equivalences**, not just isometries. For example:
- The map T(x, y, z) = (2x, y, z) is an affine equivalence
- But it's NOT an isometry (it stretches the x-coordinate by 2)

### ❓ Question: Do We Need More General Results?

We need to investigate whether:

1. **Affine equivalences** (bijective affine maps) preserve relative interiors and closures
2. OR: Can we always find an affine **isometry** to do the reduction?

## Investigation: What About General Affine Equivalences?

Let's think about this carefully:

### For Convexity
✅ **Available**: `Convex.affine_image` shows affine maps preserve convexity

### For Affine Span
✅ **Available**: `AffineEquiv.span_eq_top_iff` shows affine equivalences preserve whether the affine span is the whole space

### For Relative Interior and Closure
❓ **Unknown**: Do general affine equivalences preserve `intrinsicInterior` and `intrinsicClosure`?

**Intuition suggests YES** because:
- Affine equivalences are homeomorphisms (continuous with continuous inverse)
- They preserve affine structure
- Relative interior/closure are defined via the subspace topology

**But**: I couldn't find explicit theorems in Mathlib for this!

## What We Likely Need to Add

If the general case isn't in Mathlib, we should add:

```lean
-- Affine equivalences preserve relative interior
theorem AffineEquiv.image_intrinsicInterior
    (φ : P₁ ≃ᵃ[𝕜] P₂) (s : Set P₁) :
    intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s := by
  sorry

-- Affine equivalences preserve relative closure
theorem AffineEquiv.image_intrinsicClosure
    (φ : P₁ ≃ᵃ[𝕜] P₂) (s : Set P₁) :
    intrinsicClosure 𝕜 (φ '' s) = φ '' intrinsicClosure 𝕜 s := by
  sorry

-- Affine equivalences preserve affine dimension
theorem AffineEquiv.affineDim_image
    (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    affineDim ℝ (φ '' s) = affineDim ℝ s := by
  sorry
```

## The Reduction Technique as a Theorem

Here's how to formalize Rockafellar's technique:

```lean
/-- **Rockafellar's reduction technique**: To prove a property P of m-dimensional
convex sets in Rⁿ, it suffices to prove P for full-dimensional convex sets in Rᵐ.

This works by finding an affine equivalence that maps the affine hull of C to
a coordinate subspace, reducing to the case where aff(C) = the whole space. -/
theorem convex_property_by_full_dim_reduction
    {P : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E], Set E → Prop}
    -- P is preserved under affine equivalences
    (h_equiv : ∀ {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
                 [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂]
                 [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
                 (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁),
               P s → P (φ '' s))
    -- P holds for all full-dimensional convex sets
    (h_full_dim : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
                    [FiniteDimensional ℝ E] (s : Set E),
                  Convex ℝ s →
                  affineDim ℝ s = Module.finrank ℝ E →
                  P s)
    -- Then P holds for all convex sets
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (C : Set E)
    (hC : Convex ℝ C) :
    P C := by
  -- Strategy:
  -- 1. If C is full-dimensional, apply h_full_dim directly
  -- 2. Otherwise, find affine equivalence T : Rⁿ → Rⁿ mapping aff(C) to
  --    coordinate subspace L ≅ Rᵐ where m = dim(C)
  -- 3. Show T(C) is full-dimensional in L
  -- 4. Apply h_full_dim to T(C) in L
  -- 5. Transfer back using h_equiv and T⁻¹
  sorry
```

## How Rockafellar Uses This

In **Theorem 6.1** (page 3, line 1-2 of proof):
> "In view of the preceding remark, we can limit attention to the
> case where C is n-dimensional, so that ri C = int C."

This is the reduction technique in action! He's saying:
1. The general case follows from the full-dimensional case
2. In the full-dimensional case, relative interior = ordinary interior
3. So we only need to prove it for the simpler full-dimensional case

## Usage in Our Proofs

We should use this technique for:

1. **Theorem 6.1** (`Convex.combo_intrinsicInterior_intrinsicClosure_mem_intrinsicInterior`)
   - Reduce to full-dimensional case where intrinsicInterior = interior
   - Apply existing `Convex.combo_interior_closure_mem_interior`

2. **Helper Lemma 2** (`intrinsicClosure_eq_of_full_dim`)
   - This IS the full-dimensional case
   - Need to prove convex set with full dim equals closure of its relative interior

3. **Theorem 6.4** (`mem_intrinsicInterior_iff_extension`)
   - Could reduce to full-dimensional case for cleaner proof

## Priority

**HIGH**: We should either:
1. Find the general `AffineEquiv` preservation theorems in Mathlib (maybe they exist but I missed them?)
2. OR: Prove them ourselves as they're foundational for the reduction technique
3. OR: Find a way to always use affine **isometries** for the reduction (is this possible?)

This is blocking progress on Theorems 6.1 and 6.4.

## References

- Rockafellar, "Convex Analysis" (1970), Section 6, pages 44-45
- The technique is used implicitly throughout convex analysis
- Similar to "reduction to characteristic 0" in algebra or "reduction to the real case" in functional analysis
