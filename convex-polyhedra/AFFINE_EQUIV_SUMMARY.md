# AffineEquiv in Mathlib: Summary and What We Need

## What is AffineEquiv?

**Yes, `AffineEquiv` exists in Mathlib!** It's defined in `Mathlib.LinearAlgebra.AffineSpace.AffineEquiv`.

### Definition

```lean
structure AffineEquiv (k : Type*) (P₁ P₂ : Type*)
    {V₁ V₂ : Type*} [Ring k]
    [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
    [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
```

Notation: `P₁ ≃ᵃ[k] P₂`

An `AffineEquiv k P₁ P₂` is:
- A bijective map `P₁ → P₂`
- That is affine (preserves affine combinations)
- With an affine inverse

### Key Properties

```lean
-- AffineEquiv is bijective
AffineEquiv.bijective : ∀ (e : P₁ ≃ᵃ[k] P₂), Bijective e

-- Can construct from bijective affine map
AffineEquiv.ofBijective : {φ : P₁ →ᵃ[k] P₂} → Bijective φ → P₁ ≃ᵃ[k] P₂

-- Preserves affine combinations
AffineEquiv.apply_lineMap :
  ∀ (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c : k),
    e (lineMap a b c) = lineMap (e a) (e b) c
```

## Topological Properties

### In Finite Dimensions: AffineEquiv is a Homeomorphism

**KEY RESULT** from `Mathlib.Analysis.Normed.Module.FiniteDimension`:

```lean
AffineEquiv.toHomeomorphOfFiniteDimensional :
  ∀ [FiniteDimensional 𝕜 E] (f : PE ≃ᵃ[𝕜] PF), PE ≃ₜ PF
```

This means: **In finite-dimensional normed spaces, every affine equivalence is a homeomorphism!**

This is automatic because:
1. Affine maps on finite-dimensional spaces are continuous (`continuous_of_finiteDimensional`)
2. The inverse is also an affine map, so it's also continuous
3. Therefore it's a homeomorphism

### Homeomorphisms Preserve Topology

Since `AffineEquiv` gives us a `Homeomorph` in finite dimensions, we can use:

```lean
-- Homeomorphisms preserve interior
Homeomorph.image_interior : ∀ (h : X ≃ₜ Y) (s : Set X), h '' interior s = interior (h '' s)

-- Homeomorphisms preserve closure
Homeomorph.image_closure : ∀ (h : X ≃ₜ Y) (s : Set X), h '' closure s = closure (h '' s)
```

## What About Relative Interior and Closure?

### Current Status

❌ **NOT FOUND**: Direct theorems like:
```lean
AffineEquiv.image_intrinsicInterior :
  ∀ (φ : P₁ ≃ᵃ[𝕜] P₂) (s : Set P₁),
    intrinsicInterior 𝕜 (φ '' s) = φ '' intrinsicInterior 𝕜 s
```

✅ **AVAILABLE**: For affine **isometries** only:
```lean
AffineIsometry.image_intrinsicInterior : ...
AffineIsometry.image_intrinsicClosure : ...
```

### Why Should It Work?

The proof should follow this path:

1. **AffineEquiv preserves affine spans**:
   ```lean
   -- Should be provable
   theorem AffineEquiv.map_affineSpan (φ : P₁ ≃ᵃ[𝕜] P₂) (s : Set P₁) :
       φ '' (affineSpan 𝕜 s) = affineSpan 𝕜 (φ '' s)
   ```

2. **In finite dimensions, AffineEquiv is a homeomorphism**:
   Already have: `AffineEquiv.toHomeomorphOfFiniteDimensional`

3. **Homeomorphisms of affine subspaces preserve relative topology**:
   Need to combine the above to show that the induced homeomorphism on the affine span
   preserves interior/closure in the subspace topology

## What We Need to Prove

### Priority 1: Core AffineEquiv Properties

```lean
-- Affine equivalences preserve affine span
theorem AffineEquiv.map_affineSpan {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    φ.toAffineMap '' (affineSpan ℝ s : Set E₁) = (affineSpan ℝ (φ '' s) : Set E₂) := by
  sorry

-- Affine equivalences preserve affine dimension
theorem AffineEquiv.affineDim_image {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    affineDim ℝ (φ '' s) = affineDim ℝ s := by
  sorry
```

### Priority 2: Relative Topology Preservation

```lean
-- Affine equivalences preserve relative interior (finite-dimensional case)
theorem AffineEquiv.image_intrinsicInterior {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    intrinsicInterior ℝ (φ '' s) = φ '' intrinsicInterior ℝ s := by
  sorry

-- Affine equivalences preserve relative closure (finite-dimensional case)
theorem AffineEquiv.image_intrinsicClosure {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    intrinsicClosure ℝ (φ '' s) = φ '' intrinsicClosure ℝ s := by
  sorry
```

### Priority 3: Rockafellar's Reduction Technique

```lean
/-- **Reduction to full-dimensional case**:
Any property of convex sets that is preserved under affine equivalences
can be reduced to the case where the set has full dimension in its ambient space. -/
theorem convex_property_by_full_dim_reduction
    {P : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E], Set E → Prop}
    -- P is preserved under affine equivalences
    (h_equiv : ∀ {E₁ E₂ : Type*}
                 [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
                 [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
                 (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁),
               P s → P (φ '' s))
    -- P holds for all full-dimensional convex sets
    (h_full_dim : ∀ {E : Type*}
                    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
                    (s : Set E),
                  Convex ℝ s →
                  affineDim ℝ s = Module.finrank ℝ E →
                  P s)
    -- Then P holds for all convex sets
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : Convex ℝ C) :
    P C := by
  -- Need to construct affine equivalence mapping aff C to coordinate subspace
  -- Then apply h_full_dim and transfer back via h_equiv
  sorry
```

## Proof Strategy Sketch

For `AffineEquiv.image_intrinsicInterior`:

```lean
theorem AffineEquiv.image_intrinsicInterior (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁) :
    intrinsicInterior ℝ (φ '' s) = φ '' intrinsicInterior ℝ s := by
  -- Key steps:

  -- 1. Show φ maps affineSpan s to affineSpan (φ '' s)
  have h_span : φ '' (affineSpan ℝ s : Set E₁) = (affineSpan ℝ (φ '' s) : Set E₂) :=
    φ.map_affineSpan s

  -- 2. φ restricts to a homeomorphism between the affine subspaces
  let φ_sub := ... -- Restriction of φ.toHomeomorphOfFiniteDimensional

  -- 3. intrinsicInterior is defined as the image of interior in subspace topology
  rw [intrinsicInterior, intrinsicInterior]

  -- 4. Use that homeomorphisms preserve interior
  rw [φ_sub.image_interior]

  -- 5. Unwrap definitions and use h_span
  sorry
```

## Terminology

- **AffineEquiv**: Standard Mathlib term for bijective affine maps ✓
- **"Affine equivalence"**: Mathematical term, exactly what Mathlib formalizes ✓
- **Rockafellar's usage**: He says "one-to-one affine transformation onto itself", which is exactly an `AffineEquiv` in modern language ✓

## Next Steps

1. ✅ Confirmed `AffineEquiv` exists and is the right notion
2. ✅ Confirmed it's a homeomorphism in finite dimensions
3. ❌ Need to prove `AffineEquiv.image_intrinsicInterior` and related
4. ❌ Need to formalize Rockafellar's reduction technique
5. ❌ Need to use the technique in proofs of Theorems 6.1 and 6.4

## Files to Modify

Add to `ConvexPolyhedra/RelativeInterior.lean`:
- `AffineEquiv.map_affineSpan`
- `AffineEquiv.affineDim_image`
- `AffineEquiv.image_intrinsicInterior`
- `AffineEquiv.image_intrinsicClosure`
- `convex_property_by_full_dim_reduction`

These should eventually be PR'd to Mathlib itself, as they're general infrastructure.
