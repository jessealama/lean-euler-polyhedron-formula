# Proof Schemas in Mathlib: Patterns for Reduction Techniques

## Summary

This document explains how Mathlib handles proof schemas and induction-like patterns, specifically addressing the "reduction to full-dimensional case" technique for convex sets.

## The Problem

We have a proof schema similar to mathematical induction:
1. To prove property P holds for all convex sets
2. Show P is preserved under affine equivalences
3. Prove P for full-dimensional convex sets
4. Conclude P holds for all convex sets

Our initial attempt hit Lean 4 typeclass resolution issues with polymorphic predicates:

```lean
theorem convex_property_by_reduction_to_full_dim
    {P : ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E], Set E → Prop}
    -- ... hypotheses ...
```

Error: `typeclass instance problem is stuck, it is often due to metavariables: FiniteDimensional ℝ ?m.103`

## How Mathlib Handles This

### 1. Proof Schemas and Induction Patterns

**Key Insight**: Mathlib uses higher-order theorems but avoids embedding typeclasses in predicate types.

**Common Approaches**:

a) **Well-founded induction** (for dimension-based reduction)
   - `Mathlib.Data.Finset.Lattice`
   - `Mathlib.Order.WellFounded`

b) **Structural induction on types/structures**
   - Common in algebra/geometry for reducing to 'standard' forms via equivalences

c) **Higher-order lemmas** taking predicates as arguments
   - Take predicate and proofs of its closure under operations
   - Conclude it holds everywhere

**Concrete Examples**:

- **Dimension-based induction**: `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional`
  - `affineIndependent_iff_of_affineCombination_eq` reduces to full-rank cases

- **Equivalence preservation**: `Mathlib.Analysis.Convex.Topology`
  - `convexHull_closure`, `convexHull_inter` use dimension-based reduction

- **Affine invariance**: `Mathlib.Analysis.Convex.Independent`
  - `AffineIsometryEquiv.image_convexHull` preserves properties under affine maps

### 2. Handling Polymorphic Predicates

**The Issue**: Lean's typeclass resolution is goal-directed and fails when predicates are too abstract or universes vary.

**Mathlib Solutions**:

a) **Avoid typeclasses in predicate types**
   - Pass instances explicitly
   - Use non-instance versions

b) **Bundle into structures**
   - Encapsulates the schema without polymorphism issues
   - Example: `ConvexOn` in `Mathlib.Analysis.Convex.Function`

c) **Explicit parameters**
   - Make predicate take space E and instances as arguments: `P E [inst1] [inst2] s`

d) **Universe annotations**
   - Use `universe u v` and careful typing to control polymorphism

**Refined Pattern for Our Theorem**:

```lean
theorem convex_property_by_reduction_to_full_dim
    (P : ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
          [FiniteDimensional ℝ E], Set E → Prop)
    (h_affine_equiv : ∀ (E₁ : Type u) [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
                       [FiniteDimensional ℝ E₁]
                       (E₂ : Type v) [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
                       [FiniteDimensional ℝ E₂]
                       (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁),
                     P E₁ s → P E₂ (φ '' s))
    (h_full_dim : ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
                    [FiniteDimensional ℝ E] (s : Set E),
                  Convex ℝ s →
                  affineDim ℝ s = Module.finrank ℝ E →
                  P E s)
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (C : Set E)
    (hC : Convex ℝ C) :
    P E C := sorry
```

**Key Changes**:
- Explicit universe annotations `Type u`, `Type v`
- Pass `E` explicitly to `P` (not implicit)
- Makes typeclass resolution local to each application
- More verbose but reliable

### 3. Reduction Techniques in Analysis/Geometry

**Common Patterns**:

a) **Dimension reduction**
   - Prove for dim=0, then induct up
   - Reduce to full-dim via orthogonal complements

b) **Affine/Isometric equivalences**
   - Transfer properties without changing geometry
   - Heavily used in Mathlib

c) **Embedding into model spaces**
   - Reduce arbitrary spaces to `EuclideanSpace ℝ (Fin n)` via bases

d) **Targeted lemmas over grand schemas**
   - Mathlib avoids over-abstraction unless widely reusable

**Concrete Examples**:

- **Full-dimensional reduction**: `Mathlib.Analysis.Convex.Extreme`
  - `extremePoints_convexHull` reduces to full-dimensional convex hulls

- **Measure theory**: `Mathlib.MeasureTheory.Measure.Haar.Basic`
  - Reduces integration over convex sets to full-dim cases

- **Geometry**: `Mathlib.Geometry.Manifold.ChartedSpace`
  - Uses charts to reduce manifold properties to Euclidean spaces

- **Affine preservation**: `Mathlib.Analysis.Convex.Basic`
  - `Convex.affine_preimage` preserves convexity under affine maps

- **Finite dimensions**: `Mathlib.Analysis.NormedSpace.FiniteDimensional`
  - `FiniteDimensional.complete` reduces completeness to finite-dim Euclidean spaces

## Alternative Approach: Structure-Based Schema

Instead of a higher-order function, define a structure:

```lean
structure ConvexPropertySchema where
  P : ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E], Set E → Prop
  affine_equiv_preserves : ∀ (E₁ : Type u) [inst₁ : NormedAddCommGroup E₁]
                             [inst₂ : InnerProductSpace ℝ E₁] [inst₃ : FiniteDimensional ℝ E₁]
                             (E₂ : Type v) [inst₄ : NormedAddCommGroup E₂]
                             [inst₅ : InnerProductSpace ℝ E₂] [inst₆ : FiniteDimensional ℝ E₂]
                             (φ : E₁ ≃ᵃ[ℝ] E₂) (s : Set E₁),
                           @P E₁ inst₁ inst₂ inst₃ s → @P E₂ inst₄ inst₅ inst₆ (φ '' s)
  holds_full_dim : ∀ (E : Type u) [inst₁ : NormedAddCommGroup E]
                     [inst₂ : InnerProductSpace ℝ E] [inst₃ : FiniteDimensional ℝ E]
                     (s : Set E),
                   Convex ℝ s → affineDim ℝ s = Module.finrank ℝ E →
                   @P E inst₁ inst₂ inst₃ s

theorem ConvexPropertySchema.holds_everywhere (schema : ConvexPropertySchema.{u, v})
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : Convex ℝ C) :
    schema.P E C := sorry
```

**Trade-offs**:
- **Pros**: More maintainable, encapsulates pattern clearly, avoids some elaboration issues
- **Cons**: Slight boilerplate overhead
- **When to use**: If you have multiple properties using this pattern

## Practical Recommendations

### For Our Project

1. **Short term**: Use the helper theorems directly in proofs
   ```lean
   -- In proof of Theorem 6.1 or 6.4
   have h_full := intrinsicInterior_eq_interior_of_full_dim hs h_full_dim
   -- Continue proof using simplified topology
   ```

2. **If general schema is needed**: Use the explicit parameter version
   - Add explicit universe annotations
   - Pass E to P explicitly
   - Test with concrete properties first

3. **Edge cases to handle**:
   - Empty sets (affineDim = -∞ conventionally)
   - Singletons (affineDim = 0)
   - When ambient space itself is 0-dimensional

### General Mathlib Patterns

1. **Start specific, generalize later**
   - Prove for your specific case first
   - Extract schema only if reused multiple times

2. **Favor explicit over implicit**
   - When in doubt, make universe parameters explicit
   - Pass instances explicitly if typeclass resolution struggles

3. **Look for existing patterns**
   - Search Mathlib for similar reduction techniques
   - Reuse established patterns rather than inventing new ones

## Our Current Status

**What we have**:
- Helper theorems that compile: `intrinsicInterior_eq_interior_of_full_dim`, `intrinsicClosure_eq_closure_of_full_dim`
- These can be used directly in proofs of Theorems 6.1 and 6.4
- Clear documentation of Rockafellar's reduction technique

**What we don't have (yet)**:
- General reduction theorem (due to Lean 4 elaboration issues)
- This is noted in documentation for future work

**Recommendation**:
Focus on using the helper theorems in the actual proofs of Theorems 6.1 and 6.4 first. If we find ourselves needing the general schema multiple times, we can revisit the explicit parameter version.

## References

### Mathlib Files (for patterns)
- `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional` - dimension-based reduction
- `Mathlib.Analysis.Convex.Basic` - affine invariance patterns
- `Mathlib.Analysis.Convex.Topology` - convex set topology
- `Mathlib.Analysis.Convex.Independent` - affine equivalence preservation
- `Mathlib.Analysis.NormedSpace.FiniteDimensional` - finite-dimensional reductions

### Our Files
- `ConvexPolyhedra/RelativeInterior.lean` - Rockafellar's reduction technique (lines 130-273)
- `ROCKAFELLAR_REDUCTION_THEOREM.lean` - Reference file (does not compile)

## Next Steps

1. Use the existing helper theorems in proofs of Theorems 6.1 and 6.4
2. If we need the general schema later, implement the explicit parameter version
3. Consider contributing the helper theorems to Mathlib (they're generally useful)
