# Development Roadmap: V-Representation Approach to Euler's Formula

## Overview

This document outlines the complete strategy for proving Euler's Polyhedron Formula (V - E + F = 2) using the V-representation approach with chain complexes and homological methods.

## Core Idea

**Key Insight**: A convex polyhedron in ℝ³ is a homological 2-sphere. Therefore:
- Its Euler characteristic (homological) is χ = dim H₀ - dim H₁ + dim H₂ = 1 - 0 + 1 = 2
- By Euler-Poincaré formula: χ = Σ(-1)ᵏ · (# of k-faces) = V - E + F
- Therefore: V - E + F = 2

## File Structure

```
ConvexPolyhedra/
├── VRepresentation.lean       # Primary definition (convex hull of vertices)
├── HRepresentation.lean       # Secondary definition (half-spaces)
├── MinkowskiWeyl.lean         # H ↔ V equivalence
├── FaceLattice.lean           # Face structure and incidence
├── ChainComplex.lean          # Chain complex from faces
├── BoundaryMaps.lean          # Boundary operators ∂ₖ
├── HomologicalSphere.lean     # Prove H₀=ℤ, H₁=0, H₂=ℤ
└── EulerFormula.lean          # Main theorem
```

## Development Stages

### Stage 1: Basic Definitions (Week 1)

**VRepresentation.lean** ✓ (created, needs compilation fixes)
- [x] `ConvexPolyhedron` structure
- [x] Basic properties (compact, convex, bounded)
- [x] Extreme points theory
- [ ] Fix imports for: `affineDim`, `finrank`, `ChainComplex`
- [ ] Fix `isBounded_convexHull` usage

**HRepresentation.lean** (extract from Basic.lean)
- [ ] `HPolyhedron` structure (half-spaces)
- [ ] Basic properties
- [ ] Boundedness condition

**MinkowskiWeyl.lean**
- [ ] State equivalence theorems (all with `sorry`)
- [ ] Framework for eventual proof

### Stage 2: Face Lattice (Week 2-3)

**FaceLattice.lean**
```lean
-- Key definitions:
structure Face (P : ConvexPolyhedron E) where
  support : E →L[ℝ] ℝ              -- Supporting functional
  vertices : Finset E              -- Maximizing vertices

def faces (P : ConvexPolyhedron E) (k : ℕ) : Set (Face P)
  -- k-dimensional faces

theorem faces_finite : (P.faces k).Finite
  -- Critical: finite number of faces in each dimension

-- Incidence structure:
def incident (F G : Face P) : Prop :=
  F.dim = G.dim - 1 ∧ F.toSet ⊆ G.toSet
```

**Key results needed:**
1. Faces form a lattice
2. Face of a face is a face
3. Intersection of faces is a face
4. Each face is exposed (Mathlib already has `IsExposed`)
5. Finiteness of face complex

### Stage 3: Chain Complex Construction (Week 3-4)

**ChainComplex.lean**
```lean
-- Chain groups: free ℤ-modules on k-faces
def chainGroup (P : ConvexPolyhedron E) (k : ℕ) : Type _ :=
  (P.faces k).toFinite.toFinset →₀ ℤ

-- Build the chain complex
def faceChainComplex (P : ConvexPolyhedron E) : ChainComplex ℤ ℕ
```

**BoundaryMaps.lean**
```lean
-- Boundary operator: ∂ₖ: Cₖ → Cₖ₋₁
noncomputable def boundaryMap (P : ConvexPolyhedron E) (k : ℕ) :
    P.chainGroup k →ₗ[ℤ] P.chainGroup (k - 1)

-- For an edge [v₀, v₁]: ∂([v₀, v₁]) = v₁ - v₀
-- For a face F: ∂(F) = Σᵢ (±1) · eᵢ where eᵢ are boundary edges
-- Signs determined by orientation

-- KEY THEOREM: ∂² = 0
theorem boundary_comp_boundary :
    (P.boundaryMap (k - 1)).comp (P.boundaryMap k) = 0
```

**Proof strategy for ∂² = 0:**
- Each (k-2)-face appears in exactly two (k-1)-faces on boundary of a k-face
- With opposite orientations
- Therefore contributions cancel

### Stage 4: Homology Computation (Week 4-6)

**HomologicalSphere.lean**

```lean
-- Homology groups: Hₖ = ker(∂ₖ) / im(∂ₖ₊₁)
def homologyGroup (P : ConvexPolyhedron3D) (k : ℕ) : Type _

-- THE KEY THEOREM
theorem isHomologicalSphere (P : ConvexPolyhedron3D) :
    -- Need proper type for isomorphism
    (P.homologyGroup 0 ≅ ℤ) ∧
    (P.homologyGroup 1 ≅ 0) ∧
    (P.homologyGroup 2 ≅ ℤ)
```

**Proof approaches for homological sphere:**

**Option A: Direct topological argument**
1. Show P is homeomorphic to a sphere
2. Use Mathlib's topological homology (if available)
3. Transfer homology groups via homeomorphism

**Option B: Shellability**
1. Prove polyhedra are shellable complexes
2. Use shellability to compute homology inductively
3. Based on: faces can be added one at a time with contractible attachments

**Option C: Induction on faces**
1. Start with a tetrahedron (base case)
2. Show adding a face preserves homology type
3. Use Mayer-Vietoris sequence for computing changes

**Option D: Dual complex and duality**
1. Construct dual polyhedron
2. Use Poincaré duality
3. Reduce to simpler computation

**Most practical**: Likely Option C with careful induction, or stating the topological fact and connecting to combinatorial computation.

### Stage 5: Euler-Poincaré Formula (Week 6)

**EulerFormula.lean**

```lean
-- Combinatorial Euler characteristic
def eulerCharCombinatorial (P : ConvexPolyhedron3D) : ℤ :=
  (# vertices) - (# edges) + (# faces)

-- Homological Euler characteristic
def eulerCharHomological (P : ConvexPolyhedron3D) : ℤ :=
  Σ (-1)ᵏ · rank(Hₖ(P))

-- Euler-Poincaré formula: these coincide
theorem eulerChar_eq :
    P.eulerCharCombinatorial = P.eulerCharHomological

-- By isHomologicalSphere: eulerCharHomological = 1 - 0 + 1 = 2
theorem eulerCharHomological_eq_two :
    P.eulerCharHomological = 2

-- MAIN THEOREM
theorem euler_formula (P : ConvexPolyhedron3D) :
    V - E + F = 2
```

## Key Challenges and Dependencies

### Mathlib Dependencies Needed

1. **Affine geometry**
   - Affine dimension (`affineDim` or equivalent)
   - Affine independence
   - Affine hulls

2. **Chain complex machinery**
   - `ChainComplex` type (found: `Mathlib.Algebra.Homology.HomologicalComplex`)
   - Homology groups
   - Euler-Poincaré formula

3. **Topology** (if using topological approach)
   - Homeomorphisms
   - Topological homology
   - Sphere homology

4. **Convex geometry** (mostly available)
   - ✓ Extreme points (`Set.extremePoints`)
   - ✓ Exposed faces (`Set.exposedPoints`, `IsExposed`)
   - ✓ Convex hull properties

### Technical Challenges

1. **Orientation and signs in boundary maps**
   - Need consistent orientation on faces
   - Sign conventions for ∂
   - Proof that choices don't affect homology

2. **Finiteness**
   - Prove faces are finite in each dimension
   - Depends on: bounded polyhedra have finitely many extreme points
   - Then: faces determined by subsets of extreme points

3. **Computational homology**
   - Need to actually compute H₀, H₁, H₂
   - Either topologically or combinatorially
   - This is the deepest part of the proof

4. **3D specificity**
   - Much of the structure works in any dimension
   - But homological sphere property specific to 3D
   - May need explicit dimension arguments

## Timeline Estimate

- **Weeks 1-2**: Foundations (VRep, HRep, faces)
- **Weeks 3-4**: Chain complex construction
- **Weeks 5-8**: Homological sphere proof (hardest part)
- **Weeks 9-10**: Euler-Poincaré and final theorem
- **Weeks 11-12**: Cleanup, examples, documentation

**Total**: ~3 months for complete formalization

## Alternative: Partial Proof

If full homological sphere proof is too difficult initially:

1. **Prove Euler-Poincaré formula** abstractly
2. **State homological sphere property** as axiom/sorry
3. **Derive Euler formula** from these
4. **Add examples**: Cube, tetrahedron, octahedron (compute explicitly)
5. **Return to homological sphere proof** later

This gives a complete formal statement and most of the infrastructure, with the deepest topological result deferred.

## Next Immediate Steps

1. Fix compilation errors in `VRepresentation.lean`:
   - Import `Mathlib.LinearAlgebra.FiniteDimensional` for `finrank`
   - Import `Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional` for affine dimension
   - Import `Mathlib.Algebra.Homology.HomologicalComplex` for `ChainComplex`
   - Fix `isBounded_convexHull` usage (use `.mp` not `.mpr`)

2. Create minimal `FaceLattice.lean` with basic structure

3. Explore Mathlib's existing chain complex and homology infrastructure

4. Search for any existing results on polytope homology or shellability

5. Create working examples: Tetrahedron, Cube

## References

- Minkowski-Weyl: https://people.inf.ethz.ch/fukudak/polyfaq/node14.html
- Mathlib Convex Analysis: `Mathlib.Analysis.Convex.*`
- Mathlib Homology: `Mathlib.Algebra.Homology.*`
- Computational Geometry: de Berg et al., Chapters on polytopes
- Algebraic Topology: Hatcher, Chapter 2 (simplicial homology)
