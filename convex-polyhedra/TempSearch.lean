import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

-- Search for convexHull monotonicity
#check convexHull_mono

-- Search for theorems about affine independence
#check AffineIndependent
#check AffineIndependent.not_mem_affineSpan_diff
#check affineIndependent_iff_not_mem_affineSpan_diff

-- Search for dimension and adding points
#check finrank_vectorSpan_insert_le
#check Module.finrank_lt_finrank_of_lt

-- Search for affineSpan and strict containment
#check affineSpan_le_iff
