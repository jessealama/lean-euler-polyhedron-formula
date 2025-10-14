-- Main entry point for ConvexPolyhedra project
-- Euler's Polyhedron Formula: V - E + F = 2

-- Core definitions
import ConvexPolyhedra.Basic              -- H-representation (half-spaces)
import ConvexPolyhedra.VRepresentation    -- V-representation (convex hull) - PRIMARY
-- import ConvexPolyhedra.MinkowskiWeyl   -- H ↔ V equivalence (not needed currently)

-- Face lattice and homological machinery
import ConvexPolyhedra.Face
import ConvexPolyhedra.ChainComplex
import ConvexPolyhedra.Polyhedron
