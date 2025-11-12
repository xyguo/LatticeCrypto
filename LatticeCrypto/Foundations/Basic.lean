import Mathlib.Algebra.Group.Subgroup.Defs     -- For AddSubgroup
import Mathlib.Analysis.Normed.Group.Basic      -- For NormedAddCommGroup
import Mathlib.Topology.Algebra.Group.Basic      -- For the subspace topology on AddSubgroup
import Mathlib.Analysis.InnerProductSpace.PiL2  -- For EuclideanSpace
import Mathlib.Analysis.Normed.Group.Subgroup   -- For LinearIndependent.discrete_zspan
import Mathlib.LinearAlgebra.LinearIndependent.Defs  -- For LinearIndependent
import Mathlib.LinearAlgebra.Span.Defs               -- For AddSubgroup.zspan
-- import Mathlib.LinearAlgebra.RatCast             -- For linearIndependent_rat_cast_iff
import Mathlib.Data.Rat.Defs                   -- For ℚ (Rat)
import Mathlib.Data.Real.Basic                  -- For ℝ (Real)

open RealInnerProductSpace
open Module
open FiniteDimensional

namespace LatticeCrypto.Foundations

universe u

structure Lattice (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] where
  (subgroup : AddSubgroup V)
  (discrete : DiscreteTopology subgroup)
  (finite : Module.Finite ℤ subgroup)
  (fullRank : (Submodule.span ℝ (subgroup: Set V) = ⊤))

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

instance (L : Lattice V) : DiscreteTopology L.subgroup :=
  L.discrete

structure IntegralLattice (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] extends Lattice V where
  (integral_inner : ∀ v w : subgroup, ∃ m: ℤ, ⟪(v: V), (w: V)⟫ = (m: ℝ))


end LatticeCrypto.Foundations
