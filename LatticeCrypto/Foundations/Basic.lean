import Mathlib.Algebra.Group.Subgroup.Defs     -- For AddSubgroup
import Mathlib.Analysis.Normed.Group.Basic      -- For NormedAddCommGroup
import Mathlib.Topology.Algebra.Group.Basic      -- For the subspace topology on AddSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.InnerProductSpace.PiL2  -- For EuclideanSpace
import Mathlib.Data.Matrix.Basic                -- for type synonym support
import Mathlib.Analysis.Normed.Group.Subgroup   -- For LinearIndependent.discrete_zspan
import Mathlib.LinearAlgebra.LinearIndependent.Defs  -- For LinearIndependent
import Mathlib.LinearAlgebra.Span.Defs               -- For AddSubgroup.zspan
import Mathlib.Data.Rat.Defs                   -- For ℚ (Rat)
import Mathlib.Data.Real.Basic                  -- For ℝ (Real)
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.PNat.Basic

open RealInnerProductSpace
open Module
open FiniteDimensional

namespace LatticeCrypto.Foundations

universe u

/-- Notation for n-dimensional Euclidean space over ℝ. -/
abbrev 𝔼 (n : ℕ+) := EuclideanSpace ℝ (Fin n)

/-- Alternative notation: ℝⁿ for n-dimensional Euclidean space.
    Use as `ℝⁿ n` in code. -/
notation "ℝⁿ" => fun (n : ℕ+) => EuclideanSpace ℝ (Fin n)

section Lattice

-- V is our ambient space, usually EuclideanSpace ℝ (Fin n)
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/--
  The Abstract Lattice: A bundled Discrete Subgroup of full rank.
  This is the object you use for security reductions and geometric proofs.
-/
structure AbstractLattice where
  /-- The lattice points -/
  carrier : Submodule ℤ V
  /-- The underlying additive subgroup of the ambient space -/
  subgroup : AddSubgroup V := carrier.toAddSubgroup
  /-- Proof that it is finitely generated -/
  fg : carrier.FG
  /-- Proof that the group is discrete (which is actually implied by finite generation) -/
  discrete : DiscreteTopology carrier

def AbstractLattice.coset (L : AbstractLattice V) (v : V) : Set V :=
  { x | ∃ l ∈ L.subgroup, x = v + l }

-- Enable coset notation `v +ᵥ L`
-- Notation for cosets
notation:65 v " +ᶜ " L:65 => AbstractLattice.coset (V := _) L v

/-- The quotient V / L -/
def AbstractLattice.Quotient (L : AbstractLattice V) : Type _ :=
  V ⧸ L.subgroup

/--
  A typeclass (predicate) stating that a lattice spans the entire ambient space.
-/
class IsFullRank {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (L : AbstractLattice V) : Prop where
  span_top : Submodule.span ℝ (L.carrier : Set V) = ⊤

/-- Lattice where every lattice point is integral -/
structure IntegralLattice extends AbstractLattice V where
  (integral_inner : ∀ v w : V, ∃ m: ℤ, ⟪(v: V), (w: V)⟫ = (m: ℝ))

end Lattice

section LatticeBasis

variable {n : ℕ+}
-- A computable basis for a lattice, using rational vectors
-- We assume n = m for a full-rank lattice in V = ℝⁿ
structure LatticeBasis (n : ℕ+) where
  /- A ℚ-basis of ℚⁿ, represented as column vectors in ℚⁿ.
     Via coercion ℚ → ℝ, these live naturally in the Euclidean space
     `EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)` with the standard
     inner product and norm, using the EuclideanSpace.equiv tactic. -/
  basis : Matrix (Fin n) (Fin n) ℚ

/-- Convert a LatticeBasis with rational entries to a matrix with real entries. -/
noncomputable def LatticeBasis.to_real_matrix (B : LatticeBasis n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.map B.basis (Rat.cast : ℚ → ℝ)

/-- Convert the columns of a LatticeBasis to vectors in Euclidean space over ℝ. -/
noncomputable def LatticeBasis.real_cols (B : LatticeBasis n) :
    Fin n → EuclideanSpace ℝ (Fin n) :=
  fun j => (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => B.to_real_matrix i j)

/-- Convert the rows of a LatticeBasis to vectors in Euclidean space over ℝ. -/
noncomputable def LatticeBasis.real_rows (B : LatticeBasis n) :
    Fin n → EuclideanSpace ℝ (Fin n) :=
  fun i => (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j => B.to_real_matrix i j)

/-- Allows user to provide a proof that the lattice basis is full rank. -/
def LatticeBasis.LinearIndependentReal (B : LatticeBasis n) : Prop :=
  LinearIndependent ℝ (B.real_cols)

/-- Convert a LatticeBasis to a Module.Basis, given proof of full rank -/
noncomputable def LatticeBasis.to_module_basis (B : LatticeBasis n) (fullrank: B.LinearIndependentReal) :
    Module.Basis (Fin n) ℝ (𝔼 n) :=
  let h_span : Submodule.span ℝ (Set.range B.real_cols) = ⊤ := by
    have h_dim : Fintype.card (Fin n) = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      simp [finrank_euclideanSpace]
    apply
      LinearIndependent.span_eq_top_of_card_eq_finrank fullrank h_dim
  Module.Basis.mk fullrank h_span.ge

/-- Convert a LatticeBasis to an AbstractLattice, given proof of full rank -/
noncomputable def LatticeBasis.toAbstractLattice (B : LatticeBasis n) (fullrank: B.LinearIndependentReal) :
    AbstractLattice (𝔼 n) :=
  let module_basis : Module.Basis (Fin n) ℝ (𝔼 n) := B.to_module_basis fullrank
  let carrier_module := Submodule.span ℤ (Set.range module_basis)

  {
    carrier := carrier_module

    fg := by
      have h_fin : (Set.range module_basis).Finite :=
        Set.finite_range _
      exact Submodule.fg_span h_fin

    discrete := by
      infer_instance
  }

/--
  Separately, we prove that if the basis was full rank,
  the resulting lattice is Full Rank.
-/
instance (B : LatticeBasis n) (h : B.LinearIndependentReal) :
    IsFullRank (B.toAbstractLattice h) where
  span_top := by
    let module_basis := B.to_module_basis h
    have : (B.toAbstractLattice h).carrier = Submodule.span ℤ (Set.range module_basis) := rfl

    rw [this]
    exact ZSpan.span_top module_basis

end LatticeBasis

end LatticeCrypto.Foundations
