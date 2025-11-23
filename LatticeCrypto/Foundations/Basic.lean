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

/-!
  We define the mathematical notion of a lattice as a discrete additive subgroup
  of a finite-dimensional inner product space over the reals. We also define several related
  concepts, such as
  * Specializations: integral lattices, (TODO) ideal lattices (over polynomial rings)
  * Core concepts used in lattice cryptography: cosets, quotient spaces, (TODO) successive minimas, (TODO) dual lattices.
-/
section Lattice

-- V is our ambient space, usually EuclideanSpace ℝ (Fin n)
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/--
  The Abstract Lattice: A bundled Discrete Subgroup in the ambient space.
  Note we do not require full rank here in order to allow for sublattices.
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

/-!
  We define a computable basis for a lattice using rational vectors that can be used to implement actual algorithms.
  We also provide the function converting such a basis to an AbstractLattice, given proof of full rank.
-/
section LatticeBasis

variable {n k : ℕ+}
-- A computable basis for a lattice, using rational vectors
-- We assume n = m for a full-rank lattice in V = ℝⁿ
structure LatticeBasis (n k : ℕ+) where
  /- A ℚ-basis of ℚⁿ, represented as column vectors in ℚⁿ.
     Via coercion ℚ → ℝ, these live naturally in the Euclidean space
     `EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)` with the standard
     inner product and norm, using the EuclideanSpace.equiv tactic. -/
  basis : Matrix (Fin n) (Fin k) ℚ

/-- Convert a LatticeBasis with rational entries to a matrix with real entries. -/
noncomputable def LatticeBasis.to_real_matrix (B : LatticeBasis n k) : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.map B.basis (Rat.cast : ℚ → ℝ)

/-- Helper: Linear equivalence between EuclideanSpace ℝ (Fin n) and the function space (Fin n → ℝ). -/
noncomputable def eucToPi : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv

noncomputable def piToEuc : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv

@[simp] lemma piToEuc_apply (f : Fin n → ℝ) (i : Fin n) :
  (eucToPi (piToEuc f)) i = f i := by simp[piToEuc, eucToPi]

@[simp] lemma eucToPi_apply (x : EuclideanSpace ℝ (Fin n)) :
  piToEuc (eucToPi x) = x := by simp[piToEuc, eucToPi]

/-- Convert the columns of a LatticeBasis to vectors in Euclidean space over ℝ. -/
noncomputable def LatticeBasis.real_cols (B : LatticeBasis n k) :
    Fin k → EuclideanSpace ℝ (Fin n) :=
  fun j => piToEuc (fun i => B.to_real_matrix i j)

/-- Convert the rows of a LatticeBasis to vectors in Euclidean space over ℝ. -/
noncomputable def LatticeBasis.real_rows (B : LatticeBasis n k) :
    Fin n → EuclideanSpace ℝ (Fin k) :=
  fun i => piToEuc (fun j => B.to_real_matrix i j)

/-- Allows user to provide a proof that the lattice basis is full rank. -/
def LatticeBasis.LinearIndependentReal (B : LatticeBasis n k) : Prop :=
  LinearIndependent ℝ (B.real_cols)

/--
  A Square Lattice Basis is just the general case where n = k.
-/
abbrev SquareLatticeBasis (n : ℕ+) := LatticeBasis n n

/-- Convert a SquareLatticeBasis to a Module.Basis, given proof of full rank -/
noncomputable def LatticeBasis.to_module_basis (B : SquareLatticeBasis n) (fullrank: B.LinearIndependentReal) :
    Module.Basis (Fin n) ℝ (𝔼 n) :=
  let h_span : Submodule.span ℝ (Set.range B.real_cols) = ⊤ := by
    have h_dim : Fintype.card (Fin n) = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      simp [finrank_euclideanSpace]
    apply
      LinearIndependent.span_eq_top_of_card_eq_finrank fullrank h_dim
  Module.Basis.mk fullrank h_span.ge

/-- Convert a SquareLatticeBasis to an AbstractLattice, given proof of full rank -/
noncomputable def LatticeBasis.toAbstractLattice' (B : SquareLatticeBasis n) (fullrank: B.LinearIndependentReal) :
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
  Separately, we prove that if the square basis was full rank,
  the resulting lattice is Full Rank.
-/
instance (B : SquareLatticeBasis n) (h : B.LinearIndependentReal) :
    IsFullRank (B.toAbstractLattice' h) where
  span_top := by
    let module_basis := B.to_module_basis h
    have : (B.toAbstractLattice' h).carrier = Submodule.span ℤ (Set.range module_basis) := rfl

    rw [this]
    exact ZSpan.span_top module_basis

/-- Proof that any linear independent set of n vectors over ℝ^n has a discrete z-span -/
lemma discrete_zspan' {n : ℕ+} {v : Fin n → 𝔼 n} (h : LinearIndependent ℝ v) :
    DiscreteTopology (Submodule.span ℤ (Set.range v) : Submodule ℤ (𝔼 n)) := by
  let h_span : Submodule.span ℝ (Set.range v) = ⊤ := by
    have h_dim : Fintype.card (Fin n) = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      simp [finrank_euclideanSpace]
    apply
      LinearIndependent.span_eq_top_of_card_eq_finrank h h_dim
  let module_basis :=Module.Basis.mk h h_span.ge
  let carrier_module := Submodule.span ℤ (Set.range module_basis)
  have h_range : Set.range v = Set.range module_basis := by
    simp [module_basis]
  have : DiscreteTopology ↥(Submodule.span ℤ (Set.range module_basis)) := by exact inferInstance
  rw [h_range]
  exact this

/-- Proof that any linear independent set of k (k ≤ n) vectors over ℝ^n has a discrete z-span -/
theorem discrete_zspan {v : Fin k → 𝔼 n} (h : LinearIndependent ℝ v) :
  DiscreteTopology (Submodule.span ℤ (Set.range v) : Submodule ℤ (𝔼 n)) := by
  admit

noncomputable def LatticeBasis.toAbstractLattice (B : LatticeBasis n k) (fullrank: B.LinearIndependentReal) :
    AbstractLattice (𝔼 n) :=
  let carrier_module := Submodule.span ℤ (Set.range B.real_cols)
  {
    carrier := carrier_module

    fg := by
      have h_fin : (Set.range B.real_cols).Finite :=
        Set.finite_range _
      exact Submodule.fg_span h_fin

    discrete := by
      exact discrete_zspan fullrank
  }


end LatticeBasis

end LatticeCrypto.Foundations
