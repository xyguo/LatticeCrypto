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

namespace LatticeCrypto.Foundations.Lattice

universe u

/-!
  In this file we define the mathematical notion of a (*full-rank*) lattice .
  We also define its computational representation using rational bases, and how to convert between them.

  * `AbstractLattice`: a discrete additive subgroup of a finite-dimensional inner-product space over the reals, such that its \R-span is the whole space.
  * `LatticeBasis`: a computable basis for a lattice using *rational* vectors.
  * `LatticeWithBasis`: a lattice bundled with a computable basis using rational vectors, which is implemented as a subclass of `AbstractLattice`.
  * `FullRank`: a predicate that claims the lattice has full rank, meaning its \R-span is the entire ambient space.
-/

/-- Notation for n-dimensional Euclidean space over ℝ. -/
abbrev 𝔼 (n : ℕ+) := EuclideanSpace ℝ (Fin n)

/-- Alternative notation: ℝⁿ for n-dimensional Euclidean space.
    Use as `ℝⁿ n` in code. -/
notation "ℝⁿ" => fun (n : ℕ+) => EuclideanSpace ℝ (Fin n)


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
  /-- Proof that the carrier is discrete (which is actually implied by finite generation) -/
  discrete : DiscreteTopology carrier

/-- Lattice where every lattice point is integral -/
structure IntegralLattice extends AbstractLattice V where
  (integral_inner : ∀ v w : V, ∃ m: ℤ, ⟪(v: V), (w: V)⟫ = (m: ℝ))


/-!
  We define a computable basis for a lattice using rational vectors that can be used to implement actual algorithms.
  We also provide the function converting such a basis to an AbstractLattice, given proof of full rank.
-/

variable {n k : ℕ+}
-- A computable basis for a lattice, using rational vectors
-- We assume n = m for a full-rank lattice in V = ℝⁿ
structure LatticeBasis (n k : ℕ+) where
  /- A ℚ-basis of ℚⁿ, represented as column vectors in ℚⁿ.
     Via coercion ℚ → ℝ, these live naturally in the Euclidean space
     `EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)` with the standard
     inner product and norm, using the EuclideanSpace.equiv tactic. -/
  basis : Matrix (Fin n) (Fin k) ℚ
  /-- The number of vectors k must be less than or equal to the dimension n. -/
  le_dim : k ≤ n

/-- Convert a LatticeBasis with rational entries to a matrix with real entries. -/
noncomputable def LatticeBasis.toRealMatrix (B : LatticeBasis n k) : Matrix (Fin n) (Fin k) ℝ :=
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
noncomputable def LatticeBasis.realCols (B : LatticeBasis n k) :
    Fin k → EuclideanSpace ℝ (Fin n) :=
  fun j => piToEuc (fun i => B.toRealMatrix i j)

/-- Convert the rows of a LatticeBasis to vectors in Euclidean space over ℝ. -/
noncomputable def LatticeBasis.realRows (B : LatticeBasis n k) :
    Fin n → EuclideanSpace ℝ (Fin k) :=
  fun i => piToEuc (fun j => B.toRealMatrix i j)

/-- Allows user to provide a proof that the lattice basis is full rank. -/
def LatticeBasis.LinearIndependentReal (B : LatticeBasis n k) : Prop :=
  LinearIndependent ℝ (B.realCols)

/--
  A Square Lattice Basis is just the general case where n = k.
-/
abbrev SquareLatticeBasis (n : ℕ+) := LatticeBasis n n

/-- Convert a SquareLatticeBasis to a Module.Basis, given proof of full rank -/
noncomputable def LatticeBasis.toModuleBasis (B : SquareLatticeBasis n) (fullrank: B.LinearIndependentReal) :
    Module.Basis (Fin n) ℝ (𝔼 n) :=
  let h_span : Submodule.span ℝ (Set.range B.realCols) = ⊤ := by
    have h_dim : Fintype.card (Fin n) = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      simp [finrank_euclideanSpace]
    apply
      LinearIndependent.span_eq_top_of_card_eq_finrank fullrank h_dim
  Module.Basis.mk fullrank h_span.ge

/-- Proof that any linear independent set of k (k ≤ n) vectors over ℝ^n has a discrete z-span -/
theorem discrete_zspan {v : Fin k → 𝔼 n} (li : LinearIndependent ℝ v) :
  DiscreteTopology (Submodule.span ℤ (Set.range v) : Submodule ℤ (𝔼 n)) := by
  -- 1. Extend v to a basis v' of ℝⁿ
  have hli : LinearIndepOn ℝ id (Set.range v) := by exact LinearIndependent.linearIndepOn_id li
  let v' := Basis.extend hli

  -- 2. Use the previous lemma to show that the z-span of v' is discrete
  have discrete_v' : DiscreteTopology ↥(Submodule.span ℤ (Set.range v')) := by exact inferInstance

  -- 3. Show that the z-span of v is a subset of the z-span of v'
  have h_subset : (Submodule.span ℤ (Set.range v)) ≤ (Submodule.span ℤ (Set.range v')) := by
    apply Submodule.span_mono
    -- Since $v'$ is an extension of $v$, every element in the range of $v$ is also in the range of $v'$.
    intro x hx
    obtain ⟨i, hi⟩ := hx
    use ⟨v i, by
      -- Since $v i$ is in the range of $v$, and the extension is a superset of the range of $v$, we have $v i \in hli.extend ⋯$.
      apply hli.subset_extend;
      -- Since $v i$ is in the range of $v$, we can conclude that $v i \in \text{range}(v)$.
      use i⟩
    generalize_proofs at *;
    -- Since $v'$ is an extension of $v$, and $v i$ is in the range of $v$, then by definition of the extension, the basis element for $v i$ should be $v i$ itself.
    simp [v', hi]

  -- 4. Conclude that the z-span of v is discrete
  exact DiscreteTopology.of_subset discrete_v' h_subset

/-- Allow to claim a basis generates a lattice -/
def LatticeBasis.isBasisFor (B : LatticeBasis n k) (L : AbstractLattice (𝔼 n)) : Prop :=
  L.carrier = Submodule.span ℤ (Set.range B.realCols)


/-- A lattice together with a chosen basis. -/
structure LatticeWithBasis (n k : ℕ+) extends AbstractLattice (𝔼 n) where
  basis   : LatticeBasis n k
  is_basis : Submodule.span ℤ (Set.range basis.realCols) = carrier
  rank : ℕ+

noncomputable def LatticeBasis.toLattice (B : LatticeBasis n k) (fullrank: B.LinearIndependentReal) :
    LatticeWithBasis n k :=
  let carrier_module := Submodule.span ℤ (Set.range B.realCols)
  {
    carrier := carrier_module

    fg := by
      have h_fin : (Set.range B.realCols).Finite :=
        Set.finite_range _
      exact Submodule.fg_span h_fin

    discrete := by
      exact discrete_zspan fullrank

    basis := B

    is_basis := by rfl

    rank := k
  }

/--
  A typeclass (predicate) stating that a lattice spans the entire ambient space.
-/
class FullRank {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (L : AbstractLattice V) : Prop where
  span_top : Submodule.span ℝ (L.carrier : Set V) = ⊤

instance (B : SquareLatticeBasis n) (li : B.LinearIndependentReal) :
    FullRank (B.toLattice li).toAbstractLattice where
  span_top := by
    let L := B.toLattice li
    --  expand the goal by def
    have h_carrier : L.carrier = Submodule.span ℤ (Set.range B.realCols) := by rfl
    rw [h_carrier]
    -- The basis spans the whole space because it's fullrank
    have h_B_span_eq_top : Submodule.span ℝ (Set.range (B.realCols)) = ⊤ := by
      apply LinearIndependent.span_eq_top_of_card_eq_finrank li
      exact Eq.symm finrank_euclideanSpace
    -- The span of L is a supset of the span of its basis
    have h_supset : Submodule.span ℝ (Set.range (B.realCols)) ≤ Submodule.span ℝ (L.carrier : Set (𝔼 n)) := by
      apply Submodule.span_mono
      exact Submodule.span_le.mp fun ⦃x⦄ a => a

    simp [h_B_span_eq_top]


end Lattice

end LatticeCrypto.Foundations.Lattice
