import Mathlib.Algebra.Group.Subgroup.Defs     -- For AddSubgroup
import Mathlib.LinearAlgebra.LinearIndependent.Defs  -- For LinearIndependent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.ZLattice.Basic

import LatticeCrypto.Init
import LatticeCrypto.Utils.LinearAlgebra
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec

open scoped RealInnerProductSpace
open scoped Module
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Utils.Geometry

namespace LatticeCrypto.Foundations.Lattice

universe u

/-!
  In this file we define the mathematical notion of a lattice in ℝⁿ.

  * `LatticeBasis`: An n×k real matrix with linearly independent columns (k ≤ n).
  * `EuclideanLattice`: A lattice defined by its basis, with carrier being the ℤ-span of the basis.
  * `FullRank`: A predicate stating that n = k (the lattice has full rank).
-/

noncomputable section Lattice

-- Throughout this file we will use n to denote the dimension of the ambient space,
-- and k to denote the rank of the lattice
variable {n k : ℕ+}

/-!
## Lattice Basis

A computable basis for a lattice, represented as an n×k matrix with linearly independent columns.
-/


/--
  A lattice basis: k linearly independent vectors in ℝⁿ (k ≤ n).
  Represented as column vectors forming an n×k matrix.
-/
structure LatticeBasis (n k : ℕ+) where
  /-- The basis vectors as columns in ℝⁿ -/
  basis : Fin k → 𝓔 n
  /-- The number of vectors k must be at most n -/
  le_dim : k ≤ n
  /-- The vectors are linearly independent over ℝ -/
  li : LinearIndependent ℝ basis

@[ext] protected theorem LatticeBasis.ext {B1 B2 : LatticeBasis n k} (h : B1.basis = B2.basis) : B1 = B2 := by
  cases B1
  cases B2
  simp at h
  simp [h]

/-- A square lattice basis is one where n = k. -/
abbrev SquareLatticeBasis (n : ℕ+) := LatticeBasis n n

/-- Convert the columns of a LatticeBasis to vectors in Euclidean space over ℝ. -/
def LatticeBasis.cols (B : LatticeBasis n k) : Fin k → 𝓔 n := B.basis

/-- Convert the rows of a LatticeBasis to vectors in Euclidean space over ℝ. -/
def LatticeBasis.rows (B : LatticeBasis n k) : Fin n → 𝓔 k :=
  fun i => piToEuc (fun j => B.basis j i)

/-- Convert a LatticeBasis to a matrix representation. -/
def LatticeBasis.asMatrix (B : LatticeBasis n k) : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of (fun i j => B.basis j i)

/-- Convert a full rank matrix representation to a LatticeBasis. -/
def LatticeBasis.fromMatrix (M : Matrix (Fin n) (Fin k) ℝ) (le_dim : k ≤ n)
    (li : LinearIndependent ℝ (fun j => piToEuc (M.col j))) : LatticeBasis n k :=
  { basis := fun i => M.col i
    le_dim := le_dim
    li := li }

/-- Convert a LatticeBasis to a linear equivalence over 𝓔 n -/
def LatticeBasis.asLinearEquiv (B : SquareLatticeBasis n) : (𝓔 n) ≃ₗ[ℝ] (𝓔 n) :=
  have hu : IsUnit B.asMatrix.det := by
    unfold LatticeBasis.asMatrix
    rw [←Matrix.isUnit_iff_isUnit_det, ←Matrix.linearIndependent_cols_iff_isUnit]
    exact B.li
  B.asMatrix.toLinearEquiv (n := Fin n) stdBasis hu

/-- Convert a SquareLatticeBasis to a Basis of the ambient space -/
def LatticeBasis.asTopBasis (B : SquareLatticeBasis n) : Module.Basis (Fin n) ℝ (𝓔 n) :=
  let h_span : Submodule.span ℝ (Set.range B.cols) = ⊤ := by
    have h_dim : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      simp [finrank_euclideanSpace]
    apply LinearIndependent.span_eq_top_of_card_eq_finrank B.li h_dim
  Module.Basis.mk B.li h_span.ge

@[simp]
theorem LatticeBasis.coe_topBasis {B : SquareLatticeBasis n} : ⇑(LatticeBasis.asTopBasis B) = B.basis := by
  let h_span : Submodule.span ℝ (Set.range B.cols) = ⊤ := by
    have h_dim : Fintype.card (Fin n) = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      simp [finrank_euclideanSpace]
    apply LinearIndependent.span_eq_top_of_card_eq_finrank B.li h_dim
  exact Module.Basis.coe_mk B.li h_span.ge

lemma LatticeBasis.from_topBasis_to_matrix  (B : SquareLatticeBasis n) : stdBasis.toMatrix B.asTopBasis = B.asMatrix := by
  rw [toMatrix_on_stdBasis_eq_self B.asTopBasis, LatticeBasis.coe_topBasis]
  unfold LatticeBasis.asMatrix
  rfl


/-- Convert a LatticeBasis to a real-span Basis of the k-dimensional subspace -/
def LatticeBasis.asRealSpanBasis (B : LatticeBasis n k) :
    Module.Basis (Fin k) ℝ (Submodule.span ℝ (Set.range B.basis)) :=
  Module.Basis.span B.li

/-- Convert a LatticeBasis to a ZSpan Basis of the lattice -/
def LatticeBasis.asZSpanBasis (B : LatticeBasis n k) :
    Module.Basis (Fin k) ℤ (Submodule.span ℤ (Set.range B.basis)) :=
  have li_z : LinearIndependent ℤ B.basis := Z_linearIndependent_if_R_linearIndependent B.li
  Module.Basis.span li_z

/-!
## Geometric Lattice

A geometric lattice is defined by its basis, with the carrier being the ℤ-span of the basis.
-/

/--
  A geometric lattice in ℝⁿ, defined by a basis of k linearly independent vectors.
  The carrier is the ℤ-span of the basis.
-/
structure EuclideanLattice (n k : ℕ+) where
  /-- The basis for the lattice -/
  basis : LatticeBasis n k
  /-- The carrier is exactly the ℤ-span of the basis -/
  carrier : Submodule ℤ (𝓔 n) := Submodule.span ℤ (Set.range basis.cols)
  /-- Proof that carrier equals the span (automatically true by default) -/
  carrier_eq : carrier = Submodule.span ℤ (Set.range basis.cols) := by rfl

/-- Two geometric lattices with the same carrier are equivalent (though their bases may differ). -/
def EuclideanLattice.CarrierEquiv (L1 L2 : EuclideanLattice n k) : Prop :=
  L1.carrier = L2.carrier

/-- Carrier equivalence is reflexive. -/
theorem EuclideanLattice.CarrierEquiv.refl (L : EuclideanLattice n k) : L.CarrierEquiv L := rfl

/-- Carrier equivalence is symmetric. -/
theorem EuclideanLattice.CarrierEquiv.symm {L1 L2 : EuclideanLattice n k}
    (h : L1.CarrierEquiv L2) : L2.CarrierEquiv L1 := by
    rw [CarrierEquiv] at *
    exact h.symm

/-- Carrier equivalence is transitive. -/
theorem EuclideanLattice.CarrierEquiv.trans {L1 L2 L3 : EuclideanLattice n k}
    (h1 : L1.CarrierEquiv L2) (h2 : L2.CarrierEquiv L3) : L1.CarrierEquiv L3 := by
    rw [CarrierEquiv] at *
    exact h1.trans h2

/-- Carrier equivalence as a setoid. -/
instance EuclideanLattice.carrierSetoid : Setoid (EuclideanLattice n k) where
  r := CarrierEquiv
  iseqv := ⟨CarrierEquiv.refl, CarrierEquiv.symm, CarrierEquiv.trans⟩

/-- Notation for carrier equivalence of geometric lattices. -/
infix:50 " ≡ᵤ " => EuclideanLattice.CarrierEquiv

/-- Construct a EuclideanLattice from a LatticeBasis -/
def LatticeBasis.toLattice (B : LatticeBasis n k) : EuclideanLattice n k :=
  { basis := B }

theorem EuclideanLattice.eq_basis_toLattice (L : EuclideanLattice n k) :
    L = L.basis.toLattice := by
      let L' := L.basis.toLattice
      cases L
      cases L'
      congr

def isBasisFor (B: SquareLatticeBasis n) (L: EuclideanLattice n n) : Prop :=
  B.toLattice ≡ᵤ L

/-!
## Properties of Geometric Lattices
-/

/-- The carrier of a geometric lattice is finitely generated. -/
theorem EuclideanLattice.fg (L : EuclideanLattice n k) : L.carrier.FG := by
  rw [L.carrier_eq]
  have h_fin : (Set.range L.basis.cols).Finite := Set.finite_range _
  exact Submodule.fg_span h_fin

/-- The carrier of a geometric lattice has discrete topology. -/
theorem EuclideanLattice.discrete (L : EuclideanLattice n k) : DiscreteTopology L.carrier := by
  rw [L.carrier_eq]
  exact discrete_zspan L.basis.li

/-- The carrier of a geometric lattice is a countable set. -/
instance EuclideanLattice.instCountable (L : EuclideanLattice n k) : Countable L.carrier := by
  rw [L.carrier_eq]
  exact Finsupp.instCountableSubtypeMemSubmoduleSpanRange L.basis.cols

/-- Instance for discrete topology on the carrier. -/
instance EuclideanLattice.instDiscreteTopology (L : EuclideanLattice n k) :
    DiscreteTopology L.carrier := L.discrete

/- The lattice is a closed set because it is discrete -/
lemma EuclideanLattice.isClosed (L : EuclideanLattice n k) : IsClosed (L.carrier : Set (𝓔 n)) := by
  -- Since the lattice is a discrete subgroup of ℝ^n, it is closed.
  have h_discrete : DiscreteTopology (L.carrier : Set (𝓔 n)) := by
    simp +zetaDelta at *;
    exact instDiscreteTopology L;
  -- Since the lattice is a discrete subgroup of ℝ^n, it is closed in the topology of ℝ^n. This follows from the fact that discrete subgroups of locally compact groups are closed.
  have h_closed_subgroup : ∀ (G : AddSubgroup (𝓔 n)), DiscreteTopology G → IsClosed (G : Set (𝓔 n)) := by
    exact fun G a => AddSubgroup.isClosed_of_discrete;
  convert h_closed_subgroup ( L.carrier.toAddSubgroup ) h_discrete using 1

/- The lattice points in a closed ball form a finite set -/
lemma EuclideanLattice.finite_intersection_closedBall (L : EuclideanLattice n n) (r : ℝ) :
    Set.Finite { v ∈ L.carrier | ‖v‖ ≤ r } := by
      -- The ball of radius r in the lattice is a closed subset of the ball in R^n, which is compact. Therefore, the lattice points in the ball are finite.
      have h_closed : IsClosed {v : 𝓔 n | v ∈ L.carrier ∧ ‖v‖ ≤ r} := by
        exact IsClosed.inter L.isClosed ( isClosed_le continuous_norm continuous_const );
      have h_finite : IsCompact {v : L.carrier | ‖v‖ ≤ r} := by
        have h_finite : IsCompact (Set.image (fun v : L.carrier => v.val : L.carrier → 𝓔 n) {v : L.carrier | ‖v‖ ≤ r}) := by
          convert ProperSpace.isCompact_closedBall ( 0 : 𝓔 n ) r |> fun h => h.inter_right h_closed using 1 ; aesop;
        exact Subtype.isCompact_iff.mpr h_finite
      generalize_proofs at *;
      have := h_finite.finite_of_discrete; aesop (config := { warnOnNonterminal := false });
      exact Set.Finite.subset ( this.image Subtype.val ) fun x hx => by aesop;

/- Corollary: The lattice points in an open ball form a finite set -/
lemma EuclideanLattice.finite_intersection_ball (L : EuclideanLattice n n) (r : ℝ) :
    Set.Finite { v ∈ L.carrier | ‖v‖ < r } := by
  -- The open ball is a subset of the closed ball
  have h_subset : { v ∈ L.carrier | ‖v‖ < r } ⊆ { v ∈ L.carrier | ‖v‖ ≤ r } := by
    intro v ⟨hv_mem, hv_norm⟩
    exact ⟨hv_mem, le_of_lt hv_norm⟩
  exact Set.Finite.subset (L.finite_intersection_closedBall r) h_subset

/-!
## Full Rank Predicate
-/

/-- A lattice has full rank if n = k (the lattice spans the entire ambient space). -/
class FullRank (L : EuclideanLattice n k) : Prop where
  rank_eq : n = k

/-- A square lattice basis produces a full-rank lattice. -/
instance (B : SquareLatticeBasis n) : FullRank B.toLattice where
  rank_eq := rfl

/-- Full rank is equivalent to the real span being the whole space. -/
theorem FullRank.iff_span_top {L : EuclideanLattice n k} :
    FullRank L ↔ Submodule.span ℝ (L.carrier : Set (𝓔 n)) = ⊤ := by
  constructor
  · intro ⟨h_eq⟩
    subst h_eq
    rw [L.carrier_eq]
    have h_span_eq_top : Submodule.span ℝ (Set.range L.basis.cols) = ⊤ := by
      apply LinearIndependent.span_eq_top_of_card_eq_finrank L.basis.li
      exact Eq.symm finrank_euclideanSpace
    have h_supset : Submodule.span ℝ (Set.range L.basis.cols) ≤
        Submodule.span ℝ (Submodule.span ℤ (Set.range L.basis.cols) : Set (𝓔 n)) := by
      apply Submodule.span_mono
      exact Submodule.span_le.mp fun ⦃x⦄ a => a
    simp [h_span_eq_top]
  · intro h_span_top
    constructor
    -- If the span is top, then the basis must have n vectors
    have h_finrank : Module.finrank ℝ (Submodule.span ℝ (L.carrier : Set (𝓔 n))) = n := by
      rw [h_span_top]
      bound
    have h_le : (k : ℕ) ≤ n := L.basis.le_dim
    have h_card : Fintype.card (Fin k) = k := Fintype.card_fin k
    rw [L.carrier_eq] at h_span_top
    have h_span_basis : Submodule.span ℝ (Set.range L.basis.cols) ≤
        Submodule.span ℝ (Submodule.span ℤ (Set.range L.basis.cols) : Set (𝓔 n)) := by
      apply Submodule.span_mono
      exact Submodule.span_le.mp fun ⦃x⦄ a => a
    have h_span_basis_top : Submodule.span ℝ (Set.range L.basis.cols) = ⊤ := by
      have h1 : Submodule.span ℝ (Set.range L.basis.cols) ≤ ⊤ := le_top
      have h2 : ⊤ ≤ Submodule.span ℝ (Set.range L.basis.cols) := by
        rw [← h_span_top]
        bound
      exact le_antisymm h1 h2
    have h_k_eq_n : (k : ℕ) = n := by
      have h_finrank_k : Module.finrank ℝ (Submodule.span ℝ (Set.range L.basis.cols)) = k := by
        unfold LatticeBasis.cols
        rw [finrank_span_eq_card L.basis.li]
        exact Fintype.card_fin k
      rw [h_span_basis_top] at h_finrank_k
      simp only [finrank_top, finrank_euclideanSpace, Fintype.card_fin] at h_finrank_k
      exact h_finrank_k.symm
    exact PNat.eq (id (Eq.symm h_k_eq_n))

/-- A full-rank lattice is a ZLattice. -/
theorem FullRank.isZLattice (L : EuclideanLattice n k) [FullRank L] : IsZLattice ℝ L.carrier := by
  constructor
  exact FullRank.iff_span_top.mp ‹_›

@[simp]
theorem EuclideanLattice.full_rank_eq_module_span (L : EuclideanLattice n n) : L.carrier = Submodule.span ℤ (Set.range L.basis.asTopBasis) := by
  convert L.carrier_eq;
  -- The basis of the top subspace is the same as the basis of the lattice, which is given by the columns of the matrix.
  ext i; simp [LatticeBasis.asTopBasis];
  -- By definition of `L.basis.cols`, we have `L.basis.cols i = L.basis.basis i`.
  simp [LatticeBasis.cols]

/-!
## Unimodular Matrices and Equivalence
-/

/-- Unimodular matrices: k × k integer matrices with determinant ±1. -/
abbrev UnimodularMatrix (k : ℕ+) := Matrix.GeneralLinearGroup (Fin k) ℤ

namespace UnimodularMatrix

/-- Cast a unimodular matrix to reals -/
def real (U : UnimodularMatrix k) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.map U (Int.castRingHom ℝ)

@[simp]
lemma real_one : (1 : UnimodularMatrix k).real = 1 := by
  simp [real]

@[simp]
lemma real_mul (U V : UnimodularMatrix k) : (U * V).real = U.real * V.real := by
  unfold real
  rw [← Matrix.map_mul]
  rfl

end UnimodularMatrix

/-- Apply a unimodular transformation U to the basis B from the right: B' = B * U -/
def LatticeBasis.mul_unimodular (B : LatticeBasis n k) (U : UnimodularMatrix k) : LatticeBasis n k :=
  let basis_mat : Matrix (Fin n) (Fin k) ℝ := B.asMatrix * (Matrix.map U (Int.castRingHom ℝ))
  have h_li : LinearIndependent ℝ (fun j => basis_mat.col j) := by
    have h_lin_ind : LinearIndependent ℝ (fun j => B.asMatrix.col j) := by convert B.li
    have h_inv : ∀ x : Fin k → ℝ, B.asMatrix.mulVec x = 0 → x = 0 := by
      rw [Fintype.linearIndependent_iff] at h_lin_ind
      intro x hx
      exact funext fun i => h_lin_ind x (by ext j; simpa [Matrix.mulVec, dotProduct, mul_comm] using congr_fun hx j) i
    have h_linear_comb : ∀ (x : Fin k → ℝ), basis_mat.mulVec x = 0 → x = 0 := by
      intro x hx
      have hUx : B.asMatrix.mulVec (Matrix.mulVec (U.map (Int.castRingHom ℝ)) x) = 0 := by
        simp +zetaDelta at *
        exact hx
      specialize h_inv _ hUx
      exact Matrix.eq_zero_of_mulVec_eq_zero (show (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) U : Matrix (Fin k) (Fin k) ℝ).det ≠ 0 from by
        have h_det : (U.map (Int.castRingHom ℝ)).det = (U.det : ℝ) := by
          simp +decide [Matrix.det_apply']
        aesop (config := { warnOnNonterminal := false })
        exact absurd a (by exact Matrix.det_ne_zero_of_left_inverse U.inv_mul)) h_inv
    rw [Fintype.linearIndependent_iff]; aesop (config := { warnOnNonterminal := false })
    specialize h_linear_comb g
    contrapose! h_linear_comb
    exact ⟨by ext i; simpa [Matrix.mulVec, dotProduct, mul_comm] using congr_fun a i, fun h => h_linear_comb <| h ▸ rfl⟩
  { basis := fun i => basis_mat.col i
    le_dim := B.le_dim
    li := h_li }

-- Infix notation B ◾ U for readability
infixl:75 " ◾ " => LatticeBasis.mul_unimodular

/-- Two bases are unimodularly equivalent if there exists U such that B2 = B1 ◾ U. -/
def LatticeBasis.UnimodularEquiv (B1 B2 : LatticeBasis n k) : Prop :=
  ∃ U : Matrix.GeneralLinearGroup (Fin k) ℤ, B2 = B1 ◾ U

-- Verify it is an equivalence relation
theorem LatticeBasis.UnimodularEquiv.refl (B : LatticeBasis n k) : B.UnimodularEquiv B := by
  use 1
  simp [LatticeBasis.mul_unimodular]
  bound

theorem LatticeBasis.UnimodularEquiv.symm {B1 B2 : LatticeBasis n k}
    (h : B1.UnimodularEquiv B2) : B2.UnimodularEquiv B1 := by
  obtain ⟨U, hU⟩ := h
  use U⁻¹
  aesop (config := { warnOnNonterminal := false })
  have h_mul : (B1.mul_unimodular U).mul_unimodular U⁻¹ = B1.mul_unimodular (U * U⁻¹) := by
    have h_mul : (B1.mul_unimodular U).mul_unimodular U⁻¹ = B1.mul_unimodular (U * U⁻¹) := by
      have h_assoc : ∀ (B : LatticeBasis n k) (U V : Matrix.GeneralLinearGroup (Fin k) ℤ),
          (B.mul_unimodular U).mul_unimodular V = B.mul_unimodular (U * V) := by
        intros B U V
        ext i
        simp [LatticeBasis.mul_unimodular]
        simp +decide [Matrix.mul_apply, LatticeBasis.asMatrix]
        simp +decide only [Finset.sum_mul, mul_assoc, Finset.mul_sum _ _ _]
        rw [Finset.sum_comm]
      apply h_assoc
    exact h_mul
  aesop (config := { warnOnNonterminal := false })
  unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.mul_unimodular; aesop

theorem LatticeBasis.UnimodularEquiv.trans {B1 B2 B3 : LatticeBasis n k}
    (h1 : B1.UnimodularEquiv B2) (h2 : B2.UnimodularEquiv B3) : B1.UnimodularEquiv B3 := by
  cases h1; cases h2; aesop (config := { warnOnNonterminal := false })
  use w * w_1
  simp [LatticeBasis.mul_unimodular]
  have h_assoc : (B1.asMatrix * (w : Matrix (Fin k) (Fin k) ℤ).map (Int.castRingHom ℝ)) *
      (w_1 : Matrix (Fin k) (Fin k) ℤ).map (Int.castRingHom ℝ) =
      B1.asMatrix * ((w : Matrix (Fin k) (Fin k) ℤ) * (w_1 : Matrix (Fin k) (Fin k) ℤ)).map (Int.castRingHom ℝ) := by
    ext i j
    simp [Matrix.mul_assoc]
    simp +decide [Matrix.mul_apply, Matrix.map_apply]
  convert congr_arg (fun m => fun i => m.col i) h_assoc using 1

/-- Unimodular equivalence as a setoid. -/
instance LatticeBasis.unimodularSetoid : Setoid (LatticeBasis n k) where
  r := UnimodularEquiv
  iseqv := ⟨UnimodularEquiv.refl, UnimodularEquiv.symm, UnimodularEquiv.trans⟩

/-- Notation for unimodular equivalence of lattice bases. -/
infix:50 " =ᵤ " => LatticeBasis.UnimodularEquiv

-- Helper: Linear algebra expansion for unimodular multiplication
lemma cols_mul_unimodular (B : LatticeBasis n k) (U : UnimodularMatrix k) (i : Fin k) :
    (B ◾ U).cols i = ∑ j : Fin k, (U.val j i : ℝ) • B.cols j := by
  unfold LatticeBasis.cols
  ext; simp
  unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.mul_unimodular; aesop (config := { warnOnNonterminal := false })
  simp +decide [Matrix.mul_apply]
  rw [Finset.sum_apply, Finset.sum_congr rfl]; aesop (config := { warnOnNonterminal := false })
  exact mul_comm _ _

/-- Multiplying a basis by a unimodular matrix gives a sublattice. -/
lemma span_le_of_mul (B : LatticeBasis n k) (U : Matrix.GeneralLinearGroup (Fin k) ℤ) :
    Submodule.span ℤ (Set.range (B ◾ U).cols) ≤ Submodule.span ℤ (Set.range B.cols) := by
  rw [Submodule.span_le]
  rintro v ⟨i, rfl⟩
  rw [cols_mul_unimodular]
  apply Submodule.sum_mem
  intro j _
  convert Submodule.smul_mem _ _ (Submodule.subset_span <| Set.mem_range_self j)
  ext; simp
  left; exact rfl

/-- Helper: Get integer coefficients for a vector in the Z-span of a basis. -/
noncomputable def get_integer_coeffs {v : 𝓔 n} {B : LatticeBasis n k}
    (h_mem : v ∈ Submodule.span ℤ (Set.range B.cols)) : Fin k → ℤ := by
  have h_li_z : LinearIndependent ℤ B.cols := by
    have h_int_lin_ind : ∀ (c : Fin k → ℤ), (∑ i, c i • B.cols i = 0) → (∀ i, c i = 0) := by
      intros c hc
      have h_real : ∑ i, (c i : ℝ) • B.cols i = 0 := by
        convert hc using 1
        congr! 2
        ext; simp
      exact fun i => by have := Fintype.linearIndependent_iff.mp B.li (c ·) h_real i; aesop
    rw [Fintype.linearIndependent_iff]; aesop
  let module_basis := Module.Basis.span h_li_z
  let v_in_span : Submodule.span ℤ (Set.range B.cols) := ⟨v, h_mem⟩
  exact (module_basis.repr v_in_span : Fin k → ℤ)

/-- The transition matrix U such that B2 = B1 * U. -/
noncomputable def transition_matrix (B1 B2 : LatticeBasis n k)
    (h_subset : Submodule.span ℤ (Set.range B2.cols) ≤ Submodule.span ℤ (Set.range B1.cols)) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun j i =>
    let col_j := B2.cols j
    let h_mem_j : col_j ∈ Submodule.span ℤ (Set.range B1.cols) :=
      h_subset <| Submodule.subset_span <| Set.mem_range_self _
    get_integer_coeffs h_mem_j i

/-- If B2 is a unimodular transformation of B1, they generate the same lattice. -/
theorem LatticeBasis.span_eq_of_UnimodularEquiv {B1 B2 : LatticeBasis n k}
    (h : B1.UnimodularEquiv B2) :
    Submodule.span ℤ (Set.range B1.cols) = Submodule.span ℤ (Set.range B2.cols) := by
  obtain ⟨U, rfl⟩ := h
  apply le_antisymm
  · have h_eq : B1 = (B1 ◾ U) ◾ U⁻¹ := by
      have h_unit : U.val * U⁻¹.val = 1 := by aesop
      ext i j; aesop (config := { warnOnNonterminal := false })
      have h_unit : B1.asMatrix * (U.val.map (Int.castRingHom ℝ)) * (U⁻¹.val.map (Int.castRingHom ℝ)) = B1.asMatrix := by
        have h_unit : (U.val.map (Int.castRingHom ℝ)) * (U⁻¹.val.map (Int.castRingHom ℝ)) = 1 := by
          rw [← Matrix.map_mul]; aesop
        rw [Matrix.mul_assoc, h_unit, Matrix.mul_one]
      convert congr_fun (congr_fun h_unit j) i using 1
      · exact Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (congrFun (congrFun h_unit j) i)))
      · convert congr_fun (congr_fun h_unit j) i using 1
    nth_rw 1 [h_eq]
    apply span_le_of_mul
  · apply span_le_of_mul

/-- Two lattice bases are unimodularly equivalent iff their spans are equal. -/
theorem LatticeBasis.UnimodularEquiv_of_span_eq {B1 B2 : LatticeBasis n k}
    (h : Submodule.span ℤ (Set.range B1.cols) = Submodule.span ℤ (Set.range B2.cols)) :
    B1.UnimodularEquiv B2 := by
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin k) (Fin k) ℤ,
      B2.asMatrix = B1.asMatrix * Matrix.map U (Int.castRingHom ℝ) := by
    have h_comb : ∀ j : Fin k, ∃ u : Fin k → ℤ, B2.cols j = ∑ i : Fin k, u i • B1.cols i := by
      intro j
      have h_mem : B2.cols j ∈ Submodule.span ℤ (Set.range B1.cols) :=
        h.symm ▸ Submodule.subset_span (Set.mem_range_self j)
      rw [Finsupp.mem_span_range_iff_exists_finsupp] at h_mem; aesop (config := { warnOnNonterminal := false })
      exact ⟨_, h_1.symm⟩
    choose u hu using h_comb
    use Matrix.of (fun i j => u j i)
    ext i j; simp [Matrix.mul_apply]
    convert congr_fun (hu j) i using 1; simp +decide [mul_comm]
    rw [Finset.sum_apply]; aesop
  have h_unimodular : IsUnit (Matrix.det U) := by
    obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin k) (Fin k) ℤ,
        B1.asMatrix = B2.asMatrix * Matrix.map V (Int.castRingHom ℝ) := by
      have hV : ∀ i : Fin k, ∃ v : Fin k → ℤ, B1.cols i = ∑ j : Fin k, v j • B2.cols j := by
        intro i
        have hV : B1.cols i ∈ Submodule.span ℤ (Set.range B2.cols) :=
          h ▸ Submodule.subset_span (Set.mem_range_self i)
        rw [Finsupp.mem_span_range_iff_exists_finsupp] at hV
        exact ⟨hV.choose, by simpa [Finsupp.sum_fintype] using hV.choose_spec.symm⟩
      obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin k) (Fin k) ℤ,
          ∀ i : Fin k, B1.cols i = ∑ j : Fin k, V j i • B2.cols j :=
        ⟨fun j i => Classical.choose (hV i) j, fun i => Classical.choose_spec (hV i)⟩
      use V
      ext i j; simp +decide [Matrix.mul_apply]
      convert congr_fun (hV j) i using 1; simp +decide [mul_comm]
      rw [Finset.sum_apply, Finset.sum_congr rfl]; intros; aesop (config := { warnOnNonterminal := false })
      exact Or.inl (hU ▸ rfl)
    have h_inv : B1.asMatrix * U.map (Int.castRingHom ℝ) * V.map (Int.castRingHom ℝ) = B1.asMatrix := by
      rw [← hU, ← hV]
    have h_inv_mul : U.map (Int.castRingHom ℝ) * V.map (Int.castRingHom ℝ) = 1 := by
      have h_inv_mul : B1.asMatrix * (U.map (Int.castRingHom ℝ) * V.map (Int.castRingHom ℝ) - 1) = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h_inv, sub_self]
      have h_inv_mul : Function.Injective (Matrix.mulVec B1.asMatrix) := by
        have h_inv_mul : LinearIndependent ℝ (fun j => B1.asMatrix.col j) := by convert B1.li using 1
        rw [Fintype.linearIndependent_iff] at h_inv_mul
        have h_inj : ∀ (g : Fin k → ℝ), B1.asMatrix.mulVec g = 0 → g = 0 :=
          fun g hg => funext fun i => h_inv_mul g
            (by simpa [funext_iff, Matrix.mulVec, dotProduct, mul_comm] using hg) i
        exact fun x y hxy => sub_eq_zero.mp (h_inj (x - y)
          (by simpa [sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_neg] using sub_eq_zero.mpr hxy))
      have h_inv_mul : ∀ (M : Matrix (Fin k) (Fin k) ℝ), B1.asMatrix * M = 0 → M = 0 := by
        intro M hM; ext i j; specialize h_inv_mul
        replace h_inv_mul := @h_inv_mul (M.mulVec (Pi.single j 1)) 0
        simp_all +singlePass [Matrix.mulVec, funext_iff]
        exact h_inv_mul (fun x => by simpa [Matrix.mul_apply] using congr_fun (congr_fun hM x) j) i
      exact sub_eq_zero.mp (h_inv_mul _ ‹_›)
    have h_det : U.det * V.det = 1 := by
      replace h_inv_mul := congr_arg Matrix.det h_inv_mul; norm_num at h_inv_mul
      exact_mod_cast h_inv_mul
    exact isUnit_of_mul_eq_one _ _ h_det
  use ⟨U, U⁻¹, by
    rw [Matrix.mul_nonsing_inv _ _]; aesop, by
    exact Matrix.nonsing_inv_mul _ (show IsUnit U.det from h_unimodular)⟩
  generalize_proofs at *
  ext i j; replace hU := congr_fun (congr_fun hU j) i; aesop

theorem LatticeBasis.span_eq_iff {B1 B2 : LatticeBasis n k} :
    (Submodule.span ℤ (Set.range B1.cols) = Submodule.span ℤ (Set.range B2.cols)) ↔
    B1.UnimodularEquiv B2 :=
  ⟨UnimodularEquiv_of_span_eq, span_eq_of_UnimodularEquiv⟩

/-!
## Lattice Equivalence via Bases
-/

/-- Two geometric lattices are equal iff their bases are unimodularly equivalent. -/
theorem EuclideanLattice.eq_iff_basis_equiv {L1 L2 : EuclideanLattice n k} :
    L1 ≡ᵤ L2 ↔ L1.basis =ᵤ L2.basis := by
  constructor
  · intro h_eq
    rw [EuclideanLattice.CarrierEquiv] at h_eq
    rw [L1.carrier_eq, L2.carrier_eq] at h_eq
    exact LatticeBasis.UnimodularEquiv_of_span_eq h_eq
  · intro h_equiv
    rw [EuclideanLattice.CarrierEquiv, L1.carrier_eq, L2.carrier_eq]
    exact LatticeBasis.span_eq_of_UnimodularEquiv h_equiv

end Lattice

end LatticeCrypto.Foundations.Lattice
