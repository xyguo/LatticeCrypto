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
  * `LatticeBasis`: a linear independent basis for a lattice.
  * `LatticeWithBasis`: a lattice bundled with a basis, which is implemented as a subclass of `AbstractLattice`.
  * `FullRank`: a predicate that claims the lattice has full rank, meaning its \R-span is the entire ambient space.
-/

noncomputable section Lattice

/-- Notation for n-dimensional Euclidean space over ℝ. -/
abbrev 𝔼 (n : ℕ+) := EuclideanSpace ℝ (Fin n)

/-- Alternative notation: ℝⁿ for n-dimensional Euclidean space.
    Use as `ℝⁿ n` in code. -/
notation "ℝⁿ" => fun (n : ℕ+) => EuclideanSpace ℝ (Fin n)


-- V is our ambient space, usually EuclideanSpace ℝ (Fin n)
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

-- Throughout this file we will use n to denote the dimension of the space where the lattice lives,
-- and k to denote the rank of the lattice
variable {n k : ℕ+}

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

structure LatticeBasis (n k : ℕ+) where
  /- A ℚ-basis of ℚⁿ, represented as column vectors in ℚⁿ.
     Via coercion ℚ → ℝ, these live naturally in the Euclidean space
     `EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)` with the standard
     inner product and norm, using the EuclideanSpace.equiv tactic. -/
  basis : Fin k → 𝔼 n
  /-- The number of vectors k must be less than or equal to the dimension n. -/
  le_dim : k ≤ n
  /-- The vectors are linear independent -/
  li : LinearIndependent ℝ basis

@[ext] protected theorem ext {B1 B2 : LatticeBasis n k} (h : B1.basis = B2.basis) : B1 = B2 := by
  cases B1
  cases B2
  simp at h
  -- Since the basis functions are equal, the LatticeBasis instances are equal.
  simp [h]

/--
  A Square Lattice Basis is just the general case where n = k.
-/
abbrev SquareLatticeBasis (n : ℕ+) := LatticeBasis n n

/-- Helper: Linear equivalence between EuclideanSpace ℝ (Fin n) and the function space (Fin n → ℝ). -/
def eucToPi : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv

def piToEuc : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv

@[simp] lemma piToEuc_apply (f : Fin n → ℝ) (i : Fin n) :
  (eucToPi (piToEuc f)) i = f i := by simp[piToEuc, eucToPi]

@[simp] lemma eucToPi_apply (x : EuclideanSpace ℝ (Fin n)) :
  piToEuc (eucToPi x) = x := by simp[piToEuc, eucToPi]

lemma Z_linearIndependent_if_R_linearIndependent {v : Fin k → 𝔼 n} (li : LinearIndependent ℝ v) : LinearIndependent ℤ v := by
   -- If the cols are linearly independent over ℝ, then any linear combination with integer coefficients that equals zero must have all coefficients zero.
  have h_int_lin_ind : ∀ (c : Fin k → ℤ), (∑ i, c i • v i = 0) → (∀ i, c i = 0) := by
    -- Since the coefficients are integers, they are also real numbers. Therefore, if the sum is zero in ℝ, then each coefficient must be zero.
    intros c hc
    have h_real : ∑ i, (c i : ℝ) • v i = 0 := by
      convert hc using 1;
      congr! 2;
      -- Since the scalar multiplication in the real numbers is the same as in the integers when the scalar is an integer, the two functions are equal.
      ext; simp;
    exact fun i => by have := Fintype.linearIndependent_iff.mp li ( c · ) h_real i; aesop;
  rw [ Fintype.linearIndependent_iff ] ; aesop

lemma Q_linearIndependent_if_R_linearIndependent {v : Fin k → 𝔼 n} (li : LinearIndependent ℝ v) : LinearIndependent ℚ v := by
   -- If the cols are linearly independent over ℝ, then any linear combination with integer coefficients that equals zero must have all coefficients zero.
  have h_int_lin_ind : ∀ (c : Fin k → ℚ), (∑ i, c i • v i = 0) → (∀ i, c i = 0) := by
    -- Since the coefficients are integers, they are also real numbers. Therefore, if the sum is zero in ℝ, then each coefficient must be zero.
    intros c hc
    have h_real : ∑ i, (c i : ℝ) • v i = 0 := by
      convert hc using 1;
    exact fun i => by have := Fintype.linearIndependent_iff.mp li ( c · ) h_real i; aesop;
  rw [ Fintype.linearIndependent_iff ] ; aesop


/-- Convert the columns of a LatticeBasis to vectors in Euclidean space over ℝ. -/
def LatticeBasis.cols (B : LatticeBasis n k) :
    Fin k → 𝔼 n :=
    B.basis

/-- Convert the rows of a LatticeBasis to vectors in Euclidean space over ℝ. -/
def LatticeBasis.rows (B : LatticeBasis n k) :
    Fin n → 𝔼 k :=
  fun i => piToEuc (fun j => B.basis j i)

/-- Convert a SquareLatticeBasis to a Basis of the ambient space -/
def LatticeBasis.asTopBasis (B : SquareLatticeBasis n) :
    Module.Basis (Fin n) ℝ (𝔼 n) :=
  let h_span : Submodule.span ℝ (Set.range B.cols) = ⊤ := by
    have h_dim : Fintype.card (Fin n) = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
      simp [finrank_euclideanSpace]
    apply
      LinearIndependent.span_eq_top_of_card_eq_finrank B.li h_dim
  Module.Basis.mk B.li h_span.ge

/-- Convert a LatticeBasis to a real-span Basis of the k-dimensional subspace the lattice lives in -/
def LatticeBasis.asRealSpanBasis (B : LatticeBasis n k) :
    Module.Basis (Fin k) ℝ (Submodule.span ℝ (Set.range B.basis)) :=
    Basis.span B.li

/-- Convert a LatticeBasis to a ZSpan Basis of the lattice -/
def LatticeBasis.asZSpanBasis (B : LatticeBasis n k) :
    Module.Basis (Fin k) ℤ (Submodule.span ℤ (Set.range B.basis)) :=
    have li_z : LinearIndependent ℤ B.basis := by
     exact Z_linearIndependent_if_R_linearIndependent B.li
    Basis.span li_z

/-- Convert a LatticeBasis to a matrix representation. -/
def LatticeBasis.asMatrix (B : LatticeBasis n k) :
    Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of (fun i j => B.basis j i)

/-- Convert a full rank matrix representation to a LatticeBasis. -/
def LatticeBasis.fromMatrix (M : Matrix (Fin n) (Fin k) ℝ) (le_dim : k ≤ n) (li : LinearIndependent ℝ (fun j => piToEuc (M.col j))) : LatticeBasis n k :=
  {
    basis := fun i => M.col i

    le_dim := le_dim

    li := li
  }


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
  L.carrier = Submodule.span ℤ (Set.range B.cols)


/-- A lattice together with a chosen basis. -/
structure LatticeWithBasis (n k : ℕ+) extends AbstractLattice (𝔼 n) where
  basis   : LatticeBasis n k
  is_basis : Submodule.span ℤ (Set.range basis.cols) = carrier
  rank : ℕ+

noncomputable def LatticeBasis.toLattice (B : LatticeBasis n k) :
    LatticeWithBasis n k :=
  let carrier_module := Submodule.span ℤ (Set.range B.cols)
  {
    carrier := carrier_module

    fg := by
      have h_fin : (Set.range B.cols).Finite :=
        Set.finite_range _
      exact Submodule.fg_span h_fin

    discrete := by
      exact discrete_zspan B.li

    basis := B

    is_basis := by rfl

    rank := k
  }

/--
  A typeclass (predicate) stating that a lattice spans the entire ambient space.
-/
class FullRank {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (L : AbstractLattice V) : Prop where
  span_top : Submodule.span ℝ (L.carrier : Set V) = ⊤

instance (B : SquareLatticeBasis n) :
    FullRank B.toLattice.toAbstractLattice where
  span_top := by
    let L := B.toLattice
    --  expand the goal by def
    have h_carrier : L.carrier = Submodule.span ℤ (Set.range B.cols) := by rfl
    rw [h_carrier]
    -- The basis spans the whole space because it's fullrank
    have h_B_span_eq_top : Submodule.span ℝ (Set.range (B.cols)) = ⊤ := by
      apply LinearIndependent.span_eq_top_of_card_eq_finrank B.li
      exact Eq.symm finrank_euclideanSpace
    -- The span of L is a supset of the span of its basis
    have h_supset : Submodule.span ℝ (Set.range (B.cols)) ≤ Submodule.span ℝ (L.carrier : Set (𝔼 n)) := by
      apply Submodule.span_mono
      exact Submodule.span_le.mp fun ⦃x⦄ a => a

    simp [h_B_span_eq_top]


/--
  We represent unimodular matrices as the General Linear Group over ℤ.
  These are k × k integer matrices with determinant ±1.
-/
abbrev UnimodularMatrix (k : ℕ+) := Matrix.GeneralLinearGroup (Fin k) ℤ

/--
  Apply a unimodular transformation U to the basis B from the right.
  B' = B * U
-/
def LatticeBasis.mul_unimodular (B : LatticeBasis n k) (U : UnimodularMatrix k) :
    LatticeBasis n k :=
    let basis_mat : Matrix (Fin n) (Fin k) ℝ := B.asMatrix * (Matrix.map U (Int.castRingHom ℝ))
    have h_li : LinearIndependent ℝ (fun j => basis_mat.col j) := by
      -- Since $B$ is a lattice basis, its columns are linearly independent. Multiplying by an invertible matrix $U$ preserves linear independence.
      have h_lin_ind : LinearIndependent ℝ (fun j => B.asMatrix.col j) := by
        convert B.li;
      -- Since $U$ is invertible, the only solution to $Ux = 0$ is $x = 0$. Therefore, if the columns of $B.asMatrix$ are linearly independent, then the columns of $B.asMatrix * U$ are also linearly independent.
      have h_inv : ∀ x : Fin k → ℝ, B.asMatrix.mulVec x = 0 → x = 0 := by
        rw [ Fintype.linearIndependent_iff ] at h_lin_ind;
        intro x hx;
        exact funext fun i => h_lin_ind x ( by ext j; simpa [ Matrix.mulVec, dotProduct, mul_comm ] using congr_fun hx j ) i;
      have h_linear_comb : ∀ (x : Fin k → ℝ), basis_mat.mulVec x = 0 → x = 0 := by
        intro x hx
        have hUx : B.asMatrix.mulVec (Matrix.mulVec (U.map (Int.castRingHom ℝ)) x) = 0 := by
          simp +zetaDelta at *;
          exact hx;
        specialize h_inv _ hUx;
        exact Matrix.eq_zero_of_mulVec_eq_zero ( show ( Matrix.GeneralLinearGroup.map ( Int.castRingHom ℝ ) U : Matrix ( Fin k ) ( Fin k ) ℝ ).det ≠ 0 from by
              -- Since $U$ is a unimodular matrix, its determinant is $\pm 1$. When we map it to $\mathbb{R}$, the determinant remains $\pm 1$, which is non-zero.
          have h_det : (U.map (Int.castRingHom ℝ)).det = (U.det : ℝ) := by
            simp +decide [ Matrix.det_apply' ];
          aesop;
          exact absurd a ( by exact Matrix.det_ne_zero_of_left_inverse U.inv_mul ) ) h_inv;
      rw [ Fintype.linearIndependent_iff ] ; aesop;
      specialize h_linear_comb g;
      contrapose! h_linear_comb;
      exact ⟨ by ext i; simpa [ Matrix.mulVec, dotProduct, mul_comm ] using congr_fun a i, fun h => h_linear_comb <| h ▸ rfl ⟩
  {
    basis :=  fun i => basis_mat.col i

    -- Rank/Dimensions are preserved
    le_dim := B.le_dim

    li := h_li
  }

-- Allow the infix notation B ◾ U for readability
infixl:75 " ◾ " => LatticeBasis.mul_unimodular


/--
  Two bases are unimodularly equivalent if there exists a U such that B2 = B1 ◾ U.
-/
def LatticeBasis.UnimodularEquiv (B1 B2 : LatticeBasis n k) : Prop :=
  ∃ U : Matrix.GeneralLinearGroup (Fin k) ℤ, B2 = B1 ◾ U

-- Verify it is an equivalence relation
theorem LatticeBasis.UnimodularEquiv.refl (B : LatticeBasis n k) :
    B.UnimodularEquiv B := by
  use 1
  simp [LatticeBasis.mul_unimodular]
  bound

theorem LatticeBasis.UnimodularEquiv.symm {B1 B2 : LatticeBasis n k}
    (h : B1.UnimodularEquiv B2) : B2.UnimodularEquiv B1 := by
  -- Since $U$ is unimodular, its inverse $U^{-1}$ is also unimodular. Therefore, we can take $U' = U^{-1}$.
  obtain ⟨U, hU⟩ := h;
  use U⁻¹;
  aesop;
  -- By definition of matrix multiplication and the properties of unimodular matrices, we have:
  have h_mul : (B1.mul_unimodular U).mul_unimodular U⁻¹ = B1.mul_unimodular (U * U⁻¹) := by
    -- By definition of matrix multiplication and the properties of unimodular matrices, we can show that multiplying by U and then by U⁻¹ is the same as multiplying by the identity matrix.
    have h_mul : (B1.mul_unimodular U).mul_unimodular U⁻¹ = B1.mul_unimodular (U * U⁻¹) := by
      have h_assoc : ∀ (B : LatticeBasis n k) (U V : Matrix.GeneralLinearGroup (Fin k) ℤ), (B.mul_unimodular U).mul_unimodular V = B.mul_unimodular (U * V) := by
        -- By definition of matrix multiplication, we can show that the columns of B.mul_unimodular U are equal to the columns of B multiplied by U.
        intros B U V
        ext i
        simp [LatticeBasis.mul_unimodular];
        simp +decide [ Matrix.mul_apply, LatticeBasis.asMatrix ];
        simp +decide only [Finset.sum_mul, mul_assoc, Finset.mul_sum _ _ _];
        rw [ Finset.sum_comm ]
      -- Apply the associativity hypothesis h_assoc with V = U⁻¹.
      apply h_assoc;
    exact h_mul;
  aesop;
  unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.mul_unimodular; aesop;

theorem LatticeBasis.UnimodularEquiv.trans {B1 B2 B3 : LatticeBasis n k}
    (h1 : B1.UnimodularEquiv B2) (h2 : B2.UnimodularEquiv B3) :
    B1.UnimodularEquiv B3 := by
  cases h1 ; cases h2 ; aesop;
  -- By definition of unimodular equivalence, we need to show that B1 and (B1.mul_unimodular w).mul_unimodular w_1 are related by a unimodular transformation.
  use w * w_1;
  -- By definition of matrix multiplication, we can rewrite the left-hand side as $(B1 * w) * w_1$.
  simp [LatticeBasis.mul_unimodular];
  -- By the associativity of matrix multiplication, we can rewrite the left-hand side as B1.asMatrix * (w * w_1).
  have h_assoc : (B1.asMatrix * (w : Matrix (Fin k) (Fin k) ℤ).map (Int.castRingHom ℝ)) * (w_1 : Matrix (Fin k) (Fin k) ℤ).map (Int.castRingHom ℝ) = B1.asMatrix * ((w : Matrix (Fin k) (Fin k) ℤ) * (w_1 : Matrix (Fin k) (Fin k) ℤ)).map (Int.castRingHom ℝ) := by
    ext i j;
    -- By the associativity of matrix multiplication, we can rearrange the terms to show that the two expressions are equal.
    simp [Matrix.mul_assoc];
    simp +decide [ Matrix.mul_apply, Matrix.map_apply ];
  convert congr_arg ( fun m => fun i => m.col i ) h_assoc using 1

-- Helper: Just showing the linear algebra expansion without the full proof
lemma cols_mul_unimodular (B : LatticeBasis n k) (U : UnimodularMatrix k) (i : Fin k) :
    (B ◾ U).cols i = ∑ j : Fin k, (U.val j i : ℝ) • B.cols j := by
  unfold LatticeBasis.cols;
  ext; simp ;
  unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.mul_unimodular; aesop;
  simp +decide [ Matrix.mul_apply ];
  rw [ Finset.sum_apply, Finset.sum_congr rfl ] ; aesop;
  exact mul_comm _ _

/--
  Helper Lemma: Multiplying a basis by an integer matrix (even if not invertible)
  results in a sublattice. The span of the new columns is contained in the span of the old.
-/
lemma span_le_of_mul (B : LatticeBasis n k) (U : Matrix.GeneralLinearGroup (Fin k) ℤ) :
    Submodule.span ℤ (Set.range (B ◾ U).cols) ≤ Submodule.span ℤ (Set.range B.cols) := by
  -- We use the property that span A ≤ span B iff every element of A is in span B
  rw [Submodule.span_le]

  -- Take an arbitrary vector 'v' from the columns of the new basis (B ◾ U)
  rintro v ⟨i, rfl⟩

  -- We need to show that column 'i' of (B ◾ U) is in the Z-span of B
  rw [cols_mul_unimodular]
  -- The column is a sum: ∑ U_{ji} • (B_j).
  -- Since U_{ji} are integers, the sum of integer multiples of lattice vectors
  -- is essentially the definition of being in the lattice span.
  apply Submodule.sum_mem
  intro j _
  convert Submodule.smul_mem _ _ ( Submodule.subset_span <| Set.mem_range_self j );
  -- Since the integer is being cast to a real, this should hold because the scalar multiplication in the real numbers is just the same as in the integers when the scalar is an integer.
  ext; simp --[Int.cast_id];
  -- Since the integer is being cast to a real, this should hold because the scalar multiplication in the real numbers is just the same as in the integers when the scalar is an integer. Therefore, the first part of the disjunction is true.
  left; exact rfl

/--
  Helper: If a vector v is in the Z-span of a linearly independent basis B,
  there exists a UNIQUE integer coefficient vector expressing it.

  We return it as a function (Fin k → ℤ).
-/
noncomputable def get_integer_coeffs {v : 𝔼 n} {B : LatticeBasis n k}
  (h_mem : v ∈ Submodule.span ℤ (Set.range B.cols)) : Fin k → ℤ := by
  -- Use Mathlib's linear algebra API to extract coordinates
  -- We know v = ∑ c_i • b_i. Since B is LI over ℝ, it is LI over ℤ.
  -- Thus the representation is unique.
  have h_li_z : LinearIndependent ℤ B.cols := by
    -- If the cols are linearly independent over ℝ, then any linear combination with integer coefficients that equals zero must have all coefficients zero.
    have h_int_lin_ind : ∀ (c : Fin k → ℤ), (∑ i, c i • B.cols i = 0) → (∀ i, c i = 0) := by
      -- Since the coefficients are integers, they are also real numbers. Therefore, if the sum is zero in ℝ, then each coefficient must be zero.
      intros c hc
      have h_real : ∑ i, (c i : ℝ) • B.cols i = 0 := by
        convert hc using 1;
        congr! 2;
        -- Since the scalar multiplication in the real numbers is the same as in the integers when the scalar is an integer, the two functions are equal.
        ext; simp;
      exact fun i => by have := Fintype.linearIndependent_iff.mp B.li ( c · ) h_real i; aesop;
    rw [ Fintype.linearIndependent_iff ] ; aesop
  let module_basis := Basis.span h_li_z
  let v_in_span : Submodule.span ℤ (Set.range B.cols) := ⟨v, h_mem⟩
  exact (module_basis.repr v_in_span : Fin k → ℤ)

/--
  The constructed integer matrix U that B2 = B1 * U.
-/
noncomputable def transition_matrix (B1 B2 : LatticeBasis n k)
  (h_subset : Submodule.span ℤ (Set.range B2.cols) ≤ Submodule.span ℤ (Set.range B1.cols)) : Matrix (Fin k) (Fin k) ℤ :=
  fun j i =>
    -- The (i, j)-th entry is the i-th coefficient of the j-th column of B2
    -- when expressed in basis B1.
    let col_j := B2.cols j
    let h_mem_j : col_j ∈ Submodule.span ℤ (Set.range B1.cols) := by
      exact h_subset <| Submodule.subset_span <| Set.mem_range_self _
    get_integer_coeffs h_mem_j i


/--
  If B2 is a unimodular transformation of B1, they generate the same lattice.
  (Assumption: B1 is full rank, which implies B2 is full rank).
-/
theorem LatticeBasis.span_eq_of_UnimodularEquiv {B1 B2 : LatticeBasis n k}
    (h : B1.UnimodularEquiv B2) :
    Submodule.span ℤ (Set.range B1.cols) = Submodule.span ℤ (Set.range B2.cols) := by
  obtain ⟨U, rfl⟩ := h

  -- Use antisymmetry: L1 ≤ L2 and L2 ≤ L1 implies L1 = L2
  apply le_antisymm

  · -- Direction 1: span(B1) ≤ span(B1 ◾ U)
    -- Trick: B1 can be written as (B1 ◾ U) ◾ U⁻¹
    have h_eq : B1 = (B1 ◾ U) ◾ U⁻¹ := by
      -- Since $U$ is unimodular, we have $U * U⁻¹ = 1$, the identity matrix.
      have h_unit : U.val * U⁻¹.val = 1 := by
        aesop;
      ext i j ; aesop;
      -- Since $U$ is unimodular, we have $U * U⁻¹ = 1$, the identity matrix. Therefore, $B1 * U * U⁻¹ = B1$.
      have h_unit : B1.asMatrix * (U.val.map (Int.castRingHom ℝ)) * (U⁻¹.val.map (Int.castRingHom ℝ)) = B1.asMatrix := by
        have h_unit : (U.val.map (Int.castRingHom ℝ)) * (U⁻¹.val.map (Int.castRingHom ℝ)) = 1 := by
          rw [ ← Matrix.map_mul ] ; aesop;
        -- Since multiplying by the identity matrix doesn't change the matrix, we can conclude that B1.asMatrix * (U.val.map (Int.castRingHom ℝ)) * (U⁻¹.val.map (Int.castRingHom ℝ)) = B1.asMatrix.
        rw [Matrix.mul_assoc, h_unit, Matrix.mul_one];
      convert congr_fun ( congr_fun h_unit j ) i using 1;
      · exact?;
      · convert congr_fun ( congr_fun h_unit j ) i using 1

    -- Rewrite B1 and apply the helper lemma
    nth_rw 1 [h_eq]
    apply span_le_of_mul

  · -- Direction 2: span(B1 ◾ U) ≤ span(B1)
    -- This is exactly our helper lemma
    apply span_le_of_mul

/-- Two (n k) lattice bases are unimodularly equivalent if and only if their spans are equal. -/
theorem LatticeBasis.UnimodularEquiv_of_span_eq {B1 B2 : LatticeBasis n k}
    (h : Submodule.span ℤ (Set.range B1.cols) = Submodule.span ℤ (Set.range B2.cols)) : B1.UnimodularEquiv B2 := by
  -- Since the spans are equal, there exists a matrix U with integer entries such that B2 = B1 * U.
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin k) (Fin k) ℤ, B2.asMatrix = B1.asMatrix * Matrix.map U (Int.castRingHom ℝ) := by
    -- Since $B2$'s columns are in the span of $B1$'s columns, each column of $B2$ can be written as a linear combination of the columns of $B1$ with integer coefficients.
    have h_comb : ∀ j : Fin k, ∃ u : Fin k → ℤ, B2.cols j = ∑ i : Fin k, u i • B1.cols i := by
      -- By definition of submodule span, if $B2.cols j$ is in the submodule spanned by $B1.cols$, then there exist integers $u_i$ such that $B2.cols j = \sum_{i=0}^{k-1} u_i • B1.cols i$.
      intro j
      have h_mem : B2.cols j ∈ Submodule.span ℤ (Set.range B1.cols) := by
        exact h.symm ▸ Submodule.subset_span ( Set.mem_range_self j );
      rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_mem ; aesop;
      exact ⟨ _, h_1.symm ⟩;
    choose u hu using h_comb;
    use Matrix.of (fun i j => u j i);
    -- By definition of matrix multiplication, each entry in the product matrix is the sum of the products of the corresponding entries from B1.asMatrix and the matrix of u_j i.
    ext i j; simp [Matrix.mul_apply];
    convert congr_fun ( hu j ) i using 1 ; simp +decide [ mul_comm ];
    rw [ Finset.sum_apply ] ; aesop;
  -- Since U is an integer matrix and the spans are equal, U must be unimodular.
  have h_unimodular : IsUnit (Matrix.det U) := by
    -- Since the spans are equal, there exists a matrix V with integer entries such that B1 = B2 * V.
    obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin k) (Fin k) ℤ, B1.asMatrix = B2.asMatrix * Matrix.map V (Int.castRingHom ℝ) := by
      have hV : ∀ i : Fin k, ∃ v : Fin k → ℤ, B1.cols i = ∑ j : Fin k, v j • B2.cols j := by
        intro i;
        have hV : B1.cols i ∈ Submodule.span ℤ (Set.range B2.cols) := by
          exact h ▸ Submodule.subset_span ( Set.mem_range_self i );
        rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hV;
        exact ⟨ hV.choose, by simpa [ Finsupp.sum_fintype ] using hV.choose_spec.symm ⟩;
      -- Construct the matrix V by taking the vectors v_i from hV as its columns.
      obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin k) (Fin k) ℤ, ∀ i : Fin k, B1.cols i = ∑ j : Fin k, V j i • B2.cols j := by
        exact ⟨ fun j i => Classical.choose ( hV i ) j, fun i => Classical.choose_spec ( hV i ) ⟩;
      use V;
      ext i j; simp +decide [ Matrix.mul_apply ] ;
      convert congr_fun ( hV j ) i using 1 ; simp +decide [ mul_comm ];
      rw [ Finset.sum_apply, Finset.sum_congr rfl ] ; intros ; aesop;
      exact Or.inl ( hU ▸ rfl );
    -- Since B1 and B2 are bases, their matrices are invertible over the reals. Therefore, U must be invertible over the integers.
    have h_inv : B1.asMatrix * U.map (Int.castRingHom ℝ) * V.map (Int.castRingHom ℝ) = B1.asMatrix := by
      rw [ ← hU, ← hV ];
    -- Since B1 is a basis, its matrix is invertible over the reals. Therefore, we can multiply both sides of the equation by B1.asMatrix⁻¹.
    have h_inv_mul : U.map (Int.castRingHom ℝ) * V.map (Int.castRingHom ℝ) = 1 := by
      have h_inv_mul : B1.asMatrix * (U.map (Int.castRingHom ℝ) * V.map (Int.castRingHom ℝ) - 1) = 0 := by
        rw [ Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h_inv, sub_self ];
      have h_inv_mul : Function.Injective (Matrix.mulVec B1.asMatrix) := by
        have h_inv_mul : LinearIndependent ℝ (fun j => B1.asMatrix.col j) := by
          convert B1.li using 1;
        rw [ Fintype.linearIndependent_iff ] at h_inv_mul;
        -- If the sum of g_i times the columns of B1.asMatrix is zero, then each g_i must be zero because the columns are linearly independent.
        have h_inj : ∀ (g : Fin k → ℝ), B1.asMatrix.mulVec g = 0 → g = 0 := by
          exact fun g hg => funext fun i => h_inv_mul g ( by simpa [ funext_iff, Matrix.mulVec, dotProduct, mul_comm ] using hg ) i;
        exact fun x y hxy => sub_eq_zero.mp ( h_inj ( x - y ) ( by simpa [ sub_eq_add_neg, Matrix.mulVec_add, Matrix.mulVec_neg ] using sub_eq_zero.mpr hxy ) );
      have h_inv_mul : ∀ (M : Matrix (Fin k) (Fin k) ℝ), B1.asMatrix * M = 0 → M = 0 := by
        intro M hM; ext i j; specialize h_inv_mul; replace h_inv_mul := @h_inv_mul ( M.mulVec ( Pi.single j 1 ) ) 0; simp_all +singlePass [ Matrix.mulVec, funext_iff ] ;
        exact h_inv_mul ( fun x => by simpa [ Matrix.mul_apply ] using congr_fun ( congr_fun hM x ) j ) i;
      exact sub_eq_zero.mp ( h_inv_mul _ ‹_› );
    have h_det : U.det * V.det = 1 := by
      replace h_inv_mul := congr_arg Matrix.det h_inv_mul ; norm_num at h_inv_mul;
      exact_mod_cast h_inv_mul;
    exact isUnit_of_mul_eq_one _ _ h_det;
  use ⟨ U, U⁻¹, by
    rw [ Matrix.mul_nonsing_inv _ _ ] ; aesop, by
    exact Matrix.nonsing_inv_mul _ ( show IsUnit U.det from h_unimodular ) ⟩
  generalize_proofs at *;
  ext i j; replace hU := congr_fun ( congr_fun hU j ) i; aesop;

theorem LatticeBasis.span_eq_iff {B1 B2 : LatticeBasis n k} :
    (Submodule.span ℤ (Set.range B1.cols) = Submodule.span ℤ (Set.range B2.cols)) ↔ B1.UnimodularEquiv B2 := by
  -- This is a direct corollary of `
  apply Iff.intro
  . intro h
    exact UnimodularEquiv_of_span_eq h
  . intro h
    exact span_eq_of_UnimodularEquiv h

end Lattice

end LatticeCrypto.Foundations.Lattice
