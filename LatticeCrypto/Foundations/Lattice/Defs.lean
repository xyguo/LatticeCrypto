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

@[ext] protected theorem ext {B1 B2 : LatticeBasis n k} (h : B1.basis = B2.basis) : B1 = B2 := by
  cases B1
  cases B2
  simp at h
  (expose_names; exact congrFun (congrArg LatticeBasis.mk h) le_dim)

def LatticeBasis.cols (B : LatticeBasis n k) :
    Fin k → Fin n → ℚ :=
  fun j => fun i => B.basis i j

def LatticeBasis.rows (B : LatticeBasis n k) :
    Fin n → Fin k → ℚ :=
  fun i => fun j => B.basis i j

/-- Convert a LatticeBasis with rational entries to a matrix with real entries. -/
noncomputable def LatticeBasis.toRealMatrix (B : LatticeBasis n k) : Matrix (Fin n) (Fin k) ℝ :=
  Matrix.map B.basis (Rat.cast : ℚ → ℝ)

/--
  A Square Lattice Basis is just the general case where n = k.
-/
abbrev SquareLatticeBasis (n : ℕ+) := LatticeBasis n n

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
  {
    -- Convert U from ℤ to ℚ and multiply: (n×k) * (k×k) -> (n×k)
    basis := B.basis * (Matrix.map U (Int.castRingHom ℚ))

    -- Rank/Dimensions are preserved
    le_dim := B.le_dim
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

theorem LatticeBasis.UnimodularEquiv.symm {B1 B2 : LatticeBasis n k}
    (h : B1.UnimodularEquiv B2) : B2.UnimodularEquiv B1 := by
  obtain ⟨U, h_eq⟩ := h
  use U⁻¹
  -- Proof: B2 * U⁻¹ = (B1 * U) * U⁻¹ = B1 * (U * U⁻¹) = B1
  simp [h_eq, LatticeBasis.mul_unimodular, Matrix.mul_assoc]
  -- Since $U * U⁻¹ = 1$, we have $((U : Matrix (Fin k) (Fin k) ℤ).map (Int.castRingHom ℚ) * (U⁻¹ : Matrix (Fin k) (Fin k) ℤ).map (Int.castRingHom ℚ)) = 1$.
  have h_id : ((U : Matrix (Fin k) (Fin k) ℤ).map (Int.castRingHom ℚ) * (U⁻¹ : Matrix (Fin k) (Fin k) ℤ).map (Int.castRingHom ℚ)) = 1 := by
    exact Matrix.GeneralLinearGroup.coe_map_mul_map_inv (Int.castRingHom ℚ) U;
  aesop

theorem LatticeBasis.UnimodularEquiv.trans {B1 B2 B3 : LatticeBasis n k}
    (h1 : B1.UnimodularEquiv B2) (h2 : B2.UnimodularEquiv B3) :
    B1.UnimodularEquiv B3 := by
  obtain ⟨U, rfl⟩ := h1
  obtain ⟨V, rfl⟩ := h2
  -- Note the order: B3 = (B1 * U) * V = B1 * (U * V)
  use U * V
  simp [LatticeBasis.mul_unimodular, Matrix.mul_assoc]
  -- Matrix.map_mul ensures the cast from ℤ to ℚ works over multiplication
  -- The product of two matrices over a field is the same as the product of their entries.
  ext; simp [Matrix.mul_apply]

-- Helper: Just showing the linear algebra expansion without the full proof
lemma realCols_mul_unimodular (B : LatticeBasis n k) (U : UnimodularMatrix k) (i : Fin k) :
    (B ◾ U).realCols i = ∑ j : Fin k, (U.val j i : ℝ) • B.realCols j := by
  -- 1. Unfold definitions of realCols and matrix multiplication
  unfold LatticeBasis.realCols LatticeBasis.mul_unimodular;
  -- 2. Use the fact that projection to Euclidean space is linear
  ext j; simp +decide [ Matrix.mul_apply, LatticeBasis.toRealMatrix ];
  simp +decide [ piToEuc];
  -- 3. Show that the casting from ℚ to ℝ commutes with the sum
  rw [ Finset.sum_apply, Finset.sum_congr rfl ] ; aesop;
  ring
/--
  Helper Lemma: Multiplying a basis by an integer matrix (even if not invertible)
  results in a sublattice. The span of the new columns is contained in the span of the old.
-/
lemma span_le_of_mul (B : LatticeBasis n k) (U : Matrix.GeneralLinearGroup (Fin k) ℤ) :
    Submodule.span ℤ (Set.range (B ◾ U).realCols) ≤ Submodule.span ℤ (Set.range B.realCols) := by
  -- We use the property that span A ≤ span B iff every element of A is in span B
  rw [Submodule.span_le]

  -- Take an arbitrary vector 'v' from the columns of the new basis (B ◾ U)
  rintro v ⟨i, rfl⟩

  -- We need to show that column 'i' of (B ◾ U) is in the Z-span of B
  rw [realCols_mul_unimodular]
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
  (h_mem : v ∈ Submodule.span ℤ (Set.range B.realCols))
  (h_li : B.LinearIndependentReal) : Fin k → ℤ := by
  -- Use Mathlib's linear algebra API to extract coordinates
  -- We know v = ∑ c_i • b_i. Since B is LI over ℝ, it is LI over ℤ.
  -- Thus the representation is unique.
  have h_li_z : LinearIndependent ℤ B.realCols := by
    -- If the realCols are linearly independent over ℝ, then any linear combination with integer coefficients that equals zero must have all coefficients zero.
    have h_int_lin_ind : ∀ (c : Fin k → ℤ), (∑ i, c i • B.realCols i = 0) → (∀ i, c i = 0) := by
      -- Since the coefficients are integers, they are also real numbers. Therefore, if the sum is zero in ℝ, then each coefficient must be zero.
      intros c hc
      have h_real : ∑ i, (c i : ℝ) • B.realCols i = 0 := by
        convert hc using 1;
        congr! 2;
        -- Since the scalar multiplication in the real numbers is the same as in the integers when the scalar is an integer, the two functions are equal.
        ext; simp;
      exact fun i => by have := Fintype.linearIndependent_iff.mp h_li ( c · ) h_real i; aesop;
    rw [ Fintype.linearIndependent_iff ] ; aesop
  let module_basis := Basis.span h_li_z
  let v_in_span : Submodule.span ℤ (Set.range B.realCols) := ⟨v, h_mem⟩
  exact (module_basis.repr v_in_span : Fin k → ℤ)

/--
  The constructed integer matrix U that B2 = B1 * U.
-/
noncomputable def transition_matrix (B1 B2 : LatticeBasis n k)
  (h_subset : Submodule.span ℤ (Set.range B2.realCols) ≤ Submodule.span ℤ (Set.range B1.realCols))
  (li1 : B1.LinearIndependentReal) : Matrix (Fin k) (Fin k) ℤ :=
  fun j i =>
    -- The (i, j)-th entry is the i-th coefficient of the j-th column of B2
    -- when expressed in basis B1.
    let col_j := B2.realCols j
    let h_mem_j : col_j ∈ Submodule.span ℤ (Set.range B1.realCols) := by
      exact h_subset <| Submodule.subset_span <| Set.mem_range_self _
    get_integer_coeffs h_mem_j li1 i


/--
  If B2 is a unimodular transformation of B1, they generate the same lattice.
  (Assumption: B1 is full rank, which implies B2 is full rank).
-/
theorem LatticeBasis.span_eq_of_UnimodularEquiv {B1 B2 : LatticeBasis n k}
    (h : B1.UnimodularEquiv B2) :
    Submodule.span ℤ (Set.range B1.realCols) = Submodule.span ℤ (Set.range B2.realCols) := by
  obtain ⟨U, rfl⟩ := h

  -- Use antisymmetry: L1 ≤ L2 and L2 ≤ L1 implies L1 = L2
  apply le_antisymm

  · -- Direction 1: span(B1) ≤ span(B1 ◾ U)
    -- Trick: B1 can be written as (B1 ◾ U) ◾ U⁻¹
    have h_eq : B1 = (B1 ◾ U) ◾ U⁻¹ := by
      -- Proof that B * U * U⁻¹ = B
      -- This requires associativity of your `◾` operation
      unfold LatticeBasis.mul_unimodular; aesop;
      -- Since $U$ is invertible, $U * U⁻¹ = 1$, the identity matrix. Therefore, multiplying $B1$'s basis by $U$ and then by $U⁻¹$ gives $B1$'s basis back.
      have h_id : (B1.basis * (U : Matrix (Fin k) (Fin k) ℤ).map (Int.castRingHom ℚ)) * (U⁻¹ : Matrix (Fin k) (Fin k) ℤ).map (Int.castRingHom ℚ) = B1.basis * (1 : Matrix (Fin k) (Fin k) ℚ) := by
        rw [ Matrix.mul_assoc, ← Matrix.map_mul ] ; aesop;
      aesop

    -- Rewrite B1 and apply the helper lemma
    nth_rw 1 [h_eq]
    apply span_le_of_mul

  · -- Direction 2: span(B1 ◾ U) ≤ span(B1)
    -- This is exactly our helper lemma
    apply span_le_of_mul


theorem LatticeBasis.UnimodularEquiv_of_span_eq {B1 B2 : LatticeBasis n k}
    (h : Submodule.span ℤ (Set.range B1.realCols) = Submodule.span ℤ (Set.range B2.realCols)) (li1 : B1.LinearIndependentReal) (li2 : B2.LinearIndependentReal): B1.UnimodularEquiv B2 := by
  -- Since the spans are equal, each column of B2 can be written as a linear combination of the columns of B1 with integer coefficients.
  have h_comb : ∀ j : Fin k, ∃ c : Fin k → ℤ, B2.realCols j = ∑ i, c i • B1.realCols i := by
    intro j
    have h_mem : B2.realCols j ∈ Submodule.span ℤ (Set.range B1.realCols) := by
      exact h ▸ Submodule.subset_span ( Set.mem_range_self j );
    rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_mem;
    exact ⟨ h_mem.choose, by simpa [ Finsupp.sum_fintype ] using h_mem.choose_spec.symm ⟩;
  -- Construct the matrix U such that B2 = B1 * U.
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin k) (Fin k) ℤ, B2.basis = B1.basis * Matrix.map U (Int.castRingHom ℚ) := by
    choose c hc using h_comb;
    use Matrix.of (fun i j => c j i);
    ext i j;
    -- By definition of matrix multiplication and the hypothesis hc, we can rewrite the right-hand side of the equation.
    have h_eq : B2.basis i j = ∑ x : Fin k, c j x * B1.basis i x := by
      have h_col : B2.realCols j = ∑ x : Fin k, c j x • B1.realCols x := hc j
      convert congr_fun ( congr_arg ( fun x : EuclideanSpace ℝ ( Fin n ) => eucToPi x ) h_col ) i using 1;
      simp +decide [ ← @Rat.cast_inj ℝ];
      unfold LatticeBasis.realCols; aesop;
    simpa [ Matrix.mul_apply, mul_comm ] using h_eq;
  -- Since U is an integer matrix and the spans are equal, U must be invertible over the integers.
  have h_inv : ∃ V : Matrix (Fin k) (Fin k) ℤ, U * V = 1 := by
    -- Since $B1$ and $B2$ are both bases for the same lattice, $B1$ can be written as $B2 * V$ for some integer matrix $V$.
    obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin k) (Fin k) ℤ, B1.basis = B2.basis * Matrix.map V (Int.castRingHom ℚ) := by
      have h_comb : ∀ j : Fin k, ∃ c : Fin k → ℤ, B1.realCols j = ∑ i, c i • B2.realCols i := by
        -- Since the spans are equal, any element in the span of B1.realCols is also in the span of B2.realCols. Therefore, B1.realCols j is in the span of B2.realCols.
        have h_span : ∀ j : Fin k, B1.realCols j ∈ Submodule.span ℤ (Set.range B2.realCols) := by
          exact fun j => h ▸ Submodule.subset_span ( Set.mem_range_self j );
        intro j; specialize h_span j; rw [ Submodule.mem_span_range_iff_exists_fun ] at h_span; tauto;
      choose c hc using h_comb;
      use Matrix.of (fun i j => c j i);
      -- By definition of matrix multiplication and the hypothesis hc, we can show that B1.basis is equal to B2.basis multiplied by the matrix of coefficients c.
      ext i j; simp [Matrix.mul_apply];
      convert congr_fun ( hc j ) i using 1;
      simp +decide [ LatticeBasis.realCols, mul_comm ];
      simp +decide [ piToEuc, LatticeBasis.toRealMatrix ];
      erw [ Finset.sum_apply ] ; norm_num [ WithLp.toLp ];
      norm_cast;
    -- Since $B1$ and $B2$ are both bases for the same lattice, $B1$ can be written as $B2 * V$ for some integer matrix $V$. Substitute $B2$ from $hU$ into $hV$.
    have h_subst : B1.basis = (B1.basis * U.map (Int.castRingHom ℚ)) * V.map (Int.castRingHom ℚ) := by
      rw [ ← hU, hV ];
    -- Since $B1$ and $B2$ are both bases for the same lattice, $B1$ can be written as $B2 * V$ for some integer matrix $V$. Substitute $B2$ from $hU$ into $hV$ and simplify.
    have h_simplified : B1.basis * (U.map (Int.castRingHom ℚ) * V.map (Int.castRingHom ℚ) - 1) = 0 := by
      rw [ Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← h_subst, sub_self ];
    -- Since $B1$ is a basis, the only solution to $B1 * X = 0$ is $X = 0$.
    have h_basis : ∀ X : Matrix (Fin k) (Fin k) ℚ, B1.basis * X = 0 → X = 0 := by
      intro X hX
      have h_lin_ind : ∀ (v : Fin k → ℚ), B1.basis.mulVec v = 0 → v = 0 := by
        intro v hv
        have h_lin_ind : ∀ (v : Fin k → ℝ), Matrix.mulVec (B1.toRealMatrix) v = 0 → v = 0 := by
          intro v hv;
          have := Fintype.linearIndependent_iff.mp li1;
          ext i;
          convert this v _ i;
          ext i;
          convert congr_fun hv i using 1;
          simp +decide [ Matrix.mulVec, dotProduct, mul_comm ];
          rw [ Finset.sum_apply, Finset.sum_congr rfl ] ; intros ; simp +decide ;
          exact Or.inl rfl;
        contrapose! h_lin_ind;
        use fun i => v i;
        -- Since $v$ is a rational vector and not zero, when we cast it to real numbers, it should still not be zero.
        have h_real_v_ne_zero : (fun i => (v i : ℝ)) ≠ 0 := by
          exact fun h => h_lin_ind <| funext fun i => by simpa using congr_fun h i;
        exact ⟨ by ext i; simpa [ Matrix.mulVec, dotProduct ] using congr_arg ( fun x : Fin n → ℚ => ( x i : ℝ ) ) hv, h_real_v_ne_zero ⟩;
      -- Apply h_lin_ind to each column of X.
      have h_col_zero : ∀ j : Fin k, B1.basis.mulVec (X.mulVec (Pi.single j 1)) = 0 := by
        intro j
        have h_col_zero : B1.basis.mulVec (X.mulVec (Pi.single j 1)) = (B1.basis * X).mulVec (Pi.single j 1) := by
          rw [ Matrix.mulVec_mulVec ];
        rw [ h_col_zero, hX, Matrix.zero_mulVec ];
      exact Matrix.ext fun i j => by simpa using congr_fun ( h_lin_ind _ ( h_col_zero j ) ) i;
    specialize h_basis _ h_simplified;
    norm_num [ ← Matrix.ext_iff ] at *;
    -- Since $(U * V) i j = 1 i j$ for all $i$ and $j$, this implies that $U * V$ is the identity matrix.
    use V;
    -- Since the entries of U and V are integers, the equality (U * V) i j = 1 i j holds in the integers as well.
    intros i j
    have := h_basis i j
    simp [Matrix.mul_apply, Matrix.one_apply] at this;
    norm_cast at this;
    simpa [ Matrix.one_apply ] using eq_of_sub_eq_zero this;
  -- Since U is invertible over the integers, it is a unimodular matrix.
  have h_unimodular : IsUnit U := by
    exact Matrix.isUnit_of_right_inverse h_inv.choose_spec;
  use h_unimodular.unit;
  cases B1 ; cases B2 ; aesop

theorem LatticeBasis.span_eq_iff {B1 B2 : LatticeBasis n k} (li1 : B1.LinearIndependentReal) (li2 : B2.LinearIndependentReal) :
    (Submodule.span ℤ (Set.range B1.realCols) = Submodule.span ℤ (Set.range B2.realCols)) ↔ B1.UnimodularEquiv B2 := by
  -- This is a direct corollary of `
  apply Iff.intro
  . intro h
    exact UnimodularEquiv_of_span_eq h li1 li2
  . intro h
    exact span_eq_of_UnimodularEquiv h


end Lattice

end LatticeCrypto.Foundations.Lattice
