import Mathlib.Algebra.Group.Subgroup.Defs     -- For AddSubgroup
import Mathlib.Analysis.Normed.Group.Basic      -- For NormedAddCommGroup
import Mathlib.Topology.Algebra.Group.Basic      -- For the subspace topology on AddSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.InnerProductSpace.PiL2  -- For EuclideanSpace
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Data.Matrix.Basic                -- for type synonym support
import Mathlib.Analysis.Normed.Group.Subgroup   -- For LinearIndependent.discrete_zspan
import Mathlib.LinearAlgebra.LinearIndependent.Defs  -- For LinearIndependent
import Mathlib.LinearAlgebra.Span.Defs               -- For AddSubgroup.zspan
import Mathlib.Data.Real.Basic                  -- For ℝ (Real)
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Card

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Convex

import LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Vec

open scoped ENNReal NNReal Pointwise MeasureTheory
open scoped RealInnerProductSpace
open scoped Classical
open scoped Module
open scoped FiniteDimensional


variable {n k : ℕ+}

/-!
# Utility Functions

This module provides utility functions for mathematical analysis on lattice.
Many are light wrappers around Mathlib functions.

## Main components
* `Geometry` (**This file**) - handy lemmas in Euclidean geometry
* `LinearAlgebra` - handy lemmas in Euclidean geometry
* `Algebra.Ring` - Lemmas in ring theory
* `Algebra.Module` - Lemmas in module theory
* `Algebra.Polynomial` - Lemmas in polynomial rings
-/

namespace LatticeCrypto.Utils.LinearAlgebra

noncomputable section min_norm

/-- Minimum norm among a finite family of vectors, to be the minimum norm of
assuming the index set is nonempty. -/
def minNorm
    {V : Type*} [Norm V]
    (f : Fin k → V) : ℝ :=
  Finset.min' (Finset.image (fun i => ‖f i‖) Finset.univ) (by
    rw [Finset.image_nonempty]
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp k.pos)
  )

/-- One can find an index achieving the minNorm-/
noncomputable def argminNorm
    {V : Type*} [Norm V]
    (f : Fin k → V) : Fin k :=
  let h_nonempty : (Finset.univ : Finset (Fin k)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp k.pos)
  -- Finset.exists_min_image proves there exists an index i minimizing the function
  Classical.choose (Finset.exists_min_image Finset.univ (fun i ↦ ‖f i‖) h_nonempty)

/-- The minNorm among a finite family of vectors is no more than the norm of any vector from the family. -/
lemma minNorm_le
    {V : Type*} [Norm V]
    (f : Fin k → V) (i : Fin k) :
    minNorm f ≤ ‖f i‖ := by
  unfold minNorm
  apply Finset.min'_le
  rw [Finset.mem_image]
  use i
  simp only [Finset.mem_univ, true_and]

/-- The minimum norm among a finite family of vectors is equal to the norm at the argmin of the minNorm. -/
lemma minNorm_eq_norm_argmin
    {V : Type*} [Norm V]
    (f : Fin k → V) :
    minNorm f = ‖f (argminNorm f)‖ := by
  unfold minNorm argminNorm;
  refine' le_antisymm _ _;
  · exact Finset.min'_le _ _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) );
  · have := Classical.choose_spec ( Finset.exists_min_image Finset.univ ( fun i => ‖f i‖ ) ( Finset.univ_nonempty ) );
    aesop

/-- The norm at the argmin is less than or equal to the norm of any other vector. -/
lemma norm_argmin_le
    {V : Type*} [Norm V]
    (f : Fin k → V) (i : Fin k) :
    ‖f (argminNorm f)‖ ≤ ‖f i‖ := by
  unfold argminNorm
  have h_nonempty : (Finset.univ : Finset (Fin k)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp k.pos)
  have h_min := Classical.choose_spec (Finset.exists_min_image Finset.univ (fun i ↦ ‖f i‖) h_nonempty)
  exact h_min.2 i (Finset.mem_univ i)

/-- The minimum column norm of a matrix. -/
def Matrix.minColumnNorm
    (A : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  minNorm (fun j => fun i => A i j)

def Matrix.argminColumn
    (A : Matrix (Fin n) (Fin k) ℝ) : Fin k :=
  argminNorm (fun j => fun i => A i j)

end min_norm

/-!
# Some handy results regarding linear independence
-/
noncomputable section independence

/-- Notation for n-dimensional Euclidean space over ℝ. -/
-- private abbrev 𝓔 (n : ℕ+) := EuclideanSpace ℝ (Fin n)

lemma Z_linearIndependent_if_R_linearIndependent {v : Fin k → Fin n → ℝ} (li : LinearIndependent ℝ v) : LinearIndependent ℤ v := by
  have h_int_lin_ind : ∀ (c : Fin k → ℤ), (∑ i, c i • v i = 0) → (∀ i, c i = 0) := by
    intros c hc
    have h_real : ∑ i, (c i : ℝ) • v i = 0 := by
      convert hc using 1
      congr! 2
      ext; simp
    exact fun i => by have := Fintype.linearIndependent_iff.mp li (c ·) h_real i; aesop
  rw [Fintype.linearIndependent_iff]; aesop

lemma Q_linearIndependent_if_R_linearIndependent {v : Fin k → Fin n → ℝ} (li : LinearIndependent ℝ v) : LinearIndependent ℚ v := by
  have h_int_lin_ind : ∀ (c : Fin k → ℚ), (∑ i, c i • v i = 0) → (∀ i, c i = 0) := by
    intros c hc
    have h_real : ∑ i, (c i : ℝ) • v i = 0 := by
      convert hc using 1
    exact fun i => by have := Fintype.linearIndependent_iff.mp li (c ·) h_real i; aesop
  rw [Fintype.linearIndependent_iff]; aesop

/-!
## Discrete Z-Span Theorem
-/

/-- Proof that any linearly independent set of k (k ≤ n) vectors over ℝⁿ has a discrete Z-span -/
theorem discrete_zspan {v : Fin k → 𝓔 n} (li : LinearIndependent ℝ v) :
    DiscreteTopology (Submodule.span ℤ (Set.range v) : Submodule ℤ (Fin n → ℝ)) := by
  -- 1. Extend v to a basis v' of ℝⁿ
  have hli : LinearIndepOn ℝ id (Set.range v) := LinearIndependent.linearIndepOn_id li
  let v' := Module.Basis.extend hli

  -- 2. Use the previous lemma to show that the z-span of v' is discrete
  have discrete_v' : DiscreteTopology ↥(Submodule.span ℤ (Set.range v')) := inferInstance

  -- 3. Show that the z-span of v is a subset of the z-span of v'
  have h_subset : (Submodule.span ℤ (Set.range v)) ≤ (Submodule.span ℤ (Set.range v')) := by
    apply Submodule.span_mono
    intro x hx
    obtain ⟨i, hi⟩ := hx
    use ⟨v i, by
      apply hli.subset_extend
      use i⟩
    generalize_proofs at *
    simp [v', hi]

  -- 4. Conclude that the z-span of v is discrete
  exact DiscreteTopology.of_subset discrete_v' h_subset

theorem exists_finset_eq_card {α} {n : ℕ} (h : n ≤ Cardinal.mk α) :
    ∃ s : Finset α, n = s.card := by
  obtain hα|hα := finite_or_infinite α
  · let hα := Fintype.ofFinite α
    obtain ⟨t, -, rfl⟩ := @Finset.exists_subset_card_eq α .univ n <| by simpa using h
    exact ⟨t, rfl⟩
  · obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
    exact ⟨s, hs.symm⟩

/- This is a copy of theorem from Mathlib v2025-11-27 -/
theorem le_rank_iff_exists_finset {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M] [Nontrivial R] {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ s : Finset M, s.card = n ∧ LinearIndepOn R id (s : Set M) where
  mp le := by
    contrapose! le
    obtain _ | n := n; · simp at le
    rw [Module.rank, Cardinal.nat_succ, Order.lt_succ_iff, ciSup_le_iff (Cardinal.bddAbove_range _)]
    intro s
    contrapose! le
    rw [← Order.succ_le_iff, ← Cardinal.nat_succ] at le
    have ⟨t, ht⟩ := exists_finset_eq_card le
    exact ⟨t.map (.subtype _), by simpa using ht.symm, s.2.mono <| by simp⟩
  mpr := fun ⟨s, card_s, ind_s⟩ ↦ ind_s.cardinal_le_rank'.trans_eq' <| by simp [card_s]

/- This is a copy of theorem from Mathlib v2025-11-27 -/
theorem le_rank_iff {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M] [Nontrivial R] {n : ℕ} : n ≤ Module.rank R M ↔ ∃ v : Fin n → M, LinearIndependent R v := by
  refine le_rank_iff_exists_finset.trans ⟨fun ⟨s, s_card, s_ind⟩ ↦ ?_, fun ⟨v, v_ind⟩ ↦ ?_⟩
  · exact ⟨_, s_ind.comp _ (s.equivFinOfCardEq s_card).symm.injective⟩
  · refine ⟨.map ⟨_, v_ind.injective⟩ .univ, by simp, ?_⟩
    simpa using (linearIndepOn_id_range_iff v_ind.injective).mpr v_ind

lemma rank_span_ge_iff_subset {V : Type*} [AddCommGroup V] [Module ℝ V] (s : Set V) (k : ℕ) :
    k ≤ Module.rank ℝ (Submodule.span ℝ s) ↔
    ∃ t : Finset V, t.card = k ∧ ↑t ⊆ s ∧ LinearIndependent ℝ (fun x : t => (x : V)) := by
      bound;
      · -- By definition of rank, there exists a linearly independent subset of s with cardinality equal to the rank.
        obtain ⟨t, ht⟩ : ∃ t : Set V, t ⊆ s ∧ LinearIndependent ℝ (fun x : t => (x : V)) ∧ Cardinal.mk t = Module.rank ℝ (Submodule.span ℝ s) := by
          have := exists_linearIndependent ℝ s;
          obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := this; use t; aesop;
          rw [ ← ht₂, rank_span_set ht₃ ];
        -- Since $k \leq \text{rank}(\text{span}(s))$, there exists a subset $t' \subseteq t$ with $|t'| = k$.
        obtain ⟨t', ht'⟩ : ∃ t' : Set V, t' ⊆ t ∧ Cardinal.mk t' = k := by
          have := ht.2.2 ▸ a;
          exact Cardinal.le_mk_iff_exists_subset.mp this;
        -- Since $t'$ is a subset of $t$ with cardinality $k$, we can convert it to a finset.
        obtain ⟨t_fin, ht_fin⟩ : ∃ t_fin : Finset V, t_fin = t' ∧ t_fin.card = k := by
          have h_finite : Set.Finite t' := by
            exact Set.finite_coe_iff.mp ( Cardinal.lt_aleph0_iff_finite.mp ( ht'.2.symm ▸ Cardinal.nat_lt_aleph0 k ) );
          have := h_finite.exists_finset_coe; aesop;
        refine' ⟨ t_fin, ht_fin.2, _, _ ⟩ <;> aesop;
        · exact Set.Subset.trans left_1 left;
        · convert left_3.comp _ _;
          rotate_left;
          exacts [ fun x => ⟨ x.1, left_1 x.2 ⟩, fun x y h => by simpa [ Subtype.ext_iff ] using h, rfl ];
      · -- Since $w$ is a subset of $s$, the span of $w$ is a subspace of the span of $s$.
        have h_subspace : Submodule.span ℝ w ≤ Submodule.span ℝ s := by
          exact Submodule.span_mono left_1;
        refine' le_trans _ ( Submodule.rank_mono h_subspace );
        rw [ rank_span_set ] ; aesop;
        exact right

end independence

noncomputable section gram_schmidt

open scoped InnerProductSpace
open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [LocallyFiniteOrder n] [OrderBot n] [WellFoundedLT n]
variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable def toE (v : n → 𝕜) : EuclideanSpace 𝕜 n := WithLp.equiv 2 (n → 𝕜) v
noncomputable def fromE (v : EuclideanSpace 𝕜 n) : n → 𝕜 := WithLp.equiv 2 (n → 𝕜) v

set_option linter.unusedSectionVars false in
@[simp] lemma toE_apply (v : n → 𝕜) (i : n) :
  (fromE (toE v)) i = v i := by simp [toE, fromE]

set_option linter.unusedSectionVars false in
@[simp] lemma fromE_apply (x : EuclideanSpace 𝕜 n) :
  toE (fromE x) = x := by bound


noncomputable def gramSchmidtMatrix (M : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  fun i => fun j =>
    (fromE
      (InnerProductSpace.gramSchmidt 𝕜 (fun v => toE (M.col v)) j) -- jth gs vector
      i)

set_option linter.unusedSectionVars false in
theorem gramSchmidtMatrix_col (M : Matrix n n 𝕜) (j : n) :
    (gramSchmidtMatrix M).col j =
      fromE (InnerProductSpace.gramSchmidt 𝕜 (fun v => toE (M.col v)) j) := by
  ext i
  simp [gramSchmidtMatrix, Matrix.col]

noncomputable section AristotleLemmas

/-
If matrix B is obtained from matrix A such that the difference of their j-th columns lies in the span of the previous columns of A, then their determinants are equal.
-/
lemma det_eq_of_forall_col_diff_span
    {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [LocallyFiniteOrder n] [OrderBot n] [WellFoundedLT n]
    {𝕜 : Type*} [Field 𝕜]
    (A B : Matrix n n 𝕜)
    (h : ∀ j, A.col j - B.col j ∈ Submodule.span 𝕜 (Set.image A.col (Set.Iio j))) :
    A.det = B.det := by
      -- By definition of $B$, we know that $B = A \cdot T$ for some upper triangular matrix $T$ with $1$ on the diagonal.
      obtain ⟨T, hT⟩ : ∃ T : Matrix n n 𝕜, B = A * T ∧ ∀ i, T i i = 1 ∧ ∀ j, j < i → T i j = 0 := by
        -- Let $w_j = A.col j - B.col j$. By hypothesis, $w_j \in \text{span}(\{A_i\}_{i < j})$.
        have hw : ∀ j : n, ∃ w : n → 𝕜, B.col j = A.col j - ∑ i ∈ Finset.filter (fun i => i < j) (Finset.univ : Finset n), w i • A.col i := by
          intro j
          obtain ⟨w, hw⟩ : ∃ w : n → 𝕜, A.col j - B.col j = ∑ i ∈ Finset.filter (fun i => i < j) (Finset.univ : Finset n), w i • A.col i := by
            have := h j;
            rw [ Finsupp.mem_span_image_iff_linearCombination ] at this;
            obtain ⟨ l, hl₁, hl₂ ⟩ := this; use fun i => l i; simp_all +decide [ Finsupp.linearCombination_apply, Finsupp.sum_fintype ] ;
            rw [ ← hl₂, Finset.sum_filter_of_ne ] ; aesop;
          exact ⟨ w, by rw [ ← hw, sub_sub_cancel ] ⟩;
        choose w hw using hw;
        refine' ⟨ fun i j => if i = j then 1 else if i < j then -w j i else 0, _, _ ⟩ <;> simp_all +decide [ ← Matrix.ext_iff ];
        · intro i j; specialize hw j; replace hw := congr_fun hw i; simp_all +decide [ Matrix.mul_apply, Finset.sum_ite ] ;
          simp +decide [ Finset.filter_eq', Finset.filter_ne', mul_comm ];
          rw [ Finset.filter_erase ] ; aesop;
          ring;
        · exact fun i j hij => by rw [ if_neg hij.ne', if_neg hij.not_gt ] ;
      -- Since $T$ is upper triangular with $1$ on the diagonal, its determinant is $1$.
      have hT_det : Matrix.det T = 1 := by
        rw [ Matrix.det_of_upperTriangular ] <;> aesop;
        intro i j hij; aesop;
      aesop

/-
If a matrix has orthogonal columns, the absolute value of its determinant is the product of the norms of its columns.
-/
set_option linter.unusedSectionVars false in
lemma det_norm_eq_prod_norm_of_orthogonal_cols (A : Matrix n n 𝕜)
    (h : Pairwise (fun i j => ⟪toE (A.col i), toE (A.col j)⟫_𝕜 = 0)) :
    ‖A.det‖ = ∏ i, ‖toE (A.col i)‖ := by
      have h_sq : ‖Matrix.det A‖^2 = ∏ i, ‖toE (A.col i)‖^2 := by
        have h_det_sq : ‖Matrix.det A‖^2 = Matrix.det (Matrix.conjTranspose A * A) := by
          simp ( config := { decide := Bool.true } ) [ Matrix.det_mul, Matrix.det_conjTranspose ];
          exact Eq.symm (RCLike.conj_mul A.det)
        have h_diag : Matrix.conjTranspose A * A = Matrix.diagonal (fun i => ⟪toE (A.col i), toE (A.col i)⟫_𝕜) := by
          ext i j; by_cases hij : i = j <;> simp_all +decide [ Matrix.mul_apply, Pairwise ] ;
          · unfold LatticeCrypto.Utils.LinearAlgebra.toE; simp +decide ;
            simp +decide [ mul_comm, inner, WithLp.ofLp ];
          · convert h hij using 1 ; simp +decide [ toE ];
            simp +decide [ WithLp.ofLp ];
            exact Finset.sum_congr rfl fun _ _ => by simp ( config := { decide := Bool.true } ) [ mul_comm ] ;
        simp_all +decide [ inner_self_eq_norm_sq_to_K ];
        norm_cast at *;
      rw [ ← sq_eq_sq₀ ( norm_nonneg _ ) ( Finset.prod_nonneg fun _ _ => norm_nonneg _ ), h_sq, Finset.prod_pow ]


end AristotleLemmas


/--
The determinant of a matrix is equal to the determinant of its Gram-Schmidt matrix.
-/
theorem gramSchmidt_matrix_det (M : Matrix n n 𝕜) :
    M.det = (gramSchmidtMatrix M).det := by
  -- Let's denote the matrix `M` as `M`.
  set M' : Matrix n n 𝕜 := gramSchmidtMatrix M;
  set M' : Matrix n n 𝕜 := gramSchmidtMatrix M;
  symm;
  apply det_eq_of_forall_col_diff_span;
  intro j
  have h_proj : (InnerProductSpace.gramSchmidt 𝕜 (fun k => toE (M.col k)) j) - (toE (M.col j)) ∈ Submodule.span 𝕜 (Set.image (fun k => InnerProductSpace.gramSchmidt 𝕜 (fun k => toE (M.col k)) k) (Set.Iio j)) := by
    rw [ InnerProductSpace.gramSchmidt_def ];
    rw [ sub_sub_cancel_left ];
    refine' Submodule.neg_mem _ ( Submodule.sum_mem _ fun i hi => _ );
    refine' Submodule.span_mono _ _;
    exact { InnerProductSpace.gramSchmidt 𝕜 ( fun k => LatticeCrypto.Utils.LinearAlgebra.toE ( M.col k ) ) i };
    · aesop;
    · exact Submodule.coe_mem _;
  convert h_proj using 1

/-
The absolute value of the determinant of `M` is the product of the norms of its Gram-Schmidt vectors.
-/
theorem gramSchmidt_matrix_det_abs (M : Matrix n n 𝕜) :
    ‖M.det‖ = ∏ i, ‖InnerProductSpace.gramSchmidt 𝕜 (fun j => toE (M.col j)) i‖ := by
  have := gramSchmidt_matrix_det M;
  rw [ this, det_norm_eq_prod_norm_of_orthogonal_cols ];
  · exact Finset.prod_congr rfl fun _ _ => rfl;
  · intro i j hij; have := InnerProductSpace.gramSchmidt_orthogonal 𝕜 ( fun v => toE ( M.col v ) ) hij; aesop;

/-- Instantiate the above theorems in EuclideanSpace -/
theorem euc_gramSchmidt_matrix_det {n : ℕ+} (M : Matrix (Fin n) (Fin n) ℝ) :
    M.det = (Matrix.of
              (fun i => fun j =>
                  (eucToPi
                    (InnerProductSpace.gramSchmidt ℝ (fun v => piToEuc (M.col v)) j)
                    i))
            ).det := by
  convert gramSchmidt_matrix_det _ using 2;
  rotate_left;
  exact Fin.instLinearOrder;
  all_goals try infer_instance;
  ext i j; simp +decide [ LatticeCrypto.Utils.LinearAlgebra.gramSchmidtMatrix ];
  congr!;
  exact Subsingleton.elim _ _

/-- Instantiate the above theorems in EuclideanSpace -/
theorem euc_gramSchmidt_matrix_det_abs {n : ℕ+} (M : Matrix (Fin n) (Fin n) ℝ) :
    |M.det| = ∏ i, ‖InnerProductSpace.gramSchmidt ℝ
                      (fun j => piToEuc (M.col j)) i‖ := by
  convert ( gramSchmidt_matrix_det_abs ?_ );
  all_goals first | infer_instance | norm_cast;
  cases n using PNat.recOn <;> trivial

noncomputable def Basis_of_gramSchmidtOrthonormalBasis {n : ℕ+} (b : Module.Basis (Fin n) ℝ (𝓔 n)) : Module.Basis (Fin n) ℝ (𝓔 n) := by
  have h_eq : Module.finrank ℝ (𝓔 n) = Fintype.card (Fin n) := by bound
  exact (InnerProductSpace.gramSchmidtOrthonormalBasis h_eq b).toBasis


end gram_schmidt

end LatticeCrypto.Utils.LinearAlgebra
