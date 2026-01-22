import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Integral
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Foundations.Lattice.FundamentalDomain
import LatticeCrypto.Foundations.Lattice.SuccessiveMinima
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Nat.Log
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.LinearAlgebra
import LatticeCrypto.Utils.Vec

namespace LatticeCrypto.Foundations.Algorithms

open scoped Real RealInnerProductSpace BigOperators Matrix
open scoped Classical
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Foundations.Lattice

variable {n k : ℕ+}

namespace LLL

/-!
  Main definitions needed for describing the output of the LLL basis reduction algorithm.
  * `SizeReduced` : For a basis B, the size reduction condition |μ_ij| ≤ 1/2 for all j < i, where μ_ij are the Gram-Schmidt coefficients (projecting b_i onto b*_j).
  * `LovaszCondition` : The Lovasz condition for δ-LLL: for all i, δ * ‖b*_i‖² ≤ ‖μ_{i+1,i} * b*_i + b*_{i+1}‖².
  * `LLLReduced` : A basis is δ-LLL reduced if it is size-reduced and satisfies the Lovasz condition.
-/
noncomputable section defs


/-!
## Gram-Schmidt data and LLL predicates
-/

/-- Gram-Schmidt orthogonalization for a sequence of vectors. -/
noncomputable def bStarFun (B : Fin k → 𝓔 n) : Fin k → 𝓔 n :=
  fun i => InnerProductSpace.gramSchmidt ℝ B i

theorem bStarFun_orthogonal (B : Fin k → 𝓔 n) (i j : Fin k) (h : i ≠ j) :
    ⟪bStarFun B i, bStarFun B j⟫ = 0 := by
  convert InnerProductSpace.gramSchmidt_orthogonal ℝ B h using 1

/-- The signed length of projecting x to the direction of j-th component of B. -/
noncomputable abbrev projCoeff (x : 𝓔 n) (B : Fin k → 𝓔 n) (j : Fin k) : ℝ :=
  ⟪x, B j⟫ / ⟪B j, B j⟫

/-- Projection of x onto the j-th Gram-Schmidt vector, returning the vector component.
This is the component of x in the direction of b*_j in the Gram-Schmidt orthogonal basis. -/
noncomputable abbrev projVec (x : 𝓔 n) (B : Fin k → 𝓔 n) (j : Fin k) : 𝓔 n :=
  projCoeff x B j • B j

/-- The coefficient of x with respect to the j-th Gram-Schmidt vector.
This is the scalar c such that proj_j(x) = c • b*_j. -/
noncomputable abbrev projGsCoeff (x : 𝓔 n) (B : Fin k → 𝓔 n) (j : Fin k) : ℝ :=
  ⟪x, bStarFun B j⟫ / ⟪bStarFun B j, bStarFun B j⟫

/-- Projection of x onto the j-th Gram-Schmidt vector, returning the vector component.
This is the component of x in the direction of b*_j in the Gram-Schmidt orthogonal basis. -/
noncomputable abbrev projGsVec (x : 𝓔 n) (B : Fin k → 𝓔 n) (j : Fin k) : 𝓔 n :=
  projGsCoeff x B j • bStarFun B j

/-- Projection onto the trailing subspace span(b_i*, ..., b_{k-1}*).
This subtracts the components in directions b_0*, ..., b_{i-1}*. -/
noncomputable def projTrailingSubspace (B : LatticeBasis n k) (i : Fin k) (x : 𝓔 n) : 𝓔 n :=
  x - ∑ j : Finset.Iio i, projGsVec x B.basis j

/-- For full-rank lattices, the projection equals the sum over complementary indices.
This requires n = k since we need the Gram-Schmidt vectors to span the entire space. -/
theorem projTrailingSubspace_eq (B : SquareLatticeBasis n) (i : Fin n) (x : 𝓔 n) :
    projTrailingSubspace B i x = ∑ j : Finset.Ici i, projGsVec x B.basis j := by
  unfold projTrailingSubspace projGsVec projGsCoeff
  -- Goal: x - ∑ j < i, projGsVec x B j = ∑ j ≥ i, projGsVec x B j
  -- Rewrite as: x = ∑ j < i, projGsVec x B j + ∑ j ≥ i, projGsVec x B j
  rw [sub_eq_iff_eq_add, add_comm]
  -- Key fact: For full-rank bases (n = k), Gram-Schmidt vectors form an orthogonal
  -- basis of the entire space, so any x ∈ 𝔼 n decomposes as x = ∑ j, projGsVec x B j
  have h_decomp : x = ∑ j : Fin n, projGsVec x B.basis j := by
    -- Follows from Gram-Schmidt orthogonality and completeness (n orthogonal vectors in 𝔼 n)
    have h_decomp : ∀ (x : LatticeCrypto.Utils.Vec.𝓔 n), x = ∑ i : Fin n, (⟪x, bStarFun B.basis i⟫ / ‖bStarFun B.basis i‖ ^ 2) • bStarFun B.basis i := by
      intro x
      have h_subspace : Submodule.span ℝ (Set.range (bStarFun B.basis)) = ⊤ := by
        have h_span : Submodule.span ℝ (Set.range B.basis) = ⊤ := by
          refine' Submodule.eq_top_of_finrank_eq _;
          rw [ finrank_span_eq_card ] ; aesop;
          exact B.li;
        -- Since the Gram-Schmidt process preserves the span, the span of the Gram-Schmidt vectors is the same as the span of the original basis vectors.
        have h_span_eq : Submodule.span ℝ (Set.range (InnerProductSpace.gramSchmidt ℝ B.basis)) = Submodule.span ℝ (Set.range B.basis) := by
          exact InnerProductSpace.span_gramSchmidt ℝ B.basis;
        exact h_span_eq.trans h_span
      have h_decomp : ∀ (x : LatticeCrypto.Utils.Vec.𝓔 n), x ∈ Submodule.span ℝ (Set.range (bStarFun B.basis)) → x = ∑ j : Fin n, (⟪x, bStarFun B.basis j⟫ / ‖bStarFun B.basis j‖ ^ 2) • bStarFun B.basis j := by
        intro x hx;
        have h_decomp : ∀ (v : Fin n → ℝ), ∑ i, v i • bStarFun B.basis i = ∑ i, (⟪∑ j, v j • bStarFun B.basis j, bStarFun B.basis i⟫ / ‖bStarFun B.basis i‖ ^ 2) • bStarFun B.basis i := by
          intro v
          have h_decomp : ∀ (i : Fin n), ⟪∑ j, v j • bStarFun B.basis j, bStarFun B.basis i⟫ = v i * ‖bStarFun B.basis i‖ ^ 2 := by
            intro i
            have h_inner : ∀ j, ⟪bStarFun B.basis j, bStarFun B.basis i⟫ = if j = i then ‖bStarFun B.basis i‖ ^ 2 else 0 := by
              intro j; split_ifs <;> simp_all +decide [ inner_self_eq_norm_sq_to_K ] ;
              have h_orthogonal : ∀ (i j : Fin n), i ≠ j → ⟪bStarFun B.basis i, bStarFun B.basis j⟫ = 0 := by
                intro i j hij; exact (by
                convert InnerProductSpace.gramSchmidt_orthogonal ℝ B.basis hij.symm using 1;
                exact real_inner_comm (bStarFun B.basis j) (bStarFun B.basis i));
              (expose_names; exact h_orthogonal j i h);
            rw [ sum_inner, Finset.sum_congr rfl fun j hj => by rw [ inner_smul_left, h_inner j ] ] ; aesop;
          refine' Finset.sum_congr rfl fun i _ => _;
          by_cases hi : bStarFun B.basis i = 0 <;> simp_all +decide [ div_eq_inv_mul, mul_comm ];
        rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hx;
        obtain ⟨ c, rfl ⟩ := hx;
        convert h_decomp ( c : Fin n → ℝ ) using 1;
        · simp +decide [ Finsupp.sum_fintype ];
        · simp +decide [ Finsupp.sum_fintype ];
      exact h_decomp x <| h_subspace.symm ▸ Submodule.mem_top;
    convert h_decomp x using 2;
    simp +decide [ projGsVec, projGsCoeff, real_inner_self_eq_norm_sq ]
  -- Split the sum into j < i and j ≥ i
  have h_split : ∑ j : Fin n, projGsVec x B.basis j =
      (∑ j : Finset.Iio i, projGsVec x B.basis j) +
      (∑ j : Finset.Ici i, projGsVec x B.basis j) := by
    -- Partition Fin n into {j < i} ∪ {j ≥ i}
    simp +zetaDelta at *;
    convert Finset.sum_add_sum_compl ( Finset.Iio i ) ( fun j => projGsVec x B.basis j ) using 1;
    · rw [ Finset.sum_add_sum_compl ];
    · convert Finset.sum_add_sum_compl ( Finset.Iio i ) ( fun j => projGsVec x B.basis j ) using 1;
      congr! 1;
      · conv_rhs => rw [ ← Finset.sum_attach ] ;
      · refine' Finset.sum_bij ( fun j _ => j ) _ _ _ _ <;> simp +decide
  calc x
    _ = ∑ j : Fin n, projGsVec x B.basis j := h_decomp
    _ = _ := h_split

/-- Gram-Schmidt coefficient μ[i,j] for a sequence of vectors.
 Essentially ⟪B i, bStarFun B j⟫ / ⟪bStarFun B j, bStarFun B j⟫
-/
noncomputable abbrev muFun (B : Fin k → 𝓔 n) (i j : Fin k) : ℝ :=
  projGsCoeff (B i) B j

/-- Notation for Gram-Schmidt coefficient: μ[B; i, j]
When B is a LatticeBasis, use μ[B.basis; i, j] -/
scoped notation:max "μ[" B:arg ";" i:arg "," j:arg "]" => muFun B i j



/-- Admissible LLL δ parameters. -/
def IsDelta (δ : ℝ) : Prop := (1 / 4 : ℝ) < δ ∧ δ < 1

/-- The standard LLL constant α = 1 / (δ - 1/4). -/
abbrev alpha (δ : ℝ) : ℝ := 1 / (δ - (1 / 4 : ℝ))

/-- Notation for α as an indexed constant: α[δ] -/
scoped notation:max "α[" δ "]" => alpha δ

/-- Special-case δ value used in practice. -/
abbrev δ34 : ℝ := (3 : ℝ) / 4

/-- Notation for the standard 3/4 LLL parameter -/
scoped notation "δ₃₄" => δ34

/-- α(3/4) = 2 -/
@[simp] theorem alpha_δ34 : α[δ34] = 2 := by norm_num [alpha, δ34]
/-- δ = 3/4 is admissible. -/
theorem δ34_IsDelta : IsDelta δ34 := by norm_num [IsDelta, δ34]


/-- Size reduction condition: |mu_ij| <= 1/2 for all j < i. -/
def SizeReduced (B : LatticeBasis n k) : Prop :=
  ∀ i j : Fin k, j < i → |μ[B.basis; i, j]| ≤ (1 / 2 : ℝ)


def InCenteredParallelepiped (B : LatticeBasis n k) (x : 𝓔 n) : Prop :=
  ∀ i : Fin k, projGsCoeff x B.basis i ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)


/-- Lovasz condition (δ-LLL): handy form using only Gram-Schmidt vectors. -/
def LovaszCondition (B : LatticeBasis n k) (δ : ℝ) : Prop :=
  ∀ i : Fin k, ∀ hi : i.1 + 1 < k,
    δ * ‖bStarFun B.basis i‖ ^ 2 ≤
      ‖μ[B.basis; ⟨i.1 + 1, hi⟩, i] • bStarFun B.basis i + bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2

/-- Lovasz condition (δ-LLL): equivalent form using projections. -/
def LovaszCondition' (B : LatticeBasis n k) (δ : ℝ) : Prop :=
  ∀ i : Fin k, ∀ hi : i.1 + 1 < k,
    δ * ‖projTrailingSubspace B i (B.basis i)‖ ^ 2 ≤
      ‖projTrailingSubspace B i (B.basis ⟨i.1 + 1, hi⟩)‖ ^ 2

/-- Equivalence of Lovasz conditions -/
theorem LovaszCondition_iff_LovaszCondition'
    (B : LatticeBasis n k) (δ : ℝ) :
    LovaszCondition B δ ↔ LovaszCondition' B δ := by
  unfold LovaszCondition LovaszCondition'
  constructor <;> intro h i hi
  · -- Forward direction: LovaszCondition → LovaszCondition'
    specialize h i hi
    -- Key fact: projTrailingSubspace B i (B.basis i) = bStarFun B.basis i
    have h_proj_i : projTrailingSubspace B i (B.basis i) = bStarFun B.basis i := by
      unfold projTrailingSubspace projGsVec projGsCoeff
      -- B.basis i has no component in span of b*_0, ..., b*_{i-1} by Gram-Schmidt orthogonality
      unfold bStarFun;
      rw [ eq_comm, InnerProductSpace.gramSchmidt_def ];
      rw [ ← Finset.sum_coe_sort ];
      congr! 2;
      convert Submodule.starProjection_singleton _ _ using 1;
      simp +decide [ inner_self_eq_norm_sq_to_K ];
      rw [ real_inner_comm ]
    -- Key fact: projTrailingSubspace B i (B.basis (i+1)) = μ[i+1,i] • bStar_i + bStar_{i+1}
    have h_proj_succ : projTrailingSubspace B i (B.basis ⟨i.1 + 1, hi⟩) =
        μ[B.basis; ⟨i.1 + 1, hi⟩, i] • bStarFun B.basis i + bStarFun B.basis ⟨i.1 + 1, hi⟩ := by
      unfold projTrailingSubspace projGsVec
      -- By Gram-Schmidt decomposition and orthogonality
      rw [ show ( ∑ x : { x : Fin k // x ∈ Finset.Iio i }, ( ⟪B.basis ⟨ i + 1, hi ⟩, bStarFun B.basis ( x : Fin k ) ⟫ / ⟪bStarFun B.basis ( x : Fin k ), bStarFun B.basis ( x : Fin k ) ⟫ ) • bStarFun B.basis ( x : Fin k ) ) = ∑ x ∈ Finset.Iio i, ( ⟪B.basis ⟨ i + 1, hi ⟩, bStarFun B.basis x ⟫ / ⟪bStarFun B.basis x, bStarFun B.basis x ⟫ ) • bStarFun B.basis x from ?_ ];
      · rw [ show bStarFun B.basis ⟨ i + 1, hi ⟩ = B.basis ⟨ i + 1, hi ⟩ - ∑ j ∈ Finset.Iio ⟨ i + 1, hi ⟩, ( ⟪B.basis ⟨ i + 1, hi ⟩, bStarFun B.basis j⟫ / ⟪bStarFun B.basis j, bStarFun B.basis j⟫ ) • bStarFun B.basis j from ?_ ];
        · rw [ show ( Finset.Iio ⟨ i + 1, hi ⟩ : Finset ( Fin k ) ) = Finset.Iio i ∪ { ⟨ i, by linarith ⟩ } from ?_, Finset.sum_union ] <;> norm_num;
          · unfold muFun; ring_nf;
            abel1;
          · ext ⟨ j, hj ⟩ ; simp +decide [ Nat.lt_succ_iff ];
            exact ⟨ fun h => Nat.le_trans h ( Nat.le_refl _ ), fun h => Nat.le_trans h ( Nat.le_refl _ ) ⟩;
        · convert InnerProductSpace.gramSchmidt_def ℝ B.basis _ using 1;
          congr! 2;
          rw [ Submodule.starProjection_singleton ];
          rw [ real_inner_self_eq_norm_sq ] ; rw [ real_inner_comm ] ; norm_num [ bStarFun ] ;
      · refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> aesop
    rw [h_proj_i, h_proj_succ]
    exact h
  · -- Backward direction: LovaszCondition' → LovaszCondition
    specialize h i hi
    -- Same key facts as forward direction
    have h_proj_i : projTrailingSubspace B i (B.basis i) = bStarFun B.basis i := by
      unfold projTrailingSubspace projGsVec projGsCoeff
      unfold bStarFun;
      rw [ InnerProductSpace.gramSchmidt ];
      congr! 2;
      rw [ Submodule.starProjection_singleton ];
      rw [ real_inner_self_eq_norm_sq ] ; rw [ real_inner_comm ] ; norm_num;
    have h_proj_succ : projTrailingSubspace B i (B.basis ⟨i.1 + 1, hi⟩) =
        μ[B.basis; ⟨i.1 + 1, hi⟩, i] • bStarFun B.basis i + bStarFun B.basis ⟨i.1 + 1, hi⟩ := by
      unfold projTrailingSubspace projGsVec projGsCoeff
      rw [ show bStarFun B.basis ⟨ i + 1, hi ⟩ = B.basis ⟨ i + 1, hi ⟩ - ∑ j ∈ Finset.filter ( fun j => j < ⟨ i + 1, hi ⟩ ) Finset.univ, ( ⟪B.basis ⟨ i + 1, hi ⟩, bStarFun B.basis j⟫ / ⟪bStarFun B.basis j, bStarFun B.basis j⟫ ) • bStarFun B.basis j from ?_ ];
      · rw [ show ( Finset.filter ( fun x : Fin k => x < ⟨ i + 1, hi ⟩ ) Finset.univ : Finset ( Fin k ) ) = Finset.filter ( fun x : Fin k => x < i ) Finset.univ ∪ { i } from ?_, Finset.sum_union ] <;> norm_num;
        · rw [ show ( Finset.filter ( fun x : Fin k => x < i ) Finset.univ : Finset ( Fin k ) ) = Finset.image ( fun x : { x : Fin k // x < i } => ( x : Fin k ) ) ( Finset.univ : Finset { x : Fin k // x < i } ) from ?_, Finset.sum_image ] <;> norm_num;
          · rw [ show ( Finset.Iio i ).attach = Finset.image ( fun x : { x : Fin k // x < i } => ⟨ x, by aesop ⟩ ) ( Finset.univ : Finset { x : Fin k // x < i } ) from ?_, Finset.sum_image ] <;> norm_num;
            · unfold muFun; ring_nf;
              abel1;
            · ext ⟨ x, hx ⟩ ; aesop;
          · ext; simp [Finset.mem_image];
        · ext x; simp [Finset.mem_insert, Finset.mem_filter];
          exact ⟨ fun hx => or_iff_not_imp_left.mpr fun hx' => lt_of_le_of_ne ( Nat.le_of_lt_succ hx ) hx', fun hx => hx.elim ( fun hx => hx.symm ▸ Nat.lt_succ_self _ ) fun hx => Nat.lt_succ_of_lt hx ⟩;
      · have h_projTrailingSubspace : ∀ (i : Fin k), bStarFun B.basis i = B.basis i - ∑ j ∈ Finset.Iio i, (⟪B.basis i, bStarFun B.basis j⟫ / ⟪bStarFun B.basis j, bStarFun B.basis j⟫) • bStarFun B.basis j := by
          intro i
          rw [bStarFun];
          rw [ InnerProductSpace.gramSchmidt_def ];
          congr! 2;
          rw [ Submodule.starProjection_singleton ];
          simp +decide [ inner_self_eq_norm_sq_to_K, bStarFun ];
          rw [ real_inner_comm ];
        convert h_projTrailingSubspace ⟨ i + 1, hi ⟩ using 1;
        rcongr j ; simp ( config := { decide := Bool.true } ) [ Fin.lt_iff_val_lt_val ];
        congr! 1;
        ext ⟨ j, hj ⟩ ; simp +decide [ Nat.lt_succ_iff ];
        exact ⟨ fun h => h, fun h => Nat.le_trans h ( Nat.le_refl _ ) ⟩
    rw [h_proj_i, h_proj_succ] at h
    exact h

/-- Delta-LLL reduced basis (size reduced + Lovasz). -/
def LLLReduced (B : LatticeBasis n k) (δ : ℝ) : Prop :=
  SizeReduced B ∧ LovaszCondition B δ

noncomputable def minBstarNorm (B : LatticeBasis n k) : ℝ :=
  LatticeCrypto.Utils.LinearAlgebra.minNorm (bStarFun B.basis)

noncomputable def maxBasisNorm (B : LatticeBasis n k) : ℝ :=
  LatticeCrypto.Utils.LinearAlgebra.maxNorm B.basis

noncomputable def maxBstarNorm (B : LatticeBasis n k) : ℝ :=
  LatticeCrypto.Utils.LinearAlgebra.maxNorm (bStarFun B.basis)


end defs

end LLL

end LatticeCrypto.Foundations.Algorithms
