import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Foundations.Algorithms.LLL.Defs
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.LinearAlgebra
import LatticeCrypto.Utils.Vec

namespace LatticeCrypto.Foundations.Algorithms

namespace LLL

open scoped Real RealInnerProductSpace
open scoped Classical
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Foundations.Lattice


variable {n k : ℕ+}

noncomputable section algorithms
/-!
## Algorithm implementations

This module contains the actual LLL algorithm implementation and helper functions. Major definitions include:
 * Def `sizeReduce`: size reduction of a basis
 * Def `swapAdjacent`: swapping adjacent basis vectors
 * Def `lovaszViolation`: checking the Lovász condition
 * Def `LLLStep`: one iteration of the LLL algorithm
 * Def `LLL_Impl`: the full LLL algorithm (non-terminating version)
-/

/-- Nearest integer rounding to ℤ, using the half-up convention. -/
noncomputable def roundZ (x : ℝ) : ℤ :=
  Int.floor (x + (1 / 2 : ℝ))

/-- Helper: The property that |x - round(x)| ≤ 1/2 for the rounding function. -/
lemma roundZ_abs_sub_le (x : ℝ) : |x - (roundZ x : ℝ)| ≤ 1 / 2 := by
  unfold roundZ
  -- roundZ x = floor(x + 1/2)
  -- Need to show: |x - floor(x + 1/2)| ≤ 1/2
  -- This is a standard property of nearest-integer rounding
  exact abs_le.mpr ⟨ by linarith [ Int.floor_le ( x + 1 / 2 ) ], by linarith [ Int.lt_floor_add_one ( x + 1 / 2 ) ] ⟩

lemma roundZ_eq_zero_of_mem_Icc_Iio (x : ℝ) (hx₁ : -(1 / 2 : ℝ) ≤ x) (hx₂ : x < (1 / 2 : ℝ)) :
    roundZ x = 0 := by
  unfold roundZ
  rw [Int.floor_eq_iff]
  constructor <;> nlinarith


noncomputable section size_reduction
/-!
### SizeReduce

The size reduction algorithm ensures that |μ[i,j]| ≤ 1/2 for all j < i.
For each basis vector b_i, we subtract integer multiples of previous basis
vectors b_j (j < i) to reduce the Gram-Schmidt coefficients.

Algorithm (from Peikert Lecture 3):
  for i = 0 to k-1:
    for j = i-1 down to 0:  // Note: reverse order is essential!
      b_i := b_i - round(μ[i,j]) * b_j
-/


noncomputable section size_reduction_spec
/-!
### Matrix-based Specification of size reduction

Size reduction can be viewed as an elementary column operation on the basis matrix:
multiply the basis by an upper triangular unimodular matrix on the right.

For a size reduction step B' = sizeReduceStep B BStar i j where j < i:
- B'_t = B_t for t ≠ i
- B'_i = B_i - c • B_j where c = round(μ[i,j])

This corresponds to right-multiplication by matrix U where:
- U is upper triangular (since j < i)
- U has 1's on the diagonal
- U has -c at position (j, i)
- det(U) = 1 (unimodular)

Since multiplying by an invertible matrix preserves linear independence, this formulation
makes the proof of `sizeReduceStep_preserve_li` much cleaner than using `Function.update` directly.
-/

/--
The unimodular matrix for a size reduction step which acts on one column of the basis matrix B.
This is an upper triangular matrix with 1's on the diagonal and -c at position (j, i) where j < i.
Multiplying the basis matrix by this on the right performs the size reduction step.
-/
noncomputable def reductionMatrixZ
  (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) (i j : Fin k) :
  Matrix (Fin k) (Fin k) ℤ :=
  let coeff := projCoeff (piToEuc (B.col i)) BStar j
  let c := roundZ coeff
  -- Identity matrix with one off-diagonal entry
  fun r c' => if r = c' then 1 else if r = j ∧ c' = i then -c else 0


/-- The size reduction step matrix is upper triangular. -/
lemma reductionMatrixZ_upper_triangular (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i) :
    ∀ r c', r > c' → reductionMatrixZ B BStar i j r c' = 0 := by
  intro r c' hrc
  unfold reductionMatrixZ
  split_ifs with h1 h2
  · omega  -- r = c' but r > c' is contradiction
  · omega  -- r = j, c' = i, but j < i and r > c' implies contradiction
  · rfl

/-- The determinant of the size reduction step matrix is 1. -/
lemma reductionMatrixZ_det_one (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i) :
    (reductionMatrixZ B BStar i j).det = 1 := by
  -- The matrix is upper triangular with 1's on the diagonal, so det = product of diagonal = 1
  have h_diag : ∀ t : Fin k, reductionMatrixZ B BStar i j t t = 1 := by
    intro t
    unfold reductionMatrixZ
    simp
  -- For upper triangular matrices, det = product of diagonal entries
  convert Matrix.det_of_upperTriangular ( show ∀ t u, t > u → reductionMatrixZ B BStar i j t u = 0 from ?_ ) using 1;
  · aesop;
  · exact fun t u a => reductionMatrixZ_upper_triangular B BStar i j hij t u a

/-- The reduction matrix is unimodular (has unit determinant over ℤ) -/
lemma reductionMatrixZ_isUnit_det
  (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i) :
  IsUnit (reductionMatrixZ B BStar i j).det := by
  rw [reductionMatrixZ_det_one B BStar i j hij]
  exact isUnit_one

/-- The reduction matrix as a unimodular matrix -/
noncomputable def reductionMatrixU
  (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i) :
  UnimodularMatrix k :=
  Matrix.GeneralLinearGroup.mk''
    (reductionMatrixZ B BStar i j)
    (reductionMatrixZ_isUnit_det B BStar i j hij)

/-- The real version is just the ℤ version mapped to ℝ -/
abbrev reductionMatrix (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) (i j : Fin k) :
  Matrix (Fin k) (Fin k) ℝ :=
  (reductionMatrixZ B BStar i j).map (Int.castRingHom ℝ)

/-- The unimodular matrix's real representation is the reductionMatrix -/
@[simp]
lemma reductionMatrixU_real
  (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i) :
  (reductionMatrixU B BStar i j hij).real = reductionMatrix B BStar i j := by
  unfold reductionMatrixU UnimodularMatrix.real reductionMatrix
  simp


/-- Size reduction step expressed as matrix multiplication. -/
noncomputable def sizeReduceStepSpec
  (B : Matrix (Fin n) (Fin k) ℝ)
  (BStar : Fin k → 𝓔 n) (i j : Fin k) : Matrix (Fin n) (Fin k) ℝ :=
  B * (reductionMatrix B BStar i j)

/-- Size reduce b_i against all b_j for j < i using fixed GS decomposition.
This updates the basis by replacing b_i with its size-reduced version. -/
noncomputable def sizeReduceVectorSpec (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) (i : Fin k) : Matrix (Fin n) (Fin k) ℝ :=
  (List.finRange i.val).reverse.foldl
    (fun acc (j : Fin i.val) =>
      have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
      sizeReduceStepSpec acc BStar i ⟨j.val, hj⟩)
    B

/-- Matrix mul version of `sizeReduceBasis`. -/
noncomputable def sizeReduceBasisSpec (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) : Matrix (Fin n) (Fin k) ℝ :=
  (List.finRange k.val).foldl (fun acc (i : Fin k.val) =>
    sizeReduceVectorSpec acc BStar ⟨i.val, i.isLt⟩) B


/-- The `sizeReduceVectorSpec` is an unimodular transform. -/
theorem sizeReduceVectorSpec_eq_matrix_mul (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) (i : Fin k) :
  let RM := sizeReduceVectorSpec B BStar i
  ∃ U : UnimodularMatrix k, RM = B * U.real := by
  classical
  -- Prove a more general statement for any list
  have h_fold : ∀ (l : List (Fin i.val)) (B0 : Matrix (Fin n) (Fin k) ℝ),
      ∃ U : UnimodularMatrix k,
        (List.foldl
          (fun acc (j : Fin i.val) =>
            have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
            sizeReduceStepSpec acc BStar i ⟨j.val, hj⟩)
          B0 l) = B0 * U.real := by
    intro l
    induction l with
    | nil =>
        intro B0
        refine ⟨1, ?_⟩
        simp
    | cons j l ih =>
        intro B0
        have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
        have hij : (⟨j.val, hj⟩ : Fin k) < i := by
          exact j.isLt
        -- Unimodular matrix for this step
        have h_step : sizeReduceStepSpec B0 BStar i ⟨j.val, hj⟩
            = B0 * (reductionMatrixU B0 BStar i ⟨j.val, hj⟩ hij).real := by
          simp [sizeReduceStepSpec, reductionMatrixU_real]
        -- Induction on the remainder
        obtain ⟨U2, hU2⟩ := ih (sizeReduceStepSpec B0 BStar i ⟨j.val, hj⟩)
        have hU2' :
            (List.foldl
              (fun acc (j : Fin i.val) =>
                have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
                sizeReduceStepSpec acc BStar i ⟨j.val, hj⟩)
              (sizeReduceStepSpec B0 BStar i ⟨j.val, hj⟩) l)
              = (B0 * (reductionMatrixU B0 BStar i ⟨j.val, hj⟩ hij).real) * U2.real := by
          simpa [h_step] using hU2
        refine ⟨(reductionMatrixU B0 BStar i ⟨j.val, hj⟩ hij) * U2, ?_⟩
        calc
          (List.foldl
              (fun acc (j : Fin i.val) =>
                have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
                sizeReduceStepSpec acc BStar i ⟨j.val, hj⟩)
              B0 (j :: l))
              = (B0 * (reductionMatrixU B0 BStar i ⟨j.val, hj⟩ hij).real) * U2.real := by
                  simpa using hU2'
          _ = B0 * ((reductionMatrixU B0 BStar i ⟨j.val, hj⟩ hij).real * U2.real) := by
                  simp [Matrix.mul_assoc]
          _ = B0 * ((reductionMatrixU B0 BStar i ⟨j.val, hj⟩ hij * U2).real) := by
                  simp [UnimodularMatrix.real_mul]
  -- Apply to the actual list
  simpa [sizeReduceVectorSpec] using h_fold (List.finRange i.val).reverse B

/-- The `sizeReduceBasisSpec` is an unimodular transform. -/
theorem sizeReduceBasisSpec_eq_matrix_mul (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) :
  let RM := sizeReduceBasisSpec B BStar
  ∃ U : UnimodularMatrix k, RM = B * U.real := by
  classical
  -- Prove a more general statement for any list
  have h_fold : ∀ (l : List (Fin k.val)) (B0 : Matrix (Fin n) (Fin k) ℝ),
      ∃ U : UnimodularMatrix k,
        (List.foldl
          (fun acc (i : Fin k.val) =>
            sizeReduceVectorSpec acc BStar ⟨i.val, i.isLt⟩)
          B0 l) = B0 * U.real := by
    intro l
    induction l with
    | nil =>
        intro B0
        refine ⟨1, ?_⟩
        simp
    | cons i l ih =>
        intro B0
        -- Unimodular matrix for this step (using the previous theorem)
        obtain ⟨U1, hU1⟩ := sizeReduceVectorSpec_eq_matrix_mul B0 BStar ⟨i.val, i.isLt⟩
        -- Induction on the remainder
        obtain ⟨U2, hU2⟩ := ih (sizeReduceVectorSpec B0 BStar ⟨i.val, i.isLt⟩)
        let U1R : Matrix (Fin k) (Fin k) ℝ := U1.real
        let U2R : Matrix (Fin k) (Fin k) ℝ := U2.real
        -- Rewrite the step using U1
        have h_step : sizeReduceVectorSpec B0 BStar ⟨i.val, i.isLt⟩ = B0 * U1R := hU1
        have hU2' :
            (List.foldl
              (fun acc (i : Fin k.val) =>
                sizeReduceVectorSpec acc BStar ⟨i.val, i.isLt⟩)
              (sizeReduceVectorSpec B0 BStar ⟨i.val, i.isLt⟩) l)
              = (B0 * U1R) * U2R := by
          simpa [h_step] using hU2
        refine ⟨U1 * U2, ?_⟩
        -- Combine the two unimodular matrices
        calc
          (List.foldl
              (fun acc (i : Fin k.val) =>
                sizeReduceVectorSpec acc BStar ⟨i.val, i.isLt⟩)
              B0 (i :: l))
              = (B0 * U1R) * U2R := by simpa using hU2'
          _ = B0 * (U1R * U2R) := by simp [Matrix.mul_assoc]
          _ = B0 * (U1 * U2).real := by simp [U1R, U2R, UnimodularMatrix.real_mul]
  -- Apply to the actual list
  simpa [sizeReduceBasisSpec] using h_fold (List.finRange k.val) B

end size_reduction_spec

noncomputable section size_reduction_impl
/-!
  ### The operational definition of size reduction
-/
/--
  Helper : Reduce a vector v by subtracting round(μ) * B_j, where μ is the projection length of v over BStar_j.
  This is the core operation used in both size reduction and Babai's algorithm.
-/
noncomputable def reduceAt (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) (v : 𝓔 n) (j : Fin k) : 𝓔 n :=
  let coeff := ⟪v, BStar j⟫ / ⟪BStar j, BStar j⟫
  v - (roundZ coeff : ℝ) • B j


/-- Each `reduceAt` operation reduces the coefficient of `t` at the corresponding `b*_i` direction to ≤ 1/2 ‖b*_i‖, where b*_i is the i-th Gram-Schmidt vector. This is the key property that enables size reduction.
-/
lemma abs_projGsCoeff_of_reduceAt_le_half (B : Fin k → 𝓔 n) (t : 𝓔 n) (i : Fin k) :
    let t_reduced := reduceAt B (bStarFun B) t i
    |projGsCoeff t_reduced B i| ≤ (1 / 2) := by
  classical
  intro t_reduced
  let coeff := projGsCoeff t B i
  by_cases h0 : ⟪bStarFun B i, bStarFun B i⟫ = 0
  · have : projGsCoeff t_reduced B i = 0 := by
      simp [projGsCoeff, h0]
    simp [this]
  · have h_inner : ⟪B i, bStarFun B i⟫ =
        ⟪bStarFun B i, bStarFun B i⟫ := by
      simpa using (bStarFun_inner_self (B := B) i)
    have hproj : projGsCoeff t_reduced B i = coeff - (roundZ coeff : ℝ) := by
      unfold projGsCoeff
      have hnum : ⟪t_reduced, bStarFun B i⟫ =
          ⟪t, bStarFun B i⟫ - (roundZ coeff : ℝ) * ⟪B i, bStarFun B i⟫ := by
        calc
          ⟪t_reduced, bStarFun B i⟫ =
              ⟪t - (roundZ coeff : ℝ) • B i, bStarFun B i⟫ := by
            simp [t_reduced, reduceAt, coeff]
          _ = ⟪t, bStarFun B i⟫ - ⟪(roundZ coeff : ℝ) • B i, bStarFun B i⟫ := by
            simp [inner_sub_left]
          _ = ⟪t, bStarFun B i⟫ - (roundZ coeff : ℝ) * ⟪B i, bStarFun B i⟫ := by
            simp [inner_smul_left]
      have hnum' : ⟪t_reduced, bStarFun B i⟫ =
          ⟪t, bStarFun B i⟫ - (roundZ coeff : ℝ) * ⟪bStarFun B i, bStarFun B i⟫ := by
        simpa [h_inner] using hnum
      have : (⟪t, bStarFun B i⟫ - (roundZ coeff : ℝ) * ⟪bStarFun B i, bStarFun B i⟫) /
          ⟪bStarFun B i, bStarFun B i⟫ =
          (⟪t, bStarFun B i⟫ / ⟪bStarFun B i, bStarFun B i⟫) - (roundZ coeff : ℝ) := by
        field_simp [h0]
      simpa [hnum', coeff] using this
    simpa [hproj] using roundZ_abs_sub_le coeff


/-- One application of reduceAt makes the selected GS coefficient strictly less than 1/2. -/
lemma projGsCoeff_of_reduceAt_lt_half (B : Fin k → 𝓔 n) (t : 𝓔 n) (i : Fin k) :
    let t_reduced := reduceAt B (bStarFun B) t i
    projGsCoeff t_reduced B i < (1 / 2) := by
  classical
  intro t_reduced
  let coeff := projGsCoeff t B i
  by_cases h0 : ⟪bStarFun B i, bStarFun B i⟫ = 0
  · have : projGsCoeff t_reduced B i = 0 := by
      simp [projGsCoeff, h0]
    nlinarith [this]
  · have h_inner : ⟪B i, bStarFun B i⟫ =
        ⟪bStarFun B i, bStarFun B i⟫ := by
      simpa using (bStarFun_inner_self (B := B) i)
    have hproj : projGsCoeff t_reduced B i = coeff - (roundZ coeff : ℝ) := by
      unfold projGsCoeff
      have hnum : ⟪t_reduced, bStarFun B i⟫ =
          ⟪t, bStarFun B i⟫ - (roundZ coeff : ℝ) * ⟪B i, bStarFun B i⟫ := by
        calc
          ⟪t_reduced, bStarFun B i⟫ =
              ⟪t - (roundZ coeff : ℝ) • B i, bStarFun B i⟫ := by
            simp [t_reduced, reduceAt, coeff]
          _ = ⟪t, bStarFun B i⟫ - ⟪(roundZ coeff : ℝ) • B i, bStarFun B i⟫ := by
            simp [inner_sub_left]
          _ = ⟪t, bStarFun B i⟫ - (roundZ coeff : ℝ) * ⟪B i, bStarFun B i⟫ := by
            simp [inner_smul_left]
      have hnum' : ⟪t_reduced, bStarFun B i⟫ =
          ⟪t, bStarFun B i⟫ - (roundZ coeff : ℝ) * ⟪bStarFun B i, bStarFun B i⟫ := by
        simpa [h_inner] using hnum
      have : (⟪t, bStarFun B i⟫ - (roundZ coeff : ℝ) * ⟪bStarFun B i, bStarFun B i⟫) /
          ⟪bStarFun B i, bStarFun B i⟫ =
          (⟪t, bStarFun B i⟫ / ⟪bStarFun B i, bStarFun B i⟫) - (roundZ coeff : ℝ) := by
        field_simp [h0]
      simpa [hnum', coeff] using this
    have hlt : coeff + (1 / 2 : ℝ) < (roundZ coeff : ℝ) + 1 := by
      unfold roundZ
      exact Int.lt_floor_add_one (coeff + (1 / 2 : ℝ))
    have hlt' : coeff - (roundZ coeff : ℝ) < (1 / 2 : ℝ) := by
      nlinarith [hlt]
    simpa [hproj] using hlt'


/--
  Essientiall applying `reduceAt` to the i-th basis vector of B
-/
noncomputable def sizeReduceStep (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) (i j : Fin k) : Fin k → 𝓔 n :=
  Function.update B i (reduceAt B BStar (B i) j)

/--
  Inner loop (j from i-1 to 0): Size reduce b_i against all b_j for j < i using fixed GS decomposition.
  This updates the basis by replacing b_i with its size-reduced version.
  Note its crucial that we iterate j in descreasing order when `BStar = bStarFun B`, otherwise
  the result would be incorrect.
-/
noncomputable def sizeReduceVector (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) (i : Fin k) : Fin k → 𝓔 n :=
  (List.finRange i.val).reverse.foldl
      (fun (acc : Fin k → 𝓔 n) (j : Fin i.val) =>
        have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
        sizeReduceStep acc BStar i ⟨j.val, hj⟩)
      B

/--
  Outer loop (i from 0 to k-1): Size reduce all basis vectors using fixed BStar.
  The key insight: even though we update B throughout, we always project onto the **original**
  Gram-Schmidt basis, which makes the algorithm clearer and proofs simpler.
-/
noncomputable def sizeReduceBasis (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) : Fin k → 𝓔 n :=
  (List.finRange k.val).foldl (fun acc (i : Fin k.val) =>
    sizeReduceVector acc BStar ⟨i.val, i.isLt⟩) B

end size_reduction_impl


noncomputable section size_reduction_resp_spec
/-!
  #### Equivalence of the two formulations for size reduction
-/
/--
  Equivalence: Function.update formulation equals matrix multiplication formulation.
-/
lemma sizeReduceStep_eq_sizeReduceStepSpec (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i) :
    sizeReduceStep B BStar i j = matrixToEucBasis (sizeReduceStepSpec (eucBasisToMatrix B) BStar i j) := by
  classical
  unfold sizeReduceStep sizeReduceStepSpec;
  unfold reduceAt reductionMatrix matrixToEucBasis eucBasisToMatrix; ext a; by_cases ha : a = i <;> simp +decide [ ha ] ;
  · simp +decide [ Matrix.mul_apply, reductionMatrixZ ];
    simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', mul_comm ];
    unfold projCoeff; aesop;
  · simp +decide [ Matrix.mul_apply, reductionMatrixZ ];
    rw [ Finset.sum_eq_single a ] <;> aesop

/--
  Equivalence: Function.update formulation equals matrix multiplication formulation, and this is preserved under foldl.
-/
lemma sizeReduceVector_eq_sizeReduceVectorSpec (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) (i : Fin k) :
    sizeReduceVector B BStar i = matrixToEucBasis (sizeReduceVectorSpec (eucBasisToMatrix B) BStar i) := by
  classical
  -- Prove a more general statement for any list
  have h_fold : ∀ (l : List (Fin i.val)) (B0 : Fin k → 𝓔 n),
      (List.foldl
        (fun acc (j : Fin i.val) =>
          have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
          sizeReduceStep acc BStar i ⟨j.val, hj⟩)
        B0 l)
        = matrixToEucBasis
            (List.foldl
              (fun acc (j : Fin i.val) =>
                have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
                sizeReduceStepSpec acc BStar i ⟨j.val, hj⟩)
              (eucBasisToMatrix B0) l) := by
    intro l
    induction l with
    | nil =>
        intro B0
        simp
    | cons j l ih =>
        intro B0
        have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
        have hstep := sizeReduceStep_eq_sizeReduceStepSpec B0 BStar i ⟨j.val, hj⟩ (by
          exact j.isLt)
        -- rewrite first step then use IH
        simpa [hstep] using ih (sizeReduceStep B0 BStar i ⟨j.val, hj⟩)
  -- Apply to the actual list
  simpa [sizeReduceVector, sizeReduceVectorSpec] using
    h_fold (List.finRange i.val).reverse B

/--
  Equivalence: Function.update formulation equals matrix multiplication formulation, and this is preserved under foldl.
-/
lemma sizeReduceBasis_eq_sizeReduceBasisSpec (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) :
    sizeReduceBasis B BStar = matrixToEucBasis (sizeReduceBasisSpec (eucBasisToMatrix B) BStar) := by
  classical
  -- Prove a more general statement for any list
  have h_fold : ∀ (l : List (Fin k.val)) (B0 : Fin k → 𝓔 n),
      (List.foldl
        (fun acc (i : Fin k.val) =>
          sizeReduceVector acc BStar ⟨i.val, i.isLt⟩)
        B0 l)
        = matrixToEucBasis
            (List.foldl
              (fun acc (i : Fin k.val) =>
                sizeReduceVectorSpec acc BStar ⟨i.val, i.isLt⟩)
              (eucBasisToMatrix B0) l) := by
    intro l
    induction l with
    | nil =>
        intro B0
        simp
    | cons i l ih =>
        intro B0
        have hstep := sizeReduceVector_eq_sizeReduceVectorSpec B0 BStar ⟨i.val, i.isLt⟩
        simpa [hstep] using ih (sizeReduceVector B0 BStar ⟨i.val, i.isLt⟩)
  -- Apply to the actual list
  simpa [sizeReduceBasis, sizeReduceBasisSpec] using
    h_fold (List.finRange k.val) B


/-!
  ### Properties of the size reduction step
-/

/-- Size reduction step preserves linear independence (matrix formulation). -/
lemma sizeReduceStepSpec_preserve_li (B : Matrix (Fin n) (Fin k) ℝ) (BStar : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i)
    (h_li : LinearIndependent ℝ B.col) :
    LinearIndependent ℝ (sizeReduceStepSpec B BStar i j).col := by
  -- Since the reduction matrix is unimodular, multiplying B by it preserves linear independence.
  have h_unimodular : ∃ U : Matrix (Fin k) (Fin k) ℝ, sizeReduceStepSpec B BStar i j = B * U ∧ Matrix.det U = 1 := by
    refine' ⟨ _, rfl, _ ⟩;
    convert reductionMatrixZ_det_one B BStar i j hij;
    norm_num [ Matrix.det_apply' ];
    norm_cast;
  rcases h_unimodular with ⟨ U, hU₁, hU₂ ⟩;
  rw [ Fintype.linearIndependent_iff ] at *;
  intro g hg i;
  -- Since $U$ is invertible, we can rewrite the sum as $B * (U * g) = 0$.
  have h_sum : B.mulVec (U.mulVec g) = 0 := by
    convert hg using 1;
    ext i; simp +decide [ Matrix.mulVec, dotProduct, hU₁ ] ;
    simp +decide [ Matrix.mul_apply, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  -- Since $B$ is linearly independent, we have $U.mulVec g = 0$.
  have h_Ug : U.mulVec g = 0 := by
    specialize h_li ( U.mulVec g ) ?_;
    · convert h_sum using 1;
      ext i; simp +decide [ Matrix.mulVec, dotProduct, mul_comm ] ;
    · exact funext h_li;
  exact Matrix.eq_zero_of_mulVec_eq_zero ( show U.det ≠ 0 from by aesop ) h_Ug ▸ rfl

/--
  Size reduction step preserves linear independence of the basis, regardless of what *fixed* bstar are used
  to calculate the coefficients.
-/
lemma sizeReduceStep_preserve_li (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i)
    (h_li : LinearIndependent ℝ B) :
    LinearIndependent ℝ (sizeReduceStep B BStar i j) := by
  classical
  -- Convert to matrix formulation
  have h_li_mat : LinearIndependent ℝ (eucBasisToMatrix B).col := by
    simpa [Matrix.col, eucBasisToMatrix_apply] using h_li
  have h_li_step :
      LinearIndependent ℝ
        (sizeReduceStepSpec (eucBasisToMatrix B) BStar i j).col := by
    exact sizeReduceStepSpec_preserve_li (eucBasisToMatrix B) BStar i j hij h_li_mat
  -- Use equivalence between formulations
  have h_eq := sizeReduceStep_eq_sizeReduceStepSpec B BStar i j hij
  -- rewrite the result
  simpa [h_eq] using h_li_step

/-- The inner loop of size reduction preserves linear independence -/
lemma sizeReduceVector_preserve_li (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) (i : Fin k)
    (h : LinearIndependent ℝ B) :
    LinearIndependent ℝ (sizeReduceVector B BStar i) := by
  classical
  -- Prove a more general statement for any list
  have h_fold : ∀ (l : List (Fin i.val)) (B0 : Fin k → 𝓔 n),
      LinearIndependent ℝ B0 →
        LinearIndependent ℝ
          (List.foldl
            (fun acc (j : Fin i.val) =>
              have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
              sizeReduceStep acc BStar i ⟨j.val, hj⟩)
            B0 l) := by
    intro l
    induction l with
    | nil =>
        intro B0 hB0
        simpa using hB0
    | cons j l ih =>
        intro B0 hB0
        have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
        have hij : (⟨j.val, hj⟩ : Fin k) < i := by
          exact j.isLt
        have h_step : LinearIndependent ℝ (sizeReduceStep B0 BStar i ⟨j.val, hj⟩) :=
          sizeReduceStep_preserve_li B0 BStar i ⟨j.val, hj⟩ hij hB0
        simpa using ih _ h_step
  -- Apply to the actual list
  simpa [sizeReduceVector] using h_fold (List.finRange i.val).reverse B h

/-- The outer loop of size reduction preserves linear independence -/
lemma sizeReduceBasis_preserve_li (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n)
    (h : LinearIndependent ℝ B) :
    LinearIndependent ℝ (sizeReduceBasis B BStar) := by
  classical
  -- Prove a more general statement for any list
  have h_fold : ∀ (l : List (Fin k.val)) (B0 : Fin k → 𝓔 n),
      LinearIndependent ℝ B0 →
        LinearIndependent ℝ
          (List.foldl
            (fun acc (i : Fin k.val) =>
              sizeReduceVector acc BStar ⟨i.val, i.isLt⟩)
            B0 l) := by
    intro l
    induction l with
    | nil =>
        intro B0 hB0
        simpa using hB0
    | cons i l ih =>
        intro B0 hB0
        have h_step : LinearIndependent ℝ (sizeReduceVector B0 BStar ⟨i.val, i.isLt⟩) :=
          sizeReduceVector_preserve_li B0 BStar ⟨i.val, i.isLt⟩ hB0
        simpa using ih _ h_step
  -- Apply to the actual list
  simpa [sizeReduceBasis] using h_fold (List.finRange k.val) B h


end size_reduction_resp_spec

/-- Size reduction algorithm: produces a size-reduced basis -/
noncomputable def sizeReduce (B : LatticeBasis n k) : LatticeBasis n k where
  basis := sizeReduceBasis B.basis (bStarFun B.basis)
  le_dim := B.le_dim
  li := by
    -- Size reduction preserves linear independence:
    convert sizeReduceBasis_preserve_li B.basis (bStarFun B.basis) B.li using 1

end size_reduction



/-!
  ### Swap Adjacent Vectors Specification and Implementation
-/
noncomputable section swap_adjacent

noncomputable def swappingMatrixZ (i j : Fin k) : Matrix (Fin k) (Fin k) ℤ :=
  fun r c =>
    if r = i ∧ c = j then 1
    else if r = j ∧ c = i then 1
    else if r = c ∧ r ≠ i ∧ r ≠ j then 1
    else 0

abbrev swappingMatrix (i j : Fin k) : Matrix (Fin k) (Fin k) ℝ :=
  (swappingMatrixZ i j).map (Int.castRingHom ℝ)

lemma swappingMatrixZ_det_isUnit (i j : Fin k) :
  IsUnit (swappingMatrixZ i j).det := by
  classical
  let σ : Equiv.Perm (Fin k) := Equiv.swap i j
  have h_det : (swappingMatrixZ i j).det = (Equiv.Perm.sign σ : ℤ) := by
    have h_det : Matrix.det (Matrix.of (fun r c => if r = i ∧ c = j then 1 else if r = j ∧ c = i then 1 else if r = c ∧ r ≠ i ∧ r ≠ j then 1 else 0 : Fin k → Fin k → ℤ)) = Matrix.det (Matrix.of (fun r c => if σ r = c then 1 else 0 : Fin k → Fin k → ℤ)) := by
      norm_num +zetaDelta at *;
      congr with r c ; simp +decide [ Equiv.swap_apply_def ] ; aesop;
    -- Apply the theorem that the determinant of a permutation matrix is equal to the sign of the permutation.
    have h_det_perm : ∀ (σ : Equiv.Perm (Fin k)), Matrix.det (Matrix.of (fun r c => if σ r = c then 1 else 0 : Fin k → Fin k → ℤ)) = Equiv.Perm.sign σ := by
      intro σ; rw [ Matrix.det_apply' ] ; simp +decide ;
      rw [ Finset.sum_eq_single ( σ⁻¹ ) ] <;> simp +decide [ Equiv.Perm.sign_inv ];
      intro τ hτ; rw [ Finset.prod_eq_zero_iff ] ; simp_all +decide [ Equiv.Perm.ext_iff ] ;
      exact hτ.imp fun x hx => by simpa [ Equiv.Perm.eq_inv_iff_eq ] using hx;
    convert h_det.trans ( h_det_perm σ ) using 1 -- Prove that swappingMatrixZ equals permMatrix
  rw [h_det]
  exact Units.isUnit (Equiv.Perm.sign σ)

noncomputable def swappingMatrixU (i j : Fin k) : UnimodularMatrix k :=
  Matrix.GeneralLinearGroup.mk''
    (swappingMatrixZ i j)
    (swappingMatrixZ_det_isUnit i j)

@[simp]
lemma swappingMatrixU_real (i j : Fin k) :
  (swappingMatrixU i j).real = swappingMatrix i j := by
  unfold swappingMatrixU UnimodularMatrix.real swappingMatrix
  simp

/-- Swap adjacent vectors as a matrix multiplication -/
noncomputable def swapAdjacentVectorsSpec
    (B : Matrix (Fin n) (Fin k) ℝ) (i : Fin k) (hi : i.1 + 1 < k) : Matrix (Fin n) (Fin k) ℝ :=
  B * (swappingMatrix i ⟨i.1 + 1, hi⟩)

/-- Swap adjacent vectors Implementation -/
noncomputable def swapAdjacentVectors
    (B : Fin k → 𝓔 n) (i : Fin k) (hi : i.1 + 1 < k) : Fin k → 𝓔 n :=
  let j : Fin k := ⟨i.1 + 1, hi⟩
  fun t =>
    if t = i then B j
    else if t = j then B i
    else B t

/-- The two definitions of swapAdjacentVectors are equivalent -/
theorem swapAdjacentVectors_eq_swapAdjacentVectorsSpec
    (B : Fin k → 𝓔 n) (i : Fin k) (hi : i.1 + 1 < k) :
    swapAdjacentVectors B i hi = matrixToEucBasis (swapAdjacentVectorsSpec (eucBasisToMatrix B) i hi) := by
  classical
  simp_all +decide [ swapAdjacentVectorsSpec, swapAdjacentVectors ];
  ext t; simp +decide [ LatticeCrypto.Utils.Vec.matrixToEucBasis, swappingMatrix ];
  simp +decide [ swappingMatrixZ, Matrix.mul_apply ];
  simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne', Finset.filter_and ];
  split_ifs <;> simp_all +decide [ Finset.sum_singleton, Finset.sum_empty, Finset.inter_comm ]


/-- Swap adjacent basis vectors b_i and b_{i+1} of a LatticeBasis -/
noncomputable def swapAdjacent (B : LatticeBasis n k) (i : Fin k) (hi : i.1 + 1 < k) :
    LatticeBasis n k where
  basis := swapAdjacentVectors B.basis i hi
  le_dim := B.le_dim
  li := by
    -- Swapping two vectors preserves linear independence
    unfold swapAdjacentVectors
    let j : Fin k := ⟨i.1 + 1, hi⟩

    -- Key observation: B' ∘ swap = B where swap : Fin k → Fin k swaps i and j
    have h_perm : ∃ (σ : Equiv.Perm (Fin k)),
        (fun t => if t = i then B.basis j else if t = j then B.basis i else B.basis t) = B.basis ∘ σ := by
      use Equiv.swap i j
      ext t
      simp [Equiv.swap_apply_def]
      split_ifs <;> rfl

    -- Linear independence is preserved under bijective reindexing
    obtain ⟨σ, hσ⟩ := h_perm;
    have h_perm_bijective : Function.Bijective σ := by
      -- Since σ is a permutation, it is bijective by definition.
      apply Equiv.bijective;
    convert B.li.comp σ h_perm_bijective.injective using 1

/-
Swapping adjacent vectors is equivalent to multiplying by the swapping unimodular matrix.
-/
theorem swapAdjacent_eq_mul_unimodular (B : LatticeBasis n k) (i : Fin k) (hi : i.1 + 1 < k) :
    swapAdjacent B i hi = B ◾ (swappingMatrixU i ⟨i.1 + 1, hi⟩) := by
      unfold swapAdjacent
      ext t
      simp [swapAdjacentVectors_eq_swapAdjacentVectorsSpec];
      exact rfl



end swap_adjacent



/-!
### LLL
-/
noncomputable section lll_spec

noncomputable def lovaszViolationAt (B : LatticeBasis n k) (δ : ℝ) (i : Fin k) : Prop :=
  ∃ hi : i.1 + 1 < k,
    δ * ‖projTrailingSubspace B.basis i (B.basis i)‖ ^ 2 >
      ‖projTrailingSubspace B.basis i (B.basis ⟨i.1 + 1, hi⟩)‖ ^ 2

noncomputable def lovaszViolation (B : LatticeBasis n k) (δ : ℝ) : Prop :=
  ∃ i : Fin k, lovaszViolationAt B δ i

noncomputable def firstLovaszViolation (B : LatticeBasis n k) (δ : ℝ) :
    Option { i : Fin k // lovaszViolationAt B δ i } :=
  dite (∃ i : Fin k, lovaszViolationAt B δ i)
    (fun h => some ⟨Classical.choose h, Classical.choose_spec h⟩)
    (fun _ => none)


/-- Single LLL step: size reduce, then check for Lovasz violation and swap if needed. -/
noncomputable def LLLStep (B : LatticeBasis n k) (δ : ℝ) : LatticeBasis n k := by
  classical
  let B' := sizeReduce B
  match firstLovaszViolation B' δ with
  | none => exact B'
  | some bad =>
      let i := bad.1
      let hi := Classical.choose bad.2
      exact swapAdjacent B' i hi

/-- LLL basis reduction algorithm with explicit iteration bound.
Terminates early once a basis is `LLLReduced`. -/
noncomputable def LLL_impl : ℕ → LatticeBasis n k → ℝ → LatticeBasis n k
  | 0, B, _ => B
  | numIters + 1, B, δ =>
      by
        classical
        by_cases h : LLLReduced B δ
        · exact B
        · let B' := LLLStep B δ
          exact LLL_impl numIters B' δ

end lll_spec

end algorithms

end LLL

end LatticeCrypto.Foundations.Algorithms
