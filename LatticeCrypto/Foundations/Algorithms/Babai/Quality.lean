import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Nat.Log

import LatticeCrypto.Foundations.Lattice.Integral
import LatticeCrypto.Foundations.Lattice.SuccessiveMinima
import LatticeCrypto.Foundations.Algorithms.LLL.Quality
import LatticeCrypto.Foundations.Algorithms.Babai.Algorithm
import LatticeCrypto.Foundations.Algorithms.Babai.Correctness
import LatticeCrypto.Foundations.Hardness.Defs
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.LinearAlgebra
import LatticeCrypto.Utils.Vec


namespace LatticeCrypto.Foundations.Algorithms

namespace Babai

open scoped Real RealInnerProductSpace
open scoped Classical
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Foundations.Lattice
open LatticeCrypto.Foundations.Lattice.Integral
open LatticeCrypto.Foundations.Algorithms.LLL
open LatticeCrypto.Foundations.Hardness

variable {n k : ℕ+}

noncomputable section quality_analysis

/-!
## Quality Analysis

Babai's algorithm provides a 2^(k/2) approximation to CVP when using an LLL-reduced basis.
-/

/-- After `babaiReduce`, all Gram-Schmidt coefficients are bounded by 1/2 in absolute value. -/
lemma abs_projGsCoeff_of_babaiReduce_le_half (B : Fin k → 𝓔 n) (t : 𝓔 n) :
    ∀ i : Fin k, |projGsCoeff (babaiReduce t B) B i| ≤ 1 / 2 := by
  exact lift_projGsCoeff_property_from_reduceAt_to_babaiReduce
    (B := B) (t := t) (P := fun x => |x| ≤ 1 / 2) (by
      intro u i
      simpa using abs_projGsCoeff_of_reduceAt_le_half (B := B) (t := u) (i := i))

/-- After Babai reduction, every GS coefficient is strictly less than 1/2. -/
lemma projGsCoeff_of_babaiReduce_lt_half (B : Fin k → 𝓔 n) (t : 𝓔 n) :
    ∀ i : Fin k, projGsCoeff (babaiReduce t B) B i < 1 / 2 := by
  exact lift_projGsCoeff_property_from_reduceAt_to_babaiReduce
    (B := B) (t := t) (P := fun x => x < 1 / 2) (by
      intro u i
      simpa using projGsCoeff_of_reduceAt_lt_half (B := B) (t := u) (i := i))

/-- Upper bound on the error vector in terms of the GS norm of the basis.

The error ‖t - v‖ where v = babaiRound(t, B) can be bounded by:
  ‖t - v‖^2 ≤ (1 / 2) • ∑_j ‖b*_j‖^2

This is because each rounded coefficient contributes at most 1/2 • ‖b*_j‖ to the error.
-/
theorem babai_error_bound_by_sum_bstar_norm (B : LatticeBasis n k) (t : 𝓔 n)
    (ht: t ∈ Submodule.span ℝ (Set.range B.basis)) :
    ‖t - babaiRound t B.basis‖^2 ≤ (1 / 4) * ∑ i : Fin k, ‖bStarFun B.basis i‖^2 := by
  classical
  -- Set the reduced error vector.
  let BStar := bStarFun B.basis
  let tReduced := babaiReduce t B.basis
  have htReduced : t - babaiRound t B.basis = tReduced := by
    simp [babaiRound, babaiReduce, tReduced, sub_eq_add_neg, add_comm]

  -- Bound each GS coefficient of the final reduced vector by 1/2.
  have h_coeff : ∀ i : Fin k, |projGsCoeff tReduced B.basis i| ≤ 1 / 2 := by
    simpa [tReduced] using (abs_projGsCoeff_of_babaiReduce_le_half (B := B.basis) (t := t))

  -- Express the error vector as a sum of orthogonal GS components.
  have h_span : tReduced ∈ Submodule.span ℝ (Set.range B.basis) := by
    -- Use that babaiRound is in the ℤ-span, hence in the ℝ-span.
    have h_round : babaiRound t B.basis ∈ Submodule.span ℤ (Set.range B.basis) := by
      simpa [EuclideanLattice.mem_def, B.toLattice.carrier_eq] using
        (babaiRound_in_lattice (B := B) (t := t))
    have h_roundR : babaiRound t B.basis ∈ Submodule.span ℝ (Set.range B.basis) := by
      exact (Submodule.span_subset_span ℤ (ℝ) (Set.range B.basis)) h_round
    have hsub : t - babaiRound t B.basis ∈ Submodule.span ℝ (Set.range B.basis) := by
      exact Submodule.sub_mem (Submodule.span ℝ (Set.range B.basis)) ht h_roundR
    simpa [htReduced, tReduced] using hsub
  have h_span_bstar : tReduced ∈ Submodule.span ℝ (Set.range (bStarFun B.basis)) := by
    have h_span_eq : Submodule.span ℝ (Set.range (bStarFun B.basis)) =
        Submodule.span ℝ (Set.range B.basis) := by
      simpa [bStarFun] using (InnerProductSpace.span_gramSchmidt ℝ B.basis)
    simpa [h_span_eq] using h_span

  -- Decompose using orthogonality.
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h_span_bstar
  have hsum : tReduced = ∑ i : Fin k, c i • bStarFun B.basis i := by
    simpa [Finsupp.sum_fintype] using hc.symm
  have hcoeff_vec : ∀ i : Fin k, c i • bStarFun B.basis i = projGsVec tReduced B.basis i := by
    intro i
    by_cases h0 : bStarFun B.basis i = 0
    · simp [projGsVec, h0]
    -- compute coefficient by inner product
    have hinner : ⟪tReduced, bStarFun B.basis i⟫ =
        c i * ⟪bStarFun B.basis i, bStarFun B.basis i⟫ := by
      have horth : ∀ j : Fin k, j ≠ i → ⟪bStarFun B.basis j, bStarFun B.basis i⟫ = 0 := by
        intro j hj
        exact bStarFun_orthogonal B.basis j i hj
      calc
        ⟪tReduced, bStarFun B.basis i⟫ =
            ⟪∑ j : Fin k, c j • bStarFun B.basis j, bStarFun B.basis i⟫ := by
              simp [hsum]
        _ = ∑ j : Fin k, ⟪c j • bStarFun B.basis j, bStarFun B.basis i⟫ := by
              simp [sum_inner]
        _ = ⟪c i • bStarFun B.basis i, bStarFun B.basis i⟫ := by
              classical
              refine Finset.sum_eq_single i ?_ ?_
              · intro j hj hij
                simp [inner_smul_left, horth j hij]
              · simp [inner_smul_left]
        _ = c i * ⟪bStarFun B.basis i, bStarFun B.basis i⟫ := by
              simp [inner_smul_left]
    have h0' : ⟪bStarFun B.basis i, bStarFun B.basis i⟫ ≠ 0 := by
      have hnorm : ‖bStarFun B.basis i‖ ≠ 0 := by
        simpa using h0
      have hnorm_sq : ‖bStarFun B.basis i‖ ^ 2 ≠ 0 := by
        exact pow_ne_zero 2 hnorm
      simpa [real_inner_self_eq_norm_sq] using hnorm_sq
    have hcoeff : c i = projGsCoeff tReduced B.basis i := by
      have hinner' :
          (⟪tReduced, bStarFun B.basis i⟫ / ⟪bStarFun B.basis i, bStarFun B.basis i⟫) = c i := by
        exact (div_eq_iff h0').2 (by simpa [mul_comm] using hinner)
      simpa [projGsCoeff] using hinner'.symm
    simp [projGsVec, hcoeff]

  -- Rewrite the norm using orthogonality.
  have hsum_proj : tReduced = ∑ i : Fin k, projGsVec tReduced B.basis i := by
    calc
      tReduced = ∑ i : Fin k, c i • bStarFun B.basis i := hsum
      _ = ∑ i : Fin k, projGsVec tReduced B.basis i := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [hcoeff_vec i]
  have horth_vec : ∀ i j : Fin k, i ≠ j →
      ⟪projGsVec tReduced B.basis i, projGsVec tReduced B.basis j⟫ = 0 := by
    intro i j hij
    simp [projGsVec, inner_smul_left, inner_smul_right, bStarFun_orthogonal B.basis i j hij]
  have hnorm_sq : ‖tReduced‖^2 = ∑ i : Fin k, ‖projGsVec tReduced B.basis i‖^2 := by
    -- expand ⟪sum, sum⟫ and cancel cross terms
    calc
      ‖tReduced‖^2 = ⟪tReduced, tReduced⟫ := by
        simp [real_inner_self_eq_norm_sq]
      _ = ⟪∑ i : Fin k, projGsVec tReduced B.basis i, tReduced⟫ := by
        exact congrArg (fun x => ⟪x, tReduced⟫) hsum_proj
      _ = ⟪∑ i : Fin k, projGsVec tReduced B.basis i,
            ∑ i : Fin k, projGsVec tReduced B.basis i⟫ := by
        exact congrArg (fun x => ⟪∑ i : Fin k, projGsVec tReduced B.basis i, x⟫) hsum_proj
      _ = ∑ i : Fin k, ‖projGsVec tReduced B.basis i‖^2 := by
        classical
        -- expand into a double sum and drop off-diagonal terms
        have :
            ⟪∑ i : Fin k, projGsVec tReduced B.basis i,
              ∑ i : Fin k, projGsVec tReduced B.basis i⟫ =
            ∑ i : Fin k, ⟪projGsVec tReduced B.basis i, projGsVec tReduced B.basis i⟫ := by
          classical
          calc
            ⟪∑ i : Fin k, projGsVec tReduced B.basis i,
              ∑ i : Fin k, projGsVec tReduced B.basis i⟫
                = ∑ i : Fin k, ⟪projGsVec tReduced B.basis i,
                    ∑ j : Fin k, projGsVec tReduced B.basis j⟫ := by
                      simp [sum_inner]
            _ = ∑ i : Fin k, ∑ j : Fin k,
                    ⟪projGsVec tReduced B.basis i, projGsVec tReduced B.basis j⟫ := by
                      simp [inner_sum]
            _ = ∑ i : Fin k, ⟪projGsVec tReduced B.basis i, projGsVec tReduced B.basis i⟫ := by
                      classical
                      refine Finset.sum_congr rfl ?_
                      intro i _
                      refine Finset.sum_eq_single i ?_ ?_
                      · intro j hj hij
                        simp [horth_vec i j hij.symm]
                      · simp

        simpa [real_inner_self_eq_norm_sq] using this

  -- Bound each component with |coeff| ≤ 1/2.
  have hcomp : ∀ i : Fin k, ‖projGsVec tReduced B.basis i‖^2 ≤ (1 / 4) * ‖bStarFun B.basis i‖^2 := by
    intro i
    have hci : |projGsCoeff tReduced B.basis i| ≤ 1 / 2 := h_coeff i
    let a := projGsCoeff tReduced B.basis i
    have hci' : ‖a‖ ≤ 1 / 2 := by
      have ha : ‖a‖ = |a| := by
        simp [Real.norm_eq_abs]
      simpa [a, ha] using hci
    -- norm of scalar multiple
    have hnorm : ‖projGsVec tReduced B.basis i‖ = ‖a‖ * ‖bStarFun B.basis i‖ := by
      simp [projGsVec, norm_smul, a]
    calc
      ‖projGsVec tReduced B.basis i‖^2
          = (‖a‖ * ‖bStarFun B.basis i‖)^2 := by
              simp [hnorm]
      _ ≤ ((1 / 2) * ‖bStarFun B.basis i‖)^2 := by
              have hmul : ‖a‖ * ‖bStarFun B.basis i‖
                  ≤ (1 / 2) * ‖bStarFun B.basis i‖ := by
                exact mul_le_mul_of_nonneg_right hci' (norm_nonneg _)
              have ha : 0 ≤ ‖a‖ * ‖bStarFun B.basis i‖ := by
                exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
              have hb : 0 ≤ (1 / 2) * ‖bStarFun B.basis i‖ := by
                nlinarith [norm_nonneg (bStarFun B.basis i)]
              have hmul_sq : (‖a‖ * ‖bStarFun B.basis i‖) ^ 2 ≤ ((1 / 2) * ‖bStarFun B.basis i‖) ^ 2 := by
                simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using (mul_le_mul hmul hmul ha hb)
              exact hmul_sq
      _ = (1 / 4) * ‖bStarFun B.basis i‖^2 := by
              ring

  -- Sum up the bounds.
  have hsum_bound : ∑ i : Fin k, ‖projGsVec tReduced B.basis i‖^2 ≤
      (1 / 4) * ∑ i : Fin k, ‖bStarFun B.basis i‖^2 := by
    -- pointwise bound and linearity of sum
    have h1 : ∑ i : Fin k, ‖projGsVec tReduced B.basis i‖^2 ≤
        ∑ i : Fin k, (1 / 4) * ‖bStarFun B.basis i‖^2 := by
      refine Finset.sum_le_sum ?_
      intro i _
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcomp i
    calc
      ∑ i : Fin k, ‖projGsVec tReduced B.basis i‖^2
          ≤ ∑ i : Fin k, (1 / 4) * ‖bStarFun B.basis i‖^2 := h1
      _ = (1 / 4) * ∑ i : Fin k, ‖bStarFun B.basis i‖^2 := by
            simp [Finset.mul_sum]

  -- Combine.
  calc
    ‖t - babaiRound t B.basis‖^2 = ‖tReduced‖^2 := by simp [htReduced]
    _ = ∑ i : Fin k, ‖projGsVec tReduced B.basis i‖^2 := hnorm_sq
    _ ≤ (1 / 4) * ∑ i : Fin k, ‖bStarFun B.basis i‖^2 := hsum_bound

/-- Corollary: Upper bound on the error vector in terms of the max bStar norm of the reduced basis. -/
corollary babai_error_bound_by_max_bstar_norm (B : LatticeBasis n k) (t : 𝓔 n)
    (ht: t ∈ Submodule.span ℝ (Set.range B.basis)) :
    ‖t - babaiRound t B.basis‖^2 ≤ (1 / 4) * (n : ℝ) * (maxNorm (bStarFun B.basis))^2 := by
  have hsum := babai_error_bound_by_sum_bstar_norm (B := B) (t := t) ht
  have hpoint : ∀ i : Fin k, ‖bStarFun B.basis i‖^2 ≤ (maxNorm (bStarFun B.basis))^2 := by
    intro i
    have hle : ‖bStarFun B.basis i‖ ≤ maxNorm (bStarFun B.basis) := by
      unfold maxNorm
      let S : Finset ℝ := Finset.image (fun j => ‖bStarFun B.basis j‖) Finset.univ
      have hmem : ‖bStarFun B.basis i‖ ∈ S := by
        simp [S]
      exact Finset.le_max' S _ hmem
    have hnonneg : 0 ≤ ‖bStarFun B.basis i‖ := norm_nonneg _
    have hnonnegM : 0 ≤ maxNorm (bStarFun B.basis) := le_trans hnonneg hle
    nlinarith
  have hsum_max : ∑ i : Fin k, ‖bStarFun B.basis i‖^2 ≤ (k : ℝ) * (maxNorm (bStarFun B.basis))^2 := by
    calc
      ∑ i : Fin k, ‖bStarFun B.basis i‖^2
          ≤ ∑ i : Fin k, (maxNorm (bStarFun B.basis))^2 := by
            refine Finset.sum_le_sum ?_
            intro i _
            exact hpoint i
      _ = (k : ℝ) * (maxNorm (bStarFun B.basis))^2 := by simp
  have hk_le_n : (k : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast B.le_dim
  have hmax_nonneg : 0 ≤ (maxNorm (bStarFun B.basis))^2 := sq_nonneg _
  calc
    ‖t - babaiRound t B.basis‖^2 ≤ (1 / 4) * ∑ i : Fin k, ‖bStarFun B.basis i‖^2 := hsum
    _ ≤ (1 / 4) * ((k : ℝ) * (maxNorm (bStarFun B.basis))^2) := by
      exact mul_le_mul_of_nonneg_left hsum_max (by positivity)
    _ ≤ (1 / 4) * ((n : ℝ) * (maxNorm (bStarFun B.basis))^2) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk_le_n hmax_nonneg) (by positivity)
    _ = (1 / 4) * (n : ℝ) * (maxNorm (bStarFun B.basis))^2 := by ring

/-- Upper bound on the error vector in terms of the GS norm of bStar_n of an LLL-reduced basis. -/
theorem babaiRound_error_bound_of_LLL_reduced_by_bstar_n_norm (B : LatticeBasis n k) (t : 𝓔 n)
    (ht: t ∈ Submodule.span ℝ (Set.range B.basis))
    (h_reduced : LLLReduced B δ34) :
    ‖t - babaiRound t B.basis‖ ≤ (1 / 2) * ((2 : ℝ) ^ ((k : ℝ) / 2)) * ‖bStarFun B.basis ⟨k-1, Nat.sub_lt k.pos zero_lt_one⟩‖ := by
  let ilast : Fin k := ⟨k - 1, Nat.sub_lt k.pos zero_lt_one⟩
  have hsum := babai_error_bound_by_sum_bstar_norm (B := B) (t := t) ht
  have hpair : ∀ j : Fin k,
      ‖bStarFun B.basis j‖ ^ 2 ≤ (2 : ℝ) ^ ((k : ℕ) - 1 - j.1) * ‖bStarFun B.basis ilast‖ ^ 2 := by
    intro j
    have hjle : j ≤ ilast := by
      exact Nat.le_pred_of_lt j.isLt
    have hraw := LLLReduced_bstar_pair_sq_le_alpha_pow B δ34 δ34_IsDelta h_reduced ilast j hjle
    have hα : (α[δ34]) ^ (ilast.val - j.val) = (2 : ℝ) ^ ((k : ℕ) - 1 - j.1) := by
      simpa [ilast] using congrArg (fun x : ℝ => x ^ (ilast.val - j.val)) alpha_δ34
    calc
      ‖bStarFun B.basis j‖ ^ 2 ≤ (α[δ34]) ^ (ilast.val - j.val) * ‖bStarFun B.basis ilast‖ ^ 2 := hraw
      _ = (2 : ℝ) ^ ((k : ℕ) - 1 - j.1) * ‖bStarFun B.basis ilast‖ ^ 2 := by
            rw [hα]
  have hsum_geom :
      ∑ j : Fin k, ‖bStarFun B.basis j‖ ^ 2
        ≤ (∑ j : Fin k, (2 : ℝ) ^ ((k : ℕ) - 1 - j.1)) * ‖bStarFun B.basis ilast‖ ^ 2 := by
    calc
      ∑ j : Fin k, ‖bStarFun B.basis j‖ ^ 2
          ≤ ∑ j : Fin k, ((2 : ℝ) ^ ((k : ℕ) - 1 - j.1) * ‖bStarFun B.basis ilast‖ ^ 2) := by
            refine Finset.sum_le_sum ?_
            intro j _
            exact hpair j
      _ = (∑ j : Fin k, (2 : ℝ) ^ ((k : ℕ) - 1 - j.1)) * ‖bStarFun B.basis ilast‖ ^ 2 := by
            rw [Finset.sum_mul]
  have hgeom_le : (∑ j : Fin k, (2 : ℝ) ^ ((k : ℕ) - 1 - j.1)) ≤ (2 : ℝ) ^ (k : ℕ) := by
    calc
      (∑ j : Fin k, (2 : ℝ) ^ ((k : ℕ) - 1 - j.1))
          = ∑ j : Fin k, (2 : ℝ) ^ (j : ℕ) := by
              refine Fintype.sum_equiv Fin.revPerm
                (f := fun i : Fin k => (2 : ℝ) ^ ((k : ℕ) - 1 - i.1))
                (g := fun i : Fin k => (2 : ℝ) ^ (i : ℕ)) ?_
              intro i
              change (2 : ℝ) ^ ((k : ℕ) - 1 - i.1) = (2 : ℝ) ^ (Fin.rev i).1
              have hsub : (k : ℕ) - 1 - i.1 = (k : ℕ) - (i.1 + 1) := by
                omega
              simp [Fin.rev, hsub]
      _ = Finset.sum (Finset.range (k : ℕ)) (fun m => (2 : ℝ) ^ m) := by
            simpa using (Fin.sum_univ_eq_sum_range (n := (k : ℕ)) (f := fun m : ℕ => (2 : ℝ) ^ m))
      _ = (2 : ℝ) ^ (k : ℕ) - 1 := by
            have hgeom := (geom_sum_eq (x := (2 : ℝ)) (by norm_num : (2 : ℝ) ≠ 1) (k : ℕ))
            norm_num at hgeom
            simpa using hgeom
      _ ≤ (2 : ℝ) ^ (k : ℕ) := by linarith
  have hsq : ‖t - babaiRound t B.basis‖^2 ≤ (1 / 4) * ((2 : ℝ) ^ (k : ℕ)) * ‖bStarFun B.basis ilast‖^2 := by
    calc
      ‖t - babaiRound t B.basis‖^2 ≤ (1 / 4) * ∑ j : Fin k, ‖bStarFun B.basis j‖^2 := hsum
      _ ≤ (1 / 4) * ((∑ j : Fin k, (2 : ℝ) ^ ((k : ℕ) - 1 - j.1)) * ‖bStarFun B.basis ilast‖^2) := by
            exact mul_le_mul_of_nonneg_left hsum_geom (by positivity)
      _ ≤ (1 / 4) * (((2 : ℝ) ^ (k : ℕ)) * ‖bStarFun B.basis ilast‖^2) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hgeom_le (sq_nonneg _)) (by positivity)
      _ = (1 / 4) * ((2 : ℝ) ^ (k : ℕ)) * ‖bStarFun B.basis ilast‖^2 := by ring
  have hbound : ‖t - babaiRound t B.basis‖ ≤ (1 / 2) * ((2 : ℝ) ^ ((k : ℝ) / 2)) * ‖bStarFun B.basis ilast‖ := by
    let lhs : ℝ := ‖t - babaiRound t B.basis‖
    let rhs : ℝ := (1 / 2) * ((2 : ℝ) ^ ((k : ℝ) / 2)) * ‖bStarFun B.basis ilast‖
    have hsqR : rhs ^ 2 = (1 / 4) * ((2 : ℝ) ^ (k : ℕ)) * ‖bStarFun B.basis ilast‖^2 := by
      unfold rhs
      rw [pow_two]
      ring_nf
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      have hexp : ((k : ℝ) * (1 / 2) * 2) = (k : ℝ) := by ring
      rw [hexp]
      rw [mul_comm]
      simp
    have hsq' : lhs ^ 2 ≤ rhs ^ 2 := by
      simpa [lhs, hsqR] using hsq
    have hlhs : 0 ≤ lhs := by
      simp [lhs]
    have hrhs : 0 ≤ rhs := by
      unfold rhs
      positivity
    have : lhs ≤ rhs := by
      nlinarith
    simpa [lhs, rhs] using this
  simpa [ilast] using hbound

/-- Babai's algorithm gives 2^(k/2)-approximation for CVP when the closest lattice vector is far away -/
theorem babaiRound_approximation_factor_when_far_away (B : LatticeBasis n k) (t : 𝓔 n)
  (hB : LLLReduced B δ34)
  (ht : t ∈ Submodule.span ℝ (Set.range B.basis))
  -- If the target is at least (1/2) * ‖b*_k‖ away from the closest lattice vector, then Babai's solution is a 2^(k/2) approximation.
  (h_far : (B.toLattice).distanceToLattice t ≥ (1 / 2) * ‖bStarFun B.basis ⟨k-1, Nat.sub_lt k.pos zero_lt_one⟩‖) :
  let L := B.toLattice
  ‖t - babaiRound t B.basis‖ ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) * (L.distanceToLattice t) := by
  classical
  intro L
  have h_bound :=
    babaiRound_error_bound_of_LLL_reduced_by_bstar_n_norm (B := B) (t := t) ht hB
  have h_far' : (1 / 2) * ‖bStarFun B.basis ⟨k-1, Nat.sub_lt k.pos zero_lt_one⟩‖
      ≤ L.distanceToLattice t := by
    simpa [L] using h_far
  have hmul : ((2 : ℝ) ^ ((k : ℝ) / 2)) *
        ((1 / 2) * ‖bStarFun B.basis ⟨k-1, Nat.sub_lt k.pos zero_lt_one⟩‖)
      ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) * (L.distanceToLattice t) := by
    have hnonneg : 0 ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) := by positivity
    exact mul_le_mul_of_nonneg_left h_far' hnonneg
  calc
    ‖t - babaiRound t B.basis‖
        ≤ (1 / 2) * ((2 : ℝ) ^ ((k : ℝ) / 2)) *
            ‖bStarFun B.basis ⟨k-1, Nat.sub_lt k.pos zero_lt_one⟩‖ := h_bound
    _ = ((2 : ℝ) ^ ((k : ℝ) / 2)) *
          ((1 / 2) * ‖bStarFun B.basis ⟨k-1, Nat.sub_lt k.pos zero_lt_one⟩‖) := by
          ring
    _ ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) * (L.distanceToLattice t) := hmul

noncomputable section babaiRound_close_case

/-- Last index in `Fin k`, used by the close/far threshold. -/
abbrev lastIdx (k : ℕ+) : Fin k := ⟨k - 1, Nat.sub_lt k.pos zero_lt_one⟩

/-- The reverse of `finRange` can be expressed as the last element followed by the reverse of the prefix. -/
lemma finRange_reverse_succ_castSucc (k : ℕ) :
    (List.finRange (k + 1)).reverse =
      (Fin.last k) :: (List.map Fin.castSucc (List.finRange k)).reverse := by
  rw [List.finRange_reverse, List.finRange_succ_eq_map]
  simp [Fin.rev_zero]
  have hmap :
      List.map (Fin.rev ∘ Fin.succ) (List.finRange k) =
        List.map (Fin.castSucc ∘ Fin.rev) (List.finRange k) := by
    apply List.map_congr_left
    intro a ha
    simpa [Function.comp] using (Fin.rev_succ a)
  calc
    List.map (Fin.rev ∘ Fin.succ) (List.finRange k)
        = List.map Fin.castSucc (List.map Fin.rev (List.finRange k)) := by
            rw [hmap, List.map_map]
    _ = List.map Fin.castSucc (List.finRange k).reverse := by
          rw [List.finRange_reverse]
    _ = (List.map Fin.castSucc (List.finRange k)).reverse := by
          simp

/-- The Babai shift `t - babaiReduce t` is always a lattice vector. -/
lemma babaiReduce_shift_mem_lattice (B : LatticeBasis n k) (t : 𝓔 n) :
    t - babaiReduce t B.basis ∈ B.toLattice := by
  simpa [babaiRound] using (babaiRound_in_lattice (B := B) (t := t))

/-- Rewriting helper: `t - babaiRound t` is exactly `babaiReduce t`. -/
lemma sub_babaiRound_eq_babaiReduce (B : LatticeBasis n k) (t : 𝓔 n) :
    t - babaiRound t B.basis = babaiReduce t B.basis := by
  simp [babaiRound, sub_eq_add_neg]

/-- Distance-to-lattice is unchanged by replacing `t` with `babaiReduce t`. -/
lemma babaiReduce_distance_eq (B : LatticeBasis n k) (t : 𝓔 n) :
    let s := babaiReduce t B.basis
    (B.toLattice).distanceToLattice s = (B.toLattice).distanceToLattice t := by
  simpa using (babaiReduce_preserve_distanceToLattice (B := B) (t := t))

/-- The reduced target `babaiReduce t` lies in the real span of the basis whenever `t` does. -/
lemma babaiReduce_mem_span
    (B : LatticeBasis n k) (t : 𝓔 n)
    (ht : t ∈ Submodule.span ℝ (Set.range B.basis)) :
    babaiReduce t B.basis ∈ Submodule.span ℝ (Set.range B.basis) := by
  have h_roundZ : babaiRound t B.basis ∈ Submodule.span ℤ (Set.range B.basis) := by
    simpa [EuclideanLattice.mem_def, B.toLattice.carrier_eq] using
      (babaiRound_in_lattice (B := B) (t := t))
  have h_roundR : babaiRound t B.basis ∈ Submodule.span ℝ (Set.range B.basis) := by
    exact (Submodule.span_subset_span ℤ (ℝ) (Set.range B.basis)) h_roundZ
  have h_sub : t - babaiRound t B.basis ∈ Submodule.span ℝ (Set.range B.basis) := by
    exact Submodule.sub_mem (Submodule.span ℝ (Set.range B.basis)) ht h_roundR
  simpa [sub_babaiRound_eq_babaiReduce] using h_sub

/-- In the close-case proof, build the reduced witness `x` from the given lattice point `y`. -/
lemma close_case_reduce_witness
    (B : LatticeBasis n k) (t y : 𝓔 n) (hyL : y ∈ B.toLattice) :
    ∃ x : 𝓔 n,
      x ∈ B.toLattice ∧
      ‖babaiReduce t B.basis - x‖ = ‖t - y‖ := by
  let s := babaiReduce t B.basis
  let x : 𝓔 n := y - (t - s)
  have hsL : t - s ∈ B.toLattice := by
    simpa [s] using (babaiReduce_shift_mem_lattice (B := B) (t := t))
  have hxL : x ∈ B.toLattice := by
    dsimp [x]
    exact B.toLattice.sub_mem hyL hsL
  have hsub : s - x = t - y := by
    dsimp [x]
    abel_nf
  refine ⟨x, hxL, ?_⟩
  simp [s, hsub]

/-! Helper lemmas for the close-case induction. -/

/-- Prefix basis consisting of the first k vectors of a (k+1)-basis. -/
noncomputable def prefixBasis (B : LatticeBasis n (k + 1)) : LatticeBasis n k := by
  classical
  -- TODO: fill in the linear independence proof for the restricted basis.
  refine
    { basis := fun i => B.basis ⟨i.1, lt_trans i.2 (Nat.lt_succ_self _)⟩
      le_dim := ?_
      li := ?_ }
  · exact le_trans (Nat.le_succ _) B.le_dim
  ·
    refine (LinearIndependent.comp B.li
      (fun i : Fin k => (⟨i.1, lt_trans i.2 (Nat.lt_succ_self _)⟩ : Fin (k + 1))) ?_)
    intro a b h
    apply Fin.ext
    simpa using congrArg Fin.val h

/-- The prefix basis agrees with the original basis on indices < k. -/
lemma prefixBasis_spec (B : LatticeBasis n (k + 1)) (i : Fin k) :
    (prefixBasis (B := B)).basis i = B.basis ⟨i.1, lt_trans i.2 (Nat.lt_succ_self _)⟩ := by
  rfl

/-- Gram-Schmidt on the prefix basis agrees with the full basis on indices < k. -/
lemma bStarFun_prefix_eq (B : LatticeBasis n (k + 1)) (i : Fin k) :
    bStarFun (prefixBasis (B := B)).basis i =
      bStarFun B.basis (Fin.castSucc i) := by
  let m : ℕ+ := ⟨i.1 + 1, Nat.succ_pos _⟩
  let emb : Fin m → Fin k := fun j =>
    ⟨j.1, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩
  let vecs : Fin m → 𝓔 n := fun t => B.basis (Fin.castSucc (emb t))
  let vecs' : Fin m → 𝓔 n := fun t => (prefixBasis (B := B)).basis (emb t)
  have hvec : vecs' = vecs := by
    funext t
    simp [vecs, vecs', emb, prefixBasis]
  have hgs' : InnerProductSpace.gramSchmidt ℝ vecs'
      ⟨i.1, Nat.lt_succ_self _⟩ = bStarFun (prefixBasis (B := B)).basis i := by
    simpa [bStarFun, m, vecs', emb] using
      (LatticeCrypto.Utils.LinearAlgebra.gramSchmidt_prefix_eq
        (B := (prefixBasis (B := B)).basis) (i := i) ⟨i.1, Nat.lt_succ_self _⟩)
  have hgs : InnerProductSpace.gramSchmidt ℝ vecs
      ⟨i.1, Nat.lt_succ_self _⟩ = bStarFun B.basis (Fin.castSucc i) := by
    simpa [bStarFun, m, vecs, emb] using
      (LatticeCrypto.Utils.LinearAlgebra.gramSchmidt_prefix_eq
        (B := B.basis) (i := Fin.castSucc i) ⟨i.1, Nat.lt_succ_self _⟩)
  calc
    bStarFun (prefixBasis (B := B)).basis i
        = InnerProductSpace.gramSchmidt ℝ vecs' ⟨i.1, Nat.lt_succ_self _⟩ := by
            simpa using hgs'.symm
    _ = InnerProductSpace.gramSchmidt ℝ vecs ⟨i.1, Nat.lt_succ_self _⟩ := by
            simp [hvec]
    _ = bStarFun B.basis (Fin.castSucc i) := by
            simpa using hgs

/-- Prefix of an LLL-reduced basis is still LLL-reduced. -/
lemma LLLReduced_prefix (B : LatticeBasis n (k + 1)) (hB : LLLReduced B δ34) :
    LLLReduced (prefixBasis (B := B)) δ34 := by
  rcases hB with ⟨hsize, hlovasz⟩
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hsize' := hsize (Fin.castSucc i) (Fin.castSucc j) hij
    simpa [muFun, projGsCoeff, prefixBasis_spec, bStarFun_prefix_eq] using hsize'
  · intro i hi
    have hi' : (Fin.castSucc i).1 + 1 < (k + 1 : ℕ+) := by
      exact lt_trans hi (Nat.lt_succ_self _)
    simpa [LovaszCondition, projGsCoeff, muFun, bStarFun_prefix_eq] using
      hlovasz (Fin.castSucc i) hi'

/-- The prefix projection lies in the span of the prefix basis. -/
lemma projToSpace_mem_span_prefix (B : LatticeBasis n (k + 1)) (x : 𝓔 n) :
    projToSpace (prefixBasis (B := B)).basis x ∈
      Submodule.span ℝ (Set.range (prefixBasis (B := B)).basis) := by
  classical
  -- First show the projection is in the span of the Gram-Schmidt vectors.
  have hmem :
      projToSpace (prefixBasis (B := B)).basis x ∈
        Submodule.span ℝ (Set.range (bStarFun (prefixBasis (B := B)).basis)) := by
    unfold projToSpace
    refine Submodule.sum_mem _ ?_
    intro i _
    -- Each component is a scalar multiple of a Gram-Schmidt vector.
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨i, rfl⟩
  -- Convert the span of Gram-Schmidt vectors back to the span of the basis.
  have hspan :
      Submodule.span ℝ (Set.range (bStarFun (prefixBasis (B := B)).basis)) =
        Submodule.span ℝ (Set.range (prefixBasis (B := B)).basis) := by
    simpa using (bStarFun_span_eq (B := (prefixBasis (B := B)).basis))
  simpa [hspan] using hmem

/-- The projGsCoeff is homomorphic on the last index -/
lemma projGsCoeff_sub
    (B : LatticeBasis n (k + 1)) (u v : 𝓔 n) :
    projGsCoeff (u - v) B.basis (lastIdx (k + 1)) =
      projGsCoeff u B.basis (lastIdx (k + 1)) -
      projGsCoeff v B.basis (lastIdx (k + 1)) := by
  unfold projGsCoeff
  simp [inner_sub_left, sub_div]

/- The last GS vector B*_n is orthogonal to all previous basis vectors -/
lemma basis_castSucc_inner_bStar_last_eq_zero
    (B : LatticeBasis n (k + 1)) (i : Fin k) :
    ⟪B.basis (Fin.castSucc i), bStarFun B.basis (lastIdx (k + 1))⟫ = 0 := by
  have hne : (Fin.castSucc i : Fin (k + 1)) ≠ lastIdx (k + 1) := by
    intro h
    have hval : (i : ℕ) = (k : ℕ) := by
      simpa [lastIdx, PNat.add_coe] using congrArg Fin.val h
    exact (Nat.ne_of_lt i.2) hval
  have hsum :
      ⟪∑ t ∈ Finset.Iio (Fin.castSucc i),
          (⟪B.basis (Fin.castSucc i), bStarFun B.basis t⟫ /
              ⟪bStarFun B.basis t, bStarFun B.basis t⟫) •
            bStarFun B.basis t,
        bStarFun B.basis (lastIdx (k + 1))⟫ = 0 := by
    rw [sum_inner]
    refine Finset.sum_eq_zero ?_
    intro t ht
    have htne : t ≠ lastIdx (k + 1) := by
      exact ne_of_lt (lt_trans (Finset.mem_Iio.mp ht) (lt_of_le_of_ne (Fin.le_last _) hne))
    simp [inner_smul_left, bStarFun_orthogonal B.basis t (lastIdx (k + 1)) htne]
  rw [basis_eq_bStarFun_decomposition (B := B.basis) (Fin.castSucc i)]
  simp [inner_add_left, hsum, bStarFun_orthogonal B.basis (Fin.castSucc i) (lastIdx (k + 1)) hne]

/-- The GS coefficient of B*_n for any lattice vector x equals the coefficient of B_n  when x is represented by B -/
lemma projGsCoeff_last_eq_repr_last
    (B : LatticeBasis n (k + 1)) (x : 𝓔 n) (hxL : x ∈ B.toLattice) :
    projGsCoeff x B.basis (lastIdx (k + 1)) =
      (B.repr x hxL (lastIdx (k + 1)) : ℝ) := by
  set ilast : Fin (k + 1) := lastIdx (k + 1)
  have hx_repr : x = ∑ j : Fin (k + 1), (B.repr x hxL j) • B.basis j := by
    exact B.repr_spec x hxL
  have hx_reprR : x = ∑ j : Fin (k + 1), (B.repr x hxL j : ℝ) • B.basis j := by
    calc
      x = ∑ j : Fin (k + 1), (B.repr x hxL j) • B.basis j := hx_repr
      _ = ∑ j : Fin (k + 1), (B.repr x hxL j : ℝ) • B.basis j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [Int.cast_smul_eq_zsmul]
  have h_inner :
      ⟪x, bStarFun B.basis ilast⟫ =
        (B.repr x hxL ilast : ℝ) * ⟪bStarFun B.basis ilast, bStarFun B.basis ilast⟫ := by
    have hsum0 :
        ∑ i : Fin k,
          ((B.repr x hxL (Fin.castSucc i) : ℝ) *
            ⟪B.basis (Fin.castSucc i), bStarFun B.basis ilast⟫) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have h0 : ⟪B.basis (Fin.castSucc i), bStarFun B.basis ilast⟫ = 0 := by
        simpa [ilast] using (basis_castSucc_inner_bStar_last_eq_zero (B := B) i)
      simp [h0]
    calc
      ⟪x, bStarFun B.basis ilast⟫
          = ⟪∑ j : Fin (k + 1), (B.repr x hxL j : ℝ) • B.basis j, bStarFun B.basis ilast⟫ := by
              exact congrArg (fun z => ⟪z, bStarFun B.basis ilast⟫) hx_reprR
      _ = ∑ j : Fin (k + 1), ⟪(B.repr x hxL j : ℝ) • B.basis j, bStarFun B.basis ilast⟫ := by
            rw [sum_inner]
      _ = ∑ j : Fin (k + 1), (B.repr x hxL j : ℝ) * ⟪B.basis j, bStarFun B.basis ilast⟫ := by
            simp [inner_smul_left]
      _ = (∑ i : Fin k,
            ((B.repr x hxL (Fin.castSucc i) : ℝ) *
              ⟪B.basis (Fin.castSucc i), bStarFun B.basis ilast⟫))
            + (B.repr x hxL (lastIdx (k + 1)) : ℝ) *
                ⟪B.basis (lastIdx (k + 1)), bStarFun B.basis ilast⟫ := by
              simpa [lastIdx, PNat.add_coe] using
                (Fin.sum_univ_castSucc
                  (f := fun j : Fin (k + 1) =>
                    (B.repr x hxL j : ℝ) * ⟪B.basis j, bStarFun B.basis ilast⟫))
      _ = (B.repr x hxL (lastIdx (k + 1)) : ℝ) *
            ⟪B.basis (lastIdx (k + 1)), bStarFun B.basis ilast⟫ := by
              simp [hsum0]
      _ = (B.repr x hxL (lastIdx (k + 1)) : ℝ) *
            ⟪bStarFun B.basis ilast, bStarFun B.basis ilast⟫ := by
              simp [ilast, bStarFun_inner_self]
  have hden : ⟪bStarFun B.basis ilast, bStarFun B.basis ilast⟫ ≠ 0 := by
    have hne : bStarFun B.basis ilast ≠ 0 := bStarFun_ne_zero B ilast
    have hnorm : ‖bStarFun B.basis ilast‖ ≠ 0 := by simpa [norm_eq_zero] using hne
    have hnorm_sq : ‖bStarFun B.basis ilast‖ ^ 2 ≠ 0 := by exact pow_ne_zero 2 hnorm
    simpa [real_inner_self_eq_norm_sq] using hnorm_sq
  have hdiv :
      (⟪x, bStarFun B.basis ilast⟫ / ⟪bStarFun B.basis ilast, bStarFun B.basis ilast⟫) =
        (B.repr x hxL ilast : ℝ) := by
    exact (div_eq_iff hden).2 (by simpa [mul_comm] using h_inner)
  simpa [projGsCoeff, ilast] using hdiv

/-- A vector v's length is at least its projection on the last GS vector -/
lemma abs_projGsCoeff_last_le_norm_div
    (B : LatticeBasis n (k + 1)) (v : 𝓔 n) :
    |projGsCoeff v B.basis (lastIdx (k + 1))| ≤
      ‖v‖ / ‖bStarFun B.basis (lastIdx (k + 1))‖ := by
  set ilast : Fin (k + 1) := lastIdx (k + 1)
  have hne : bStarFun B.basis ilast ≠ 0 := bStarFun_ne_zero B ilast
  have hnorm_pos : 0 < ‖bStarFun B.basis ilast‖ := by
    exact norm_pos_iff.mpr hne
  have hnorm_ne : ‖bStarFun B.basis ilast‖ ≠ 0 := ne_of_gt hnorm_pos
  calc
    |projGsCoeff v B.basis ilast|
        = |⟪v, bStarFun B.basis ilast⟫ / ⟪bStarFun B.basis ilast, bStarFun B.basis ilast⟫| := by
            rfl
    _ = |⟪v, bStarFun B.basis ilast⟫| / ‖bStarFun B.basis ilast‖ ^ 2 := by
          simp [abs_div, real_inner_self_eq_norm_sq]
    _ ≤ (‖v‖ * ‖bStarFun B.basis ilast‖) / ‖bStarFun B.basis ilast‖ ^ 2 := by
          gcongr
          exact abs_real_inner_le_norm v (bStarFun B.basis ilast)
    _ = ‖v‖ / ‖bStarFun B.basis ilast‖ := by
          field_simp [hnorm_ne]

/--
  Suppose a vector `s` has its projection coefficient on `B*_n` bounded by 1/2,
Further more, there is a lattice vector `x` close to `s` (within `1/2 * ‖B*_n‖`). Then `x` must lie in the prefix lattice (spanned by the first n-1 basis vectors).
 -/
theorem mem_prefix_lattice_of_close_and_projGsCoeff_last_le_half
    (B : LatticeBasis n (k + 1)) (s x : 𝓔 n)
    (hxL : x ∈ B.toLattice)
    (h_close : ‖s - x‖ < (1 / 2) * ‖bStarFun B.basis (lastIdx (k + 1))‖)
    (h_coeff : |projGsCoeff s B.basis (lastIdx (k + 1))| ≤ 1 / 2) :
    x ∈ (prefixBasis (B := B)).toLattice := by
  let ilast : Fin (k + 1) := lastIdx (k + 1)
  have hdiv_lt :
      ‖s - x‖ / ‖bStarFun B.basis ilast‖ < (1 / 2 : ℝ) := by
    have hnorm_pos : 0 < ‖bStarFun B.basis ilast‖ := by
      exact norm_pos_iff.mpr (bStarFun_ne_zero B ilast)
    exact (div_lt_iff₀ hnorm_pos).2 (by simpa [ilast] using h_close)
  have hxs :
      |projGsCoeff (x - s) B.basis ilast| < (1 / 2 : ℝ) := by
    have hle :=
      abs_projGsCoeff_last_le_norm_div (B := B) (v := x - s)
    have hnorm_eq : ‖x - s‖ = ‖s - x‖ := by simp [norm_sub_rev]
    have hdiv_lt' : ‖x - s‖ / ‖bStarFun B.basis ilast‖ < (1 / 2 : ℝ) := by
      simpa [hnorm_eq] using hdiv_lt
    exact lt_of_le_of_lt hle hdiv_lt'
  have hcoeff_x_lt_one :
      |projGsCoeff x B.basis ilast| < (1 : ℝ) := by
    have hsub :
        projGsCoeff (x - s) B.basis ilast =
          projGsCoeff x B.basis ilast - projGsCoeff s B.basis ilast := by
      exact projGsCoeff_sub (B := B) (u := x) (v := s)
    have habs_sub :
        |projGsCoeff x B.basis ilast - projGsCoeff s B.basis ilast| < (1 / 2 : ℝ) := by
      simpa [hsub] using hxs
    have habs :
        |projGsCoeff x B.basis ilast| ≤
          |projGsCoeff x B.basis ilast - projGsCoeff s B.basis ilast| +
          |projGsCoeff s B.basis ilast| := by
      calc
        |projGsCoeff x B.basis ilast|
            = |(projGsCoeff x B.basis ilast - projGsCoeff s B.basis ilast) +
                projGsCoeff s B.basis ilast| := by ring_nf
        _ ≤ |projGsCoeff x B.basis ilast - projGsCoeff s B.basis ilast| +
              |projGsCoeff s B.basis ilast| := by
                exact abs_add_le _ _
    have hrhs_lt :
        |projGsCoeff x B.basis ilast - projGsCoeff s B.basis ilast| +
          |projGsCoeff s B.basis ilast| < 1 := by
      linarith
    exact lt_of_le_of_lt habs hrhs_lt
  have hrepr :
      (B.repr x hxL ilast : ℝ) = projGsCoeff x B.basis ilast := by
    simpa [ilast] using (projGsCoeff_last_eq_repr_last (B := B) (x := x) hxL).symm
  have hm_zero : B.repr x hxL ilast = 0 := by
    by_contra hm
    have hge1 : (1 : ℝ) ≤ |(B.repr x hxL ilast : ℝ)| := by
      have hz : (1 : ℤ) ≤ |B.repr x hxL ilast| := Int.one_le_abs hm
      have hzR : (1 : ℝ) ≤ (|B.repr x hxL ilast| : ℝ) := by exact_mod_cast hz
      simpa [Int.cast_abs] using hzR
    have hlt1 : |(B.repr x hxL ilast : ℝ)| < 1 := by
      simpa [hrepr] using hcoeff_x_lt_one
    exact (not_lt_of_ge hge1) hlt1
  rw [EuclideanLattice.mem_iff_exists_coeffs]
  refine ⟨fun i => B.repr x hxL (Fin.castSucc i), ?_⟩
  have hrepr_spec : x = ∑ j : Fin (k + 1), (B.repr x hxL j) • B.basis j := B.repr_spec x hxL
  calc
    x = ∑ j : Fin (k + 1), (B.repr x hxL j) • B.basis j := hrepr_spec
    _ = (∑ i : Fin k, (B.repr x hxL (Fin.castSucc i)) • B.basis (Fin.castSucc i)) +
          (B.repr x hxL (lastIdx (k + 1))) • B.basis (lastIdx (k + 1)) := by
            simpa [lastIdx, PNat.add_coe] using
              (Fin.sum_univ_castSucc
                (f := fun j : Fin (k + 1) => (B.repr x hxL j) • B.basis j))
    _ = ∑ i : Fin k, (B.repr x hxL (Fin.castSucc i)) • B.basis (Fin.castSucc i) := by
          simp [ilast, hm_zero]
    _ = ∑ i : Fin k, (B.repr x hxL (Fin.castSucc i)) • (prefixBasis (B := B)).basis i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact congrArg (fun y => (B.repr x hxL (Fin.castSucc i)) • y)
            (prefixBasis_spec (B := B) i).symm

end babaiRound_close_case

/-- Any vector in the prefix span is orthogonal to the projection residual. -/
lemma inner_prefix_span_sub_proj_eq_zero
    (B : LatticeBasis n (k + 1)) (s v : 𝓔 n)
    (hv_span : v ∈ Submodule.span ℝ (Set.range (prefixBasis (B := B)).basis)) :
    ⟪v, s - projToSpace (prefixBasis (B := B)).basis s⟫ = 0 := by
  let Bp := (prefixBasis (B := B)).basis
  have hgen : ∀ i : Fin k, ⟪bStarFun Bp i, s - projToSpace Bp s⟫ = 0 := by
    intro i
    have hsum :
        ⟪bStarFun Bp i, projToSpace Bp s⟫ = ⟪bStarFun Bp i, s⟫ := by
      classical
      unfold projToSpace
      rw [inner_sum]
      have hdiag : ⟪bStarFun Bp i, projGsVec s Bp i⟫ = ⟪bStarFun Bp i, s⟫ := by
        unfold projGsVec projGsCoeff
        by_cases h0 : ⟪bStarFun Bp i, bStarFun Bp i⟫ = 0
        · have hb0 : bStarFun Bp i = 0 := by
            have hnorm_sq : ‖bStarFun Bp i‖ ^ 2 = 0 := by
              simpa [real_inner_self_eq_norm_sq] using h0
            have hnorm : ‖bStarFun Bp i‖ = 0 := by nlinarith
            exact norm_eq_zero.mp hnorm
          simp [hb0]
        · calc
            ⟪bStarFun Bp i, (⟪s, bStarFun Bp i⟫ / ⟪bStarFun Bp i, bStarFun Bp i⟫) • bStarFun Bp i⟫
                = (⟪s, bStarFun Bp i⟫ / ⟪bStarFun Bp i, bStarFun Bp i⟫) *
                    ⟪bStarFun Bp i, bStarFun Bp i⟫ := by
                      simp [inner_smul_right]
            _ = ⟪s, bStarFun Bp i⟫ := by field_simp [h0]
            _ = ⟪bStarFun Bp i, s⟫ := by simp [real_inner_comm]
      have hoff : ∀ j : Fin k, j ≠ i → ⟪bStarFun Bp i, projGsVec s Bp j⟫ = 0 := by
        intro j hij
        unfold projGsVec projGsCoeff
        by_cases h0j : ⟪bStarFun Bp j, bStarFun Bp j⟫ = 0
        · have hb0j : bStarFun Bp j = 0 := by
            have hnorm_sq : ‖bStarFun Bp j‖ ^ 2 = 0 := by
              simpa [real_inner_self_eq_norm_sq] using h0j
            have hnorm : ‖bStarFun Bp j‖ = 0 := by nlinarith
            exact norm_eq_zero.mp hnorm
          simp [hb0j]
        · simp [inner_smul_right, bStarFun_orthogonal Bp i j hij.symm]
      have hsum' :
          ∑ j : Fin k, ⟪bStarFun Bp i, projGsVec s Bp j⟫ =
            ⟪bStarFun Bp i, projGsVec s Bp i⟫ := by
        classical
        refine Finset.sum_eq_single i ?_ ?_
        · intro j hj hij
          simp [hoff j hij]
        · simp
      calc
        ∑ j : Fin k, ⟪bStarFun Bp i, projGsVec s Bp j⟫
            = ⟪bStarFun Bp i, projGsVec s Bp i⟫ := hsum'
        _ = ⟪bStarFun Bp i, s⟫ := hdiag
    calc
      ⟪bStarFun Bp i, s - projToSpace Bp s⟫
          = ⟪bStarFun Bp i, s⟫ - ⟪bStarFun Bp i, projToSpace Bp s⟫ := by
              simp [inner_sub_right]
      _ = 0 := by simp [hsum]
  have hv_bstar : v ∈ Submodule.span ℝ (Set.range (bStarFun (prefixBasis (B := B)).basis)) := by
    have hspan :
        Submodule.span ℝ (Set.range (bStarFun (prefixBasis (B := B)).basis)) =
          Submodule.span ℝ (Set.range (prefixBasis (B := B)).basis) := by
      simpa using (bStarFun_span_eq (B := (prefixBasis (B := B)).basis))
    simpa [hspan] using hv_span
  exact
    Submodule.span_induction
      (s := Set.range (bStarFun (prefixBasis (B := B)).basis))
      (p := fun z _ => ⟪z, s - projToSpace (prefixBasis (B := B)).basis s⟫ = 0)
      (mem := by
        intro u hu
        rcases hu with ⟨i, rfl⟩
        exact hgen i)
      (zero := by simp)
      (add := by
        intro u w hu hw hu0 hw0
        simp [inner_add_left, hu0, hw0])
      (smul := by
        intro c u hu hu0
        simp [inner_smul_left, hu0])
      hv_bstar

/-- Distance splits between prefix projection and the orthogonal remainder. -/
lemma norm_sq_split_prefix
    (B : LatticeBasis n (k + 1)) (s x : 𝓔 n)
    (hx_span : x ∈ Submodule.span ℝ (Set.range (prefixBasis (B := B)).basis)) :
    ‖s - x‖^2 =
      ‖projToSpace (prefixBasis (B := B)).basis s - x‖^2 +
        ‖s - projToSpace (prefixBasis (B := B)).basis s‖^2 := by
  let pi := projToSpace (prefixBasis (B := B)).basis s
  have hpi_span : pi ∈ Submodule.span ℝ (Set.range (prefixBasis (B := B)).basis) := by
    simpa [pi] using (projToSpace_mem_span_prefix (B := B) (x := s))
  have hdiff_span : pi - x ∈ Submodule.span ℝ (Set.range (prefixBasis (B := B)).basis) := by
    exact Submodule.sub_mem _ hpi_span hx_span
  have horth : ⟪pi - x, s - pi⟫ = 0 := by
    simpa [pi] using
      (inner_prefix_span_sub_proj_eq_zero (B := B) (s := s) (v := pi - x) hdiff_span)
  have hdecomp : s - x = (pi - x) + (s - pi) := by
    dsimp [pi]
    abel_nf
  have hpyth :
      ‖(pi - x) + (s - pi)‖ * ‖(pi - x) + (s - pi)‖ =
        ‖pi - x‖ * ‖pi - x‖ + ‖s - pi‖ * ‖s - pi‖ :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (x := pi - x) (y := s - pi) horth
  calc
    ‖s - x‖^2 = ‖(pi - x) + (s - pi)‖^2 := by
      rw [pow_two, pow_two]
      have hnorm : ‖s - x‖ = ‖(pi - x) + (s - pi)‖ := by
        rw [hdecomp]
      rw [hnorm]
    _ = ‖pi - x‖^2 + ‖s - pi‖^2 := by
      rw [pow_two, pow_two, pow_two]
      exact hpyth
    _ = ‖projToSpace (prefixBasis (B := B)).basis s - x‖^2 +
          ‖s - projToSpace (prefixBasis (B := B)).basis s‖^2 := by
            rfl

/-- Babai reduction is idempotent. -/
lemma babaiReduce_idempotent (B : Fin k → 𝓔 n) (t : 𝓔 n) :
    babaiReduce (babaiReduce t B) B = babaiReduce t B := by
  classical
  let s := babaiReduce t B
  let BStar := bStarFun B
  let L := (List.finRange k.val).reverse
  have hs_nonpos : ∀ i : Fin k, -(1 / 2 : ℝ) ≤ projGsCoeff s B i := by
    intro i
    have hle : |projGsCoeff s B i| ≤ 1 / 2 := by
      simpa [s] using (abs_projGsCoeff_of_babaiReduce_le_half (B := B) (t := t) i)
    exact (abs_le.mp hle).1
  have hs_lt : ∀ i : Fin k, projGsCoeff s B i < 1 / 2 := by
    intro i
    simpa [s] using (projGsCoeff_of_babaiReduce_lt_half (B := B) (t := t) i)
  have hstep_noop : ∀ j : Fin k.val,
      reduceAt B BStar s ⟨j.val, j.isLt⟩ = s := by
    intro j
    have hround0 : roundZ (projGsCoeff s B ⟨j.val, j.isLt⟩) = 0 := by
      exact roundZ_eq_zero_of_mem_Icc_Iio
        (x := projGsCoeff s B ⟨j.val, j.isLt⟩)
        (hs_nonpos ⟨j.val, j.isLt⟩)
        (hs_lt ⟨j.val, j.isLt⟩)
    simp [reduceAt, BStar, hround0]
  have hfold_noop : L.foldl
      (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩) s = s := by
    induction L with
    | nil =>
        simp
    | cons j L ih =>
        simp [hstep_noop j, ih]
  unfold babaiReduce
  change L.foldl
      (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩) s = s
  exact hfold_noop

/-- Babai rounding of a reduced target is zero. -/
lemma babaiRound_babaiReduce_eq_zero (B : Fin k → 𝓔 n) (t : 𝓔 n) :
    babaiRound (babaiReduce t B) B = 0 := by
  simp [babaiRound, babaiReduce_idempotent]

/-- Projection of a closest vector remains closest in the prefix lattice -/
lemma distanceToLattice_projToSpace_eq_of_mem_prefix_lattice
    (B : LatticeBasis n (k + 1)) (s x : 𝓔 n)
    (hxL' : x ∈ (prefixBasis (B := B)).toLattice)
    (h_dist : ‖s - x‖ = (B.toLattice).distanceToLattice s) :
    ‖projToSpace (prefixBasis (B := B)).basis s - x‖ =
      ((prefixBasis (B := B)).toLattice).distanceToLattice
        (projToSpace (prefixBasis (B := B)).basis s) := by
  let Bp := prefixBasis (B := B)
  let pi := projToSpace Bp.basis
  have hx_span : x ∈ Submodule.span ℝ (Set.range Bp.basis) := by
    have hxZ : x ∈ Submodule.span ℤ (Set.range Bp.basis) := by
      simpa [EuclideanLattice.mem_def, Bp.toLattice.carrier_eq] using hxL'
    exact (Submodule.span_subset_span ℤ (ℝ) (Set.range Bp.basis)) hxZ
  have hxL : x ∈ B.toLattice := by
    have hxZ' : x ∈ Submodule.span ℤ (Set.range B.basis) := by
      have hsub :
          Submodule.span ℤ (Set.range Bp.basis) ≤ Submodule.span ℤ (Set.range B.basis) := by
        refine Submodule.span_mono ?_
        intro y hy
        rcases hy with ⟨i, rfl⟩
        exact ⟨Fin.castSucc i, (prefixBasis_spec (B := B) i).symm⟩
      exact hsub (by simpa [EuclideanLattice.mem_def, Bp.toLattice.carrier_eq] using hxL')
    simpa [EuclideanLattice.mem_def, B.toLattice.carrier_eq] using hxZ'
  have hmin_full : ∀ z : 𝓔 n, z ∈ Bp.toLattice → ‖s - x‖ ≤ ‖s - z‖ := by
    intro z hzL'
    have hzL : z ∈ B.toLattice := by
      have hzZ' : z ∈ Submodule.span ℤ (Set.range B.basis) := by
        have hsub :
            Submodule.span ℤ (Set.range Bp.basis) ≤ Submodule.span ℤ (Set.range B.basis) := by
          refine Submodule.span_mono ?_
          intro y hy
          rcases hy with ⟨i, rfl⟩
          exact ⟨Fin.castSucc i, (prefixBasis_spec (B := B) i).symm⟩
        exact hsub (by simpa [EuclideanLattice.mem_def, Bp.toLattice.carrier_eq] using hzL')
      simpa [EuclideanLattice.mem_def, B.toLattice.carrier_eq] using hzZ'
    calc
      ‖s - x‖ = (B.toLattice).distanceToLattice s := h_dist
      _ ≤ ‖s - z‖ := distanceToLattice_le_norm_sub_of_mem (L := B.toLattice) (t := s) (v := z) hzL
  have hmin_proj : ∀ z : 𝓔 n, z ∈ Bp.toLattice → ‖pi s - x‖ ≤ ‖pi s - z‖ := by
    intro z hzL'
    have hz_span : z ∈ Submodule.span ℝ (Set.range Bp.basis) := by
      have hzZ : z ∈ Submodule.span ℤ (Set.range Bp.basis) := by
        simpa [EuclideanLattice.mem_def, Bp.toLattice.carrier_eq] using hzL'
      exact (Submodule.span_subset_span ℤ (ℝ) (Set.range Bp.basis)) hzZ
    have hx_split :
        ‖s - x‖^2 = ‖pi s - x‖^2 + ‖s - pi s‖^2 := by
      simpa [pi, Bp] using (norm_sq_split_prefix (B := B) (s := s) (x := x) hx_span)
    have hz_split :
        ‖s - z‖^2 = ‖pi s - z‖^2 + ‖s - pi s‖^2 := by
      simpa [pi, Bp] using (norm_sq_split_prefix (B := B) (s := s) (x := z) hz_span)
    have h_sq : ‖pi s - x‖^2 ≤ ‖pi s - z‖^2 := by
      have hfull : ‖s - x‖ ≤ ‖s - z‖ := hmin_full z hzL'
      have hfull_sq : ‖s - x‖^2 ≤ ‖s - z‖^2 := by
        nlinarith [hfull, norm_nonneg (s - x), norm_nonneg (s - z)]
      linarith [hx_split, hz_split]
    have hnonneg1 : 0 ≤ ‖pi s - x‖ := norm_nonneg _
    have hnonneg2 : 0 ≤ ‖pi s - z‖ := norm_nonneg _
    have habs : |‖pi s - x‖| ≤ |‖pi s - z‖| := sq_le_sq.mp h_sq
    simpa [abs_of_nonneg hnonneg1, abs_of_nonneg hnonneg2] using habs
  have h_lower :
      ‖pi s - x‖ ≤ (Bp.toLattice).distanceToLattice (pi s) := by
    unfold EuclideanLattice.distanceToLattice
    refine le_csInf ?_ ?_
    · exact ⟨‖pi s - x‖, ⟨x, hxL', rfl⟩⟩
    · intro r hr
      rcases hr with ⟨z, hzL', rfl⟩
      exact hmin_proj z hzL'
  have h_upper :
      (Bp.toLattice).distanceToLattice (pi s) ≤ ‖pi s - x‖ := by
    exact distanceToLattice_le_norm_sub_of_mem (L := Bp.toLattice) (t := pi s) (v := x) hxL'
  exact le_antisymm h_lower h_upper

/-- Base case for k = 1: Babai rounding is exact at dimension 1. -/
theorem babaiRound_base_case
    (B : LatticeBasis n 1) (t : 𝓔 n) :
    ‖t - babaiRound t B.basis‖ ≤ ((2 : ℝ) ^ ((1 : ℝ) / 2)) * ((B.toLattice).distanceToLattice t) := by
  have hopt : ∀ z : 𝓔 n, z ∈ B.toLattice → ‖t - babaiRound t B.basis‖ ≤ ‖t - z‖ := by
    intro z hzL
    rcases (EuclideanLattice.mem_iff_exists_coeffs (L := B.toLattice) (v := z)).1 hzL with ⟨c, hc⟩
    let bs : 𝓔 n := bStarFun B.basis 0
    let coeff : ℝ := projGsCoeff t B.basis 0
    let u : 𝓔 n := t - coeff • bs
    have hbs : bs = B.basis 0 := by
      have hbs0 : bStarFun B.basis 0 = B.basis 0 := by
        calc
          bStarFun B.basis 0
              = B.basis 0 -
                ∑ x ∈ Finset.Iio (0 : Fin 1),
                  (⟪B.basis 0, bStarFun B.basis x⟫ / ⟪bStarFun B.basis x, bStarFun B.basis x⟫) •
                    bStarFun B.basis x := by
                      simpa using (bStarFun_def_eq (B := B.basis) (i := (0 : Fin 1)))
          _ = B.basis 0 := by
                have hIio : Finset.Iio (0 : Fin 1) = ∅ := by
                  ext x
                  simp
                simp [hIio]
      simpa [bs] using hbs0
    have hz0 : z = (c 0 : ℤ) • B.basis 0 := by
      simpa using hc
    have hz : z = (c 0 : ℝ) • bs := by
      calc
        z = (c 0 : ℤ) • B.basis 0 := hz0
        _ = (c 0 : ℝ) • B.basis 0 := by
              simpa using (Int.cast_smul_eq_zsmul (R := ℝ) (n := c 0) (b := B.basis 0)).symm
        _ = (c 0 : ℝ) • bs := by simp [hbs]
    have hround : babaiRound t B.basis = (roundZ coeff : ℝ) • bs := by
      subst bs
      subst coeff
      unfold babaiRound babaiReduce
      simp [List.finRange, reduceAt, projGsCoeff, hbs]
    have hu_orth : ⟪u, bs⟫ = 0 := by
      unfold u coeff projGsCoeff
      have hden : ⟪bs, bs⟫ ≠ 0 := by
        have hne : bs ≠ 0 := by
          simpa [bs] using (bStarFun_ne_zero B (0 : Fin 1))
        have hnorm : ‖bs‖ ≠ 0 := by simpa [norm_eq_zero] using hne
        have hnorm_sq : ‖bs‖ ^ 2 ≠ 0 := by exact pow_ne_zero 2 hnorm
        simpa [real_inner_self_eq_norm_sq] using hnorm_sq
      calc
        ⟪t - (⟪t, bs⟫ / ⟪bs, bs⟫) • bs, bs⟫
            = ⟪t, bs⟫ - (⟪t, bs⟫ / ⟪bs, bs⟫) * ⟪bs, bs⟫ := by
                simp [inner_sub_left, inner_smul_left]
        _ = 0 := by
              field_simp [hden]
              ring
    have hnorm_sq_form : ∀ m : ℝ,
        ‖t - m • bs‖^2 = ‖u‖^2 + (coeff - m)^2 * ‖bs‖^2 := by
      intro m
      have hdecomp : t - m • bs = u + ((coeff - m) • bs) := by
        unfold u coeff
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_smul]
      have horth : ⟪u, (coeff - m) • bs⟫ = 0 := by
        simp [hu_orth, inner_smul_right]
      have hpyth :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (x := u) (y := (coeff - m) • bs) horth
      calc
        ‖t - m • bs‖^2 = ‖u + ((coeff - m) • bs)‖^2 := by simp [hdecomp]
        _ = ‖u‖^2 + ‖(coeff - m) • bs‖^2 := by
              simpa [pow_two] using hpyth
        _ = ‖u‖^2 + (coeff - m)^2 * ‖bs‖^2 := by
              have habs : |coeff - m| * |coeff - m| = (coeff - m) * (coeff - m) := by
                simp
              calc
                ‖u‖^2 + ‖(coeff - m) • bs‖^2
                    = ‖u‖^2 + (|coeff - m| * ‖bs‖) * (|coeff - m| * ‖bs‖) := by
                        simp [norm_smul, pow_two]
                _ = ‖u‖^2 + (|coeff - m| * |coeff - m|) * (‖bs‖ * ‖bs‖) := by ring
                _ = ‖u‖^2 + (coeff - m)^2 * ‖bs‖^2 := by
                      simp [habs, pow_two]
    have hcoeff_min : |coeff - (roundZ coeff : ℝ)| ≤ |coeff - (c 0 : ℝ)| := by
      have hround_eq : round coeff = roundZ coeff := by
        simpa [roundZ] using (round_eq coeff)
      simpa [hround_eq] using (round_le coeff (c 0))
    have hcoeff_min_sq : (coeff - (roundZ coeff : ℝ))^2 ≤ (coeff - (c 0 : ℝ))^2 := by
      exact (sq_le_sq).2 hcoeff_min
    have hnorm_bs_nonneg : 0 ≤ ‖bs‖^2 := sq_nonneg _
    have hscaled :
        (coeff - (roundZ coeff : ℝ))^2 * ‖bs‖^2 ≤
          (coeff - (c 0 : ℝ))^2 * ‖bs‖^2 := by
      exact mul_le_mul_of_nonneg_right hcoeff_min_sq hnorm_bs_nonneg
    have hsq :
        ‖t - babaiRound t B.basis‖^2 ≤ ‖t - z‖^2 := by
      calc
        ‖t - babaiRound t B.basis‖^2
            = ‖u‖^2 + (coeff - (roundZ coeff : ℝ))^2 * ‖bs‖^2 := by
                simpa [hround] using (hnorm_sq_form (roundZ coeff : ℝ))
        _ ≤ ‖u‖^2 + (coeff - (c 0 : ℝ))^2 * ‖bs‖^2 := by
              exact add_le_add_left hscaled _
        _ = ‖t - z‖^2 := by
              simpa [hz] using (hnorm_sq_form (c 0 : ℝ)).symm
    have habs := sq_le_sq.mp hsq
    have hleft : 0 ≤ ‖t - babaiRound t B.basis‖ := norm_nonneg _
    have hright : 0 ≤ ‖t - z‖ := norm_nonneg _
    simpa [abs_of_nonneg hleft, abs_of_nonneg hright] using habs
  obtain ⟨y, hyL, hyDist⟩ := exists_closest_lattice_point (L := B.toLattice) (t := t)
  have hle_dist : ‖t - babaiRound t B.basis‖ ≤ (B.toLattice).distanceToLattice t := by
    simpa [hyDist] using (hopt y hyL)
  have hdist_nonneg : 0 ≤ (B.toLattice).distanceToLattice t := by
    simpa [hyDist] using (norm_nonneg (t - y))
  have hfac : (1 : ℝ) ≤ ((2 : ℝ) ^ ((1 : ℝ) / 2)) := by
    exact Real.one_le_rpow (by norm_num) (by positivity)
  calc
    ‖t - babaiRound t B.basis‖ ≤ (B.toLattice).distanceToLattice t := hle_dist
    _ = (1 : ℝ) * (B.toLattice).distanceToLattice t := by ring
    _ ≤ ((2 : ℝ) ^ ((1 : ℝ) / 2)) * (B.toLattice).distanceToLattice t := by
          exact mul_le_mul_of_nonneg_right hfac hdist_nonneg

/-- Split the Babai error into prefix and orthogonal parts. -/
lemma babaiRound_prefix_split
    (B : LatticeBasis n (k + 1)) (s : 𝓔 n)
    (h_coeff_lo : -(1 / 2 : ℝ) ≤ projGsCoeff s B.basis (lastIdx (k + 1)))
    (h_coeff_hi : projGsCoeff s B.basis (lastIdx (k + 1)) < 1 / 2) :
    ‖s - babaiRound s B.basis‖^2 =
      ‖projToSpace (prefixBasis (B := B)).basis s -
          babaiRound (projToSpace (prefixBasis (B := B)).basis s) (prefixBasis (B := B)).basis‖^2 +
        ‖s - projToSpace (prefixBasis (B := B)).basis s‖^2 := by
  let B' := prefixBasis (B := B)
  let pi := projToSpace B'.basis
  let r : 𝓔 n := s - pi s
  let ilast : Fin (k + 1) := lastIdx (k + 1)
  have h_round0 : roundZ (projGsCoeff s B.basis ilast) = 0 := by
    exact roundZ_eq_zero_of_mem_Icc_Iio (x := projGsCoeff s B.basis ilast) h_coeff_lo h_coeff_hi
  have hr_orth_prefix : ∀ i : Fin k, ⟪r, bStarFun B.basis (Fin.castSucc i)⟫ = 0 := by
    intro i
    have h :
        ⟪bStarFun (prefixBasis (B := B)).basis i,
          s - projToSpace (prefixBasis (B := B)).basis s⟫ = 0 := by
      have hmem :
          bStarFun (prefixBasis (B := B)).basis i ∈
            Submodule.span ℝ (Set.range (prefixBasis (B := B)).basis) := by
        have hspan :
            Submodule.span ℝ (Set.range (bStarFun (prefixBasis (B := B)).basis)) =
              Submodule.span ℝ (Set.range (prefixBasis (B := B)).basis) := by
          simpa using (bStarFun_span_eq (B := (prefixBasis (B := B)).basis))
        have hmem' :
            bStarFun (prefixBasis (B := B)).basis i ∈
              Submodule.span ℝ (Set.range (bStarFun (prefixBasis (B := B)).basis)) := by
          exact Submodule.subset_span ⟨i, rfl⟩
        simpa [hspan] using hmem'
      simpa using
        (inner_prefix_span_sub_proj_eq_zero (B := B) (s := s)
          (v := bStarFun (prefixBasis (B := B)).basis i) hmem)
    have h' : ⟪r, bStarFun B.basis (Fin.castSucc i)⟫ = 0 := by
      simpa [r, bStarFun_prefix_eq, real_inner_comm] using h
    exact h'
  have hs_decomp : s = pi s + r := by
    simp [r]
  have hlast_noop : reduceAt B.basis (bStarFun B.basis) s ilast = s := by
    simp [reduceAt, ilast, h_round0]
  let Lk : List (Fin k.val) := (List.finRange k.val).reverse
  have hlist_split :
      (List.finRange (k + 1).val).reverse =
        (Fin.last k.val) :: List.map Fin.castSucc Lk := by
    simpa [Lk, PNat.add_coe, List.map_reverse] using (finRange_reverse_succ_castSucc k.val)
  have hstep_rel :
      ∀ (accP : 𝓔 n) (j : Fin k.val),
        reduceAt B.basis (bStarFun B.basis) (accP + r)
            (Fin.castSucc j) =
          reduceAt B'.basis (bStarFun B'.basis) accP ⟨j.val, j.isLt⟩ + r := by
    intro accP j
    let i : Fin k := ⟨j.val, j.isLt⟩
    have horthj : ⟪r, bStarFun B.basis (Fin.castSucc i)⟫ = 0 := hr_orth_prefix i
    have hbstar : bStarFun B'.basis i = bStarFun B.basis (Fin.castSucc i) := by
      simpa [B'] using (bStarFun_prefix_eq (B := B) (i := i))
    have hcoeff :
        projGsCoeff (accP + r) B.basis (Fin.castSucc i) =
          projGsCoeff accP B'.basis i := by
      have horthj' : ⟪r, bStarFun B'.basis i⟫ = 0 := by
        simpa [hbstar] using horthj
      unfold projGsCoeff
      calc
        ⟪accP + r, bStarFun B.basis (Fin.castSucc i)⟫ /
            ⟪bStarFun B.basis (Fin.castSucc i), bStarFun B.basis (Fin.castSucc i)⟫
            = (⟪accP, bStarFun B'.basis i⟫ + ⟪r, bStarFun B'.basis i⟫) /
                ⟪bStarFun B'.basis i, bStarFun B'.basis i⟫ := by
                  simp [hbstar, inner_add_left]
        _ = ⟪accP, bStarFun B'.basis i⟫ / ⟪bStarFun B'.basis i, bStarFun B'.basis i⟫ := by
              simp [horthj']
    have hbasis : B'.basis i = B.basis (Fin.castSucc i) := by
      simpa [i] using (prefixBasis_spec (B := B) i)
    calc
      reduceAt B.basis (bStarFun B.basis) (accP + r) (Fin.castSucc j)
          = (accP + r) -
              (roundZ (projGsCoeff (accP + r) B.basis (Fin.castSucc i)) : ℝ) •
                B.basis (Fin.castSucc i) := by
                  simp [reduceAt, i]
      _ = (accP + r) -
            (roundZ (projGsCoeff accP B'.basis i) : ℝ) •
              B.basis (Fin.castSucc i) := by simp [hcoeff]
      _ = (accP + r) -
            (roundZ (projGsCoeff accP B'.basis i) : ℝ) • B'.basis i := by
            simp [hbasis]
      _ = (accP -
            (roundZ (projGsCoeff accP B'.basis i) : ℝ) • B'.basis i) + r := by
            abel_nf
      _ = reduceAt B'.basis (bStarFun B'.basis) accP i + r := by
            simp [reduceAt]
      _ = reduceAt B'.basis (bStarFun B'.basis) accP ⟨j.val, j.isLt⟩ + r := by
            simp [i]
  have hfold_rel :
      ∀ (l : List (Fin k.val)) (accP : 𝓔 n),
        l.foldl
          (fun acc (j : Fin k.val) =>
            reduceAt B.basis (bStarFun B.basis) acc (Fin.castSucc j))
          (accP + r)
        =
        (l.foldl
          (fun acc (j : Fin k.val) =>
            reduceAt B'.basis (bStarFun B'.basis) acc ⟨j.val, j.isLt⟩)
          accP) + r := by
    intro l
    induction l with
    | nil =>
        intro accP
        simp
    | cons j l ih =>
        intro accP
        simp [hstep_rel, ih]
  have hred_eq :
      babaiReduce s B.basis = babaiReduce (pi s) B'.basis + r := by
    have hlast_noop' :
        reduceAt B.basis (bStarFun B.basis) s
            ⟨(Fin.last k.val).val, (Fin.last k.val).isLt⟩ = s := by
      simpa [ilast, lastIdx, PNat.add_coe] using hlast_noop
    unfold babaiReduce
    rw [hlist_split]
    simp only [List.foldl_cons]
    rw [hlast_noop']
    nth_rewrite 1 [hs_decomp]
    rw [List.foldl_map]
    calc
      List.foldl (fun acc j => reduceAt B.basis (bStarFun B.basis) acc (Fin.castSucc j)) (pi s + r) Lk
          = List.foldl (fun acc j => reduceAt B'.basis (bStarFun B'.basis) acc ⟨j.val, j.isLt⟩) (pi s) Lk + r := by
              simpa using (hfold_rel Lk (pi s))
      _ = babaiReduce (pi s) B'.basis + r := by
            simp [babaiReduce, Lk]
  have hround_eq :
      babaiRound s B.basis = babaiRound (pi s) B'.basis := by
    unfold babaiRound
    have hsub :
        s - (babaiReduce (pi s) B'.basis + r) = pi s - babaiReduce (pi s) B'.basis := by
      dsimp [r]
      abel_nf
    calc
      s - babaiReduce s B.basis
          = s - (babaiReduce (pi s) B'.basis + r) := by simp [hred_eq]
      _ = pi s - babaiReduce (pi s) B'.basis := hsub
      _ = babaiRound (pi s) B'.basis := by
            simp [babaiRound]
  have hround_mem_span :
      babaiRound (pi s) B'.basis ∈ Submodule.span ℝ (Set.range B'.basis) := by
    have hZ : babaiRound (pi s) B'.basis ∈ Submodule.span ℤ (Set.range B'.basis) := by
      simpa [EuclideanLattice.mem_def, B'.toLattice.carrier_eq] using
        (babaiRound_in_lattice (B := B') (t := pi s))
    exact (Submodule.span_subset_span ℤ ℝ (Set.range B'.basis)) hZ
  calc
    ‖s - babaiRound s B.basis‖^2
        = ‖s - babaiRound (pi s) B'.basis‖^2 := by simp [hround_eq]
    _ = ‖pi s - babaiRound (pi s) B'.basis‖^2 + ‖s - pi s‖^2 := by
          simpa [pi] using
            (norm_sq_split_prefix (B := B) (s := s)
              (x := babaiRound (pi s) B'.basis) hround_mem_span)
    _ = ‖projToSpace (prefixBasis (B := B)).basis s -
          babaiRound (projToSpace (prefixBasis (B := B)).basis s)
            (prefixBasis (B := B)).basis‖^2 +
        ‖s - projToSpace (prefixBasis (B := B)).basis s‖^2 := by
          simp [B', pi]

/--
Inductive CVP approximation factor with the close/far split in the step.

PROVIDED SOLUTION
The idea is by induction on the dimension `k` of the lattice:
0. In the base case when k = 1, the `babaiRound` will round to the closest lattice vector, giving a factor of 1 ≤ 2^(1/2).

1. Assume the proposition holds for i = 1, ..., k-1. For i = k, let `t' := babaiReduce t B` be the shift vector. It suffice to find a close lattice vector `x'` to `t'`, because if we let `y' = t - t' + x'` (which is a lattice vector), we know that `‖t - y'‖ = ‖t' - x'‖`. So we w.l.o.g. can assume that `t` is already reduced, i.e., `t = t'`.

2. Since `t` is already an output of `babaiReduce`, then `abs_projGsCoeff_of_babaiReduce_le_half` implies that ‖ projGsCoeff t B k‖ ≤ 1/2, or equivalently, `|⟨t, b*_k)| ≤ (1/2) * ‖b*_k‖^2`.

3. Now we do the induction: assume `babaiNearestPlane t B` gives a 2^((k-1)/2)-approximation for (k-1)-dimension LLL-reduced lattice basis B and t in span(B). Now consider the k-dimension lattice:

Let y be the closest lattice point to t, and `x = babaiNearestPlane t B`. If `‖y-k‖>1/2*‖b*_k‖`, then by `babaiRound_approximation_factor_when_far_away`, we directly get the desired factor. What's remained is the case when `‖t - y‖ < (1/2) ‖b*_k‖`.

4. Combined with the observation in step 2, `‖t - y‖ < (1/2) ‖b*_k‖` implies that `|⟨y, b*_k⟩| ≤ |⟨y - t, b*_k⟩| + |⟨t, b*_k)| ≤ ‖y-t‖ * ‖b*_k‖ + (1/2) * ‖b*_k‖^2 < (1/2) * ‖b*_k‖^2 + (1/2) * ‖b*_k‖^2 = ‖b*_k‖^2`. Since `y ∈ L`, it must contain an integer multiple of `b_k`, and `|⟨y, b*_k⟩| < ‖b*_k‖^2` implies that this integer is 0. i.e., the closest lattice point `y` is in the span of the first k-1 basis vectors.

5. Furthermore, `x` is also in the span of the first k-1 basis vectors since `babaiRound` rounds the last coefficient to 0 (also an implication from step 2). So both `x` and `y` are in the span of the first k-1 basis vectors, and we can apply the induction hypothesis to the projection of `t` to this subspace.

3. Specifically, consider the projection `π(t) := projToSpace {b_1,...,b_{k-1}} t`. Then `‖y - t‖ = ‖y - π(t)‖ + ‖π(t) - t‖`, which means y is still the closest lattice vector to `π(t)` in the lattice generated by `{b_1,...,b_{k-1}}`. By the induction hypothesis, we have
   `‖π(t) - babaiRound π(t) B'‖ ≤ 2^((k-1)/2) * ‖π(t) - y‖`, where B' is the basis formed by the first k-1 vectors of B.
We can also show that `babaiRound t B` is the same as `babaiRound π(t) B'` since the last coefficient is rounded to 0, i.e., `x = babaiRound t B = babaiRound π(t) B'` is the same as the Babai rounding of the projection, thus `‖π(t) - x‖ ≤ 2^((k-1)/2) * ‖π(t) - y‖`.

4. Finally we can show that `‖t - x‖^2 = ‖t - π(t)‖^2 + ‖π(t) - x‖^2` by orthogonality of the projection, and `‖t - y‖^2 = ‖t - π(t)‖^2 + ‖π(t) - y‖^2` by the same reason. Combining these with step 3 gives the desired approximation factor.
-/
lemma babaiRound_approximation_factor_induction
    (B : LatticeBasis n k) (t : 𝓔 n)
    (hB : LLLReduced B δ34)
    (ht : t ∈ Submodule.span ℝ (Set.range B.basis)) :
    ‖t - babaiRound t B.basis‖ ≤
      ((2 : ℝ) ^ ((k : ℝ) / 2)) * (B.toLattice).distanceToLattice t := by
  classical
  revert B t hB ht
  induction k using PNat.recOn with
  | one =>
      intro B t hB ht
      -- k = 1: split into close/far and use the existing lemmas.
      have base_case := babaiRound_base_case B t
      simpa using base_case
  | succ k ih =>
      intro B t hB ht
      -- Induction step: split into far/close for dimension k+1.
      by_cases h_close :
        (B.toLattice).distanceToLattice t <
          (1 / 2) * ‖bStarFun B.basis (lastIdx (k + 1))‖
      ·
        -- Close case: reduce, project to the prefix subspace, and use the IH.
        obtain ⟨y, hyL, hyDist⟩ :=
          exists_closest_lattice_point (L := B.toLattice) (t := t)
        let s := babaiReduce t B.basis
        obtain ⟨x, hxL, hxDist⟩ :=
          close_case_reduce_witness (B := B) (t := t) (y := y) hyL
        have hs_span : s ∈ Submodule.span ℝ (Set.range B.basis) :=
          babaiReduce_mem_span (B := B) (t := t) ht
        have hdist_sx : ‖s - x‖ = (B.toLattice).distanceToLattice s := by
          have hdist_s : (B.toLattice).distanceToLattice s =
              (B.toLattice).distanceToLattice t := by
            simpa [s] using (babaiReduce_distance_eq (B := B) (t := t))
          calc
            ‖s - x‖ = ‖t - y‖ := by simpa [s] using hxDist
            _ = (B.toLattice).distanceToLattice t := hyDist
            _ = (B.toLattice).distanceToLattice s := by simp [hdist_s]
        have h_close_sx : ‖s - x‖ <
            (1 / 2) * ‖bStarFun B.basis (lastIdx (k + 1))‖ := by
          have hxDist' : ‖s - x‖ = ‖t - y‖ := by simpa [s] using hxDist
          have hyDist' : ‖t - y‖ = (B.toLattice).distanceToLattice t := hyDist
          simpa [hxDist', hyDist'] using h_close
        have h_coeff : |projGsCoeff s B.basis (lastIdx (k + 1))| ≤ 1 / 2 := by
          simpa [s] using
            (abs_projGsCoeff_of_babaiReduce_le_half (B := B.basis) (t := t) (i := lastIdx (k + 1)))
        have h_coeff_lo : -(1 / 2 : ℝ) ≤ projGsCoeff s B.basis (lastIdx (k + 1)) := by
          exact (abs_le.mp h_coeff).1
        have h_coeff_hi : projGsCoeff s B.basis (lastIdx (k + 1)) < (1 / 2 : ℝ) := by
          simpa [s] using
            (projGsCoeff_of_babaiReduce_lt_half (B := B.basis) (t := t) (i := lastIdx (k + 1)))

        let B' := prefixBasis (B := B)
        let pi := projToSpace B'.basis
        have hB' : LLLReduced B' δ34 := LLLReduced_prefix (B := B) hB
        have hxL' : x ∈ B'.toLattice :=
          mem_prefix_lattice_of_close_and_projGsCoeff_last_le_half (B := B) (s := s) (x := x) hxL h_close_sx h_coeff
        have hs_span' : pi s ∈ Submodule.span ℝ (Set.range B'.basis) := by
          simpa [pi] using (projToSpace_mem_span_prefix (B := B) (x := s))
        have hdist' : ‖pi s - x‖ = (B'.toLattice).distanceToLattice (pi s) := by
          simpa [pi] using
            (distanceToLattice_projToSpace_eq_of_mem_prefix_lattice (B := B) (s := s) (x := x) hxL' hdist_sx)

        have h_ih : ‖pi s - babaiRound (pi s) B'.basis‖ ≤
            ((2 : ℝ) ^ ((k : ℝ) / 2)) * ‖pi s - x‖ := by
          have h_ih' := ih B' (pi s) hB' hs_span'
          simpa [hdist'] using h_ih'

        have h_split := babaiRound_prefix_split (B := B) (s := s) h_coeff_lo h_coeff_hi
        have h_split_x :=
          norm_sq_split_prefix (B := B) (s := s) (x := x)
            (by
              have hxZ : x ∈ Submodule.span ℤ (Set.range B'.basis) := by
                simpa [EuclideanLattice.mem_def, B'.toLattice.carrier_eq] using hxL'
              exact (Submodule.span_subset_span ℤ (ℝ) (Set.range B'.basis)) hxZ)

        have h_ih_sq : ‖pi s - babaiRound (pi s) B'.basis‖^2 ≤
            ((2 : ℝ) ^ ((k : ℝ) / 2) * ‖pi s - x‖)^2 := by
          have hnonnegA : 0 ≤ ‖pi s - babaiRound (pi s) B'.basis‖ := by
            exact norm_nonneg _
          have hnonnegB : 0 ≤ ((2 : ℝ) ^ ((k : ℝ) / 2) * ‖pi s - x‖) := by
            exact mul_nonneg (by positivity) (norm_nonneg _)
          have hmul := mul_le_mul h_ih h_ih hnonnegA hnonnegB
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
        have hsum_sq : ‖s - babaiRound s B.basis‖^2 ≤
            ((2 : ℝ) ^ ((k : ℝ) / 2) * ‖s - x‖)^2 := by
          have hsplit' : ‖s - babaiRound s B.basis‖^2 =
              ‖pi s - babaiRound (pi s) B'.basis‖^2 + ‖s - pi s‖^2 := by
            simpa [pi, B'] using h_split
          have hsplit_x' : ‖s - x‖^2 = ‖pi s - x‖^2 + ‖s - pi s‖^2 := by
            simpa [pi, B'] using h_split_x
          have hC : 0 ≤ ‖s - pi s‖^2 := by exact sq_nonneg _
          have hpow_ge1 : (1 : ℝ) ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) := by
            have hbase : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
            have hexp : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
            exact Real.one_le_rpow hbase hexp
          have hpow_ge1_sq : (1 : ℝ) ≤ ((2 : ℝ) ^ ((k : ℝ) / 2))^2 := by
            nlinarith [hpow_ge1]
          have hC' : ‖s - pi s‖^2 ≤ ((2 : ℝ) ^ ((k : ℝ) / 2))^2 * ‖s - pi s‖^2 := by
            simpa using (mul_le_mul_of_nonneg_right hpow_ge1_sq hC)
          calc
            ‖s - babaiRound s B.basis‖^2
                = ‖pi s - babaiRound (pi s) B'.basis‖^2 + ‖s - pi s‖^2 := hsplit'
            _ ≤ ((2 : ℝ) ^ ((k : ℝ) / 2) * ‖pi s - x‖)^2 + ‖s - pi s‖^2 := by
              exact add_le_add_right h_ih_sq _
            _ ≤ ((2 : ℝ) ^ ((k : ℝ) / 2))^2 * ‖pi s - x‖^2 +
                ((2 : ℝ) ^ ((k : ℝ) / 2))^2 * ‖s - pi s‖^2 := by
              have hC'' :=
                add_le_add_left hC' (((2 : ℝ) ^ ((k : ℝ) / 2))^2 * ‖pi s - x‖^2)
              simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hC''
            _ = ((2 : ℝ) ^ ((k : ℝ) / 2))^2 * (‖pi s - x‖^2 + ‖s - pi s‖^2) := by
              ring
            _ = ((2 : ℝ) ^ ((k : ℝ) / 2))^2 * ‖s - x‖^2 := by
              simp [hsplit_x']
            _ = ((2 : ℝ) ^ ((k : ℝ) / 2) * ‖s - x‖)^2 := by
              ring
        have h_le : ‖s - babaiRound s B.basis‖ ≤
            ((2 : ℝ) ^ ((k : ℝ) / 2)) * ‖s - x‖ := by
          have habs := sq_le_sq.mp hsum_sq
          have hleft : 0 ≤ ‖s - babaiRound s B.basis‖ := by
            exact norm_nonneg _
          have hright : 0 ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) * ‖s - x‖ := by
            exact mul_nonneg (by positivity) (norm_nonneg _)
          simpa [abs_of_nonneg hleft, abs_of_nonneg hright] using habs
        have hpow : ((2 : ℝ) ^ ((k : ℝ) / 2)) ≤
            ((2 : ℝ) ^ ((((k + 1 : ℕ+) : ℝ)) / 2)) := by
          have hbase : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
          have hcoe : (((k + 1 : ℕ+) : ℝ)) = (k : ℝ) + 1 := by
            norm_num [PNat.add_coe]
          have hexp : (k : ℝ) / 2 ≤ (((k + 1 : ℕ+) : ℝ) / 2) := by
            nlinarith [hcoe]
          exact Real.rpow_le_rpow_of_exponent_le hbase hexp
        have h_main : ‖s - babaiRound s B.basis‖ ≤
            ((2 : ℝ) ^ ((((k + 1 : ℕ+) : ℝ)) / 2)) * ‖s - x‖ := by
          exact le_trans h_le (mul_le_mul_of_nonneg_right hpow (by positivity))
        have h_round_s : babaiRound s B.basis = 0 := by
          simpa [s] using (babaiRound_babaiReduce_eq_zero (B := B.basis) (t := t))
        have h_err_t : ‖t - babaiRound t B.basis‖ = ‖s‖ := by
          simp [s, sub_babaiRound_eq_babaiReduce]
        have h_err_s : ‖s - babaiRound s B.basis‖ = ‖s‖ := by
          simp [h_round_s]
        calc
          ‖t - babaiRound t B.basis‖ = ‖s‖ := h_err_t
          _ = ‖s - babaiRound s B.basis‖ := by simpa using h_err_s.symm
          _ ≤ ((2 : ℝ) ^ ((((k + 1 : ℕ+) : ℝ)) / 2)) * ‖s - x‖ := h_main
          _ = ((2 : ℝ) ^ ((((k + 1 : ℕ+) : ℝ)) / 2)) * (B.toLattice).distanceToLattice t := by
            have hxDist' : ‖s - x‖ = ‖t - y‖ := by simpa [s] using hxDist
            simp [hxDist', hyDist]
      ·
        have h_far :
          (B.toLattice).distanceToLattice t ≥
            (1 / 2) * ‖bStarFun B.basis (lastIdx (k + 1))‖ := by
          exact le_of_not_gt h_close
        simpa using
          (babaiRound_approximation_factor_when_far_away
            (B := B) (t := t) hB ht h_far)

/-! Helper lemmas for the final Babai CVP approximation theorem. -/
/-- Helper lemma: an integral lattice can be LLL-reduced within sufficient iterations -/
lemma lll_output_reduced_of_integral
    (B : LatticeBasis n k) [hBint : IsIntegralBasis B] :
    LLLReduced (LLL_impl (LLL_sufficient_iters B δ34) B δ34) δ34 := by
  have hiter :
      ∀ numIters ≥ LLL_sufficient_iters B δ34,
        LLLReduced (LLL_impl numIters B δ34) δ34 := by
    simpa using (LLL_iteration_bound (B := B) (δ := δ34) δ34_IsDelta)
  exact hiter _ le_rfl

/-- Helper lemma: LLL preserves the span of the basis vectors -/
lemma span_transport_of_lll_equiv
    (B : LatticeBasis n k) (t : 𝓔 n)
    (ht : t ∈ Submodule.span ℝ (Set.range B.basis)) (δ : ℝ):
    let N := LLL_sufficient_iters B δ
    let B' := LLL_impl N B δ
    t ∈ Submodule.span ℝ (Set.range B'.basis) := by
  -- `LLL_equiv` preserves the lattice carrier; the real spans coincide.
  intro N B'
  have h_equiv : B'.toLattice ≡ᵤ B.toLattice := by
    simpa [B'] using (LLL_equiv B δ N)
  have h_carrier : B'.toLattice.carrier = B.toLattice.carrier := by
    simpa [EuclideanLattice.CarrierEquiv] using h_equiv
  have h_basis_mem :
      ∀ j : Fin k, B.basis j ∈ Submodule.span ℝ (Set.range B'.basis) := by
    intro j
    have hmemB : B.basis j ∈ B.toLattice.carrier := by
      exact EuclideanLattice.basis_mem (L := B.toLattice) j
    have hmemB' : B.basis j ∈ B'.toLattice.carrier := by
      simpa [h_carrier] using hmemB
    have hmemZ : B.basis j ∈ Submodule.span ℤ (Set.range B'.basis) := by
      simpa [B'.toLattice.carrier_eq] using hmemB'
    exact (Submodule.span_subset_span ℤ (ℝ) (Set.range B'.basis)) hmemZ
  have hsub :
      Submodule.span ℝ (Set.range B.basis) ≤ Submodule.span ℝ (Set.range B'.basis) := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact h_basis_mem j
  exact hsub ht

/-- Helper lemma: LLL preserves the distance to the lattice -/
lemma distanceToLattice_eq_of_lll_equiv
    (B : LatticeBasis n k) (t : 𝓔 n) :
    let N := LLL_sufficient_iters B δ34
    let B' := LLL_impl N B δ34
    (B'.toLattice).distanceToLattice t = (B.toLattice).distanceToLattice t := by
  -- Distance depends only on the carrier, and `LLL_equiv` preserves the carrier.
  intro N B'
  have h_equiv : B'.toLattice ≡ᵤ B.toLattice := by
    simpa [B'] using (LLL_equiv B δ34 N)
  have h_carrier : B'.toLattice.carrier = B.toLattice.carrier := by
    simpa [EuclideanLattice.CarrierEquiv] using h_equiv
  unfold EuclideanLattice.distanceToLattice
  simp [h_carrier]

/-- Babai's algorithm achieves a 2^(k/2) approximation for CVP.

If v* is the true closest lattice vector to t, and v is Babai's output, then:
  ‖t - v‖ ≤ 2^(k/2) • ‖t - v*‖
-/
theorem babaiNearestPlane_approximation_factor (cvp : CVPInstance n k)
  (hL : IsIntegralLattice cvp.L)
  (ht : cvp.t ∈ Submodule.span ℝ (Set.range cvp.L.basis.basis)) :
  let B := cvp.L.basis
  let t := cvp.t
  approxCVPSolution cvp ((2 : ℝ) ^ ((k : ℝ) / 2)) (babaiNearestPlane t B) := by
  classical
  intro B t
  have hLB : cvp.L = B.toLattice := by
    simpa [B] using (EuclideanLattice.eq_basis_toLattice cvp.L)
  have hL' : IsIntegralLattice B.toLattice := by
    simpa [hLB] using hL
  unfold approxCVPSolution
  constructor
  · have hmemB : babaiNearestPlane t B ∈ B.toLattice :=
      babaiNearestPlane_in_lattice (B := B) (t := t)
    simpa [hLB] using hmemB
  · let N := LLL_sufficient_iters B δ34
    let B' := LLL_impl N B δ34
    have h_eq : babaiNearestPlane t B = babaiRound t B'.basis := by
      simp [babaiNearestPlane, N, B']
    have h_red : LLLReduced B' δ34 := by
      have hBint : IsIntegralBasis B :=
        (isIntegralLattice_iff_isIntegralBasis B.toLattice).mp hL'
      letI : IsIntegralBasis B := hBint
      simpa [N, B'] using (lll_output_reduced_of_integral (B := B))
    have ht' : t ∈ Submodule.span ℝ (Set.range B'.basis) := by
      simpa [N, B'] using (span_transport_of_lll_equiv (B := B) (t := t) (ht := ht) (δ := δ34))
    have h_dist_eq : (B'.toLattice).distanceToLattice t = cvp.L.distanceToLattice t := by
      simpa [hLB, N, B'] using (distanceToLattice_eq_of_lll_equiv (B := B) (t := t))
    have hmain :=
      babaiRound_approximation_factor_induction (B := B') (t := t) h_red ht'
    calc
      ‖cvp.t - babaiNearestPlane t B‖ = ‖t - babaiRound t B'.basis‖ := by
        simp [h_eq, t]
      _ ≤ ((2 : ℝ) ^ ((k : ℝ) / 2)) * ((B'.toLattice).distanceToLattice t) := by
        simpa using hmain
      _ = ((2 : ℝ) ^ ((k : ℝ) / 2)) * (cvp.L.distanceToLattice t) := by
        simp [h_dist_eq]

end quality_analysis

end Babai

end LatticeCrypto.Foundations.Algorithms
