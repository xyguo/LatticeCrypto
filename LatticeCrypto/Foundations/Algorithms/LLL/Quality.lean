import LatticeCrypto.Foundations.Algorithms.LLL.Defs

namespace LatticeCrypto.Foundations.Algorithms

open scoped Real RealInnerProductSpace BigOperators
open scoped Classical
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Foundations.Lattice

variable {n k : ℕ+}

namespace LLL


noncomputable section quality_analysis
/-!
## Reduction quality
  Proofs that the reduced basis is short. Main results:
  * Theorem `LLLReduced_b1_le_alpha_pow_succMin₁`: The first basis vector of a LLL-reduced basis is bounded by 2^((n-1)/2) times the lattice's shortest vector length.
  * Theorem `LLLReduced_basis_maxNorm_le_alpha_pow_succMinₙ`: The maximum basis vector norm is bounded by α^((n-1)/2) times the lattice's nth successive minima.
-/

/-! ### Basic bounds on Gram-Schmidt vectors -/

/-- Lovász condition implies bounds on consecutive Gram-Schmidt vectors. -/
theorem LLLReduced_bstar_sq_le (B : LatticeBasis n k) (δ : ℝ) (hB: LLLReduced B δ) (hδ : IsDelta δ) :
  ∀ i : Fin k, ∀ hi : i.1 + 1 < k,
    ‖bStarFun B.basis i‖ ^ 2 ≤ α[δ] * ‖bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2 := by
  intro i hi
  -- Unpack LLLReduced into SizeReduced and LovaszCondition
  obtain ⟨h_size, h_lovasz⟩ := hB
  -- Apply Lovász condition for index i
  specialize h_lovasz i hi
  -- Key fact: bStar_i and bStar_{i+1} are orthogonal by Gram-Schmidt
  have h_orthog : ⟪bStarFun B.basis i, bStarFun B.basis ⟨i.1 + 1, hi⟩⟫ = 0 := by
    -- Follows from Gram-Schmidt orthogonality
    convert bStarFun_orthogonal B.basis _ _ _ using 1
    grind
  -- Expand the norm squared using orthogonality (Pythagorean theorem)
  have h_pyth : ‖μ[B.basis; ⟨i.1 + 1, hi⟩, i] • bStarFun B.basis i +
                  bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2 =
                |μ[B.basis; ⟨i.1 + 1, hi⟩, i]| ^ 2 * ‖bStarFun B.basis i‖ ^ 2 +
                ‖bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2 := by
    -- ‖a • v + w‖² = |a|² * ‖v‖² + ‖w‖² when v ⊥ w
    -- First show that scalar multiplication preserves orthogonality
    have h_smul_orthog : ⟪μ[B.basis; ⟨i.1 + 1, hi⟩, i] • bStarFun B.basis i,
                           bStarFun B.basis ⟨i.1 + 1, hi⟩⟫ = 0 := by
      rw [inner_smul_left, h_orthog, mul_zero]
    -- Use the Pythagorean theorem for orthogonal vectors
    have := @norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ℝ (𝓔 n) _ _ _
      (μ[B.basis; ⟨i.1 + 1, hi⟩, i] • bStarFun B.basis i)
      (bStarFun B.basis ⟨i.1 + 1, hi⟩) h_smul_orthog
    simp only [sq] at this ⊢
    rw [this, norm_smul, Real.norm_eq_abs]
    ring
  -- Apply size reduction: |μ[i+1,i]| ≤ 1/2
  have h_mu_bound : |μ[B.basis; ⟨i.1 + 1, hi⟩, i]| ≤ 1 / 2 := by
    apply h_size
    exact Nat.lt_succ_self i.1
  -- Therefore |μ[i+1,i]|² ≤ 1/4
  have h_mu_sq : |μ[B.basis; ⟨i.1 + 1, hi⟩, i]| ^ 2 ≤ (1 / 4 : ℝ) := by
    calc |μ[B.basis; ⟨i.1 + 1, hi⟩, i]| ^ 2
      _ = |μ[B.basis; ⟨i.1 + 1, hi⟩, i]| * |μ[B.basis; ⟨i.1 + 1, hi⟩, i]| := by ring
      _ ≤ (1 / 2) * (1 / 2) := by apply mul_le_mul h_mu_bound h_mu_bound (abs_nonneg _) (by norm_num)
      _ = 1 / 4 := by norm_num
  -- Combine: from Lovász and Pythagorean theorem
  rw [h_pyth] at h_lovasz
  -- δ * ‖bStar_i‖² ≤ |μ|² * ‖bStar_i‖² + ‖bStar_{i+1}‖²
  -- δ * ‖bStar_i‖² ≤ (1/4) * ‖bStar_i‖² + ‖bStar_{i+1}‖²
  have h_bound : δ * ‖bStarFun B.basis i‖ ^ 2 ≤
                 (1 / 4) * ‖bStarFun B.basis i‖ ^ 2 + ‖bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2 := by
    calc δ * ‖bStarFun B.basis i‖ ^ 2
      _ ≤ |μ[B.basis; ⟨i.1 + 1, hi⟩, i]| ^ 2 * ‖bStarFun B.basis i‖ ^ 2 +
          ‖bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2 := h_lovasz
      _ ≤ (1 / 4) * ‖bStarFun B.basis i‖ ^ 2 + ‖bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2 := by
          apply add_le_add_right
          apply mul_le_mul_of_nonneg_right h_mu_sq (sq_nonneg _)
  -- Rearrange: (δ - 1/4) * ‖bStar_i‖² ≤ ‖bStar_{i+1}‖²
  have h_rearrange : (δ - 1 / 4) * ‖bStarFun B.basis i‖ ^ 2 ≤
                     ‖bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2 := by
    linarith
  -- Divide by (δ - 1/4) > 0 to get the result
  have h_delta_pos : 0 < δ - 1 / 4 := by
    exact (sub_pos.2 hδ.left)
  -- Final inequality: divide both sides by (δ - 1/4)
  have h_final : ‖bStarFun B.basis i‖ ^ 2 ≤
                 (1 / (δ - 1 / 4)) * ‖bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h_delta_pos]
    rw [mul_comm] at h_rearrange
    exact h_rearrange
  calc ‖bStarFun B.basis i‖ ^ 2
    _ ≤ (1 / (δ - 1 / 4)) * ‖bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2 := h_final
    _ = α[δ] * ‖bStarFun B.basis ⟨i.1 + 1, hi⟩‖ ^ 2 := by rfl

/--
  The norm of the first Gram-Schmidt vector ‖BStar_1‖^2 of an LLL-reduced basis is bounded
  by α^i * ‖BStar_i‖^2.
-/
theorem LLLReduced_bstar1_sq_le_alpha_pow {n k : ℕ+} (B : LatticeBasis n k) (δ : ℝ) (hδ : IsDelta δ) (h : LLLReduced B δ) (i : Fin k) :
    ‖bStarFun B.basis ⟨0, k.pos⟩‖ ^ 2 ≤ (α[δ]) ^ (i.val : ℕ) * ‖bStarFun B.basis i‖ ^ 2 := by
  -- Let's choose any `j` such that `i.val < j.val` and `j.val < k`.
  by_contra h_contra; push_neg at h_contra
  generalize_proofs at *;
  -- Let $j$ be the smallest index such that $\|b^*_0\|^2 > \alpha^j \|b^*_j\|^2$.
  obtain ⟨j, hj⟩ : ∃ j : Fin k, ‖bStarFun B.basis ⟨0, by
    positivity⟩‖ ^ 2 > α[δ] ^ (j.val) * ‖bStarFun B.basis j‖ ^ 2 ∧ ∀ i : Fin k, i < j → ‖bStarFun B.basis ⟨0, by
    (expose_names; exact pf)⟩‖ ^ 2 ≤ α[δ] ^ (i.val) * ‖bStarFun B.basis i‖ ^ 2 := by
    exact ⟨ Finset.min' ( Finset.univ.filter fun j : Fin k => ‖bStarFun B.basis ⟨ 0, by aesop ⟩‖ ^ 2 > α[δ] ^ ( j : ℕ ) * ‖bStarFun B.basis j‖ ^ 2 ) ⟨ i, by aesop ⟩, Finset.mem_filter.mp ( Finset.min'_mem ( Finset.univ.filter fun j : Fin k => ‖bStarFun B.basis ⟨ 0, by aesop ⟩‖ ^ 2 > α[δ] ^ ( j : ℕ ) * ‖bStarFun B.basis j‖ ^ 2 ) ⟨ i, by aesop ⟩ ) |>.2, fun j hj => not_lt.1 fun contra => hj.not_ge ( Finset.min'_le _ _ <| by aesop ) ⟩
  generalize_proofs at *;
  rcases j with ⟨ _ | j, hj ⟩ <;> norm_num at *;
  have := hj.2 ⟨ j, by linarith ⟩ ( Nat.lt_succ_self _ );
  have := LLLReduced_bstar_sq_le B δ h hδ ⟨ j, by linarith ⟩ ( by linarith ) ; norm_num [ pow_succ' ] at * ; nlinarith [ inv_pos.mpr ( show 0 < ( δ - 1 / 4 ) ^ j by exact pow_pos ( by linarith [ hδ.1 ] ) _ ), inv_pos.mpr ( show 0 < ( δ - 1 / 4 ) ^ ( j + 1 ) by exact pow_pos ( by linarith [ hδ.1 ] ) _ ), mul_inv_cancel₀ ( ne_of_gt ( show 0 < ( δ - 1 / 4 ) ^ j by exact pow_pos ( by linarith [ hδ.1 ] ) _ ) ), mul_inv_cancel₀ ( ne_of_gt ( show 0 < ( δ - 1 / 4 ) ^ ( j + 1 ) by exact pow_pos ( by linarith [ hδ.1 ] ) _ ) ) ] ;


/-
If a sequence u satisfies u_i ≤ C * u_{i+1} for i+1 < n, then u_i ≤ C^(j-i) * u_j for i ≤ j < n.
-/
lemma geometric_bound_nat {u : ℕ → ℝ} {C : ℝ} {n : ℕ} (hC : 0 ≤ C)
    (h : ∀ i, i + 1 < n → u i ≤ C * u (i + 1)) :
    ∀ i j, i ≤ j → j < n → u i ≤ C ^ (j - i) * u j := by
      intro i j hij hjn; induction hij <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
      rename_i k hk₁ hk₂;
      convert le_trans ( hk₂ ( by linarith ) ) ( mul_le_mul_of_nonneg_left ( h k hjn ) ( pow_nonneg hC _ ) ) using 1 ; rw [ ← mul_assoc, ← pow_succ, Nat.succ_sub hk₁ ]

/-- Generalization of `LLLReduced_bstar1_sq_le_alpha_pow` that relates the norms of bStar_i and bStar_j-/
theorem LLLReduced_bstar_pair_sq_le_alpha_pow
    (B : LatticeBasis n k) (δ : ℝ) (hδ : IsDelta δ) (h : LLLReduced B δ)
    (i j : Fin k) (hij : j ≤ i) :
    ‖bStarFun B.basis j‖ ^ 2 ≤ (α[δ]) ^ (i.val - j.val) * ‖bStarFun B.basis i‖ ^ 2 := by
      -- We apply the lemma `geometric_bound_nat` to the sequence of squares of the norms of the Gram-Schmidt vectors.
      let u := fun m : ℕ => if hm : m < k then ‖LatticeCrypto.Foundations.Algorithms.LLL.bStarFun B.basis ⟨m, hm⟩‖ ^ 2 else 0;
      have h_bound : ∀ m : ℕ, m + 1 < k → u m ≤ α[δ] * u (m + 1) := by
        intros m hm
        simp [u];
        split_ifs <;> try linarith;
        have := LLLReduced_bstar_sq_le B δ h hδ ⟨ m, by assumption ⟩ hm; aesop;
      have := geometric_bound_nat ( show 0 ≤ α[δ] by exact div_nonneg zero_le_one <| sub_nonneg_of_le <| by linarith [ hδ.1, hδ.2 ] ) h_bound j i hij ( Fin.is_lt i ) ; aesop;



/--
  The norm of the first basis vector ‖B_1‖ of an LLL-reduced basis is bounded
  by α^(i/2) times the norm of the i-th Gram-Schmidt vector ‖b*_i‖.
-/
theorem LLLReduced_b1_sq_le_alpha_pow_mul_bi_sq
    (B : LatticeBasis n k) (δ : ℝ) (hδ : IsDelta δ) (h : LLLReduced B δ) (i : Fin k) :
    ‖B.basis ⟨0, k.pos⟩‖ ≤ (α[δ]) ^ ((i.val : ℝ) / 2) * ‖bStarFun B.basis i‖ := by
  -- Strategy: repeatedly apply LLLReduced_bstar_sq_le to chain the bounds
  -- ‖b_0‖ = ‖b*_0‖ ≤ α^(1/2) ‖b*_1‖ ≤ ... ≤ α^(i/2) ‖b*_i‖
  have h_norm : ‖bStarFun B.basis ⟨0, k.pos⟩‖ = ‖B.basis ⟨0, k.pos⟩‖ := by
    unfold LatticeCrypto.Foundations.Algorithms.LLL.bStarFun;
    rw [ InnerProductSpace.gramSchmidt_def ];
    rw [ Finset.sum_eq_zero ] <;> aesop;
  convert Real.sqrt_le_sqrt ( LLLReduced_bstar1_sq_le_alpha_pow B δ hδ h i ) using 1 <;> norm_num [ h_norm ];
  · exact h_norm.symm;
  · rw [ Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith [ hδ.1 ] ) ] ; ring_nf ; norm_num;
    exact Or.inl ( by rw [ Real.inv_rpow ( by linarith [ hδ.1 ] ) ] )

/--
  The norm of the first basis vector ‖B_1‖ of an LLL-reduced basis is bounded
  by α^((k-1)/2) times the minimum Gram-Schmidt vector norm
-/
theorem LLLReduced_b1_le_alpha_pow_minBstar
    (B : LatticeBasis n k) (δ : ℝ) (hδ : IsDelta δ) (h : LLLReduced B δ) :
    ‖B.basis ⟨0, k.pos⟩‖ ≤ (α[δ]) ^ ((k - 1 : ℝ) / 2) * minBstarNorm B := by
  -- By definition of minBstarNorm, there exists some i such that ‖bStarFun B.basis i‖ = minBstarNorm B.
  obtain ⟨i, hi⟩ : ∃ i : Fin k, ‖bStarFun B.basis i‖ = LLL.minBstarNorm B := by
    have := Finset.min'_mem ( Finset.image ( fun i : Fin k => ‖bStarFun B.basis i‖ ) Finset.univ ) ⟨ _, Finset.mem_image_of_mem _ ( Finset.mem_univ ⟨ 0, k.pos ⟩ ) ⟩ ; aesop;
  -- Applying the lemma LLLReduced_b1_sq_le_alpha_pow_mul_bi_sq with i = ⟨0, k.pos⟩ and using the fact that minBstarNorm B is the minimum of the norms of the Gram-Schmidt vectors.
  have h_apply_lemma : ‖B.basis ⟨0, k.pos⟩‖ ≤ (α[δ]) ^ ((i.val : ℝ) / 2) * ‖bStarFun B.basis i‖ := by
    exact LLLReduced_b1_sq_le_alpha_pow_mul_bi_sq B δ hδ h i;
  refine le_trans h_apply_lemma ?_;
  gcongr;
  · exact Real.rpow_nonneg ( one_div_nonneg.mpr ( sub_nonneg.mpr ( by linarith [ hδ.1, hδ.2 ] ) ) ) _;
  · exact one_le_div ( sub_pos_of_lt hδ.1 ) |>.2 ( by linarith [ hδ.2 ] );
  · exact le_tsub_of_add_le_right ( mod_cast Fin.is_lt i );
  · exact hi.le

/-
The squared norm of the i-th basis vector is the sum of the squared norm of the i-th Gram-Schmidt vector and the squared norms of the projections onto the previous Gram-Schmidt vectors.
-/
lemma norm_sq_basis_eq_sum_mu_sq_norm_sq_bstar (B : LatticeBasis n k) (i : Fin k) :
    ‖B.basis i‖ ^ 2 = ‖bStarFun B.basis i‖ ^ 2 + ∑ j ∈ Finset.Iio i, (μ[B.basis; i, j]) ^ 2 * ‖bStarFun B.basis j‖ ^ 2 := by
      -- By definition of the Gram-Schmidt process, we can express the i-th basis vector as the sum of its component in the direction of the i-th Gram-Schmidt vector and its projections onto the previous Gram-Schmidt vectors.
      have h_decomp : B.basis i = ∑ j ∈ Finset.Iio i, (μ[B.basis; i, j]) • bStarFun B.basis j + bStarFun B.basis i := by
        -- By definition of Gram-Schmidt, we can express the i-th basis vector as the sum of its projection onto the previous Gram-Schmidt vectors and the i-th Gram-Schmidt vector.
        have h_decomp : B.basis i = ∑ j ∈ Finset.Iio i, (inner ℝ (B.basis i) (bStarFun B.basis j) / inner ℝ (bStarFun B.basis j) (bStarFun B.basis j)) • bStarFun B.basis j + bStarFun B.basis i := by
          have h_gram_schmidt : ∀ i, B.basis i = ∑ j ∈ Finset.Iio i, (inner ℝ (B.basis i) (bStarFun B.basis j) / inner ℝ (bStarFun B.basis j) (bStarFun B.basis j)) • bStarFun B.basis j + bStarFun B.basis i := by
            intro i
            have h_gram_schmidt : B.basis i = ∑ j ∈ Finset.Iio i, (inner ℝ (B.basis i) (bStarFun B.basis j) / inner ℝ (bStarFun B.basis j) (bStarFun B.basis j)) • bStarFun B.basis j + bStarFun B.basis i := by
              have h_gram_schmidt_def : ∀ i, bStarFun B.basis i = B.basis i - ∑ j ∈ Finset.Iio i, (inner ℝ (B.basis i) (bStarFun B.basis j) / inner ℝ (bStarFun B.basis j) (bStarFun B.basis j)) • bStarFun B.basis j := by
                intro i
                rw [LatticeCrypto.Foundations.Algorithms.LLL.bStarFun];
                rw [ InnerProductSpace.gramSchmidt_def ];
                congr! 2;
                simp +decide [ LatticeCrypto.Foundations.Algorithms.LLL.bStarFun ];
                convert Submodule.starProjection_singleton _ _ using 1;
                simp +decide [ inner_self_eq_norm_sq_to_K ];
                rw [ real_inner_comm ]
              rw [ h_gram_schmidt_def i, add_sub_cancel ];
            exact h_gram_schmidt
          exact h_gram_schmidt i;
        exact h_decomp;
      -- Apply the Pythagorean theorem to the decomposition.
      have h_pyth : ‖B.basis i‖ ^ 2 = ‖∑ j ∈ Finset.Iio i, (μ[B.basis; i, j]) • bStarFun B.basis j‖ ^ 2 + ‖bStarFun B.basis i‖ ^ 2 := by
        rw [ h_decomp, @norm_add_sq ℝ ];
        norm_num +zetaDelta at *;
        rw [ sum_inner ];
        refine Finset.sum_eq_zero fun j hj => ?_;
        rw [ inner_smul_left, bStarFun_orthogonal ] ; aesop;
        exact ne_of_lt ( Finset.mem_Iio.mp hj );
      -- Apply the Pythagorean theorem to the sum of projections.
      have h_pyth_sum : ‖∑ j ∈ Finset.Iio i, (μ[B.basis; i, j]) • bStarFun B.basis j‖ ^ 2 = ∑ j ∈ Finset.Iio i, ‖(μ[B.basis; i, j]) • bStarFun B.basis j‖ ^ 2 := by
        have h_pyth_sum : ∀ (s : Finset (Fin k)), (∀ j ∈ s, ∀ k ∈ s, j ≠ k → ⟪bStarFun B.basis j, bStarFun B.basis k⟫ = 0) → ‖∑ j ∈ s, (μ[B.basis; i, j]) • bStarFun B.basis j‖ ^ 2 = ∑ j ∈ s, ‖(μ[B.basis; i, j]) • bStarFun B.basis j‖ ^ 2 := by
          intros s hs_orthogonal
          have h_pyth_sum : ‖∑ j ∈ s, (μ[B.basis; i, j]) • bStarFun B.basis j‖ ^ 2 = ∑ j ∈ s, ∑ k ∈ s, ⟪(μ[B.basis; i, j]) • bStarFun B.basis j, (μ[B.basis; i, k]) • bStarFun B.basis k⟫ := by
            simp +decide only [← real_inner_self_eq_norm_sq, sum_inner];
            simp +decide only [inner_sum];
          rw [ h_pyth_sum, Finset.sum_congr rfl ];
          intro j hj; rw [ Finset.sum_eq_single j ] <;> simp +contextual ;
          · rw [ real_inner_self_eq_norm_sq ];
          · exact fun k hk hk' => by rw [ inner_smul_left, inner_smul_right ] ; simp +decide [ hs_orthogonal _ hj _ hk ( Ne.symm hk' ) ] ;
          · tauto;
        exact h_pyth_sum _ fun j hj k hk hjk => LLL.bStarFun_orthogonal _ _ _ hjk;
      field_simp;
      rw [ h_pyth, h_pyth_sum, add_comm ];
      norm_num [ norm_smul, mul_pow ];
      norm_num [ div_pow, abs_mul, abs_div, abs_of_nonneg, inner_self_eq_norm_sq_to_K ] ; congr ; ext ; ring;


/-
For any valid LLL parameter δ and natural number n, 1 + n/4 ≤ α^n.
-/
theorem one_add_div_four_le_alpha_pow (δ : ℝ) (hδ : IsDelta δ) (n : ℕ) : 1 + (n : ℝ) / 4 ≤ (α[δ]) ^ n := by
  have h_exp_growth : ∀ n : ℕ, 1 + (n : ℝ) / 4 ≤ (4 / 3) ^ n := by
    intro n; induction n <;> norm_num [ pow_succ' ] at * ; linarith [ div_nonneg ( Nat.cast_nonneg ‹_› : ( 0 : ℝ ) ≤ ↑‹ℕ› ) zero_le_four ] ;
  exact le_trans ( h_exp_growth n ) ( pow_le_pow_left₀ ( by positivity ) ( by rw [ show α[δ] = 1 / ( δ - 1 / 4 ) by rfl ] ; rw [ le_div_iff₀ ] <;> nlinarith [ hδ.1, hδ.2 ] ) _ )


/-- All basis vectors are bounded by a power of α times the maximum Gram-Schmidt norm. -/
theorem LLLReduced_basis_maxNorm_le_alpha_pow_bstar_maxNorm
    (B : LatticeBasis n k) (δ : ℝ) (hδ : IsDelta δ) (h : LLLReduced B δ) :
    maxNorm B.basis ≤ (α[δ]) ^ ((k - 1 : ℝ) / 2) * maxNorm (bStarFun B.basis) := by
  unfold LatticeCrypto.Utils.LinearAlgebra.maxNorm;
  rw [ Finset.max'_le_iff ];
  intro y hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
  have h_bound : ‖B.basis i‖ ^ 2 ≤ (α[δ]) ^ (i.val) * (maxBstarNorm B) ^ 2 := by
    have h_bound : ‖B.basis i‖ ^ 2 ≤ (1 + (i.val : ℝ) / 4) * (maxBstarNorm B) ^ 2 := by
      have h_bound : ‖B.basis i‖ ^ 2 ≤ ‖bStarFun B.basis i‖ ^ 2 + ∑ j ∈ Finset.Iio i, (1 / 4 : ℝ) * ‖bStarFun B.basis j‖ ^ 2 := by
        have h_bound : ‖B.basis i‖ ^ 2 = ‖bStarFun B.basis i‖ ^ 2 + ∑ j ∈ Finset.Iio i, (μ[B.basis; i, j]) ^ 2 * ‖bStarFun B.basis j‖ ^ 2 := by
          exact norm_sq_basis_eq_sum_mu_sq_norm_sq_bstar B i;
        rw [h_bound];
        gcongr;
        have := h.1 i ‹_› ( Finset.mem_Iio.mp ‹_› ) ; norm_num at * ; nlinarith [ abs_le.mp this ] ;
      have h_bound : ∑ j ∈ Finset.Iio i, (1 / 4 : ℝ) * ‖bStarFun B.basis j‖ ^ 2 ≤ (i.val : ℝ) / 4 * (maxBstarNorm B) ^ 2 := by
        have h_bound : ∀ j ∈ Finset.Iio i, ‖bStarFun B.basis j‖ ^ 2 ≤ (maxBstarNorm B) ^ 2 := by
          intros j hj;
          exact pow_le_pow_left₀ ( norm_nonneg _ ) ( Finset.le_max' ( Finset.univ.image fun i => ‖bStarFun B.basis i‖ ) _ <| Finset.mem_image_of_mem _ <| Finset.mem_univ _ ) _;
        convert Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ( h_bound j hj ) ( by norm_num : ( 0 : ℝ ) ≤ 1 / 4 ) using 1 ; norm_num ; ring;
      have h_bound : ‖bStarFun B.basis i‖ ^ 2 ≤ (maxBstarNorm B) ^ 2 := by
        exact pow_le_pow_left₀ ( norm_nonneg _ ) ( Finset.le_max' ( Finset.univ.image fun i => ‖bStarFun B.basis i‖ ) _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) ) _;
      linarith;
    exact h_bound.trans ( mul_le_mul_of_nonneg_right ( one_add_div_four_le_alpha_pow δ hδ _ ) ( sq_nonneg _ ) );
  have h_bound : ‖B.basis i‖ ^ 2 ≤ (α[δ]) ^ (k - 1 : ℕ) * (maxBstarNorm B) ^ 2 := by
    exact h_bound.trans ( mul_le_mul_of_nonneg_right ( pow_le_pow_right₀ ( show 1 ≤ α[δ] by rw [ show α[δ] = 1 / ( δ - 1 / 4 ) by rfl ] ; exact one_le_one_div ( by linarith [ hδ.1 ] ) ( by linarith [ hδ.2 ] ) ) ( Nat.le_sub_one_of_lt i.2 ) ) ( sq_nonneg _ ) );
  convert Real.le_sqrt_of_sq_le h_bound using 1;
  rw [ Real.sqrt_mul ( pow_nonneg ( show 0 ≤ α[δ] by exact one_div_nonneg.mpr ( sub_nonneg.mpr ( by linarith [ hδ.1, hδ.2 ] ) ) ) _ ), Real.sqrt_sq ( by exact le_trans ( by norm_num ) ( Finset.le_max' _ _ <| Finset.mem_image_of_mem _ <| Finset.mem_univ 0 ) ) ];
  rw [ Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ( by exact one_div_nonneg.mpr ( sub_nonneg.mpr ( by linarith [ hδ.1, hδ.2 ] ) ) ) ] ; norm_num [ Nat.cast_pred k.pos ];
  ring_nf;
  unfold maxBstarNorm;
  unfold LatticeCrypto.Utils.LinearAlgebra.maxNorm; aesop;

/-!
### Reduction quality: full-rank specializations
-/

/-- First basis vector bounded by first successive minimum. -/
theorem LLLReduced_b1_le_alpha_pow_succMin₁
    (B : SquareLatticeBasis n) (δ : ℝ) (hδ : IsDelta δ) (h : LLLReduced B δ) :
    ‖B.basis ⟨0, n.pos⟩‖ ≤
      (α[δ]) ^ ((n - 1 : ℝ) / 2) * (B.toLattice).succMin₁ := by
  have h_first_vector : ‖B.basis ⟨0, n.pos⟩‖ ≤ (α[δ]) ^ ((n - 1 : ℝ) / 2) * minBstarNorm B := by
    exact LLLReduced_b1_le_alpha_pow_minBstar B δ hδ h;
  refine le_trans h_first_vector <| mul_le_mul_of_nonneg_left ?_ <| by exact Real.rpow_nonneg ( by unfold alpha; norm_num ; linarith [ hδ.1, hδ.2 ] ) _;
  convert shortestVectorLength_ge_gramSchmidt_minNorm _ _ _;
  · funext; (expose_names; exact GeometricLattice.successiveMinima_one x_1);
  · exact rfl

noncomputable section AristotleLemmas
/-
If a lattice vector has a non-zero coefficient for the last basis vector, its norm is at least the norm of the last Gram-Schmidt vector.
-/
lemma norm_bstar_last_le_of_last_coeff_ne_zero
    {n : ℕ+}
    (B : SquareLatticeBasis n)
    (v : 𝓔 n)
    (hv : v ∈ B.toLattice)
    (h_coeff : B.repr v hv ⟨n - 1, Nat.sub_lt n.pos zero_lt_one⟩ ≠ 0) :
    ‖bStarFun B.basis ⟨n - 1, Nat.sub_lt n.pos zero_lt_one⟩‖ ≤ ‖v‖ := by
      -- By definition of $bstarFun$, we know that $\langle v, bstarFun k \rangle = c_k \|bstarFun k\|^2$.
      have h_inner : ⟪v, bStarFun B.basis ⟨(n : ℕ) - 1, by
        exact Nat.pred_lt n.ne_zero⟩⟫ = (LatticeCrypto.Foundations.Lattice.LatticeBasis.repr B v hv ⟨(n : ℕ) - 1, by
        exact Nat.pred_lt n.ne_zero⟩) * ‖bStarFun B.basis ⟨(n : ℕ) - 1, by
        exact Nat.pred_lt n.ne_zero⟩‖ ^ 2 := by
        all_goals generalize_proofs at *;
        convert projection_on_gramSchmidt_of_max_index B ( fun i => B.repr v hv i ) ⟨ ( n : ℕ ) - 1, by assumption ⟩ _ _ _ using 1;
        · exact fun i hi => False.elim <| hi.not_ge <| Nat.le_pred_of_lt i.2;
        · convert B.repr_spec v hv;
          ext; norm_num
      generalize_proofs at *;
      -- Since $c_k$ is an integer and $c_k \neq 0$, we have $|c_k| \ge 1$.
      have h_abs_coeff : |(LatticeCrypto.Foundations.Lattice.LatticeBasis.repr B v hv ⟨(n : ℕ) - 1, by
        grind⟩ : ℝ)| ≥ 1 := by
        exact mod_cast abs_pos.mpr h_coeff
      generalize_proofs at *;
      -- By Cauchy-Schwarz inequality, we have $|\langle v, bstarFun k \rangle| \le \|v\| \|bstarFun k\|$.
      have h_cauchy_schwarz : |⟪v, bStarFun B.basis ⟨(n : ℕ) - 1, by
        exact Nat.pred_lt n.ne_zero⟩⟫| ≤ ‖v‖ * ‖bStarFun B.basis ⟨(n : ℕ) - 1, by
        exact Nat.pred_lt n.ne_zero⟩‖ := by
        exact abs_real_inner_le_norm _ _
      generalize_proofs at *;
      simp_all +decide [ abs_mul, sq ];
      nlinarith [ norm_nonneg v, norm_nonneg ( bStarFun B.basis ⟨ n - 1, by assumption ⟩ ), mul_le_mul_of_nonneg_right h_abs_coeff ( norm_nonneg v ), mul_le_mul_of_nonneg_right h_abs_coeff ( norm_nonneg ( bStarFun B.basis ⟨ n - 1, by assumption ⟩ ) ) ]

/-
Given a basis B and n linearly independent lattice vectors V, at least one vector in V has a non-zero coefficient for the last basis vector of B.
-/
lemma exists_lattice_vec_with_nonzero_last_coeff
    {n : ℕ+}
    (B : SquareLatticeBasis n)
    (V : Fin n → 𝓔 n)
    (h_mem : ∀ i, V i ∈ B.toLattice)
    (h_li : LinearIndependent ℝ V) :
    ∃ i : Fin n, B.repr (V i) (h_mem i) ⟨n - 1, Nat.sub_lt n.pos zero_lt_one⟩ ≠ 0 := by
      by_contra! h; simp_all +decide [ Fintype.linearIndependent_iff ] ;
      -- Since $B$ is a basis, the vectors $V_i$ lie in the subspace spanned by the first $n-1$ basis vectors of $B$.
      have h_subspace : ∀ i, V i ∈ Submodule.span ℝ (Set.range (fun i : Fin (n - 1) => B.basis (Fin.castLE (Nat.sub_le n 1) i))) := by
        intro i
        have h_sum : V i = ∑ j ∈ Finset.univ.erase ⟨n - 1, Nat.sub_lt n.pos zero_lt_one⟩, (B.repr (V i) (h_mem i) j) • B.basis j := by
          have h_sum : V i = ∑ j ∈ Finset.univ, (B.repr (V i) (h_mem i) j) • B.basis j := by
            exact LatticeBasis.repr_spec B (V i) (h_mem i);
          rw [ ← Finset.sum_erase_add _ _ ( Finset.mem_univ ⟨ n - 1, Nat.sub_lt n.pos zero_lt_one ⟩ ), h i ] at h_sum ; simp +decide at h_sum ⊢ ; tauto;
        rw [h_sum];
        refine' Submodule.sum_mem _ _;
        intro j hj; rw [ Submodule.mem_span ] ; simp +decide [ Finset.mem_erase, Finset.mem_univ ] at hj ⊢;
        intro p hp; convert p.smul_mem ( LatticeCrypto.Foundations.Lattice.LatticeBasis.repr B ( V i ) ( h_mem i ) j ) ( hp <| Set.mem_range_self <| ⟨ j, lt_of_le_of_ne ( Nat.le_sub_one_of_lt <| Fin.is_lt j ) fun h => hj <| Fin.ext <| by linarith [ Nat.sub_add_cancel n.pos ] ⟩ ) using 1;
        ext; simp +decide [ Algebra.smul_def ];
      -- Since the vectors $V_i$ are linearly independent and lie in a subspace of dimension $n-1$, this contradicts the fact that the dimension of the space is $n$.
      have h_contradiction : Module.finrank ℝ (Submodule.span ℝ (Set.range V)) ≤ (n - 1 : ℕ) := by
        have h_contradiction : Module.finrank ℝ (Submodule.span ℝ (Set.range V)) ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : Fin (n - 1) => B.basis (Fin.castLE (Nat.sub_le n 1) i)))) := by
          exact Submodule.finrank_mono <| Submodule.span_le.mpr <| Set.range_subset_iff.mpr h_subspace;
        refine le_trans h_contradiction ?_;
        refine' le_trans ( finrank_span_le_card _ ) _ ; norm_num;
        exact Finset.card_image_le.trans ( by simp );
      have h_card : Module.finrank ℝ (Submodule.span ℝ (Set.range V)) = n := by
        rw [ finrank_span_eq_card ] <;> norm_num [ h_li ];
        exact Fintype.linearIndependent_iff.mpr h_li;
      exact h_contradiction.not_gt ( h_card.symm ▸ Nat.pred_lt ( ne_bot_of_gt n.pos ) )

/-
The norm of the last Gram-Schmidt vector is at most the last successive minimum.
-/
theorem norm_bstar_last_le_succMin_last {n : ℕ+} (B : SquareLatticeBasis n) :
    ‖bStarFun B.basis ⟨n - 1, Nat.sub_lt n.pos zero_lt_one⟩‖ ≤
    (B.toLattice).succMinₙ := by
      -- By definition of $successiveMinima$, there exist $n$ linearly independent vectors $v_1, \ldots, v_n$ in the lattice such that $\|v_i\| = \text{successiveMinima}(i)$.
      obtain ⟨V, hV_mem, hV_ind⟩ : ∃ V : Fin n → 𝓔 n, (∀ i, V i ∈ B.toLattice ∧ V i ≠ 0 ∧ ‖V i‖ = (B.toLattice).successiveMinima i) ∧ LinearIndependent ℝ V := by
        have := @GeometricLattice.linearIndependent_successiveMinima_attained;
        exact this B.toLattice |> fun ⟨ V, hV₁, hV₂ ⟩ => ⟨ V, fun i => ⟨ hV₁ i |>.1.1, hV₁ i |>.1.2, hV₁ i |>.2 ⟩, hV₂ ⟩;
      -- By `exists_lattice_vec_with_nonzero_last_coeff`, there exists an index $k$ such that $V_k$ has a non-zero coefficient for the last basis vector.
      obtain ⟨k, hk⟩ : ∃ k : Fin n, B.repr (V k) (hV_mem k |>.1) ⟨n - 1, Nat.sub_lt n.pos zero_lt_one⟩ ≠ 0 := by
        exact exists_lattice_vec_with_nonzero_last_coeff B V (fun i => (hV_mem i).left) hV_ind;
      -- By `norm_bstar_last_le_of_last_coeff_ne_zero`, we have $\|b^*_{n-1}\| \le \|V_k\|$.
      have h_norm_bstar_le_norm_Vk : ‖bStarFun B.basis ⟨n - 1, Nat.sub_lt n.pos zero_lt_one⟩‖ ≤ ‖V k‖ := by
        exact norm_bstar_last_le_of_last_coeff_ne_zero B ( V k ) ( hV_mem k |>.1 ) hk;
      refine le_trans h_norm_bstar_le_norm_Vk ?_;
      convert hV_mem k |>.2.2.le.trans _;
      convert GeometricLattice.successiveMinima_mono _ _;
      exact Nat.le_pred_of_lt k.is_lt

end AristotleLemmas


/--
  The longest Gram-Schmidt vector bounded by last successive minimum.

PROVIDED SOLUTION
Using `GeometricLattice.linearIndependent_successiveMinima_attained` we get a set of n linearly independent vectors {v_1,...,v_n} that attain the n successive minima.
Then there must be some v_k that's in span{b^*_1,...,b^*_n} but not in span{b^*_1,...,b^*_{n-1}}, then v_k when expressed as the linear combination of lattice basis {b_1,...,b_n}, must have a nonzero (integral) coefficient for b_n.
In particular, this means that the projection of v_k onto b^*_n is some nonzero integer, and hence the norm of b^*_n is at most the norm of v_k, which is at most the last successive minimum.
Now we just use `LLLReduced_bstar_pair_sq_le_alpha_pow` to chain the bounds from b^*_n to any b^*_i, and conclude.
-/
theorem LLLReduced_bstar_maxNorm_le_alpha_pow_succMinₙ
    (B : SquareLatticeBasis n) (δ : ℝ) (hδ : IsDelta δ) (h : LLLReduced B δ) :
    maxNorm (bStarFun B.basis) ≤
      (α[δ]) ^ ((n - 1 : ℝ) / 2) *
        (B.toLattice).succMinₙ := by
  -- By combining the results from `LLLReduced_bstar_pair_sq_le_alpha_pow` and `norm_bstar_last_le_succMin_last`, we can bound the maximum norm of the Gram-Schmidt vectors.
  have h_max_bstar : ∀ i : Fin n, ‖bStarFun B.basis i‖ ≤ (α[δ]) ^ ((n - 1 - i.val : ℝ) / 2) * (B.toLattice).succMinₙ := by
    intro i
    have h_bound_i : ‖bStarFun B.basis i‖ ^ 2 ≤ (α[δ]) ^ ((n - 1 - i.val : ℝ)) * ‖bStarFun B.basis ⟨n - 1, Nat.sub_lt n.pos zero_lt_one⟩‖ ^ 2 := by
      have h_bound_i : ‖bStarFun B.basis i‖ ^ 2 ≤ (α[δ]) ^ ((n - 1 - i.val : ℕ)) * ‖bStarFun B.basis ⟨n - 1, Nat.sub_lt n.pos zero_lt_one⟩‖ ^ 2 := by
        have h_bound : ∀ i j : Fin n, j ≤ i → ‖bStarFun B.basis j‖ ^ 2 ≤ (α[δ]) ^ (i.val - j.val) * ‖bStarFun B.basis i‖ ^ 2 := by
          exact fun i j a => LLLReduced_bstar_pair_sq_le_alpha_pow B δ hδ h i j a;
        convert h_bound ⟨ n - 1, Nat.sub_lt n.pos zero_lt_one ⟩ i ( Nat.le_sub_one_of_lt i.2 ) using 1;
      norm_cast;
      rw [ Int.subNatNat_of_le ( Nat.one_le_iff_ne_zero.mpr n.ne_zero ) ] ; norm_cast;
      rw [ Int.subNatNat_of_le ( Nat.le_sub_one_of_lt i.2 ) ] ; norm_cast;
    have h_bound_i_sqrt : ‖bStarFun B.basis i‖ ≤ Real.sqrt ((α[δ]) ^ ((n - 1 - i.val : ℝ)) * ‖bStarFun B.basis ⟨n - 1, Nat.sub_lt n.pos zero_lt_one⟩‖ ^ 2) := by
      exact Real.le_sqrt_of_sq_le h_bound_i;
    convert h_bound_i_sqrt.trans _ using 1;
    rw [ Real.sqrt_mul <| by exact Real.rpow_nonneg ( by exact one_div_nonneg.mpr <| sub_nonneg.mpr <| le_of_lt <| hδ.1.trans_le' <| by norm_num ) _, Real.sqrt_sq <| norm_nonneg _ ];
    rw [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( by exact one_div_nonneg.mpr <| sub_nonneg.mpr <| le_of_lt <| hδ.1.trans_le' <| by norm_num ) ] ; ring_nf ; norm_num;
    exact mul_le_mul_of_nonneg_left ( norm_bstar_last_le_succMin_last B ) ( Real.rpow_nonneg ( inv_nonneg.mpr ( by linarith [ hδ.1, hδ.2 ] ) ) _ );
  convert ciSup_le fun i => h_max_bstar i |> le_trans <| mul_le_mul_of_nonneg_right ( Real.rpow_le_rpow_of_exponent_le ( show 1 ≤ α[δ] from ?_ ) <| show ( ( n - 1 - i : ℝ ) / 2 ) ≤ ( n - 1 : ℝ ) / 2 by linarith [ show ( i : ℝ ) ≥ 0 from Nat.cast_nonneg _ ] ) <| ?_;
  · unfold LatticeCrypto.Utils.LinearAlgebra.maxNorm;
    rw [ @ciSup_eq_of_forall_le_of_forall_lt_exists_gt ];
    · exact fun i => Finset.le_max' ( Finset.image ( fun i => ‖LatticeCrypto.Foundations.Algorithms.LLL.bStarFun B.basis i‖ ) Finset.univ ) _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) );
    · intro w hw; contrapose! hw; aesop;
  · exact one_le_div ( by linarith [ hδ.1 ] ) |>.2 ( by linarith [ hδ.1, hδ.2 ] );
  · exact le_trans ( by positivity ) ( norm_bstar_last_le_succMin_last B )

/-- Direct corollary of `LLLReduced_bstar_maxNorm_le_alpha_pow_succMin` and
`LLLReduced_basis_maxNorm_le_alpha_pow_bstar_maxNorm`.
-/
theorem LLLReduced_basis_maxNorm_le_alpha_pow_succMinₙ
    (B : SquareLatticeBasis n) (δ : ℝ) (hδ : IsDelta δ) (h : LLLReduced B δ) :
    maxNorm B.basis ≤
      (α[δ]) ^ (n - 1 : ℝ) *
        (B.toLattice).succMinₙ := by
  have h1 : maxNorm B.basis ≤ (α[δ]) ^ ((n - 1 : ℝ) / 2) * maxNorm (bStarFun B.basis) := by
    simpa using LLLReduced_basis_maxNorm_le_alpha_pow_bstar_maxNorm (B := B) (δ := δ) hδ h
  have h2 : maxNorm (bStarFun B.basis) ≤
      (α[δ]) ^ ((n - 1 : ℝ) / 2) * (B.toLattice).succMinₙ := by
    simpa using LLLReduced_bstar_maxNorm_le_alpha_pow_succMinₙ (B := B) (δ := δ) hδ h
  have hαnonneg : 0 ≤ α[δ] := by
    have : 0 ≤ δ - 1 / 4 := by linarith [hδ.1, hδ.2]
    exact one_div_nonneg.mpr this
  have hαpos : 0 < α[δ] := by
    have : 0 < δ - 1 / 4 := by linarith [hδ.1]
    exact one_div_pos.mpr this
  calc
    maxNorm B.basis
        ≤ (α[δ]) ^ ((n - 1 : ℝ) / 2) * maxNorm (bStarFun B.basis) := h1
    _ ≤ (α[δ]) ^ ((n - 1 : ℝ) / 2) *
          ((α[δ]) ^ ((n - 1 : ℝ) / 2) * (B.toLattice).succMinₙ) := by
          exact mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hαnonneg _)
    _ = ((α[δ]) ^ ((n - 1 : ℝ) / 2) * (α[δ]) ^ ((n - 1 : ℝ) / 2)) * (B.toLattice).succMinₙ := by
          simp [mul_assoc]
    _ = (α[δ]) ^ (n - 1 : ℝ) * (B.toLattice).succMinₙ := by
          have hpow : (α[δ]) ^ ((n - 1 : ℝ) / 2 + (n - 1 : ℝ) / 2)
              = (α[δ]) ^ ((n - 1 : ℝ) / 2) * (α[δ]) ^ ((n - 1 : ℝ) / 2) := by
            exact Real.rpow_add (x := α[δ]) (y := (n - 1 : ℝ) / 2) (z := (n - 1 : ℝ) / 2) hαpos
          have hsum : ((n - 1 : ℝ) / 2 + (n - 1 : ℝ) / 2) = (n - 1 : ℝ) := by
            ring
          calc
            (α[δ]) ^ ((n - 1 : ℝ) / 2) * (α[δ]) ^ ((n - 1 : ℝ) / 2) * (B.toLattice).succMinₙ
                = (α[δ]) ^ ((n - 1 : ℝ) / 2 + (n - 1 : ℝ) / 2) * (B.toLattice).succMinₙ := by
                    have hpow' := congrArg (fun t => t * (B.toLattice).succMinₙ) (hpow.symm)
                    simpa [mul_assoc] using hpow'
            _ = (α[δ]) ^ (n - 1 : ℝ) * (B.toLattice).succMinₙ := by
                    simp [hsum]

/-- Hermite bound: first basis vector in terms of determinant. -/
theorem LLLReduced_b1_le_det
    (B : SquareLatticeBasis n) (δ : ℝ) (hδ : IsDelta δ) (h : LLLReduced B δ) :
    ‖B.basis ⟨0, n.pos⟩‖ ≤
      (α[δ]) ^ ((n - 1 : ℝ) / 4) * (B.toLattice).det ^ (1 / (n : ℝ)) := by
  have h_prod : ∏ i : Fin n, ‖B.basis ⟨0, n.pos⟩‖ ≤ (α[δ]) ^ ((n * (n - 1) / 4 : ℝ)) * (LatticeCrypto.Foundations.Lattice.LatticeBasis.volume B) := by
    have h_prod : ∏ i : Fin n, ‖B.basis ⟨0, n.pos⟩‖ ≤ (∏ i : Fin n, (α[δ]) ^ ((i.val : ℝ) / 2)) * (∏ i : Fin n, ‖bStarFun B.basis i‖) := by
      have h_prod : ∀ i : Fin n, ‖B.basis ⟨0, n.pos⟩‖ ≤ (α[δ]) ^ ((i.val : ℝ) / 2) * ‖bStarFun B.basis i‖ := by
        exact fun i => LLLReduced_b1_sq_le_alpha_pow_mul_bi_sq B δ hδ h i;
      simpa only [ ← Finset.prod_mul_distrib ] using Finset.prod_le_prod ( fun _ _ => norm_nonneg _ ) fun _ _ => h_prod _;
    convert h_prod using 2;
    · rw [ ← Real.rpow_sum_of_pos ];
      · exact congr_arg _ ( Nat.recOn n ( by norm_num ) fun n ih => by norm_num [ Fin.sum_univ_castSucc ] at * ; linarith );
      · exact one_div_pos.mpr ( sub_pos.mpr hδ.1 );
    · convert euc_gramSchmidt_matrix_det_abs B.asMatrix using 1;
  have h_root : ‖B.basis ⟨0, n.pos⟩‖ ^ (n : ℝ) ≤ (α[δ]) ^ ((n * (n - 1) / 4 : ℝ)) * (LatticeCrypto.Foundations.Lattice.LatticeBasis.volume B) := by
    convert h_prod using 1 ; norm_num [ Finset.prod_const ];
  convert Real.rpow_le_rpow ( by positivity ) h_root ( inv_nonneg.mpr ( Nat.cast_nonneg n ) ) using 1;
  · rw [ ← Real.rpow_mul ( norm_nonneg _ ), mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr n.ne_zero ), Real.rpow_one ];
  · rw [ Real.mul_rpow ( by exact Real.rpow_nonneg ( by exact div_nonneg zero_le_one ( sub_nonneg.mpr <| by linarith [ hδ.1, hδ.2 ] ) ) _ ) ( by exact abs_nonneg _ ), ← Real.rpow_mul ( by exact div_nonneg zero_le_one ( sub_nonneg.mpr <| by linarith [ hδ.1, hδ.2 ] ) ) ] ; ring_nf;
    norm_num [ sq, mul_assoc ];
    exact mul_eq_mul_left_iff.mp rfl

/-!
### SVP approximation

LLL provides an approximation algorithm for the Shortest Vector Problem (SVP).
-/

/-- LLL gives an exponential approximation to SVP. -/
theorem LLLReduced_SVP_approx
    (B : SquareLatticeBasis n) (δ : ℝ) (hδ : IsDelta δ) (h : LLLReduced B δ) :
    ‖B.basis ⟨0, n.pos⟩‖ ≤ (α[δ]) ^ ((n - 1 : ℝ) / 2) * (B.toLattice).succMin₁ := by
  exact LLLReduced_b1_le_alpha_pow_succMin₁ B δ hδ h

/-- For δ = 3/4, LLL gives a 2^(n/2) approximation to SVP. -/
theorem LLLReduced_SVP_approx_delta34
    (B : SquareLatticeBasis n) (h : LLLReduced B δ34) :
    ‖B.basis ⟨0, n.pos⟩‖ ≤ (2 : ℝ) ^ ((n - 1 : ℝ) / 2) * (B.toLattice).succMin₁ := by
  -- Apply the LLLReduced_b1_le_alpha_pow_succMin₁ theorem with δ = 3/4.
  have := LLLReduced_b1_le_alpha_pow_succMin₁ B δ₃₄ ⟨by norm_num, by norm_num⟩ h;
  grind

/-!
### Delta = 3/4 corollaries
-/

theorem LLLReduced_b1_le_lambda1_delta34
    (B : SquareLatticeBasis n) (h : LLLReduced B δ34) :
    ‖B.basis ⟨0, n.pos⟩‖ ≤
      (2 : ℝ) ^ ((n - 1 : ℝ) / 2) * (B.toLattice).succMin₁ := by
  apply LLLReduced_SVP_approx_delta34 B h

theorem LLLReduced_b1_le_det_delta34
    (B : SquareLatticeBasis n) (h : LLLReduced B δ34) :
    ‖B.basis ⟨0, n.pos⟩‖ ≤
      (2 : ℝ) ^ ((n - 1 : ℝ) / 4) * (B.toLattice).det ^ (1 / (n : ℝ)) := by
  -- Apply the known result that the first basis vector of an LLL-reduced basis is bounded by α^(k-1)/4 times the determinant raised to 1/k for α = 2.
  have h_bound : ‖B.basis ⟨0, n.pos⟩‖ ≤ (α[δ34]) ^ ((n - 1 : ℝ) / 4) * (B.toLattice).det ^ (1 / (n : ℝ)) := by
    -- Apply the known result that the first basis vector of an LLL-reduced basis is bounded by α^(k-1)/4 times the determinant raised to 1/k for α = 2. This follows from the properties of the LLL algorithm.
    apply LLLReduced_b1_le_det B δ34 ⟨by norm_num, by norm_num⟩ h;
  grind

end quality_analysis

end LLL

end LatticeCrypto.Foundations.Algorithms
