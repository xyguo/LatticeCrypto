import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

import LatticeCrypto.Foundations.Gaussian.Defs
import LatticeCrypto.Foundations.Gaussian.Fourier
import LatticeCrypto.Foundations.Gaussian.PoissonSummation
import LatticeCrypto.Foundations.Lattice.Distance
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec

namespace LatticeCrypto.Foundations.Gaussian

section concentration

open scoped Real Complex MeasureTheory
open scoped RealInnerProductSpace
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Foundations.Lattice
open scoped FourierTransform

variable {n : ℕ+} (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s)

/-- The open Euclidean ball centered at c with radius r -/
abbrev 𝔅 {n : ℕ+} (c : 𝓔 n) (r : ℝ) := Metric.ball c r


/-!
  ## Numeric bounds used for deriving tail bounds
  * `numeric_bound_for_tail_bound`: exp(-3πn/4) * 2^n < 2^{-n}.
  * `base_bound_strong` : Real.exp (-3 * Real.pi / 4) * 2 < 0.2
  * `stronger_numeric_bound_for_tail_bound`: Real.exp (-3 * Real.pi * n / 4) * (2 ^ n) < (0.2 ^ n)
-/
section numeric_bounds
/-
ln(4) < 3π/4 using proven bounds.
-/
private fact log_four_lt_three_pi_div_four : Real.log 4 < 3 * Real.pi / 4 := by
  have h_log : Real.log 4 < 2 := by
    rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ];
    have := Real.log_lt_sub_one_of_pos two_pos ; norm_num at * ; linarith;
  -- Since $\pi > 3$, we have $3\pi/4 > 9/4 = 2.25$.
  have h_pi : Real.pi > 3 := by
    exact Real.pi_gt_three;
  linarith

/-
Numeric bound: exp(-3πn/4) * 2^n < 2^{-n}.
-/
private fact numeric_bound_for_tail_bound (n : ℕ+) :
  Real.exp (-3 * Real.pi * n / 4) * (2 : ℝ)^(n : ℝ) < (2 : ℝ)^(-(n : ℝ)) := by
    -- We want to show exp(-3 * pi * n / 4) * 2^n < 2^{-n}.
    -- Multiply by 2^n: exp(-3 * pi * n / 4) * 4^n < 1.
    suffices h_exp : Real.exp (-3 * Real.pi * ↑↑n / 4) * 4 ^ (n : ℕ) < 1 by
      norm_num [ Real.rpow_neg ] at *;
      rw [ inv_eq_one_div, lt_div_iff₀ ] <;> first | positivity | convert h_exp using 1 ; ring_nf;
      norm_num [ pow_mul' ];
    rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ] <;> norm_num;
    rw [ ← Real.exp_add ] ; ring_nf ; norm_num;
    have := log_four_lt_three_pi_div_four; nlinarith [ show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr n.2 ] ;

private fact log_ten_lt_231 : Real.log 10 < 2.31 := by
  norm_num [ Real.log_lt_iff_lt_exp ];
  rw [ Real.exp_eq_exp_ℝ ];
  rw [ NormedSpace.exp_eq_tsum_div ] ; exact lt_of_lt_of_le ( by norm_num [ Finset.sum_range_succ, Nat.factorial ] ) ( Summable.sum_le_tsum ( Finset.range 11 ) ( fun _ _ => by positivity ) ( by exact Real.summable_pow_div_factorial _ ) ) ;

private fact pi_gt_31 : Real.pi > 3.1 := by
  -- From `assump_const`, we have that `Real.pi ≤ 3.1`.
  have : Real.pi > 3.14 := Real.pi_gt_d2
  linarith

private fact base_bound_strong : Real.exp (-3 * Real.pi / 4) * 2 < 0.2 := by
  -- We'll use that $e^{-3\pi/4} \cdot 2 < 0.2$ to bound the expression. This follows from the fact that $e^{-3\pi/4} < 0.1$.
  have h_exp : Real.exp (-3 * Real.pi / 4) < 0.1 := by
    rw [ ← Real.log_lt_log_iff ( by positivity ) ] <;> norm_num;
    -- We'll use that $3\pi/4 > \ln 10$.
    have h_pi_gt_log : 3 * Real.pi / 4 > Real.log 10 := by
      have h_pi_gt_log : Real.log 10 < 3 * Real.pi / 4 := by
        have h_log_10_lt_231 : Real.log 10 < 2.31 := by
          exact log_ten_lt_231
        have h_pi_gt_31 : Real.pi > 3.1 := by
          exact pi_gt_31
        norm_num at * ; linarith;
      exact h_pi_gt_log;
    rw [ Real.log_div ] <;> norm_num ; linarith;
  norm_num at * ; linarith

private fact stronger_numeric_bound_for_tail_bound (n : ℕ+) :
  Real.exp (-3 * Real.pi * n / 4) * (2 : ℝ)^(n : ℝ) < (0.2 : ℝ)^(n : ℝ) := by
  set K : ℝ := Real.exp (-3 * Real.pi / 4) * 2;
  have hK : K < 0.2 := by
    have hK : K < 0.2 := by
      exact base_bound_strong;
    exact hK;
  -- Substitute $K < 0.2$ into the inequality.
  have h_sub : K ^ (n : ℝ) < (0.2 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]
    exact pow_lt_pow_left₀ hK ( by positivity ) ( by positivity : ( n : ℕ ) ≠ 0 );
  convert h_sub using 1 ; norm_num [ Real.rpow_mul, Real.rpow_neg, inv_pow ]
  simp [K]; ring_nf;
  rw [← Real.exp_nat_mul]; ring_nf

private fact numeric_bound_strong (n : ℕ+) :
  (Real.exp (-3 * Real.pi * n / 4) * (2 : ℝ)^(n : ℝ)) / (1 - (Real.exp (-3 * Real.pi * n / 4) * (2 : ℝ)^(n : ℝ))) < (0.2 : ℝ)^(n : ℝ) / (1 - (0.2 : ℝ)^(n : ℝ)) := by
    -- Substitute $K = \exp(-3\pi n/4) \cdot 2^n$ and use the bound $K < 0.2^n$.
    set K : ℝ := Real.exp (-3 * Real.pi * n / 4) * 2 ^ (n : ℝ)
    have hK : K < (0.2 : ℝ) ^ (n : ℝ) := by
      have hK : K < (0.2 : ℝ)^(n : ℝ) := by
        have := base_bound_strong
        norm_num +zetaDelta at *;
        convert pow_lt_pow_left₀ this ( by positivity ) ( by positivity : ( n : ℕ ) ≠ 0 ) using 1 ; ring_nf;
        rw [ ← Real.exp_nat_mul ] ; ring_nf;
      exact hK;
    -- Substitute $K < 0.2^n$ into the inequality.
    have h_sub : K / (1 - K) < (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) := by
      gcongr ; norm_num at *;
      exact pow_lt_one₀ ( by norm_num ) ( by norm_num ) ( by positivity );
    exact h_sub

private corollary numeric_bound_weaker (n : ℕ+) :
  (Real.exp (-3 * Real.pi * n / 4) * (2 : ℝ)^(n : ℝ)) / (1 - (Real.exp (-3 * Real.pi * n / 4) * (2 : ℝ)^(n : ℝ))) < (2 : ℝ)^(-(n : ℝ)) * (1 - (2 : ℝ)^(-(n : ℝ))) := by
    set K : ℝ := Real.exp (-3 * Real.pi * n / 4) * 2 ^ (n : ℝ)
    have h_sub : K / (1 - K) < (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) := by
      unfold K
      exact numeric_bound_strong n;
    -- We need to show that $0.2^n / (1 - 0.2^n) \le (1/2)^n * (1 - (1/2)^n)$.
    have h_final : (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) ≤ (1 / 2 : ℝ) ^ (n : ℝ) * (1 - (1 / 2 : ℝ) ^ (n : ℝ)) := by
      rw [ div_le_iff₀ ] <;> norm_num;
      · rcases n with ( _ | _ | n ) <;> norm_num [ pow_succ' ] at *;
        · contradiction;
        · nlinarith only [ show ( 1 / 5 : ℝ ) ^ n ≤ ( 1 / 2 : ℝ ) ^ n by gcongr ; norm_num, show ( 1 / 5 : ℝ ) ^ n ≥ 0 by positivity, show ( 1 / 2 : ℝ ) ^ n ≥ 0 by positivity, show ( 1 / 5 : ℝ ) ^ n ≤ 1 by exact pow_le_one₀ ( by norm_num ) ( by norm_num ), show ( 1 / 2 : ℝ ) ^ n ≤ 1 by exact pow_le_one₀ ( by norm_num ) ( by norm_num ), mul_le_mul_of_nonneg_left ( show ( 1 / 5 : ℝ ) ^ n ≤ ( 1 / 2 : ℝ ) ^ n by gcongr ; norm_num ) ( show ( 0 : ℝ ) ≤ ( 1 / 2 : ℝ ) ^ n by positivity ) ];
      · exact pow_lt_one₀ ( by norm_num ) ( by norm_num ) ( by positivity );
    convert h_sub.trans_le h_final using 1 ; norm_num [ Real.rpow_neg ];
    norm_num [ ← inv_pow ]


/-- The upper bound of `rhoMassOn (0 : 𝓔 n) L (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ` -/
noncomputable abbrev rhoMassTailBoundConst (n : ℕ+) : ℝ :=
  0.2 ^ (n : ℝ) / (1 - 0.2 ^ (n : ℝ))

/-- Handy upperbound for rhoMassTailBoundConst-/
lemma rhoMassTailBoundConst_le_four_rpow_neg (n : ℕ+) :
  rhoMassTailBoundConst n ≤ (4 : ℝ) ^ (-n : ℝ) := by
  -- By simplifying, we can see that the inequality holds for all positive integers n.
  have h_simplify : ∀ n : ℕ+, (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) ≤ (4 : ℝ) ^ (-(n : ℝ)) := by
    intro n; rw [ div_le_iff₀ ] <;> norm_num [ Real.rpow_neg ];
    · induction n using PNat.recOn <;> norm_num [ pow_succ' ] at *;
      nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 5 ) ( ↑‹ℕ+› : ℕ ), pow_le_pow_of_le_one ( by norm_num : ( 0 : ℝ ) ≤ 1 / 5 ) ( by norm_num ) ( show ( ↑‹ℕ+› : ℕ ) ≥ 1 from Nat.one_le_iff_ne_zero.mpr <| PNat.ne_zero _ ) ];
    · exact pow_lt_one₀ ( by norm_num ) ( by norm_num ) ( by positivity );
  exact h_simplify n

end numeric_bounds


/-
  Handy bound relating ρ₁ and ρ₂.
-/
lemma rho_le_exp_mul_rhoS_two_of_norm_ge_sqrt {n : ℕ+} (v : 𝓔 n) (hv : ‖v‖ ≥ Real.sqrt n) :
  rho v ≤ Real.exp (-3 * Real.pi * n / 4) * rhoS 2 v := by
    unfold rhoS at *;
    unfold rho;
    rw [ ← Real.exp_add ];
    norm_num [ norm_smul ];
    nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 from Nat.one_le_cast.mpr n.pos, Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, mul_le_mul_of_nonneg_left hv <| Real.pi_pos.le ]

/-
Bound the mass of the Gaussian on a set by a factor times the mass of the scaled Gaussian on the same set.
-/
lemma rhoMassOn_outside_ball_sqrt_le_exp_mul_rhoSMassOn_two (c : 𝓔 n) (L : EuclideanLattice n n) :
  rhoMassOn c L (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ ≤
  Real.exp (-3 * Real.pi * n / 4) * rhoSMassOn 2 c L (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ := by
    -- Apply the pointwise inequality to each term in the sum.
    rw [←rhoSMassOn_one_eq_rhoMassOn]
    have h_term_le : ∀ v : L.carrier, (Set.indicator (𝔅 0 (Real.sqrt n))ᶜ (rhoS 1)) ((v : 𝓔 n) + c) ≤ (Real.exp (-3 * Real.pi * n / 4)) * (Set.indicator (𝔅 0 (Real.sqrt n))ᶜ (rhoS 2)) ((v : 𝓔 n) + c) := by
      intro v; by_cases hv : ( v : 𝓔 n ) + c ∈ 𝔅 0 ( Real.sqrt n ) <;> simp_all +decide [ Set.indicator ] ;
      convert rho_le_exp_mul_rhoS_two_of_norm_ge_sqrt _ hv using 1 ; ring_nf;
    convert Summable.tsum_le_tsum h_term_le _ _ using 1;
    · rw [ tsum_mul_left, rhoSMassOn ];
      aesop;
    · exact SummationFilter.instNeBotUnconditional ↥L.carrier;
    · convert summable_rhoSMassOn 1 zero_lt_one c L ( 𝔅 0 ( Real.sqrt n ) ) ᶜ using 1;
    · refine' Summable.mul_left _ _;
      convert summable_rhoSMassOn 2 ( by norm_num ) c L ( 𝔅 0 ( Real.sqrt n ) ) ᶜ using 1

/--
  Let Bₙ denote the open Euclidean unit ball. Then, for any lattice L and any s > 0,
    rho(c + L \setminus \sqrt{n} B_n)  < 2^{−n} rho(L),
  where L \setminus \sqrt{n} B_n is the set of lattice points of norm no-shorter than √{n}.
-/
theorem rhoMassOn_outside_ball_sqrt_lt_zero_point_two_rpow_mul_rhoMass (c : 𝓔 n) (L : EuclideanLattice n n) :
  rhoMassOn c L (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ < (0.2 : ℝ)^(n : ℝ) * (rhoMass 0 L) := by
    have := rhoMassOn_outside_ball_sqrt_le_exp_mul_rhoSMassOn_two c L;
    -- Apply Lemma 2 to bound the mass outside the ball.
    have h_bound : rhoMassOn c L (𝔅 0 (Real.sqrt (n : ℝ)))ᶜ ≤ Real.exp (-3 * Real.pi * n / 4) * (2 : ℝ)^(n : ℝ) * rhoSMass 1 0 L := by
      have h_bound : rhoMassOn c L (𝔅 0 (Real.sqrt (n : ℝ)))ᶜ ≤ Real.exp (-3 * Real.pi * n / 4) * rhoSMass 2 c L := by
        have h_bound : rhoSMassOn 2 c L (𝔅 0 (Real.sqrt (n : ℝ)))ᶜ ≤ rhoSMass 2 c L := by
          have h_nonneg : ∀ v : L.carrier, 0 ≤ (𝔅 0 (Real.sqrt (n : ℝ)))ᶜ.indicator (rhoS 2) ((v : 𝓔 n) + c) := by
            intro v; by_cases hv : ( v : 𝓔 n ) + c ∈ ( 𝔅 0 ( Real.sqrt n ) )ᶜ <;> simp +decide [ hv, rhoS ] ;
            exact Real.exp_nonneg _
          apply Summable.tsum_le_tsum ;
          · intro v; by_cases hv : ( v : 𝓔 n ) + c ∈ 𝔅 0 ( Real.sqrt n ) <;> simp_all +decide  ;
            exact Real.exp_nonneg _;
          · convert summable_rhoSMassOn 2 ( by norm_num ) c L ( 𝔅 0 ( Real.sqrt ( n : ℝ ) ) ) ᶜ using 1;
          · convert summable_rhoSMassOn 2 ( by norm_num ) c L Set.univ using 1 ; aesop;
        exact this.trans ( mul_le_mul_of_nonneg_left h_bound <| by positivity );
      have h_bound : rhoSMass 2 c L ≤ 2 ^ (n : ℝ) * rhoSMass 1 0 L := by
        exact le_trans ( rhoSMass_shift_mono L 2 ( by norm_num ) c ) ( by simpa using rhoSMass_scaling_mono 2 ( by norm_num ) L );
      nlinarith [ Real.exp_pos ( -3 * Real.pi * n / 4 ) ];
    have h_bound : Real.exp (-3 * Real.pi * n / 4) * (2 : ℝ)^(n : ℝ) * rhoSMass 1 0 L < (0.2 : ℝ)^(n : ℝ) * rhoSMass 1 0 L := by
      gcongr;
      · refine' lt_of_lt_of_le _ ( Summable.le_tsum _ 0 _ ) <;> norm_num;
        · exact Real.exp_pos _;
        · simp ; convert summable_rhoSMassOn 1 zero_lt_one 0 L Set.univ using 1;
          ext; simp ;
        · exact fun _ _ _ => Real.exp_nonneg _;
      · convert stronger_numeric_bound_for_tail_bound n using 1;
    convert lt_of_le_of_lt ‹_› h_bound using 1
    rw [ rhoSMass_one_eq_rhoMass ]

/-- Handy bound 2^{-n} on rhoMass on lattice points outside ball of radius √n -/
corollary rhoMassOn_outside_ball_sqrt_lt_two_rpow_neg_mul_rhoMass (c : 𝓔 n) (L : EuclideanLattice n n) :
  rhoMassOn c L (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ < (2 : ℝ)^(-n : ℝ) * (rhoMass 0 L) := by
  have : (0.2 : ℝ)^(n : ℝ) < (2 : ℝ)^(-(n : ℝ)) := by
    norm_num [ Real.rpow_def_of_pos ];
    simp +zetaDelta at *;
    -- Since $2 < 5$, we can apply the logarithm function to both sides, preserving the inequality.
    apply Real.log_lt_log; norm_num; norm_num
  have h_bound := rhoMassOn_outside_ball_sqrt_lt_zero_point_two_rpow_mul_rhoMass c L;
  -- By combining the results from h_bound and this, we can conclude the proof.
  apply lt_of_lt_of_le h_bound (mul_le_mul_of_nonneg_right this.le (by
  -- The Gaussian function is non-negative, so the sum of non-negative terms is non-negative.
  apply tsum_nonneg; intro v; exact Real.exp_nonneg _))


/-- Corollary : lattices with long shortest vector have exponentially small Gaussian mass outside the origin -/
theorem rhoMassOn_nonzero_lt_zero_point_two_rpow_div_one_sub_of_shortestVectorLength_ge_sqrt (L : EuclideanLattice n n) (h_svl : L.shortestVectorLength ≥ Real.sqrt (n : ℝ)) :
  rhoMassOn 0 L {0}ᶜ < 0.2 ^ (n : ℝ) / (1 - 0.2 ^ (n : ℝ)) := by
  have h_eq : (L.carrier : Set (𝓔 n)) ∩ {0}ᶜ = (L.carrier : Set (𝓔 n)) ∩ (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ := by
    have h_len : ∀ v : L.carrier, v ≠ 0 → ‖(v : 𝓔 n)‖ ≥ Real.sqrt (n : ℝ) := by
      intro v hv;
      have h_vlen : ‖(v : 𝓔 n)‖ ≥ L.shortestVectorLength := by
        -- Since $v$ is a non-zero lattice point, its norm is in the set of non-zero norms, so the infimum (which is the shortest vector length) must be less than or equal to any element in that set.
        have h_norm_ge_svl : ∀ v : L.carrier, v ≠ 0 → L.shortestVectorLength ≤ ‖(v : LatticeCrypto.Utils.Vec.𝓔 n)‖ := by
          intros v hv_nonzero
          apply ciInf_le_of_le;
          exact ⟨ 0, Set.forall_mem_range.mpr fun _ => norm_nonneg _ ⟩;
          swap;
          -- Since $v$ is non-zero, it is in the set of non-zero vectors, so we can use it directly.
          exact ⟨v, by
            exact ⟨ v.2, by simpa using hv_nonzero ⟩⟩
          generalize_proofs at *;
          simp +zetaDelta at *;
        exact h_norm_ge_svl v hv
      linarith;
    apply Set.ext;
    simp +zetaDelta at *;
    exact fun x hx => ⟨ fun hx' => ( h_len x hx hx' ), fun hx' => by contrapose! hx'; aesop ⟩

  have h_eq' : rhoMassOn 0 L {0}ᶜ = rhoMassOn 0 L (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ := by
    unfold rhoMassOn
    simp +decide [ Set.ext_iff ] at h_eq;
    apply tsum_congr; intro v; simp [Set.indicator];
    specialize h_eq v ; aesop

  have h_concentration := rhoMassOn_outside_ball_sqrt_lt_zero_point_two_rpow_mul_rhoMass 0 L
  rw [←h_eq'] at h_concentration

  have : rhoMass 0 L = 1 + rhoMassOn 0 L {0}ᶜ := by
    have h_eq := rhoSMass_eq_one_add_rhoSMassOn_nonzero L 1 zero_lt_one
    rw [ rhoSMass_one_eq_rhoMass, rhoSMassOn_one_eq_rhoMassOn ] at h_eq
    exact h_eq
  rw [ this ] at h_concentration

  have h1 : rhoMassOn 0 L {0}ᶜ < 0.2 ^ (n : ℝ) + 0.2 ^ (n : ℝ) * rhoMassOn 0 L {0}ᶜ := by
    linarith;
  have h2 : (1 - 0.2 ^ (n : ℝ)) * rhoMassOn 0 L {0}ᶜ < 0.2 ^ (n : ℝ) := by
    linarith;
  have h_final : rhoMassOn 0 L {0}ᶜ < 0.2 ^ (n : ℝ) / (1 - 0.2 ^ (n : ℝ)) := by
    have h_pos : 0 < (1 - (0.2 : ℝ) ^ (n : ℝ)) := by
      exact sub_pos_of_lt ( Real.rpow_lt_one ( by norm_num ) ( by norm_num ) ( by positivity ) );
    rwa [ lt_div_iff₀' h_pos ]
  exact h_final

/-- The weaker but handy bound that's less than 2^{-n} -/
corollary rhoMassOn_nonzero_lt_two_rpow_neg_mul_one_sub_two_rpow_neg_of_shortestVectorLength_ge_sqrt (L : EuclideanLattice n n) (h_svl : L.shortestVectorLength ≥ Real.sqrt (n : ℝ)) :
  rhoMassOn 0 L {0}ᶜ < (2 : ℝ)^(-n : ℝ) * (1 - (2 : ℝ)^(-n : ℝ)) := by
  have h_bound := rhoMassOn_nonzero_lt_zero_point_two_rpow_div_one_sub_of_shortestVectorLength_ge_sqrt L h_svl;
  have h_num_le : (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) ≤ (1 / 2 : ℝ) ^ (n : ℝ) * (1 - (1 / 2 : ℝ) ^ (n : ℝ)) := by
    rw [ div_le_iff₀ ] <;> norm_num;
    · rcases n with ( _ | _ | n ) <;> norm_num [ pow_succ' ] at *;
      · contradiction;
      · nlinarith only [ show ( 1 / 5 : ℝ ) ^ n ≤ ( 1 / 2 : ℝ ) ^ n by gcongr ; norm_num, show ( 1 / 5 : ℝ ) ^ n ≥ 0 by positivity, show ( 1 / 2 : ℝ ) ^ n ≥ 0 by positivity, show ( 1 / 5 : ℝ ) ^ n ≤ 1 by exact pow_le_one₀ ( by norm_num ) ( by norm_num ), show ( 1 / 2 : ℝ ) ^ n ≤ 1 by exact pow_le_one₀ ( by norm_num ) ( by norm_num ), mul_le_mul_of_nonneg_left ( show ( 1 / 5 : ℝ ) ^ n ≤ ( 1 / 2 : ℝ ) ^ n by gcongr ; norm_num ) ( show ( 0 : ℝ ) ≤ ( 1 / 2 : ℝ ) ^ n by positivity ) ];
    · exact pow_lt_one₀ ( by norm_num ) ( by norm_num ) ( by positivity );
  have : (1 / 2 : ℝ) ^ (n : ℝ) = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [one_div, Real.inv_rpow, Real.rpow_neg]; norm_num; norm_num
  rw [ this ] at h_num_le;
  exact lt_of_lt_of_le h_bound h_num_le

/-- Corollary : lattices with long shortest vector have almost uniform rhoMass on the dual cosets -/
corollary rhoMass_dual_le_one_add_two_mul_two_rpow_neg_mul_det_of_shortestVectorLength_ge_sqrt (L : EuclideanLattice n n) (h_svl : L.shortestVectorLength ≥ Real.sqrt (n : ℝ)) (u : 𝓔 n) :
  rhoMass u L.dual ≤ (1 + 2 * (2 : ℝ)^(-n : ℝ)) * L.det := by
  have h_poisson := poisson_summation_rhoS_coset L.dual 1 (by positivity) u
  unfold EuclideanLattice.latticeSum at h_poisson
  have : L.dual.dual.carrier = L.carrier := by
    rw [ L.dual_dual ];
  rw [this] at h_poisson
  have : (1 / L.dual.det : ℂ) = L.det := by
    rw [ EuclideanLattice.dual_det_eq_inv ]; norm_num
  rw [ this, rhoSMass_one_eq_rhoMass ] at h_poisson; norm_num at h_poisson;
  have h_sum_abs : ‖∑' v : L.carrier, cexp (-2 * Real.pi * Complex.I * ⟪u, v⟫) * rho v‖ ≤ ∑' v : L.carrier, rho v := by
    refine' le_trans ( norm_tsum_le_tsum_norm _ ) _;
    · simp_all +decide [ Complex.norm_exp ];
      have h_summable : Summable (fun v : L.carrier => rho v) := by
        have := LatticeCrypto.Foundations.Gaussian.summable_rhoSMassOn 1 zero_lt_one 0 L Set.univ
        simp_all +decide [ LatticeCrypto.Foundations.Gaussian.rhoS, LatticeCrypto.Foundations.Gaussian.rho ];
      exact h_summable.abs;
    · simp_all +decide [ Complex.norm_exp ];
      exact le_of_eq ( tsum_congr fun _ => abs_of_nonneg <| by exact Real.exp_nonneg _ );
  have h_sum_abs : ∑' v : L.carrier, rho v ≤ (1 + 2 * 2 ^ (-(n : ℝ))) := by
    have h_sum_abs : ∑' v : L.carrier, rho v = 1 + ∑' v : L.carrier, if v = 0 then 0 else rho v := by
      rw [ Summable.tsum_eq_add_tsum_ite ];
      congr! 1;
      · unfold Gaussian.rho; norm_num;
      · convert summable_rhoSMassOn 1 zero_lt_one 0 L ( Set.univ : Set ( 𝓔 n ) ) using 1;
        ext; simp [LatticeCrypto.Foundations.Gaussian.rho];
    have h_sum_abs : ∑' v : L.carrier, (if v = 0 then 0 else rho v) ≤ 2 * 2 ^ (-(n : ℝ)) := by
      have h_sum_abs : ∑' v : L.carrier, (if v = 0 then 0 else rho v) ≤ rhoMassOn 0 L {0}ᶜ := by
        simp +decide [ LatticeCrypto.Foundations.Gaussian.rhoMassOn ];
        exact le_of_eq <| tsum_congr fun x => by aesop;
      have := rhoMassOn_nonzero_lt_two_rpow_neg_mul_one_sub_two_rpow_neg_of_shortestVectorLength_ge_sqrt L h_svl;
      exact h_sum_abs.trans ( this.le.trans ( by nlinarith [ Real.rpow_pos_of_pos zero_lt_two ( - ( n : ℝ ) ), Real.rpow_le_rpow_of_exponent_le ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show ( - ( n : ℝ ) ) ≤ 0 by norm_num ) ] ) );
    linarith;
  replace h_poisson := congr_arg Complex.re h_poisson ; norm_num [ Complex.exp_re ] at h_poisson;
  rw [ h_poisson, mul_comm ];
  gcongr;
  · exact L.det_pos.le;
  · refine' le_trans _ h_sum_abs;
    refine' le_trans _ ‹_›;
    convert Complex.re_le_norm _ using 2 ; norm_num [ Complex.exp_neg ];
    exact rfl

/-- Corollary : lattices with long shortest vector have almost uniform rhoMass on the dual cosets -/
corollary rhoMass_dual_ge_one_sub_two_mul_two_rpow_neg_mul_det_of_shortestVectorLength_ge_sqrt (L : EuclideanLattice n n) (h_svl : L.shortestVectorLength ≥ Real.sqrt (n : ℝ)) (u : 𝓔 n) :
  rhoMass u L.dual ≥ (1 - 2 * (2 : ℝ)^(-n : ℝ)) * L.det := by
  have h_poisson := poisson_summation_rhoS_coset L.dual 1 (by positivity) u
  unfold EuclideanLattice.latticeSum at h_poisson
  have : L.dual.dual.carrier = L.carrier := by
    rw [ L.dual_dual ];
  rw [this] at h_poisson
  have : (1 / L.dual.det : ℂ) = L.det := by
    rw [ EuclideanLattice.dual_det_eq_inv ]; norm_num
  rw [ this, rhoSMass_one_eq_rhoMass ] at h_poisson; norm_num at h_poisson;
  -- The term for `v = 0` is `exp(0) * rho(0) = 1`.
  have h_v_zero : (rhoMass u (L.dual) : ℝ) ≥ (L.det : ℝ) * (1 - rhoMassOn 0 L {0}ᶜ) := by
    -- The sum is L.det * ∑_{v ∈ L} exp(-2πi ⟨u, v⟩) * rho(v).
    have h_sum : (rhoMass u (L.dual) : ℝ) = (L.det : ℝ) * (∑' v : ↥L.carrier, cexp (-2 * Real.pi * Complex.I * inner ℝ u v) * rho (v : 𝓔 n)) := by
      aesop;
    -- The sum is L.det * ∑_{v ∈ L} exp(-2πi ⟨u, v⟩) * rho(v). We separate the v=0 term from the sum.
    have h_sum_separated : (rhoMass u (L.dual) : ℝ) = (L.det : ℝ) * (1 + ∑' v : ↥L.carrier, if v = 0 then 0 else cexp (-2 * Real.pi * Complex.I * inner ℝ u v) * rho (v : 𝓔 n)) := by
      rw [ h_sum, Summable.tsum_eq_add_tsum_ite ];
      field_simp;
      · norm_num [ Gaussian.rho ];
      · contrapose! h_sum;
        -- If the sum is not summable, then the Gaussian mass would be zero, which contradicts the assumption that the Gaussian mass is positive.
        have h_gauss_mass_pos : 0 < LatticeCrypto.Foundations.Gaussian.rhoMass u L.dual := by
          apply_rules [ Summable.tsum_pos ];
          rotate_right;
          exact ⟨ 0, by simp +decide ⟩;
          · convert summable_rhoSMassOn 1 zero_lt_one u L.dual ( Set.univ ) using 1;
            ext; simp +decide  ;
          · exact fun _ => Real.exp_nonneg _;
          · exact Real.exp_pos _;
        rw [ tsum_eq_zero_of_not_summable h_sum ] ; norm_num [ h_gauss_mass_pos.ne' ];
    -- The magnitude of the sum is bounded by the sum of the magnitudes.
    have h_sum_abs : ‖∑' v : ↥L.carrier, if v = 0 then 0 else cexp (-2 * Real.pi * Complex.I * inner ℝ u v) * rho (v : 𝓔 n)‖ ≤ ∑' v : ↥L.carrier, if v = 0 then 0 else rho (v : 𝓔 n) := by
      convert norm_tsum_le_tsum_norm _ <;> norm_num [ Complex.norm_exp ];
      · split_ifs <;> norm_num [ Complex.norm_exp ];
        exact Eq.symm ( abs_of_nonneg ( Real.exp_nonneg _ ) );
      · refine' Summable.of_nonneg_of_le ( fun v => norm_nonneg _ ) ( fun v => _ ) ( show Summable fun v : L.carrier => ( rho ( v : 𝓔 n ) : ℝ ) from _ );
        · split_ifs <;> simp_all +decide [ Complex.norm_exp ];
          · exact Real.exp_nonneg _;
          · rw [ abs_of_nonneg ( by exact Real.exp_pos _ |> le_of_lt ) ];
        · convert summable_rhoSMassOn 1 zero_lt_one 0 L Set.univ using 1 ; norm_num [ rhoMassOn ];
    -- The sum of the magnitudes is bounded by rhoMassOn 0 L {0}ᶜ.
    have h_sum_abs_le : ∑' v : ↥L.carrier, (if v = 0 then 0 else rho (v : 𝓔 n)) = rhoMassOn 0 L {0}ᶜ := by
      simp [rhoMassOn];
      exact tsum_congr fun v => by by_cases hv : v = 0 <;> simp +decide [ hv ] ;
    norm_num [ Complex.ext_iff ] at *;
    rw [ h_sum_separated.1 ];
    exact mul_le_mul_of_nonneg_left ( by linarith [ abs_le.mp ( Complex.abs_re_le_norm ( ∑' v : L.carrier, if v = 0 then 0 else cexp ( - ( 2 * Real.pi * Complex.I * ⟪u, ( v : 𝓔 n)⟫ ) ) * ( rho ( v : 𝓔 n ) : ℂ ) ) ) ] ) ( show 0 ≤ L.det from by exact le_of_lt L.det_pos );
  -- Use `rhoMassOn_nonzero_lt_two_rpow_neg_mul_one_sub_two_rpow_neg_of_shortestVectorLength_ge_sqrt` to bound `rhoMassOn 0 L {0}ᶜ < 2^{-n} * (1 - 2^{-n}) < 2^{-n}`.
  have h_rhoMassOn_zero : rhoMassOn 0 L {0}ᶜ < (2 : ℝ)^(-n : ℝ) := by
    exact lt_of_lt_of_le ( rhoMassOn_nonzero_lt_two_rpow_neg_mul_one_sub_two_rpow_neg_of_shortestVectorLength_ge_sqrt L h_svl ) ( by norm_num [ Real.rpow_neg ] );
  nlinarith [ show ( L.det : ℝ ) ≥ 0 by exact_mod_cast L.det_pos.le, show ( 2 : ℝ ) ^ ( - ( n : ℝ ) ) ≥ 0 by positivity ]


end concentration

noncomputable section tailbound_smoothing

open scoped Real Complex MeasureTheory
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Foundations.Gaussian
open LatticeCrypto.Foundations.Lattice

/-- Handy bound 4^{-n} on rhoMass on nonzero lattice points -/
lemma rhoMassOn_nonzero_le_four_rpow_neg_of_succMin₁_ge_sqrt {n : ℕ+} (L : EuclideanLattice n n) (h : L.succMin₁ ≥ Real.sqrt n) :
  rhoMassOn (0 : 𝓔 n) L {0}ᶜ ≤ (4 : ℝ) ^ (-(n : ℝ)) := by
  -- Let $M = \rho(L \setminus \{0\})$.
  have : L.succMin₁ = L.shortestVectorLength := by exact L.successiveMinima_one
  rw [ this ] at h
  -- By the previous steps, we have $M \leq (0.2)^n / (1 - (0.2)^n)$.
  have h_M_le : rhoMassOn (0 : 𝓔 n) L {0}ᶜ < (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) := by
    exact rhoMassOn_nonzero_lt_zero_point_two_rpow_div_one_sub_of_shortestVectorLength_ge_sqrt L h;
  have : (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) ≤ (4 : ℝ) ^ (-(n : ℝ)) := by
    -- By simplifying, we can see that the inequality holds for all positive integers n.
    have h_simplify : ∀ n : ℕ+, (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) ≤ (4 : ℝ) ^ (-(n : ℝ)) := by
      intro n; rw [ div_le_iff₀ ] <;> norm_num [ Real.rpow_neg ];
      · induction n using PNat.recOn <;> norm_num [ pow_succ' ] at *;
        nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 5 ) ( ↑‹ℕ+› : ℕ ), pow_le_pow_of_le_one ( by norm_num : ( 0 : ℝ ) ≤ 1 / 5 ) ( by norm_num ) ( show ( ↑‹ℕ+› : ℕ ) ≥ 1 from Nat.one_le_iff_ne_zero.mpr <| PNat.ne_zero _ ) ];
      · exact pow_lt_one₀ ( by norm_num ) ( by norm_num ) ( by positivity );
    exact h_simplify n
  linarith

end tailbound_smoothing

noncomputable section tight_upperbound

open scoped Real Complex MeasureTheory
open scoped RealInnerProductSpace
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Foundations.Gaussian
open LatticeCrypto.Foundations.Lattice


variable {n : ℕ+} (L : EuclideanLattice n n) (s : ℝ)

set_option linter.unusedVariables false in
/-- Affine (open) half-space -/
def AffineHalfSpace (u : 𝓔 n) (hu : ‖u‖ = 1) (t : ℝ) : Set (𝓔 n) :=
  { x : 𝓔 n | inner ℝ u x < t }

abbrev 𝓗 (u : 𝓔 n) (hu : ‖u‖ = 1) (t : ℝ) := AffineHalfSpace u hu t

/-
Algebraic identity for completing the square in the exponent.
-/
private lemma square_completion {n : ℕ+} (v u : 𝓔 n) (t : ℝ) (hu : ‖u‖ = 1) :
    -π * ‖v‖^2 + 2 * π * inner ℝ v (t • u) = -π * ‖v - t • u‖^2 + π * t^2 := by
      norm_num [ @norm_sub_sq ℝ ];
      rw [ norm_smul, hu ] ; ring_nf;
      norm_num [ Real.norm_eq_abs ];
      ring

/-
Pointwise inequality for the Gaussian terms in the half-space tail bound.
-/
private lemma gaussian_ineq {n : ℕ+} (v u : 𝓔 n) (t : ℝ) (hu : ‖u‖ = 1) (h : inner ℝ u v ≥ t) (ht : t ≥ 0) :
    Real.exp (-Real.pi * ‖v‖^2) ≤ Real.exp (-Real.pi * t^2) * Real.exp (-Real.pi * ‖v - t • u‖^2) := by
  rw [ ← Real.exp_add ];
  -- Substitute the expression for ‖v - t • u‖^2 into the inequality.
  have h_sub : ‖v‖^2 ≥ t^2 + ‖v - t • u‖^2 := by
    rw [ @norm_sub_sq ℝ ];
    simp_all +decide [ norm_smul, inner_smul_right ];
    rw [ real_inner_comm ] ; nlinarith;
  exact Real.exp_le_exp.mpr ( by nlinarith [ Real.pi_pos ] )

/-
Intermediate bound: mass outside half-space is bounded by shifted mass times exponential factor.
-/
protected lemma rhoMassOn_compl_affineHalfSpace_le_exp_neg_pi_mul_sq_mul_rhoMass_shifted {n : ℕ+} (L : EuclideanLattice n n) (u : 𝓔 n) (hu : ‖u‖ = 1) (t : ℝ) (ht : t ≥ 0) (x : 𝓔 n) :
    rhoMassOn x L (𝓗 u hu t)ᶜ ≤ Real.exp (-Real.pi * t ^ 2) * rhoMass (x - t • u) L := by
  convert Summable.tsum_le_tsum _ _ _ using 1;
  rw [ tsum_mul_left ];
  congr! 1;
  all_goals try infer_instance;
  · intro v;
    by_cases hv : inner ℝ u ( v + x ) ≥ t <;> simp_all +decide [ Set.indicator ];
    · rw [ if_pos ];
      · convert gaussian_ineq _ _ _ hu _ ht using 1;
        · norm_num [ rhoST ];
          rw [ show ( v : 𝓔 n ) + ( x - t • u ) = ( v : 𝓔 n ) + x - t • u by abel1 ] ; unfold rho; norm_num [ Real.exp_neg, mul_comm ] ;
        · aesop;
      · exact fun h => hv.not_gt <| by simpa using h.out;
    · rw [ if_neg ];
      · exact mul_nonneg ( Real.exp_nonneg _ ) ( Real.exp_nonneg _ );
      · exact fun h => hv.not_ge <| by simpa [ hu ] using h ( by simpa [ hu ] ) ;
  · convert summable_rhoMassOn x L ( 𝓗 u hu t ) ᶜ using 1;
  · refine' Summable.mul_left _ _;
    convert summable_rhoMassOn ( x - t • u ) L ( Set.univ : Set ( 𝓔 n ) ) using 1;
       ext; simp

/-
For any lattice L, unit vector u ∈ R n, real t ≥ 0, and x ∈ R^n, we have that
ρ((x + L) \setminus 𝓗 u t) ≤ exp(−πt^2) * ρ(L).
-/
theorem rhoMassOn_compl_affineHalfSpace_le_exp_neg_pi_mul_sq_mul_rhoMass {n : ℕ+} (L : EuclideanLattice n n) (u : 𝓔 n) (hu : ‖u‖ = 1) (t : ℝ) (ht : t ≥ 0) (x : 𝓔 n) :
    rhoMassOn (x : 𝓔 n) L (𝓗 u hu t)ᶜ ≤ Real.exp (-Real.pi * t ^ 2) * rhoMass 0 L := by
  have := @rhoSMass_shift_mono n L 1 zero_lt_one ( x - t • u );
  rw [rhoSMass_one_eq_rhoMass] at this ;
  convert le_trans ( Gaussian.rhoMassOn_compl_affineHalfSpace_le_exp_neg_pi_mul_sq_mul_rhoMass_shifted L u hu t ht x ) ( mul_le_mul_of_nonneg_left this <| by positivity ) using 1
  rw [rhoSMass_one_eq_rhoMass]

/-
For any non-zero vector w in the dual lattice and any basis v of the primal lattice, there is a basis vector v_i such that |<w, v_i>| >= 1.
-/
private lemma exists_dual_inner_ge_one {n : ℕ+} (L : EuclideanLattice n n) (w : 𝓔 n)
    (hw : w ∈ L.dual.carrier) (hw_ne : w ≠ 0)
    (v : Fin n → 𝓔 n) (hv_li : LinearIndependent ℝ v) (hv_mem : ∀ i, v i ∈ L.carrier) :
    ∃ i, 1 ≤ |inner ℝ w (v i)| := by
      -- Since $w$ is in the dual lattice and $v_i$ are in the primal lattice, the inner product $\langle w, v_i \rangle$ is an integer for all $i$.
      have h_int : ∀ i, ∃ k : ℤ, inner ℝ w (v i) = k := by
        norm_num +zetaDelta at *;
        intro i;
        convert EuclideanLattice.inner_lattice_dual_int L ( v i ) w ( by simpa using hv_mem i ) ( by simpa using hw ) using 1;
        norm_num [ real_inner_comm ];
      -- Since $w$ is non-zero, there must exist some $i$ such that $\langle w, v_i \rangle \neq 0$.
      obtain ⟨i, hi⟩ : ∃ i, inner ℝ w (v i) ≠ 0 := by
        by_contra h_contra; push_neg at h_contra; (
        -- Since $v$ is a basis, we can write $w$ as a linear combination of the $v_i$.
        obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, w = ∑ i, c i • v i := by
          have h_basis : Submodule.span ℝ (Set.range v) = ⊤ := by
            refine' Submodule.eq_top_of_finrank_eq _;
            rw [ finrank_span_eq_card ] <;> aesop;
          have := h_basis.ge ( Submodule.mem_top : w ∈ ⊤ ) ; rw [ Submodule.mem_span_range_iff_exists_fun ] at this; tauto;
        have h_zero : ⟪w, w⟫ = 0 := by
          simp_all +decide [ inner_sum, inner_smul_right ];
        exact hw_ne ( by simpa [ inner_self_eq_norm_sq_to_K ] using h_zero ));
      exact ⟨ i, by obtain ⟨ k, hk ⟩ := h_int i; norm_num [ hk ] ; exact mod_cast abs_pos.mpr ( show ( k : ℝ ) ≠ 0 from mod_cast by aesop ) ⟩

/-
Any non-zero lattice vector is in the complement of at least one of the halfspaces defined by u_i or -u_i.
-/
private lemma covering_of_nonzero {n : ℕ+} (L : EuclideanLattice n n)
    (u : Fin n → 𝓔 n) (hu : ∀ i, ‖u i‖ = 1) (t : ℝ)
    (h_cover : ∀ w ∈ L.carrier, w ≠ 0 → ∃ i, |inner ℝ w (u i)| ≥ t) :
    ∀ w ∈ L.carrier, w ≠ 0 → ∃ i, w ∈ (AffineHalfSpace (u i) (hu i) t)ᶜ ∨ w ∈ (AffineHalfSpace (-(u i)) (by simp [hu]) t)ᶜ := by
      intro w hw hw'; rcases h_cover w hw hw' with ⟨ i, hi ⟩ ; use i; cases abs_cases ( ⟪w, u i⟫ ) <;> simp_all +decide [ AffineHalfSpace ] ;
      · exact Or.inl ( by rwa [ real_inner_comm ] );
      · exact Or.inr ( by rw [ real_inner_comm ] ; linarith )

/-
The Gaussian mass of a union of sets is at most the sum of the Gaussian masses of the individual sets.
-/
lemma rhoMassOn_iUnion_le_sum {n : ℕ+} (L : EuclideanLattice n n) {ι : Type*} [Fintype ι] (S : ι → Set (𝓔 n)) :
    rhoMassOn 0 L (⋃ i, S i) ≤ ∑ i, rhoMassOn 0 L (S i) := by
  -- By definition of rhoMassOn, we can expand the left-hand side as a sum over lattice vectors.
  simp [rhoMassOn];
  have h_union_expansion : ∀ v : L.carrier, (⋃ i, S i).indicator rho (v : 𝓔 n) ≤ ∑ i, (S i).indicator rho (v : 𝓔 n) := by
    intro v
    simp [Set.indicator];
    split_ifs <;> simp_all +decide [ Finset.sum_ite ];
    exact le_mul_of_one_le_left ( by exact le_of_lt ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by unfold rho; positivity ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ( mod_cast Finset.card_pos.mpr ⟨ Classical.choose ‹∃ i, ( v : 𝓔 n ) ∈ S i›, by simpa using Classical.choose_spec ‹∃ i, ( v : 𝓔 n ) ∈ S i› ⟩ );
  -- By definition of summability, we can interchange the order of summation.
  have h_summable : Summable (fun v : L.carrier => (⋃ i, S i).indicator rho (v : 𝓔 n)) ∧ ∀ i, Summable (fun v : L.carrier => (S i).indicator rho (v : 𝓔 n)) := by
    have h_summable : Summable (fun v : L.carrier => rho (v : 𝓔 n)) := by
      convert summable_rhoMassOn 0 L _ using 1;
      swap;
      exact Set.univ;
      aesop;
    refine' ⟨ _, fun i => _ ⟩;
    · refine' .of_nonneg_of_le ( fun v => _ ) ( fun v => _ ) h_summable;
      · exact Set.indicator_nonneg ( fun _ _ => Real.exp_nonneg _ ) _;
      · by_cases hv : ( v : 𝓔 n ) ∈ ⋃ i, S i <;> simp +decide [ hv ];
        exact Real.exp_nonneg _;
    · refine' Summable.of_nonneg_of_le ( fun v => _ ) ( fun v => _ ) h_summable;
      · by_cases hi : v.val ∈ S i <;> simp +decide [ hi ];
        exact Real.exp_nonneg _;
      · by_cases hi : v.val ∈ S i <;> simp +decide [ hi ];
        exact Real.exp_nonneg _;
  have h_summable : ∑' v : L.carrier, (⋃ i, S i).indicator rho (v : 𝓔 n) ≤ ∑' v : L.carrier, ∑ i, (S i).indicator rho (v : 𝓔 n) := by
    apply_rules [ Summable.tsum_le_tsum ];
    · exact h_summable.1;
    · exact summable_sum fun i _ => h_summable.2 i;
  have h_fubini : ∑' v : L.carrier, ∑ i, (S i).indicator rho (v : 𝓔 n) = ∑ i, ∑' v : L.carrier, (S i).indicator rho (v : 𝓔 n) := by
    have h_fubini : ∀ {f : ι → L.carrier → ℝ}, (∀ i, Summable (fun v : L.carrier => f i v)) → (∑' v : L.carrier, ∑ i, f i v) = ∑ i, ∑' v : L.carrier, f i v := by
      exact fun {f} a => Summable.tsum_finsetSum fun i a_1 => a i;
    exact h_fubini fun i => by tauto;
  convert h_summable.trans_eq h_fubini using 1

/-
If every non-zero lattice vector is outside at least one of the slabs defined by u_i and t, then the total Gaussian mass of non-zero vectors is bounded by the sum of the masses outside each halfspace.
-/
private lemma rhoMass_le_sum_halfspaces {n : ℕ+} (L : EuclideanLattice n n)
  (u : Fin n → 𝓔 n) (hu : ∀ i, ‖u i‖ = 1) (t : ℝ)
  (h_cover : ∀ w ∈ L.carrier, w ≠ 0 → ∃ i, |inner ℝ w (u i)| ≥ t) :
  rhoMassOn 0 L {0}ᶜ ≤ ∑ i : Fin n, (rhoMassOn 0 L (AffineHalfSpace (u i) (hu i) t)ᶜ + rhoMassOn 0 L (AffineHalfSpace (-(u i)) (by simp [hu]) t)ᶜ) := by

  have h_union : {0}ᶜ ∩ (L.carrier : Set (𝓔 n)) ⊆ ⋃ i, ((AffineHalfSpace (u i) (hu i) t)ᶜ ∪ (AffineHalfSpace (-(u i)) (by
  rw [ norm_neg, hu ]) t)ᶜ) := by
    intros w hw;
    rcases h_cover _ hw.2 hw.1 with ⟨ i, hi ⟩ ; simp_all +decide [ AffineHalfSpace ];
    exact ⟨ i, by rw [ real_inner_comm ] ; cases abs_cases ( ⟪w, u i⟫ ) <;> first | left; linarith | right; linarith ⟩
  generalize_proofs at *;
  refine' le_trans ( _ : _ ≤ _ ) ( _ : _ ≤ _ );
  exact rhoMassOn 0 L ( ⋃ i, ( AffineHalfSpace ( u i ) ( hu i ) t ) ᶜ ∪ ( AffineHalfSpace ( -u i ) ( by simpa using ‹∀ i, ‖-u i‖ = 1› i ) t ) ᶜ );
  · apply_rules [ Summable.tsum_le_tsum ];
    · intro i; by_cases hi : ( i : 𝓔 n ) = 0 <;> simp_all +decide [ Set.indicator ] ;
      · split_ifs <;> norm_num [ rhoST ];
        exact Real.exp_nonneg _;
      · rw [ if_pos ];
        convert h_union ⟨ _, _ ⟩ <;> aesop;
    · convert summable_rhoMassOn 0 L { 0 } ᶜ using 1;
    · convert summable_rhoMassOn 0 L _;
  · refine' le_trans ( _ : _ ≤ _ ) ( Finset.sum_le_sum fun i _ => _ );
    convert rhoMassOn_iUnion_le_sum L _;
    convert rhoMassOn_iUnion_le_sum L _;
    any_goals exact Fin 2;
    rotate_right;
    use fun j => if j = 0 then ( AffineHalfSpace ( u i ) ( hu i ) t ) ᶜ else ( AffineHalfSpace ( -u i ) ( by simpa using ‹∀ i, ‖-u i‖ = 1› i ) t ) ᶜ;
    all_goals try infer_instance;
    · ext; simp ;
    · rw [ Fin.sum_univ_two ] ; aesop

/-
If the non-zero lattice vectors are covered by the complements of halfspaces defined by `u_i` and `t`, then the Gaussian mass of the non-zero vectors is bounded by `2n * exp(-pi * t^2) * rho(L)`.
-/
private lemma rhoMass_nonzero_bound_of_covering {n : ℕ+} (L : EuclideanLattice n n)
  (u : Fin n → 𝓔 n) (hu : ∀ i, ‖u i‖ = 1) (t : ℝ) (ht : t ≥ 0)
  (h_cover : ∀ w ∈ L.carrier, w ≠ 0 → ∃ i, |inner ℝ w (u i)| ≥ t) :
  rhoMassOn 0 L {0}ᶜ ≤ 2 * n * Real.exp (-Real.pi * t^2) * rhoMass 0 L := by

  -- Applying the lemma `rhoMassOn_compl_affineHalfSpace_le_exp_neg_pi_mul_sq_mul_rhoMass` to each halfspace.
  have h_bound : ∀ i, rhoMassOn 0 L (AffineHalfSpace (u i) (hu i) t)ᶜ ≤ Real.exp (-Real.pi * t^2) * rhoMass 0 L := by
    exact fun i => rhoMassOn_compl_affineHalfSpace_le_exp_neg_pi_mul_sq_mul_rhoMass L (u i) (hu i) t ht 0;
  convert le_trans ( rhoMass_le_sum_halfspaces L u hu t h_cover ) ?_;
  refine' le_trans ( Finset.sum_le_sum fun i _ => add_le_add ( h_bound i ) _ ) _;
  use fun i => Real.exp ( -Real.pi * t ^ 2 ) * rhoMass 0 L;
  · convert rhoMassOn_compl_affineHalfSpace_le_exp_neg_pi_mul_sq_mul_rhoMass L ( -u i ) ( by simpa using hu i ) t ht 0 using 1;
  · norm_num ; ring_nf ; norm_num

/-
If the n-th successive minimum of L is at most 1/t, then the Gaussian mass of the non-zero dual vectors is bounded by 2n * exp(-pi * t^2) * rho(L*).
-/
lemma rhoMassOn_nonzero_dual_le_of_succMinₙ_le_inv {n : ℕ+} (L : EuclideanLattice n n) (t : ℝ) (ht : t > 0)
  (h_lambda : L.succMinₙ ≤ 1 / t) :
  rhoMassOn 0 L.dual {0}ᶜ ≤ 2 * n * Real.exp (-Real.pi * t^2) * rhoMass 0 L.dual := by
  -- By definition of successive minima, there exist vectors $v_i \in L$ such that $\|v_i\| = \lambda_i(L)$ and these vectors are linearly independent.
  obtain ⟨v, hv⟩ : ∃ v : Fin n → 𝓔 n, LinearIndependent ℝ v ∧ (∀ i, v i ∈ L.carrier) ∧ (∀ i, ‖v i‖ ≤ 1 / t) := by
    have := L.linearIndependent_successiveMinima_attained;
    obtain ⟨ v, hv₁, hv₂ ⟩ := this;
    refine' ⟨ v, hv₂, fun i => _, fun i => _ ⟩;
    · exact hv₁ i |>.1.1;
    · have := h_lambda;
      refine' le_trans _ this;
      have h_succMin_le : ∀ i j : Fin n, i ≤ j → L.successiveMinima i ≤ L.successiveMinima j := by
        exact fun i j a => EuclideanLattice.successiveMinima_mono L a;
      exact hv₁ i |>.2.symm ▸ h_succMin_le _ _ ( Nat.le_pred_of_lt i.2 );
  -- Let $u_i = v_i / \|v_i\|$.
  obtain ⟨u, hu⟩ : ∃ u : Fin n → 𝓔 n, (∀ i, ‖u i‖ = 1) ∧ (∀ i, u i = (1 / ‖v i‖) • v i) := by
    use fun i => (1 / ‖v i‖) • v i;
    norm_num +zetaDelta at *;
    intro i; rw [ norm_smul, norm_inv, norm_norm ] ; by_cases hi : v i = 0 <;> simp_all +decide [ hv.1.ne_zero ] ;
  -- For any $w \in L^* \setminus \{0\}$, by `exists_dual_inner_ge_one`, there exists $i$ such that $|\langle w, v_i \rangle| \ge 1$.
  have h_cover : ∀ w ∈ L.dual.carrier, w ≠ 0 → ∃ i, |inner ℝ w (u i)| ≥ t := by
    intros w hw hw_ne_zero
    obtain ⟨i, hi⟩ : ∃ i, 1 ≤ |inner ℝ w (v i)| := by
      apply exists_dual_inner_ge_one L w hw hw_ne_zero v hv.1 hv.2.1;
    use i; simp_all +decide [ inner_smul_right ];
    rw [ inv_mul_eq_div, le_div_iff₀ ] <;> nlinarith [ norm_pos_iff.mpr ( show v i ≠ 0 from by intro h; norm_num [ h ] at hi ), hv.2.2 i, mul_inv_cancel₀ ( ne_of_gt ht ) ];
  convert rhoMass_nonzero_bound_of_covering L.dual u hu.1 t ht.le h_cover using 1

/-
If the scaled n-th successive minimum is small enough, the Gaussian mass of the dual tail is bounded.
-/
lemma rhoSMassOn_nonzero_dual_le_of_succMinₙ_div_le_inv {n : ℕ+} (L : EuclideanLattice n n) (s t : ℝ) (hs : s > 0) (ht : t > 0)
    (h_lambda : L.succMinₙ / s ≤ 1 / t) :
    rhoSMassOn (1 / s) 0 L.dual {0}ᶜ ≤ 2 * n * Real.exp (-Real.pi * t^2) * rhoSMass (1 / s) 0 L.dual := by
      convert rhoMassOn_nonzero_dual_le_of_succMinₙ_le_inv ( L.smul ( 1/s ) ( by positivity ) ) t ht _ using 1;
      · rw [ rhoSMassOn_scale ];
        -- Since the dual of a lattice scaled by $c$ is the dual of the original lattice scaled by $1/c$, we have:
        have h_dual_smul : (L.smul (1 / s) (by positivity)).dual ≡ᵤ L.dual.smul s (by positivity) := by
          convert L.dual_of_smul_eq_dual_smul_inv ( 1 / s ) ( by positivity ) using 1;
          norm_num;
        have h_dual_smul : ∀ (L L' : EuclideanLattice n n) (S : Set (𝓔 n)), L ≡ᵤ L' → rhoMassOn 0 L S = rhoMassOn 0 L' S := by
          intros L L' S hL_L'
          simp [rhoMassOn];
          unfold EuclideanLattice.latticeSum;
          have h_dual_smul : L.carrier = L'.carrier := by
            exact hL_L';
          rw [ h_dual_smul ];
        convert h_dual_smul _ _ _ ‹_› |> Eq.symm using 1;
        congr! 1;
        ext; simp [Set.mem_smul_set];
        exact ⟨ fun hx => ⟨ ( 1 / s ) • ‹_›, by simpa [ hs.ne' ] using hx, by simp +decide [ hs.ne' ] ⟩, by rintro ⟨ y, hy, rfl ⟩ ; simpa [ hs.ne' ] using hy ⟩;
      · congr! 1;
        have h_dual_smul : (L.smul (1 / s) (by positivity)).dual ≡ᵤ L.dual.smul s (by positivity) := by
          convert L.dual_of_smul_eq_dual_smul_inv ( 1 / s ) ( by positivity ) using 1;
          norm_num;
        have h_dual_smul : ∀ (L L' : EuclideanLattice n n), L ≡ᵤ L' → rhoMass 0 L = rhoMass 0 L' := by
          intros L L' h_equiv;
          unfold rhoMass;
          unfold EuclideanLattice.latticeSum;
          have h_dual_smul : L.carrier = L'.carrier := by
            exact h_equiv;
          rw [ h_dual_smul ];
        convert h_dual_smul _ _ ‹_› |> Eq.symm using 1;
        exact rhoSMass_scale s hs L.dual;
      · refine' le_trans _ h_lambda;
        -- Apply the lemma that states the n-th successive minimum of a scaled lattice is the original n-th successive minimum multiplied by the scaling factor.
        have h_succMinₙ_smul : ∀ (L : EuclideanLattice n n) (s : ℝ) (hs : s > 0), (L.smul s hs.ne').succMinₙ = s * L.succMinₙ := by
          exact fun L s hs =>
            EuclideanLattice.successiveMinima_scale L ⟨↑n - 1, EuclideanLattice.succMinₙ._proof_1⟩ s
              hs;
        rw [ h_succMinₙ_smul L ( 1 / s ) ( one_div_pos.mpr hs ), one_div, inv_mul_eq_div ]


end tight_upperbound

end LatticeCrypto.Foundations.Gaussian
