import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

import LatticeCrypto.Foundations.Gaussian.Defs
import LatticeCrypto.Foundations.Gaussian.Fourier
import LatticeCrypto.Foundations.Gaussian.PoissonSummation
import LatticeCrypto.Foundations.Lattice.Distance
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec


namespace LatticeCrypto.Foundations.Gaussian

/-!
  # Tail bounds for Discrete Gaussians
  * `rhoMass_outside_ball_stronger`:  Let Bₙ denote the open Euclidean unit ball. Then, for any lattice L and any s > 0, then we have rho(c + L \setminus \sqrt{n} B_n)  < (0.2)^n rho(L),
  where $L \setminus \sqrt{n} B_n$ is the set of lattice points of norm no-shorter than √{n}.
  * `rhoMass_outside_ball`: Weaker similar bound but with 2^{-n} instead of (0.2)^n.
  * Corollary `rhoMass_with_long_sv_stronger` : lattices with long shortest vector have exponentially small Gaussian mass outside the origin: `L.shortestVectorLength ≥ Real.sqrt (n : ℝ))` implies
    `rhoMassOn 0 L {0}ᶜ < 0.2 ^ (n : ℝ) / (1 - 0.2 ^ (n : ℝ))`
  * Corollary `rhoMass_with_long_sv` : weaker similar bound but with 2^{-n} instead of (0.2)^n

  The tail bounds also have some uniformity implications for discrete Gaussians over lattices with long shortest vector.
  * `rhoMass_ub_on_dual_with_long_sv`: lattices with long shortest vector have upperbounded rhoMass on the dual cosets: `L.shortestVectorLength ≥ Real.sqrt (n : ℝ)) (u : 𝓔 n)` →
    `rhoMass u L.dual ≤ (1 + 2 * (2 : ℝ)^(-n : ℝ)) * L.det`
  * `rhoMass_lb_on_dual_with_long_sv`: lattices with long shortest vector have lowerbounded rhoMass on the dual cosets: `L.shortestVectorLength ≥ Real.sqrt (n : ℝ)) (u : 𝓔 n)` →
    `rhoMass u L.dual ≥ (1 - 2 * (2 : ℝ)^(-n : ℝ)) * L.det`
--/
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
lemma rhoMassTailBoundConst_le_4_pow_neg_n (n : ℕ+) :
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
lemma rho_le_rhoS_mul_factor {n : ℕ+} (v : 𝓔 n) (hv : ‖v‖ ≥ Real.sqrt n) :
  rho v ≤ Real.exp (-3 * Real.pi * n / 4) * rhoS 2 v := by
    unfold rhoS at *;
    unfold rho;
    rw [ ← Real.exp_add ];
    norm_num [ norm_smul ];
    nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 from Nat.one_le_cast.mpr n.pos, Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, mul_le_mul_of_nonneg_left hv <| Real.pi_pos.le ]

/-
Bound the mass of the Gaussian on a set by a factor times the mass of the scaled Gaussian on the same set.
-/
lemma rhoMassOn_le_factor_mul_rhoSMassOn (c : 𝓔 n) (L : EuclideanLattice n n) :
  rhoMassOn c L (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ ≤
  Real.exp (-3 * Real.pi * n / 4) * rhoSMassOn 2 c L (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ := by
    -- Apply the pointwise inequality to each term in the sum.
    rw [←rhoSMassOn_one_eq_rhoMassOn]
    have h_term_le : ∀ v : L.carrier, (Set.indicator (𝔅 0 (Real.sqrt n))ᶜ (rhoS 1)) ((v : 𝓔 n) + c) ≤ (Real.exp (-3 * Real.pi * n / 4)) * (Set.indicator (𝔅 0 (Real.sqrt n))ᶜ (rhoS 2)) ((v : 𝓔 n) + c) := by
      intro v; by_cases hv : ( v : 𝓔 n ) + c ∈ 𝔅 0 ( Real.sqrt n ) <;> simp_all +decide [ Set.indicator ] ;
      convert rho_le_rhoS_mul_factor _ hv using 1 ; ring_nf;
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
theorem rhoMass_outside_ball_stronger (c : 𝓔 n) (L : EuclideanLattice n n) :
  rhoMassOn c L (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ < (0.2 : ℝ)^(n : ℝ) * (rhoMass 0 L) := by
    have := rhoMassOn_le_factor_mul_rhoSMassOn c L;
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
corollary rhoMass_outside_ball (c : 𝓔 n) (L : EuclideanLattice n n) :
  rhoMassOn c L (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ < (2 : ℝ)^(-n : ℝ) * (rhoMass 0 L) := by
  have : (0.2 : ℝ)^(n : ℝ) < (2 : ℝ)^(-(n : ℝ)) := by
    norm_num [ Real.rpow_def_of_pos ];
    simp +zetaDelta at *;
    -- Since $2 < 5$, we can apply the logarithm function to both sides, preserving the inequality.
    apply Real.log_lt_log; norm_num; norm_num
  have h_bound := rhoMass_outside_ball_stronger c L;
  -- By combining the results from h_bound and this, we can conclude the proof.
  apply lt_of_lt_of_le h_bound (mul_le_mul_of_nonneg_right this.le (by
  -- The Gaussian function is non-negative, so the sum of non-negative terms is non-negative.
  apply tsum_nonneg; intro v; exact Real.exp_nonneg _))


/-- Corollary : lattices with long shortest vector have exponentially small Gaussian mass outside the origin -/
theorem rhoMass_with_long_sv_stronger (L : EuclideanLattice n n) (h_svl : L.shortestVectorLength ≥ Real.sqrt (n : ℝ)) :
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

  have h_concentration := rhoMass_outside_ball_stronger 0 L
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
corollary rhoMass_with_long_sv (L : EuclideanLattice n n) (h_svl : L.shortestVectorLength ≥ Real.sqrt (n : ℝ)) :
  rhoMassOn 0 L {0}ᶜ < (2 : ℝ)^(-n : ℝ) * (1 - (2 : ℝ)^(-n : ℝ)) := by
  have h_bound := rhoMass_with_long_sv_stronger L h_svl;
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
corollary rhoMass_ub_on_dual_with_long_sv (L : EuclideanLattice n n) (h_svl : L.shortestVectorLength ≥ Real.sqrt (n : ℝ)) (u : 𝓔 n) :
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
      have := rhoMass_with_long_sv L h_svl;
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
corollary rhoMass_lb_on_dual_with_long_sv (L : EuclideanLattice n n) (h_svl : L.shortestVectorLength ≥ Real.sqrt (n : ℝ)) (u : 𝓔 n) :
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
  -- Use `rhoMass_with_long_sv` to bound `rhoMassOn 0 L {0}ᶜ < 2^{-n} * (1 - 2^{-n}) < 2^{-n}`.
  have h_rhoMassOn_zero : rhoMassOn 0 L {0}ᶜ < (2 : ℝ)^(-n : ℝ) := by
    exact lt_of_lt_of_le ( rhoMass_with_long_sv L h_svl ) ( by norm_num [ Real.rpow_neg ] );
  nlinarith [ show ( L.det : ℝ ) ≥ 0 by exact_mod_cast L.det_pos.le, show ( 2 : ℝ ) ^ ( - ( n : ℝ ) ) ≥ 0 by positivity ]


end concentration

end LatticeCrypto.Foundations.Gaussian


namespace LatticeCrypto.Foundations.Gaussian

/-!
  # The Transference Theorem
  We prove Banaszczyk's Transference Theorem (weaker version):
    1/2 ≤ μ(L^*) * λ₁(L) ≤ n
  Or equivalently:
    1 ≤ λₙ(L^*) * λ₁(L) ≤ 2n
  * `theorem transference_lb` : `1 ≤ L.dual.succMinₙ * L.succMin₁`
  * `theorem transference_ub_μ_succMin₁` : `L.dual.μ * L.succMin₁ ≤ n`
  * `theorem transference_ub` : `L.dual.succMinₙ * L.succMin₁ ≤ 2 * n`
-/
section transference_theorem

open Real Complex MeasureTheory
open RealInnerProductSpace
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Foundations.Lattice
open scoped FourierTransform

variable {n : ℕ+} (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s)

/-- The number of dimensions where our proof of transference holds -/
def Banaszczyk_transference_threshold_constant : ℕ+ := 2

/--
  If there's a lattice with L.dual.μ * L.succMin₁ > n, then WLOG one can assume there exists
  another lattice L' also satisfies L'.dual.μ * L'.succMin₁ > n, while at the same time having both L'.succMin₁ > Real.sqrt n ∧ L'.dual.μ > Real.sqrt n
-/
lemma transference_reduction_lemma {n : ℕ+} (L : EuclideanLattice n n) (h : L.dual.μ * L.succMin₁ > n) :
  ∃ (s : ℝ) (hs : 0 < s), let L' := L.smul s hs.ne.symm; L'.succMin₁ > Real.sqrt n ∧ L'.dual.μ > Real.sqrt n := by
    have h_bounds : ∃ s : ℝ, 0 < s ∧ Real.sqrt (n : ℝ) / L.succMin₁ < s ∧ s < L.dual.μ / Real.sqrt (n : ℝ) := by
      by_cases h_pos : 0 < L.succMin₁;
      · refine' exists_between _ |> fun ⟨ s, hs₁, hs₂ ⟩ => ⟨ s, by nlinarith [ show 0 < Real.sqrt n / L.succMin₁ by positivity ], hs₁, hs₂ ⟩;
        rw [ div_lt_div_iff₀ ] <;> nlinarith [ Real.sqrt_pos.mpr ( Nat.cast_pos.mpr n.pos ), Real.mul_self_sqrt ( Nat.cast_nonneg n ) ];
      · exact False.elim <| h_pos <| by exact
        EuclideanLattice.successiveMinima_pos L ⟨0, PNat.pos n⟩;
    field_simp;
    rcases h_bounds with ⟨ s, hs₀, hs₁, hs₂ ⟩ ; exact ⟨ s, hs₀, by
      rw [ div_lt_iff₀ ] at hs₁;
      · convert hs₁ using 1;
        exact EuclideanLattice.successiveMinima_scale L ⟨0, PNat.pos n⟩ s hs₀;
      · exact EuclideanLattice.successiveMinima_pos L ⟨0, PNat.pos n⟩, by
      -- By definition of $L'$, we know that its dual covering radius is $L.dual.μ / s$.
      have h_dual_covering_radius : (L.smul s hs₀.ne.symm).dual.μ = L.dual.μ / s := by
        exact EuclideanLattice.coveringRadius_scale_dual L s hs₀;
      rw [ h_dual_covering_radius, lt_div_iff₀ ] at * <;> first | positivity | linarith; ⟩

/-
If a lattice has first successive minimum greater than sqrt(n) and its dual has covering radius greater than sqrt(n), we derive a contradiction for n >= 2.
-/
lemma transference_contradiction (hn : n ≥ Banaszczyk_transference_threshold_constant) (L : EuclideanLattice n n)
  (h1 : L.succMin₁ > Real.sqrt n) (h2 : L.dual.μ > Real.sqrt n) : False := by
    -- By `rhoMass_outside_ball`, `rhoMass (-v) L.dual < 2^{-n} * rhoMass 0 L.dual`.
    obtain ⟨v, hv⟩ : ∃ v : 𝓔 n, L.dual.distanceToLattice v > Real.sqrt n := by
      field_simp;
      have h_inf : ∀ M < L.dual.μ, ∃ v : 𝓔 n, L.dual.distanceToLattice v > M := by
        intros M hM
        have h_inf : M < sSup {L.dual.distanceToLattice x | x : 𝓔 n} := by
          convert hM using 1;
          convert L.dual.coveringRadius_eq_alt_def.symm using 1;
        exact by rcases exists_lt_of_lt_csSup ( show { x : ℝ | ∃ x_1 : 𝓔 n, EuclideanLattice.distanceToLattice x_1 L.dual = x }.Nonempty from ⟨ _, ⟨ 0, rfl ⟩ ⟩ ) h_inf with ⟨ x, ⟨ v, rfl ⟩, hx ⟩ ; exact ⟨ v, hx ⟩ ;
      exact Exists.elim ( h_inf _ h2 ) fun v hv => ⟨ v, hv ⟩;
    have h_contradiction : rhoMass (-v) L.dual < (2 : ℝ)^(-n : ℝ) * rhoMass 0 L.dual := by
      have h_contradiction : rhoMass (-v) L.dual = rhoMassOn (-v) L.dual (𝔅 (0 : 𝓔 n) (Real.sqrt (n : ℝ)))ᶜ := by
        refine' tsum_congr fun w => _;
        simp_all +decide [ Set.indicator ];
        contrapose! hv;
        refine' le_trans ( csInf_le _ _ ) hv.1.le;
        · exact ⟨ 0, by rintro x ⟨ y, hy, rfl ⟩ ; exact norm_nonneg _ ⟩;
        · exact ⟨ w, w.2, by rw [ ← norm_neg ] ; abel_nf ⟩
      generalize_proofs at *; (
      convert rhoMass_outside_ball ( -v ) L.dual using 1);
    -- By `rhoMass_ub_on_dual_with_long_sv` and `rhoMass_lb_on_dual_with_long_sv`, for any `u`, `rhoMass u L.dual` is bounded:
    have h_bounds : rhoMass 0 L.dual ≤ (1 + 2 * (2 : ℝ)^(-n : ℝ)) * L.det ∧ rhoMass (-v) L.dual ≥ (1 - 2 * (2 : ℝ)^(-n : ℝ)) * L.det := by
      apply And.intro;
      · apply rhoMass_ub_on_dual_with_long_sv;
        have : L.succMin₁ = L.shortestVectorLength := by exact L.successiveMinima_one
        rw [ ←this ]; exact le_of_lt h1
      · apply rhoMass_lb_on_dual_with_long_sv;
        have : L.succMin₁ = L.shortestVectorLength := by exact L.successiveMinima_one
        rw [ ←this ]; exact le_of_lt h1
    -- Let `x = 2^{-n}`. The inequality is `(1 - 2x) / (1 + 2x) < x`, which simplifies to `1 - 3x - 2x^2 < 0`.
    set x : ℝ := (2 : ℝ)^(-n : ℝ)
    have h_ineq : (1 - 2 * x) / (1 + 2 * x) < x := by
      rw [ div_lt_iff₀ ] <;> nlinarith [ show 0 < L.det from L.det_pos, show 0 < x from by positivity ];
    rw [ div_lt_iff₀ ] at h_ineq <;> nlinarith [ show ( 0 : ℝ ) < x by positivity, show ( x : ℝ ) ≤ 1 / 4 by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_num ) <| show ( -n : ℝ ) ≤ -2 by exact neg_le_neg <| Nat.cast_le.mpr hn ) <| by norm_num ]

/-
The product of the covering radius of the dual lattice and the first successive minimum of the lattice is at most n, for n >= 2.
-/
theorem transference_ub_μ_succMin₁ {n : ℕ+} (L : EuclideanLattice n n) (hn : n ≥ Banaszczyk_transference_threshold_constant):
  L.dual.μ * L.succMin₁ ≤ n := by
    apply le_of_not_gt; intro h_prod_gt_n; (
    have := transference_reduction_lemma L h_prod_gt_n; obtain ⟨ s, hs_pos, hs_bounds ⟩ := this; exact transference_contradiction hn ( L.smul s hs_pos.ne.symm ) hs_bounds.left hs_bounds.right;)

/-
The product of the n-th successive minimum of the dual lattice and the first successive minimum of the lattice is at most 2n.
-/
theorem transference_ub {n : ℕ+} (L : EuclideanLattice n n) (hn : n ≥ Banaszczyk_transference_threshold_constant) :
  L.dual.succMinₙ * L.succMin₁ ≤ 2 * n := by
    field_simp;
    -- We know from `transference_ub_μ_succMin₁` that `L.dual.μ * L.succMin₁ ≤ n`.
    have h1 : L.dual.μ * L.succMin₁ ≤ n := by
      exact transference_ub_μ_succMin₁ L hn;
    -- We also know from `EuclideanLattice.coveringRadius_ge_half_succMinₙ` applied to `L.dual` that `L.dual.μ ≥ L.dual.succMinₙ / 2`, which implies `L.dual.succMinₙ ≤ 2 * L.dual.μ`.
    have h2 : L.dual.succMinₙ ≤ 2 * L.dual.μ := by
      have := L.dual.coveringRadius_ge_half_succMinₙ; norm_num at *; linarith;
    refine le_trans ?_ ( mul_le_mul_of_nonneg_left h1 zero_le_two );
    convert mul_le_mul_of_nonneg_right h2 ( show 0 ≤ L.succMin₁ from le_of_lt ( show L.succMin₁ > 0 from ?_ ) ) using 1 ; ring;
    exact EuclideanLattice.successiveMinima_pos L ⟨0, PNat.pos n⟩

/-
There exists a basis of the dual lattice consisting of vectors with length at most the n-th successive minimum of the dual lattice.
-/
lemma exists_dual_basis_bounded {n : ℕ+} (L : EuclideanLattice n n) :
  ∃ b : Fin n → 𝓔 n, LinearIndependent ℝ b ∧ (∀ i, b i ∈ L.dual.carrier) ∧ (∀ i, ‖b i‖ ≤ L.dual.succMinₙ) := by
    have := L.dual.linearIndependent_successiveMinima_attained;
    obtain ⟨ x, hx₁, hx₂ ⟩ := this;
    refine' ⟨ x, hx₂, _, _ ⟩;
    · intro i;
      exact hx₁ i |>.1.1;
    · intro i;
      rw [ hx₁ i |>.2 ];
      -- Since the successive minima are non-decreasing, we have `L.dual.successiveMinima i ≤ L.dual.succMinₙ` for all `i`.
      have h_succ_min_le : ∀ i j : Fin n, i ≤ j → L.dual.successiveMinima i ≤ L.dual.successiveMinima j := by
        exact fun i j a => EuclideanLattice.successiveMinima_mono L.dual a;
      exact h_succ_min_le i ( ⟨ n - 1, Nat.sub_lt n.pos zero_lt_one ⟩ : Fin n ) ( Nat.le_pred_of_lt i.2 )

/-
The inner product of a vector in the lattice and a vector in the dual lattice is an integer.
-/
lemma inner_lattice_dual_int {n : ℕ+} (L : EuclideanLattice n n) (v : 𝓔 n) (w : 𝓔 n)
  (hv : v ∈ L.carrier) (hw : w ∈ L.dual.carrier) : ∃ k : ℤ, inner ℝ v w = k := by
    -- Since $w \in L.dual.carrier$, we have $\langle v, w \rangle \in \mathbb{Z}$ for all $v \in L.carrier$.
    have h_inner_int : ∀ v ∈ L.carrier, ∃ k : ℤ, ⟪v, w⟫ = k := by
      intro v hv
      obtain ⟨k, hk⟩ : ∃ k : ℤ, ⟪v, w⟫ = k := by
        have := L.dual_carrier_eq_integralDual
        replace this := Set.ext_iff.mp this w; aesop;
      use k;
    exact h_inner_int v hv

/-
The product of the n-th successive minimum of the dual lattice and the first successive minimum of the lattice is at least 1.
-/
theorem transference_lb {n : ℕ+} (L : EuclideanLattice n n) :
  1 ≤ L.dual.succMinₙ * L.succMin₁ := by
    -- Let `v` be a vector in `L` such that `‖v‖ = L.succMin₁` (exists by `successiveMinima_attained`).
    obtain ⟨v, hv⟩ : ∃ v ∈ L.carrier, ‖v‖ = L.succMin₁ := by
      have := L.successiveMinima_attained 0;
      exact ⟨ this.choose, this.choose_spec.1.1, this.choose_spec.2 ⟩;
    -- Since `b` is a basis, `v` cannot be orthogonal to all `b i`. There exists `k` such that `⟪v, b k⟫ ≠ 0`.
    obtain ⟨b, hb⟩ : ∃ b : Fin n → 𝓔 n, LinearIndependent ℝ b ∧ (∀ i, b i ∈ L.dual.carrier) ∧ (∀ i, ‖b i‖ ≤ L.dual.succMinₙ) ∧ ∃ k, inner ℝ v (b k) ≠ 0 := by
      obtain ⟨b, hb⟩ : ∃ b : Fin n → 𝓔 n, LinearIndependent ℝ b ∧ (∀ i, b i ∈ L.dual.carrier) ∧ (∀ i, ‖b i‖ ≤ L.dual.succMinₙ) := by
        exact exists_dual_basis_bounded L;
      refine' ⟨ b, hb.1, hb.2.1, hb.2.2, _ ⟩;
      have h_not_orthogonal : ¬(∀ i, ⟪v, b i⟫ = 0) := by
        intro h_orthogonal
        have h_v_zero : v = 0 := by
          have h_v_zero : ∀ w ∈ Submodule.span ℝ (Set.range b), ⟪v, w⟫ = 0 := by
            intro w hw; rw [ Submodule.mem_span_range_iff_exists_fun ] at hw; obtain ⟨ f, rfl ⟩ := hw; simp +decide [ *, inner_sum, inner_smul_right ] ;
          have h_v_zero : v ∈ (Submodule.span ℝ (Set.range b))ᗮ := by
            exact (Submodule.mem_orthogonal' (Submodule.span ℝ (Set.range b)) v).mpr h_v_zero;
          have h_v_zero : Submodule.span ℝ (Set.range b) = ⊤ := by
            refine' Submodule.eq_top_of_finrank_eq _;
            rw [ finrank_span_eq_card ] <;> aesop;
          aesop
        exact absurd hv.2 ( by rw [ h_v_zero, norm_zero ] ; exact ne_of_lt <| by exact
          (EuclideanLattice.successiveMinima_pos L ⟨0, PNat.pos n⟩) );
      exact not_forall.mp h_not_orthogonal;
    -- By `inner_lattice_dual_int`, `⟪v, b k⟫` is an integer.
    obtain ⟨k, hk⟩ : ∃ k, inner ℝ v (b k) ≠ 0 := hb.2.2.2
    have h_int : ∃ m : ℤ, inner ℝ v (b k) = m := by
      have := inner_lattice_dual_int L v ( b k ) hv.1 ( hb.2.1 k ) ; aesop;
    -- Since `⟪v, b k⟫` is non-zero and an integer, `|⟪v, b k⟫| ≥ 1`.
    have h_abs : |inner ℝ v (b k)| ≥ 1 := by
      field_simp;
      exact h_int.elim fun m hm => by rw [ hm ] ; exact mod_cast abs_pos.mpr ( show ( m : ℝ ) ≠ 0 from mod_cast fun h => hk <| by simp +decide [ h ] at hm; exact hm ) ;
    exact h_abs.trans ( by simpa [ mul_comm, hv.2 ] using abs_real_inner_le_norm v ( b k ) |> le_trans <| mul_le_mul ( show ‖v‖ ≤ L.succMin₁ from hv.2.le ) ( show ‖b k‖ ≤ L.dual.succMinₙ from hb.2.2.1 k ) ( by positivity ) ( by linarith [ norm_nonneg v, norm_nonneg ( b k ) ] ) )

end transference_theorem

end LatticeCrypto.Foundations.Gaussian
