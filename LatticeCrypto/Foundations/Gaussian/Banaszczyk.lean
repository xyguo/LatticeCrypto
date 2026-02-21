import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

import LatticeCrypto.Foundations.Gaussian.Defs
import LatticeCrypto.Foundations.Gaussian.Fourier
import LatticeCrypto.Foundations.Gaussian.PoissonSummation
import LatticeCrypto.Foundations.Lattice.Distance
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec
import LatticeCrypto.Foundations.Gaussian.TailBound

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
    -- By `rhoMassOn_outside_ball_sqrt_lt_two_rpow_neg_mul_rhoMass`, `rhoMass (-v) L.dual < 2^{-n} * rhoMass 0 L.dual`.
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
      convert rhoMassOn_outside_ball_sqrt_lt_two_rpow_neg_mul_rhoMass ( -v ) L.dual using 1);
    -- By `rhoMass_dual_le_one_add_two_mul_two_rpow_neg_mul_det_of_shortestVectorLength_ge_sqrt` and `rhoMass_dual_ge_one_sub_two_mul_two_rpow_neg_mul_det_of_shortestVectorLength_ge_sqrt`, for any `u`, `rhoMass u L.dual` is bounded:
    have h_bounds : rhoMass 0 L.dual ≤ (1 + 2 * (2 : ℝ)^(-n : ℝ)) * L.det ∧ rhoMass (-v) L.dual ≥ (1 - 2 * (2 : ℝ)^(-n : ℝ)) * L.det := by
      apply And.intro;
      · apply rhoMass_dual_le_one_add_two_mul_two_rpow_neg_mul_det_of_shortestVectorLength_ge_sqrt;
        have : L.succMin₁ = L.shortestVectorLength := by exact L.successiveMinima_one
        rw [ ←this ]; exact le_of_lt h1
      · apply rhoMass_dual_ge_one_sub_two_mul_two_rpow_neg_mul_det_of_shortestVectorLength_ge_sqrt;
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
    -- By `EuclideanLattice.inner_lattice_dual_int`, `⟪v, b k⟫` is an integer.
    obtain ⟨k, hk⟩ : ∃ k, inner ℝ v (b k) ≠ 0 := hb.2.2.2
    have h_int : ∃ m : ℤ, inner ℝ v (b k) = m := by
      have := EuclideanLattice.inner_lattice_dual_int L v ( b k ) hv.1 ( hb.2.1 k ) ; aesop;
    -- Since `⟪v, b k⟫` is non-zero and an integer, `|⟪v, b k⟫| ≥ 1`.
    have h_abs : |inner ℝ v (b k)| ≥ 1 := by
      field_simp;
      exact h_int.elim fun m hm => by rw [ hm ] ; exact mod_cast abs_pos.mpr ( show ( m : ℝ ) ≠ 0 from mod_cast fun h => hk <| by simp +decide [ h ] at hm; exact hm ) ;
    exact h_abs.trans ( by simpa [ mul_comm, hv.2 ] using abs_real_inner_le_norm v ( b k ) |> le_trans <| mul_le_mul ( show ‖v‖ ≤ L.succMin₁ from hv.2.le ) ( show ‖b k‖ ≤ L.dual.succMinₙ from hb.2.2.1 k ) ( by positivity ) ( by linarith [ norm_nonneg v, norm_nonneg ( b k ) ] ) )

end transference_theorem

end LatticeCrypto.Foundations.Gaussian
