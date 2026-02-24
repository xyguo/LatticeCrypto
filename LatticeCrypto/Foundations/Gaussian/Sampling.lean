import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import LatticeCrypto.Foundations.Gaussian.PoissonSummation
import LatticeCrypto.Foundations.Lattice.FundamentalDomain
import LatticeCrypto.Utils.Probability

open scoped Real Complex MeasureTheory ENNReal
open scoped RealInnerProductSpace
open LatticeCrypto.Utils.Probability
open LatticeCrypto.Foundations.Lattice
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.Vec

namespace LatticeCrypto.Foundations.Gaussian.Sampling

/-!
  # Gaussian Coset Sampling
  This section defines the probability density of sampling from with a parallelpiped `B.fundamentalDomain` for any given `LatticeBasis` `B` using Gaussian rounding.
  * Class `IsProbabilityDensityOn`: predicate claiming that a given density is a valid probability density on a set.
  * `gaussianModParallelpiped`: The Gaussian rounding procedure.
  * `modGaussianDensity`: The density function of sampling from a parallelpiped with Gaussian rounding.
-/
noncomputable section coset_sampling

variable {n : ℕ+}

/--
  The uniform density on a lattice `L`'s fundamental domain (specified with basis `B`)
-/
noncomputable def uniformDensity (L : EuclideanLattice n n) (_ : 𝓔 n) : ℝ  :=
  L.dual.det

/--
Uniform density clipped to a specific fundamental domain (`0` outside the domain).
This is often the most convenient subroutine when composing density-based constructions.
-/
noncomputable def uniformOnFundamentalDomain
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n) : 𝓔 n → ℝ :=
  Set.indicator B.fundamentalDomain (uniformDensity L)

/-- The uniform density on a lattice `L`'s fundamental domain is a probability density. -/
theorem uniformDensity_isProbabilityDensityOn_fundamentalDomain
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) :
    IsProbabilityDensityOn (uniformDensity L) B.fundamentalDomain := by
  refine ⟨?_, ?_⟩
  · intro x hx
    unfold uniformDensity
    exact L.dual.det_pos.le
  · unfold uniformDensity
    have h_det_eq : B.volume = L.det := by
      have h' : B.toLattice.det = L.det := EuclideanLattice.det_eq_of_equiv hB
      simpa [EuclideanLattice.det_def] using h'
    have h_real : (MeasureTheory.volume B.fundamentalDomain).toReal = B.volume := by
      have h_real' : (LatticeCrypto.Utils.Geometry.lebesgueMeasure B.fundamentalDomain).toReal = B.volume :=
        LatticeBasis.volume_real_fundamentalDomain B
      simpa [LatticeCrypto.Utils.Geometry.lebesgueMeasure] using h_real'
    calc
      ∫ x in B.fundamentalDomain, L.dual.det
          = (MeasureTheory.volume.real B.fundamentalDomain) * L.dual.det := by
              simp [MeasureTheory.integral_const]
      _ = (MeasureTheory.volume B.fundamentalDomain).toReal * L.dual.det := by
            simp [MeasureTheory.Measure.real]
      _ = B.volume * L.dual.det := by rw [h_real]
      _ = L.det * L.dual.det := by rw [h_det_eq]
      _ = 1 := by
            rw [EuclideanLattice.dual_det_eq_inv]
            field_simp [L.det_pos.ne']


/-- The modulo-Gaussian density `Y(x) = (1 / s^n) * rhoSMass s x L`. -/
noncomputable def modGaussianDensity (L : EuclideanLattice n n) (s : ℝ) (x : 𝓔 n) : ℝ :=
  (1 / s ^ (n : ℕ)) * rhoSMass s x L

/--
Modulo-Gaussian density clipped to a specific fundamental domain (`0` outside the domain).
This is often the most convenient subroutine when composing density-based constructions.
-/
noncomputable def modGaussianOnFundamentalDomain
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n) (s : ℝ) : 𝓔 n → ℝ :=
  Set.indicator B.fundamentalDomain (modGaussianDensity L s)

/-- Integral of the continuous Gaussian `rhoS s` over the whole space. -/
lemma integral_rhoS_eq_pow (s : ℝ) (hs : 0 < s) :
    (∫ x : 𝓔 n, rhoS s x) = s ^ (n : ℕ) := by
  have hft := rhoS_FT_eq (n := n) s hs (0 : 𝓔 n)
  unfold rhoS_FT at hft
  have hre := congrArg Complex.re hft
  have hint : MeasureTheory.Integrable (fun v : 𝓔 n => (rhoS s v : ℂ)) := by
    exact rhoS.integrable s (ne_of_gt hs)
  have hre_int : (∫ x : 𝓔 n, rhoS s x) = (∫ x : 𝓔 n, (rhoS s x : ℂ)).re := by
    simpa using (integral_re (μ := MeasureTheory.volume) (f := fun v : 𝓔 n => (rhoS s v : ℂ)) hint)
  have hre0 : (∫ x : 𝓔 n, (rhoS s x : ℂ)).re = (↑s ^ (n : ℕ) : ℂ).re := by
    simpa [Real.fourierIntegral, VectorFourier.fourierIntegral, Real.fourierChar, rhoS] using hre
  have hsre : (↑s ^ (n : ℕ) : ℂ).re = s ^ (n : ℕ) := by
    norm_cast
  exact hre_int.trans (hre0.trans hsre)

/-- `rhoSMass` is invariant under replacing a lattice by a carrier-equivalent basis lattice. -/
lemma rhoSMass_eq_of_basis_equiv
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) (s : ℝ) (x : 𝓔 n) :
    rhoSMass s x L = rhoSMass s x B.toLattice := by
  have h_carrier : B.toLattice.carrier = L.carrier := by
    simpa [isBasisFor, EuclideanLattice.CarrierEquiv] using hB
  unfold rhoSMass EuclideanLattice.latticeSum
  rw [h_carrier]

/-- Pointwise nonnegativity of the modulo-Gaussian density. -/
lemma modGaussianDensity_nonneg
    (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (x : 𝓔 n) :
    0 ≤ modGaussianDensity L s x := by
  unfold modGaussianDensity
  refine mul_nonneg ?_ ?_
  · positivity
  · exact tsum_nonneg (fun _ => rhoS_nonneg s _)

/-- The modulo-Gaussian density integrates to `1` over a fundamental domain. -/
lemma integral_modGaussianDensity_eq_one
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) (s : ℝ) (hs : 0 < s) :
    ∫ x in B.fundamentalDomain, modGaussianDensity L s x = 1 := by
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hIntR : MeasureTheory.Integrable (fun x : 𝓔 n => rhoS s x) := by
    have hIntC : MeasureTheory.Integrable (fun x : 𝓔 n => (rhoS s x : ℂ)) := rhoS.integrable s hs_ne
    convert Complex.reCLM.integrable_comp hIntC using 1
  calc
    ∫ x in B.fundamentalDomain, modGaussianDensity L s x
        = (1 / s ^ (n : ℕ)) * ∫ x in B.fundamentalDomain, rhoSMass s x L := by
            simp [modGaussianDensity, MeasureTheory.integral_const_mul]
    _ = (1 / s ^ (n : ℕ)) * ∫ x in B.fundamentalDomain, rhoSMass s x B.toLattice := by
          congr 1
          refine MeasureTheory.setIntegral_congr_fun (LatticeBasis.fundamentalDomain_measurableSet B) ?_
          intro x hx
          simpa using rhoSMass_eq_of_basis_equiv L B hB s x
    _ = (1 / s ^ (n : ℕ)) * ∫ x in B.fundamentalDomain, rhoS_periodize s B.toLattice x := by
          congr 2
          ext x
          symm
          exact rhoS_periodize_eq_rhoSMass_on_coset s B.toLattice x
    _ = (1 / s ^ (n : ℕ)) * ∫ x, rhoS s x := by
          congr 1
          simpa [rhoS_periodize] using
            integral_periodize_eq_integral_real (f := fun x : 𝓔 n => rhoS s x) (L := B.toLattice) hIntR
    _ = (1 / s ^ (n : ℕ)) * (s ^ (n : ℕ)) := by
          rw [integral_rhoS_eq_pow (n := n) s hs]
    _ = 1 := by
          field_simp [hs_ne]

/-- The modulo-Gaussian density is a probability density on `B.fundamentalDomain`. -/
theorem modGaussianDensity_isProbabilityDensityOn_fundamentalDomain
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) (s : ℝ) (hs : 0 < s) :
    IsProbabilityDensityOn (modGaussianDensity L s) B.fundamentalDomain := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact modGaussianDensity_nonneg L s hs x
  · exact integral_modGaussianDensity_eq_one L B hB s hs

/-- The clipped modulo-Gaussian density integrates to `1` on the fundamental domain. -/
theorem setIntegral_modGaussianOnFundamentalDomain_eq_one
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) (s : ℝ) (hs : 0 < s) :
    ∫ x in B.fundamentalDomain, modGaussianOnFundamentalDomain L B s x = 1 := by
  rw [modGaussianOnFundamentalDomain]
  have h_eq :
      ∫ x in B.fundamentalDomain, B.fundamentalDomain.indicator (modGaussianDensity L s) x
        = ∫ x in B.fundamentalDomain, modGaussianDensity L s x := by
    refine MeasureTheory.setIntegral_congr_fun (LatticeBasis.fundamentalDomain_measurableSet B) ?_
    intro x hx
    simp [hx]
  exact h_eq.trans (integral_modGaussianDensity_eq_one L B hB s hs)

/-- The ENNReal-valued clipped modulo-Gaussian density used by `withDensity`. -/
noncomputable def modGaussianOnFundamentalDomainENNReal
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n) (s : ℝ) : 𝓔 n → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (modGaussianOnFundamentalDomain L B s x)

/-- Summability of the twisted Fourier series term in Poisson expansion. -/
private lemma summable_twisted_rhoS
    (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (x : 𝓔 n) :
    Summable (fun v : L.dual.carrier =>
      cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)) := by
  have hρ : Summable (fun v : L.dual.carrier => rhoS (1 / s) (v : 𝓔 n)) := by
    simpa using summable_rhoS L.dual (1 / s) (one_div_pos.mpr hs) 0
  have hnorm : Summable (fun v : L.dual.carrier =>
      ‖cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)‖) := by
    convert hρ using 1
    funext v
    simp [Complex.norm_exp, rhoS_nonneg]
  exact Summable.of_norm hnorm

/-- Summability of the nonzero-frequency tail of the twisted Fourier series. -/
private lemma summable_twisted_rhoS_tail
    (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (x : 𝓔 n) :
    Summable (fun v : L.dual.carrier =>
      if v = 0 then 0 else
        cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)) := by
  have hρ : Summable (fun v : L.dual.carrier => rhoS (1 / s) (v : 𝓔 n)) := by
    simpa using summable_rhoS L.dual (1 / s) (one_div_pos.mpr hs) 0
  have hρtail : Summable (fun v : L.dual.carrier => if v = 0 then 0 else rhoS (1 / s) (v : 𝓔 n)) := by
    refine Summable.of_nonneg_of_le (fun v => ?_) (fun v => ?_) hρ
    · by_cases hv : v = 0 <;> simp [hv, rhoS_nonneg]
    · by_cases hv : v = 0 <;> simp [hv, rhoS_nonneg]
  have hnorm : Summable (fun v : L.dual.carrier =>
      ‖if v = 0 then 0 else
        cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)‖) := by
    convert hρtail using 1
    funext v
    by_cases hv : v = 0
    · simp [hv]
    · simp [hv, Complex.norm_exp, rhoS_nonneg]
  exact Summable.of_norm hnorm

/-- The norm of the nonzero-frequency tail is bounded by nonzero dual Gaussian mass. -/
private lemma tail_norm_le_rhoSMassOn_nonzero
    (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (x : 𝓔 n) :
    ‖∑' v : L.dual.carrier,
        if v = 0 then 0 else
          cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)‖
      ≤ rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
  have htail : Summable (fun v : L.dual.carrier =>
      if v = 0 then 0 else
        cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)) :=
    summable_twisted_rhoS_tail L s hs x
  have hnorm_le :
      ‖∑' v : L.dual.carrier,
          if v = 0 then 0 else
            cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)‖
        ≤
      ∑' v : L.dual.carrier,
          ‖if v = 0 then 0 else
              cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)‖ := by
    exact norm_tsum_le_tsum_norm htail.norm
  have hnorm_eq :
      (∑' v : L.dual.carrier,
          ‖if v = 0 then 0 else
              cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)‖)
      =
      (∑' v : L.dual.carrier, if v = 0 then 0 else rhoS (1 / s) (v : 𝓔 n)) := by
    refine tsum_congr ?_
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · simp [hv, Complex.norm_exp, rhoS_nonneg]
  have htail_eq :
      (∑' v : L.dual.carrier, if v = 0 then 0 else rhoS (1 / s) (v : 𝓔 n))
        = rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
    unfold rhoSMassOn EuclideanLattice.latticeSum
    refine tsum_congr ?_
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · simp [hv]
  calc
    ‖∑' v : L.dual.carrier,
        if v = 0 then 0 else
          cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)‖
      ≤
    ∑' v : L.dual.carrier,
        ‖if v = 0 then 0 else
            cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)‖ := hnorm_le
    _ = (∑' v : L.dual.carrier, if v = 0 then 0 else rhoS (1 / s) (v : 𝓔 n)) := hnorm_eq
    _ = rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := htail_eq

/--
Pointwise deviation between modulo-Gaussian density and uniform density on a lattice
fundamental domain.
-/
theorem modGaussian_vs_uniform_pointwise_le
    (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (x : 𝓔 n) :
    |modGaussianDensity L s x - uniformDensity L x|
      ≤ L.dual.det * rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
  let f : L.dual.carrier → ℂ :=
    fun v => cexp (-2 * Real.pi * Complex.I * inner ℝ x (v : 𝓔 n)) * (rhoS (1 / s) (v : 𝓔 n) : ℂ)
  have hsumf : Summable f := by
    simpa [f] using summable_twisted_rhoS L s hs x
  have hpoisson := poisson_summation_rhoS_coset L s hs x
  have hdet : (1 / L.det : ℂ) = L.dual.det := by
    rw [EuclideanLattice.dual_det_eq_inv]
    norm_num
  have hpoisson' :
      (rhoSMass s x L : ℂ)
        = (L.dual.det : ℂ) * (s ^ (n : ℕ)) * (∑' v : L.dual.carrier, f v) := by
    simpa [f, EuclideanLattice.latticeSum, hdet, mul_assoc, mul_left_comm, mul_comm] using hpoisson
  have hs_pow_ne : ((s : ℂ) ^ (n : ℕ)) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast (ne_of_gt hs))
  have hscaled :
      ((1 / (s ^ (n : ℕ)) : ℂ) * (rhoSMass s x L : ℂ))
        = (L.dual.det : ℂ) * (∑' v : L.dual.carrier, f v) := by
    rw [hpoisson']
    field_simp [hs_pow_ne]
  have hf0 : f 0 = 1 := by
    simp [f, rhoS]
  have hsplit :
      (∑' v : L.dual.carrier, f v)
        = 1 + ∑' v : L.dual.carrier, (if v = 0 then 0 else f v) := by
    rw [Summable.tsum_eq_add_tsum_ite hsumf 0]
    simp [hf0]
  have hdiff :
      ((1 / (s ^ (n : ℕ)) : ℂ) * (rhoSMass s x L : ℂ) - (L.dual.det : ℂ))
        =
      (L.dual.det : ℂ) * (∑' v : L.dual.carrier, if v = 0 then 0 else f v) := by
    calc
      ((1 / (s ^ (n : ℕ)) : ℂ) * (rhoSMass s x L : ℂ) - (L.dual.det : ℂ))
          = (L.dual.det : ℂ) * (∑' v : L.dual.carrier, f v) - (L.dual.det : ℂ) := by
              simpa [one_div] using congrArg (fun t => t - (L.dual.det : ℂ)) hscaled
      _ = (L.dual.det : ℂ) * (1 + ∑' v : L.dual.carrier, if v = 0 then 0 else f v) - (L.dual.det : ℂ) := by
              rw [hsplit]
      _ = (L.dual.det : ℂ) * (∑' v : L.dual.carrier, if v = 0 then 0 else f v) := by ring
  have hnorm_tail :
      ‖∑' v : L.dual.carrier, if v = 0 then 0 else f v‖
        ≤ rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
    simpa [f] using tail_norm_le_rhoSMassOn_nonzero L s hs x
  have hcomplex :
      ‖((1 / (s ^ (n : ℕ)) : ℂ) * (rhoSMass s x L : ℂ) - (L.dual.det : ℂ))‖
        ≤ L.dual.det * rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
    have hdet_nonneg : 0 ≤ L.dual.det := L.dual.det_pos.le
    calc
      ‖((1 / (s ^ (n : ℕ)) : ℂ) * (rhoSMass s x L : ℂ) - (L.dual.det : ℂ))‖
          = L.dual.det * ‖∑' v : L.dual.carrier, if v = 0 then 0 else f v‖ := by
              rw [hdiff, norm_mul]
              simp [abs_of_nonneg hdet_nonneg]
      _ ≤ L.dual.det * rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
            gcongr
  have hreal :
      ‖((1 / (s ^ (n : ℕ)) : ℂ) * (rhoSMass s x L : ℂ) - (L.dual.det : ℂ))‖
        = |(1 / s ^ (n : ℕ)) * rhoSMass s x L - L.dual.det| := by
    have hcast :
        ((1 / (s ^ (n : ℕ)) : ℂ) * (rhoSMass s x L : ℂ) - (L.dual.det : ℂ))
          = (((1 / s ^ (n : ℕ)) * rhoSMass s x L - L.dual.det : ℝ) : ℂ) := by
      norm_num
    rw [hcast, Complex.norm_real]
    simp
  exact hreal ▸ hcomplex

/--
Statistical-distance bound between uniform on `B.fundamentalDomain` and modulo-Gaussian
density induced by `rhoS`.
-/
theorem statDist_modGaussian_vs_uniform_le
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) (s : ℝ) (hs : 0 < s) :
    (1 / 2) * ∫ x in B.fundamentalDomain,
        |modGaussianDensity L s x - uniformDensity L x|
      ≤ (1 / 2) * rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
  unfold modGaussianDensity uniformDensity
  let f : 𝓔 n → ℝ := fun x => |(1 / s ^ (n : ℕ)) * rhoSMass s x L - L.dual.det|
  let C : ℝ := L.dual.det * rhoSMassOn (1 / s) 0 L.dual {0}ᶜ
  have h_meas_lt_top : (MeasureTheory.volume : MeasureTheory.Measure (𝓔 n)) B.fundamentalDomain < ⊤ := by
    have h_meas_lt_top' : LatticeCrypto.Utils.Geometry.lebesgueMeasure B.fundamentalDomain < ⊤ := by
      rw [LatticeBasis.volume_fundamentalDomain]
      exact ENNReal.ofReal_lt_top
    simpa [LatticeCrypto.Utils.Geometry.lebesgueMeasure] using h_meas_lt_top'
  have h_bound : ∀ x ∈ B.fundamentalDomain, ‖f x‖ ≤ C := by
    intro x hx
    dsimp [f, C]
    have hx' := modGaussian_vs_uniform_pointwise_le L s hs x
    unfold modGaussianDensity uniformDensity at hx'
    simpa [Real.norm_eq_abs] using hx'
  have h_int_norm :
      ‖∫ x in B.fundamentalDomain, f x‖
        ≤ C * (MeasureTheory.volume B.fundamentalDomain).toReal := by
    simpa [MeasureTheory.Measure.real] using
      (MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (𝓔 n))) h_meas_lt_top h_bound)
  have h_int_nonneg :
      0 ≤ ∫ x in B.fundamentalDomain, f x := by
    refine MeasureTheory.setIntegral_nonneg (LatticeBasis.fundamentalDomain_measurableSet B) ?_
    intro x hx
    dsimp [f]
    exact abs_nonneg _
  have h_int_le :
      ∫ x in B.fundamentalDomain, f x
        ≤ C * (MeasureTheory.volume B.fundamentalDomain).toReal := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h_int_nonneg] using h_int_norm
  have h_measure_real :
      (MeasureTheory.volume B.fundamentalDomain).toReal = B.volume := by
    have h_measure_real' :
        (LatticeCrypto.Utils.Geometry.lebesgueMeasure B.fundamentalDomain).toReal = B.volume := by
      exact LatticeBasis.volume_real_fundamentalDomain B
    simpa [LatticeCrypto.Utils.Geometry.lebesgueMeasure] using h_measure_real'
  have h_det_eq : B.volume = L.det := by
    have h' : B.toLattice.det = L.det := EuclideanLattice.det_eq_of_equiv hB
    simpa [EuclideanLattice.det_def] using h'
  have h_cancel :
      C * (MeasureTheory.volume B.fundamentalDomain).toReal
        = rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
    dsimp [C]
    rw [h_measure_real, h_det_eq]
    rw [EuclideanLattice.dual_det_eq_inv]
    field_simp [L.det_pos.ne']
  have h_main :
      ∫ x in B.fundamentalDomain, f x
        ≤ rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
    exact h_int_le.trans_eq h_cancel
  have h_half := mul_le_mul_of_nonneg_left h_main (by norm_num : 0 ≤ (1 / 2 : ℝ))
  simpa [f] using h_half


/-!
  # The density properties expressed in Mathlib's MeasureTheory framework
-/
section mathlib_measures
/-- The measure on the fundamental domain induced by the modulo-Gaussian density. -/
abbrev modGaussianMeasureOnFundamentalDomain
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n) (s : ℝ) : MeasureTheory.Measure (𝓔 n) :=
  measureOfDensityOn (modGaussianDensity L s) B.fundamentalDomain

/-- The measure on the fundamental domain induced by the uniform density. -/
abbrev uniformMeasureOnFundamentalDomain
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n) : MeasureTheory.Measure (𝓔 n) :=
  measureOfDensityOn (uniformDensity L) B.fundamentalDomain

/--
The modulo-Gaussian density induces a Mathlib probability measure on the fundamental domain.
-/
theorem modGaussianMeasureOnFundamentalDomain_isProbabilityMeasure
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.IsProbabilityMeasure (modGaussianMeasureOnFundamentalDomain L B s) :=
  measureOfDensityOn_isProbabilityMeasure
    (hS := LatticeBasis.fundamentalDomain_measurableSet B)
    (hpdf := modGaussianDensity_isProbabilityDensityOn_fundamentalDomain L B hB s hs)

/-- One-line specialization: the uniform density induces a Mathlib probability measure. -/
theorem uniformMeasureOnFundamentalDomain_isProbabilityMeasure
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) :
    MeasureTheory.IsProbabilityMeasure (uniformMeasureOnFundamentalDomain L B) :=
  measureOfDensityOn_isProbabilityMeasure
    (hS := LatticeBasis.fundamentalDomain_measurableSet B)
    (hpdf := uniformDensity_isProbabilityDensityOn_fundamentalDomain L B hB)

lemma modGaussianDensity_integrableOn_fundamentalDomain
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.IntegrableOn (modGaussianDensity L s) B.fundamentalDomain := by
  have hpdf := modGaussianDensity_isProbabilityDensityOn_fundamentalDomain L B hB s hs
  exact IsProbabilityDensityOn.integrableOn hpdf
    (LatticeBasis.fundamentalDomain_measurableSet B)

/-- The L1 distance (Statistical distance / Total Variation distance) between the mod-Gaussian and uniform measures on the fundamental domain. -/
theorem measure_L1Dist_modGaussian_vs_uniform_le
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) (s : ℝ) (hs : 0 < s) :
    (1 / 2) * ∫ x in B.fundamentalDomain,
        |modGaussianDensity L s x - uniformDensity L x|
      ≤ (1 / 2) * rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
  simpa using statDist_modGaussian_vs_uniform_le L B hB s hs

/--
The probability measure induced by the modulo-Gaussian density on
`B.fundamentalDomain`.
-/
noncomputable def modGaussianProbabilityMeasureOnFundamentalDomain
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) (s : ℝ) (hs : 0 < s) :
    MeasureTheory.ProbabilityMeasure (𝓔 n) :=
  ⟨modGaussianMeasureOnFundamentalDomain L B s,
    modGaussianMeasureOnFundamentalDomain_isProbabilityMeasure L B hB s hs⟩

/--
The probability measure induced by the uniform density on `B.fundamentalDomain`.
-/
noncomputable def uniformProbabilityMeasureOnFundamentalDomain
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) :
    MeasureTheory.ProbabilityMeasure (𝓔 n) :=
  ⟨uniformMeasureOnFundamentalDomain L B,
    uniformMeasureOnFundamentalDomain_isProbabilityMeasure L B hB⟩

/--
TV-distance bound between modulo-Gaussian and uniform laws on a fundamental domain.
-/
theorem tvDist_modGaussian_vs_uniform_le
    (L : EuclideanLattice n n) (B : SquareLatticeBasis n)
    (hB : isBasisFor B L) (s : ℝ) (hs : 0 < s) :
    LatticeCrypto.Utils.Probability.tvDist
        (modGaussianProbabilityMeasureOnFundamentalDomain L B hB s hs)
        (uniformProbabilityMeasureOnFundamentalDomain L B hB)
      ≤ ENNReal.ofReal (rhoSMassOn (1 / s) 0 L.dual {0}ᶜ) := by
  let p : MeasureTheory.ProbabilityMeasure (𝓔 n) :=
    modGaussianProbabilityMeasureOnFundamentalDomain L B hB s hs
  let q : MeasureTheory.ProbabilityMeasure (𝓔 n) :=
    uniformProbabilityMeasureOnFundamentalDomain L B hB
  let f : 𝓔 n → ℝ := densityOnSet (modGaussianDensity L s) B.fundamentalDomain
  let g : 𝓔 n → ℝ := densityOnSet (uniformDensity L) B.fundamentalDomain
  have hf_int_on : MeasureTheory.IntegrableOn (modGaussianDensity L s) B.fundamentalDomain := by
    exact modGaussianDensity_integrableOn_fundamentalDomain L B hB s hs
  have hg_int_on : MeasureTheory.IntegrableOn (uniformDensity L) B.fundamentalDomain := by
    have hpdf : IsProbabilityDensityOn (uniformDensity L) B.fundamentalDomain :=
      uniformDensity_isProbabilityDensityOn_fundamentalDomain L B hB
    exact IsProbabilityDensityOn.integrableOn hpdf (LatticeBasis.fundamentalDomain_measurableSet B)
  have hf_int : MeasureTheory.Integrable f := by
    simpa [f, densityOnSet, MeasureTheory.integrable_indicator_iff
      (LatticeBasis.fundamentalDomain_measurableSet B)] using hf_int_on
  have hg_int : MeasureTheory.Integrable g := by
    simpa [g, densityOnSet, MeasureTheory.integrable_indicator_iff
      (LatticeBasis.fundamentalDomain_measurableSet B)] using hg_int_on
  have hf_nonneg : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (𝓔 n))] f := by
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : x ∈ B.fundamentalDomain
    · simp [f, densityOnSet, hx, modGaussianDensity_nonneg L s hs x]
    · simp [f, densityOnSet, hx]
  have hg_nonneg : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (𝓔 n))] g := by
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : x ∈ B.fundamentalDomain
    · have hx_nonneg : 0 ≤ uniformDensity L x := by
        unfold uniformDensity
        exact L.dual.det_pos.le
      simp [g, densityOnSet, hx, hx_nonneg]
    · simp [g, densityOnSet, hx]
  have hf_mass : ∫ x, f x = 1 := by
    calc
      ∫ x, f x = ∫ x in B.fundamentalDomain, modGaussianDensity L s x := by
        simpa [f, densityOnSet] using
          (MeasureTheory.integral_indicator (LatticeBasis.fundamentalDomain_measurableSet B)
            (f := modGaussianDensity L s))
      _ = 1 := integral_modGaussianDensity_eq_one L B hB s hs
  have hg_mass : ∫ x, g x = 1 := by
    calc
      ∫ x, g x = ∫ x in B.fundamentalDomain, uniformDensity L x := by
        simpa [g, densityOnSet] using
          (MeasureTheory.integral_indicator (LatticeBasis.fundamentalDomain_measurableSet B)
            (f := uniformDensity L))
      _ = 1 := (uniformDensity_isProbabilityDensityOn_fundamentalDomain L B hB).2
  have hp :
      (p : MeasureTheory.Measure (𝓔 n))
        = (MeasureTheory.volume : MeasureTheory.Measure (𝓔 n)).withDensity
            (fun x => ENNReal.ofReal (f x)) := by
    change modGaussianMeasureOnFundamentalDomain L B s =
      (MeasureTheory.volume : MeasureTheory.Measure (𝓔 n)).withDensity
        (fun x => ENNReal.ofReal (f x))
    simp [modGaussianMeasureOnFundamentalDomain, measureOfDensityOn, f]
  have hq :
      (q : MeasureTheory.Measure (𝓔 n))
        = (MeasureTheory.volume : MeasureTheory.Measure (𝓔 n)).withDensity
            (fun x => ENNReal.ofReal (g x)) := by
    change uniformMeasureOnFundamentalDomain L B =
      (MeasureTheory.volume : MeasureTheory.Measure (𝓔 n)).withDensity
        (fun x => ENNReal.ofReal (g x))
    simp [uniformMeasureOnFundamentalDomain, measureOfDensityOn, g]
  have h_tv_le_l1 :
      LatticeCrypto.Utils.Probability.tvDist p q
        ≤ ENNReal.ofReal (∫ x, |f x - g x|) := by
    exact LatticeCrypto.Utils.Probability.tvDist_le_l1_of_withDensity
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (𝓔 n)))
      (p := p) (q := q) (f := f) (g := g)
      hf_int hg_int hf_nonneg hg_nonneg hp hq
  have h_l1_eq :
      ∫ x, |f x - g x|
        = ∫ x in B.fundamentalDomain, |modGaussianDensity L s x - uniformDensity L x| := by
    have h_zero_out : ∀ x, x ∉ B.fundamentalDomain → |f x - g x| = 0 := by
      intro x hx
      simp [f, g, densityOnSet, hx]
    have h_set :
        ∫ x in B.fundamentalDomain, |f x - g x|
          = ∫ x in B.fundamentalDomain, |modGaussianDensity L s x - uniformDensity L x| := by
      refine MeasureTheory.setIntegral_congr_fun (LatticeBasis.fundamentalDomain_measurableSet B) ?_
      intro x hx
      simp [f, g, densityOnSet, hx]
    calc
      ∫ x, |f x - g x| = ∫ x in B.fundamentalDomain, |f x - g x| := by
        symm
        exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero h_zero_out
      _ = ∫ x in B.fundamentalDomain, |modGaussianDensity L s x - uniformDensity L x| := h_set
  have h_real_bound :
      ∫ x, |f x - g x| ≤ rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
    have hhalf :
        (1 / 2) * ∫ x, |f x - g x|
          ≤ (1 / 2) * rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
      simpa [h_l1_eq] using measure_L1Dist_modGaussian_vs_uniform_le L B hB s hs
    nlinarith [hhalf]
  have h_bound :
      ENNReal.ofReal (∫ x, |f x - g x|)
        ≤ ENNReal.ofReal (rhoSMassOn (1 / s) 0 L.dual {0}ᶜ) := by
    apply ENNReal.ofReal_le_ofReal
    exact h_real_bound
  calc
    LatticeCrypto.Utils.Probability.tvDist
        (modGaussianProbabilityMeasureOnFundamentalDomain L B hB s hs)
        (uniformProbabilityMeasureOnFundamentalDomain L B hB)
      = LatticeCrypto.Utils.Probability.tvDist p q := by rfl
    _ ≤ ENNReal.ofReal (∫ x, |f x - g x|) := h_tv_le_l1
    _ ≤ ENNReal.ofReal (rhoSMassOn (1 / s) 0 L.dual {0}ᶜ) := h_bound

end mathlib_measures

end coset_sampling

end LatticeCrypto.Foundations.Gaussian.Sampling
