import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.AddCircleMulti

import LatticeCrypto.Foundations.Gaussian.Defs
import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Foundations.Lattice.FundamentalDomain
import LatticeCrypto.Foundations.Lattice.Integral
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec


open scoped Real
open scoped RealInnerProductSpace
open scoped FourierTransform
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Foundations.Lattice
open LatticeCrypto.Foundations.Lattice.Integral

namespace LatticeCrypto.Foundations.Gaussian

/-!
  ## Basic results on Fourier transform (of the `rho` function)
-/
noncomputable section fourier_transform

variable {n : ℕ+}

open scoped Real Complex MeasureTheory
open LatticeCrypto.Foundations.Lattice
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Foundations.Gaussian

/-! Fourier transform of rhoS -/
noncomputable def rhoS_FT {n : ℕ+} (s : ℝ) (x : 𝓔 n) : ℂ :=
  𝓕 (fun v => (rhoS s v : ℂ)) x

/-- The Fourier transform of rhoS is a scaled version of itself -/
theorem rhoS_FT_eq {n : ℕ+} (s : ℝ) (h : 0 < s) (x : 𝓔 n) :
    rhoS_FT s x = (s ^ (n : ℕ) : ℂ) * (rhoS (1 / s) x : ℂ) := by
      -- Apply the theorem `fourierIntegral_gaussian_innerProductSpace` with `b = (π / s^2 : ℂ)`.
      have h_ft : Real.fourierIntegral (fun v => Complex.exp (- (Real.pi / s^2) * ‖v‖ ^ 2)) x = ((Real.pi / (Real.pi / s^2)) ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) / 2 : ℂ)) * Complex.exp (- Real.pi ^ 2 * ‖x‖ ^ 2 / (Real.pi / s^2)) := by
        convert fourierIntegral_gaussian_innerProductSpace _ _ using 3 ; ring_nf ; norm_num [ h.ne', Real.pi_pos.le ];
        exact mul_pos Real.pi_pos ( div_pos ( by norm_cast; positivity ) ( by positivity ) );
      convert h_ft using 1;
      · unfold rhoS_FT;
        rw [show (fun v : 𝓔 n => (rhoS s v : ℂ)) = (fun v : 𝓔 n => Complex.exp (-(Real.pi / s^2) * ‖v‖^2)) from by
          funext v
          rw [rhoS_of_ne_zero h.ne']
          norm_num [Complex.exp_neg, neg_div]
          norm_num [← Complex.exp_neg, norm_smul]
          ring_nf
          norm_num [abs_of_pos h]
          congr 1
          ring
        ];
      · norm_cast; simp +decide [ Real.pi_ne_zero ];
        rw [ ← Complex.cpow_natCast _ 2 ] ; rw [ ← Complex.cpow_mul ] ; ring_nf ; norm_num [ h.ne', Real.pi_pos.ne' ] ;
        · norm_cast; simp +decide [ mul_comm, mul_left_comm ] ;
          norm_num [ norm_smul, mul_pow, mul_assoc, mul_comm, mul_left_comm, Real.pi_pos.ne' ];
          simp +decide [ sq, mul_assoc, mul_left_comm, Real.pi_ne_zero ];
        · norm_num [ Complex.log_im, h.le ];
          rw [ Complex.arg_ofReal_of_nonneg h.le ] ; linarith [ Real.pi_pos ];
        · norm_num [ Complex.log_im ];
          rw [ Complex.arg_ofReal_of_nonneg h.le ] ; linarith [ Real.pi_pos ]


/-
g(x) = f(Bx)  =>  𝓕[g](y) = (1/det B) * 𝓕[f](B⁻ᵀ y)
-/
lemma fourier_transform_comp_linear_map
    {n : ℕ+}
    (f : 𝓔 n → ℂ) (B : (𝓔 n) ≃L[ℝ] (𝓔 n)) (y : 𝓔 n) :
    Real.fourierIntegral (f ∘ B) y =
    |LinearMap.det B.toLinearMap|⁻¹ *
    Real.fourierIntegral f ((LinearMap.toMatrix stdBasis stdBasis B.symm.toLinearMap).transpose.mulVec y) := by
  unfold Real.fourierIntegral;
  norm_num [ VectorFourier.fourierIntegral ];
  -- Apply the substitution $u = B(v)$ to the integral.
  have h_subst : ∀ {g : 𝓔 n → ℂ}, ∫ v, g v ∂MeasureTheory.volume = ∫ u, g (B.symm u) * (abs (B.toLinearEquiv.det : ℝ))⁻¹ ∂MeasureTheory.volume := by
    intro g;
    have := @MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul;
    specialize @this ( EuclideanSpace ℝ ( Fin n ) ) ( ℂ ) _ _ _ _ _ _;
    exact Set.univ;
    specialize @this ( fun x => B.symm x ) ( fun x => B.symm.toContinuousLinearMap );
    convert this ( MeasureTheory.MeasureSpace.volume ) ( by norm_num ) ( fun x _ => ?_ ) ( fun x _ y _ hxy => ?_ ) g using 1 <;> norm_num [ ContinuousLinearMap.det ];
    · simp +decide [ mul_comm, MeasureTheory.integral_mul_const ];
      exact Or.inl rfl;
    · exact ContinuousLinearEquiv.hasFDerivAt B.symm;
    · simpa using congr_arg ( fun z => B z ) hxy;
  convert @h_subst ( fun v => 𝐞 ( -⟪v, y⟫ ) • f ( B v ) ) using 1;
  rw [ ← MeasureTheory.integral_const_mul ] ; congr ; ext ; norm_num ; ring_nf;
  -- By definition of matrix multiplication and the properties of the inner product, we can simplify the expression.
  have h_inner : ∀ (x : 𝓔 n), ⟪B.symm x, y⟫ = ⟪x, (LinearMap.toMatrix stdBasis stdBasis B.symm).transpose.mulVec y⟫ := by
    intro x; rw [ EuclideanSpace.inner_eq_star_dotProduct ] ; rw [ EuclideanSpace.inner_eq_star_dotProduct ] ; norm_num [ Matrix.mulVec, dotProduct ] ;
    simp +decide [ mul_comm, mul_left_comm, Finset.mul_sum _ _ _, LinearMap.toMatrix_apply ];
    rw [ Finset.sum_comm ];
    -- By definition of matrix multiplication and the properties of the inner product, we can simplify the expression further.
    have h_inner : ∀ (x : 𝓔 n), B.symm x = ∑ i, x i • B.symm (stdBasis i) := by
      intro x; exact (by
      convert B.symm.pi_apply_eq_sum_univ x using 1;
      congr! 2;
      congr! 1;
      ext; simp [stdBasis];
      grind +ring);
    rw [ h_inner ] ; simp +decide ;
    rw [ Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_apply ] ; simp +decide [ Finset.mul_sum _ _ _ ];
    congr! 3;
  aesop

/-- Specialization of theorem `fourier_transform_comp_linear_map` with the linear
  map coming from a lattice basis.
-/
theorem fourier_transform_comp_linear_map_from_lattice (L : EuclideanLattice n n) (f : 𝓔 n → ℂ) (y : 𝓔 n) :
    𝓕 (f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) y = L.det⁻¹ * 𝓕 f (L.basis.asMatrix.transpose⁻¹.mulVec y) := by
  convert fourier_transform_comp_linear_map f _ _ using 4;
  · unfold EuclideanLattice.det;
    unfold LatticeBasis.volume;
    erw [ LinearMap.det_toLin' ];
  · rw [ Matrix.inv_eq_left_inv ];
    ext i j ; simp +decide [ Matrix.mul_apply, Matrix.transpose_apply ];
    have := Matrix.mul_nonsing_inv ( L.basis.asMatrix ) ( show IsUnit ( Matrix.det L.basis.asMatrix ) from ?_ );
    · convert congr_fun ( congr_fun this j ) i using 1;
      · rw [ Matrix.mul_apply ];
        congr! 1;
        rw [ mul_comm ];
        congr! 2;
        exact (LinearEquiv.eq_symm_apply (LinearMap.toMatrix stdBasis stdBasis)).mp rfl;
      · simp +decide [ Matrix.one_apply ];
        grind;
    · exact isUnit_iff_ne_zero.mpr ( by simpa [ Matrix.det_transpose ] using L.basis.det_ne_zero )

/-- Alternative form of `fourier_transform_comp_linear_map_from_lattice`
  that connects the Fourier transform of `f` composed with the dual lattice basis.
-/
theorem fourier_transform_comp_linear_map_from_lattice_dual (L : EuclideanLattice n n) (f : 𝓔 n → ℂ) (y : 𝓔 n) :
    𝓕 (f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) y = L.dual.det * 𝓕 f (L.basis.dual.asMatrix.mulVec y) := by
  convert fourier_transform_comp_linear_map_from_lattice L f y using 2;
  -- Apply the theorem that states the determinant of the dual lattice is the inverse of the determinant of the original lattice.
  have h_det_dual : L.dual.det = 1 / L.det := by
    exact EuclideanLattice.dual_det_eq_inv L;
  aesop

/-- Specialization of theorem `fourier_transform_comp_linear_map` with `f` being `rhoS` -/
noncomputable def rhoST_FT {n : ℕ+} (s : ℝ) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (x : 𝓔 n) : ℂ :=
  𝓕 (fun v => (rhoST s T v : ℂ)) x

/-- The Fourier transform of rhoST is a scaled-tilted version of the Fourier transform of rhoS -/
theorem rhoST_FT_eq_scaled_rhoS {n : ℕ+} (s : ℝ) (T: (𝓔 n) ≃L[ℝ] (𝓔 n)) (x : 𝓔 n) :
  rhoST_FT s T x = |LinearMap.det T.toLinearMap|⁻¹ * rhoS_FT s ((T.symm.toLinearMap.toMatrix stdBasis stdBasis).transpose.mulVec x) := by
  simpa [rhoST_FT, rhoS_FT, rhoST_eq_rhoS_T_x] using
    (fourier_transform_comp_linear_map (f := fun v => (rhoS s v : ℂ)) (B := T) (y := x))

end fourier_transform

/-!
  # Fourier Series of periodic functions over lattices
-/
noncomputable section fourier_series

variable {n : ℕ+}

open scoped Real Complex MeasureTheory
open scoped RealInnerProductSpace
/-
  Define the measure on the quotient space 𝓔 n / L as the pushforward of the Lebesgue measure
  restricted to the fundamental domain.
-/

/-- The measure on the quotient space 𝓔 n ⧸ L.carrier, defined as the pushforward of
    the Lebesgue measure restricted to the fundamental domain. -/
noncomputable def quotientMeasure (L : EuclideanLattice n n) : MeasureTheory.Measure (𝓔 n ⧸ L.carrier.toAddSubgroup) :=
  MeasureTheory.Measure.map QuotientAddGroup.mk (MeasureTheory.volume.restrict L.basis.fundamentalDomain)

/-- The measure space instance on the quotient 𝓔 n ⧸ L.carrier -/
noncomputable def quotientMeasureSpace (L : EuclideanLattice n n) : MeasureTheory.MeasureSpace (𝓔 n ⧸ L.carrier.toAddSubgroup) where
  volume := quotientMeasure L

/-- The total measure of the quotient space equals the determinant of the lattice -/
lemma quotientMeasure_univ (L : EuclideanLattice n n) :
    quotientMeasure L Set.univ = ENNReal.ofReal L.det := by
  unfold quotientMeasure
  rw [MeasureTheory.Measure.map_apply QuotientAddGroup.measurable_coe MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  simp [lebesgueMeasure, EuclideanLattice.det_eq_measure_fundamentalDomain L]

/-- The induced topology on the quotient space -/
instance (L : EuclideanLattice n n) : TopologicalSpace L.Quotient :=
  _root_.instTopologicalSpaceQuotient


/-
  Define the Fourier coefficient of a function `g` over a lattice `L` as the integral of `g` over the fundamental domain of `L` multiplied by a complex exponential, normalized by the determinant of `L`.
  Note here `g` is not explicitly specified as a periodic function, but this definition makes sense only when `g` is periodic with respect to the lattice `L`.
-/
noncomputable def fourierCoefficient (L : EuclideanLattice n n) (g : 𝓔 n → ℂ) (w : L.dual.carrier) : ℂ :=
  (1 / L.det : ℂ) * ∫ x in L.basis.fundamentalDomain, g x * cexp (-2 * π * Complex.I * (inner ℝ x (w : 𝓔 n)))

/-- The Fourier coefficient of a real-valued function -/
noncomputable def fourierCoefficientReal
  (L : EuclideanLattice n n)
  (g : 𝓔 n → ℝ)
  (w : L.dual.carrier) : ℂ :=
  fourierCoefficient L (fun x => (g x : ℂ)) w

@[simp]
lemma fourierCoefficientReal_apply
  (L : EuclideanLattice n n)
  (g : 𝓔 n → ℝ)
  (w : L.dual.carrier) :
  fourierCoefficientReal L g w
    =
  (1 / L.det : ℂ) *
    ∫ x in L.basis.fundamentalDomain,
      (g x : ℂ) * cexp (-2 * π * Complex.I * (inner ℝ x (w : 𝓔 n))) :=
  rfl

/-
  Define the Fourier series of a function `g` as the sum of its Fourier coefficients multiplied by complex exponentials.
  Note here both `g` and its Fourier coeff will be bundled in `coeffs`.
-/
noncomputable def fourierSeries (L : EuclideanLattice n n) (g : 𝓔 n → ℂ) (x : 𝓔 n) : ℂ :=
  ∑' w : L.dual.carrier, fourierCoefficient L g w * cexp (2 * π * Complex.I * (inner ℝ x (w : 𝓔 n)))


/--
  Fourier coefficient for a function explicitly defined on the quotient space.
  It lifts the function to the fundamental domain and applies the standard definition.
-/
noncomputable def fourierCoefficientOnQuotient
    (L : EuclideanLattice n n)
    (g : L.Quotient → ℂ)
    (w : L.dual.carrier) : ℂ :=
  fourierCoefficient L (fun x => g (QuotientAddGroup.mk x)) w

/-- The Fourier coefficient of a function on the quotient space equals the Fourier coefficient of its lift -/
theorem fourierCoefficientOnQuotient_eq (L : EuclideanLattice n n)
    (g : L.Quotient → ℂ) (w : L.dual.carrier) :
    fourierCoefficientOnQuotient L g w = fourierCoefficient L (g ∘ QuotientAddGroup.mk) w :=
  rfl

/--
  If you have a periodic function `f` on the whole space, and you descend it to the quotient,
  the coefficients match your original definition.
-/
theorem fourierCoefficient_eq_quotient (L : EuclideanLattice n n) (f : 𝓔 n → ℂ) (w : L.dual.carrier) :
    fourierCoefficientOnQuotient L (periodizeQuotient f L) w =
    fourierCoefficient L (periodize f L) w := by
  -- This follows immediately from the property that periodizeQuotient lifted is periodize
  simp only [fourierCoefficientOnQuotient]
  congr

/--
  The Fourier series viewed as a function on the Quotient.
  This is well-defined because the Fourier series terms (exponentials of dual vectors)
  are naturally periodic over L.
-/
noncomputable def fourierSeriesOnQuotient (L : EuclideanLattice n n)
    (g : 𝓔 n → ℂ) (x_quot : L.Quotient) : ℂ :=
  fourierSeries L g (Quot.out x_quot)

/--
The complex exponential term involving the inner product with a dual lattice vector is periodic with respect to the lattice.
-/
lemma cexp_inner_dual_periodicity (L : EuclideanLattice n n) (v : L.carrier) (w : L.dual.carrier) (x : 𝓔 n) :
    cexp (-2 * π * Complex.I * inner ℝ (x + v) (w : 𝓔 n)) = cexp (-2 * π * Complex.I * inner ℝ x (w : 𝓔 n)) := by
      -- Since $⟨v, w⟩_ℝ = m$ for some integer $m$, we have $e^{-2π i m} = 1$.
      have h_inner : ∃ m : ℤ, (inner ℝ (v : 𝓔 n) (w : 𝓔 n)) = m := by
        have := LatticeCrypto.Foundations.Lattice.EuclideanLattice.dual_carrier_eq_integralDual L;
        replace this := Set.ext_iff.mp this w; aesop;
      obtain ⟨ m, hm ⟩ := h_inner; simp +decide ;
      rw [ inner_add_left ] ; push_cast [ hm ] ; rw [ Complex.exp_eq_exp_iff_exists_int ] ; exact ⟨ -m, by push_cast; ring ⟩ ;

/--
The integral of `|f(x + v)|` over the fundamental domain is equal to the integral of `|f(x)|` over the shifted fundamental domain.
-/
lemma integral_shift_eq_integral_domain (f : 𝓔 n → ℝ) (L : EuclideanLattice n n) (v : L.carrier) :
    ∫ x in L.basis.fundamentalDomain, |f (x + v)| = ∫ x in Set.image (fun y => (v : 𝓔 n) + y) L.basis.fundamentalDomain, |f x| := by
      rw [ MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul ] <;> norm_num [ add_comm ];
      any_goals intro x hx; exact hasFDerivAt_id x |> HasFDerivAt.hasFDerivWithinAt;
      · norm_num [ ContinuousLinearMap.det ];
      · exact L.basis.fundamentalDomain_measurableSet;

/--
The sum of the integrals of the absolute value of the shifted function over the fundamental domain is summable, assuming the function is integrable.
-/
lemma summable_integral_abs_shift (f : 𝓔 n → ℝ) (L : EuclideanLattice n n) (hf : MeasureTheory.Integrable f) :
    Summable (fun v : L.carrier => ∫ x in L.basis.fundamentalDomain, |f (x + v)|) := by
      have h_partition : ∫ x, |f x| = ∑' v : L.carrier, ∫ x in (Set.image (fun y => (v : 𝓔 n) + y) L.basis.fundamentalDomain), |f x| := by
        have := @MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum L.carrier;
        convert this _ _ _;
        · constructor;
          exact fun x => Measurable.of_discrete;
        · constructor;
          simp +zetaDelta at *;
          intro a ha s hs; erw [ MeasureTheory.measure_preimage_add ] ;
        · exact EuclideanLattice.fundamentalDomain_isAddFundamentalDomain L MeasureTheory.volume;
        · exact hf.norm;
      have h_abs_integrable : Summable (fun v : L.carrier => ∫ x in (Set.image (fun y => (v : 𝓔 n) + y) L.basis.fundamentalDomain), |f x|) := by
        contrapose! h_partition;
        rw [ tsum_eq_zero_of_not_summable h_partition ] ; norm_num;
        rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg ( fun x => abs_nonneg _ ) ];
        · intro h; simp_all +decide [ Filter.EventuallyEq ] ;
          exact h_partition <| ⟨ _, hasSum_single 0 fun v hv => by rw [ MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero ] ; filter_upwards [ h ] with x hx; aesop ⟩;
        · exact hf.abs;
      convert h_abs_integrable using 2 ; rw [ integral_shift_eq_integral_domain ]

/--
The integral of the periodization of `f` over the fundamental domain is equal to the sum of the integrals of `f(x + v)` over the fundamental domain.
-/
lemma integral_periodize_eq_tsum_integral_shifts (f : 𝓔 n → ℝ) (L : EuclideanLattice n n) (hf : MeasureTheory.Integrable f) :
    ∫ x in L.basis.fundamentalDomain, periodize f L x = ∑' v : L.carrier, ∫ x in L.basis.fundamentalDomain, f (x + v) := by
      rw [ ← MeasureTheory.integral_tsum ];
      · rfl;
      · exact fun v => hf.comp_add_right _ |> MeasureTheory.Integrable.aestronglyMeasurable |> fun h => h.mono_measure <| MeasureTheory.Measure.restrict_le_self;
      · convert ENNReal.ofReal_ne_top;
        swap;
        exact ∑' v : L.carrier, ∫ x in L.basis.fundamentalDomain, |f ( x + v )|;
        rw [ ENNReal.ofReal_tsum_of_nonneg ];
        · congr! 2;
          rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
          · norm_num [ ENNReal.ofReal ];
            exact rfl;
          · exact MeasureTheory.Integrable.abs ( hf.comp_add_right _ |> MeasureTheory.Integrable.integrableOn );
          · exact Filter.Eventually.of_forall fun x => abs_nonneg _;
        · exact fun _ => MeasureTheory.integral_nonneg fun _ => abs_nonneg _;
        · exact summable_integral_abs_shift f L hf

/--
The integral of `f(x + v)` over the fundamental domain is equal to the integral of `f(x)` over the shifted fundamental domain.
-/
lemma integral_shift_eq_integral_domain_real (f : 𝓔 n → ℝ) (L : EuclideanLattice n n) (v : L.carrier) :
    ∫ x in L.basis.fundamentalDomain, f (x + v) = ∫ x in Set.image (fun y => (v : 𝓔 n) + y) L.basis.fundamentalDomain, f x := by
      -- Since the function (v : 𝓔 n) + y is just a translation, which is a measure-preserving transformation, the integrals should be equal.
      have h_measure_preserving : MeasureTheory.MeasurePreserving (fun y => (v : 𝓔 n) + y) MeasureTheory.volume MeasureTheory.volume := by
        exact MeasureTheory.measurePreserving_add_left _ _;
      rw [ MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul ];
      any_goals intro x hx; exact hasFDerivAt_id x |> HasFDerivAt.const_add _ |> HasFDerivAt.hasFDerivWithinAt;
      · simp +decide [ add_comm, ContinuousLinearMap.det ];
      · exact L.basis.fundamentalDomain_measurableSet
      · exact fun x hx y hy hxy => by simpa using hxy;

/--
The integral of the periodization of a real-valued function `f` over the fundamental domain of a lattice `L` is equal to the integral of `f` over the entire space, assuming `f` is integrable.
-/
lemma integral_periodize_eq_integral_real (f : 𝓔 n → ℝ) (L : EuclideanLattice n n) (hf : MeasureTheory.Integrable f) :
    ∫ x in L.basis.fundamentalDomain, periodize f L x = ∫ x, f x := by
      -- Using the fact that $f$ is integrable, we can apply the result from the previous steps to rewrite the integral.
      have h_integral : (∫ x in L.basis.fundamentalDomain, periodize f L x) = ∑' v : L.carrier, (∫ x in L.basis.fundamentalDomain, f (x + v)) := by
        exact integral_periodize_eq_tsum_integral_shifts f L hf;
      rw [ h_integral ];
      have h_integral : ∑' v : L.carrier, ∫ x in Set.image (fun y => (v : 𝓔 n) + y) L.basis.fundamentalDomain, f x = ∫ x, f x := by
        have := L.fundamentalDomain_isAddFundamentalDomain (MeasureTheory.volume (α := 𝓔 n));
        convert this.integral_eq_tsum _ using 1;
        any_goals exact ℝ;
        any_goals try infer_instance;
        any_goals exact f;
        ·
          rw [ eq_comm ];
          bound;
        · -- Since the lattice is a discrete subgroup, the addition is measurable.
          have h_measurable_vadd : Measurable (fun (p : L.carrier × 𝓔 n) => (p.1 : 𝓔 n) + p.2) := by
            fun_prop;
          constructor;
          exact fun x => h_measurable_vadd.comp ( measurable_id.prodMk measurable_const );
        · constructor;
          simp +zetaDelta at *;
          intro a ha s hs; erw [ MeasureTheory.measure_preimage_add ] ;
      convert h_integral using 3;
      (expose_names; exact integral_shift_eq_integral_domain_real f L x)

/-- The Periodization Lemma: If `g = periodize f L` for some `Integrable f`, then g_FS(w) = f_FT(w) / L.det -/
theorem fourierCoefficient_of_periodization_eq_fourierTransform (L : EuclideanLattice n n) (f : 𝓔 n → ℂ) (hf : MeasureTheory.Integrable f) (w : L.dual.carrier) :
    fourierCoefficient L (fun x => periodize f L x) w = (1 / L.det : ℂ) * 𝓕 (fun v => f v) (w : 𝓔 n) := by
      -- By definition of the Fourier transform, we can rewrite the integral as the sum of the Fourier transforms of the shifted functions.
      have h_fourier_transform : ∫ x in L.basis.fundamentalDomain, (periodize f L x) * cexp (-2 * Real.pi * Complex.I * (inner ℝ x (w : 𝓔 n))) = ∑' v : L.carrier, ∫ x in L.basis.fundamentalDomain, f (x + v) * cexp (-2 * Real.pi * Complex.I * (inner ℝ x (w : 𝓔 n))) := by
        rw [ ← MeasureTheory.integral_tsum ];
        · simp +decide [ periodize ];
          simp +decide only [EuclideanLattice.latticeSum, ← tsum_mul_right];
        · intro i;
          field_simp;
          refine' MeasureTheory.AEStronglyMeasurable.mul _ _;
          · exact MeasureTheory.Integrable.aestronglyMeasurable ( hf.comp_add_right _ ) |> fun h => h.mono_measure ( MeasureTheory.Measure.restrict_le_self );
          · fun_prop;
        · refine' ne_of_lt ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum fun v => _ ) _ );
          use fun v => ENNReal.ofReal ( ∫ x in L.basis.fundamentalDomain, ‖f ( x + v )‖ );
          · rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
            · refine' MeasureTheory.lintegral_mono fun x => _;
              rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num [ Complex.norm_exp ];
              exact not_eq_of_beq_eq_false rfl;
            · exact MeasureTheory.Integrable.norm ( hf.comp_add_right _ ) |> MeasureTheory.Integrable.restrict;
            · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
          · rw [ ← ENNReal.ofReal_tsum_of_nonneg ];
            · refine' ENNReal.ofReal_lt_top;
            · exact fun _ => MeasureTheory.integral_nonneg fun _ => norm_nonneg _;
            · simpa using summable_integral_abs_shift ( fun x => ‖f x‖ ) L ( hf.norm );
      -- By definition of the Fourier transform, we can rewrite the integral as the sum of the Fourier transforms of the shifted functions, using the periodicity of the exponential.
      have h_fourier_transform_shift : ∑' v : L.carrier, ∫ x in L.basis.fundamentalDomain, f (x + v) * cexp (-2 * Real.pi * Complex.I * (inner ℝ x (w : 𝓔 n))) = ∑' v : L.carrier, ∫ x in Set.image (fun y => (v : 𝓔 n) + y) L.basis.fundamentalDomain, f x * cexp (-2 * Real.pi * Complex.I * (inner ℝ x (w : 𝓔 n))) := by
        refine' tsum_congr fun v => _;
        rw [ MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul ];
        rotate_right;
        use fun x => 1;
        · have := cexp_inner_dual_periodicity L v w; simp_all +decide [ add_comm, inner_add_left ] ;
          erw [ ContinuousLinearMap.det ];
          erw [ LinearMap.det_id ] ; norm_num;
        · exact LatticeBasis.fundamentalDomain_measurableSet L.basis;
        · exact fun x hx => HasFDerivAt.hasFDerivWithinAt ( hasFDerivAt_id x |> HasFDerivAt.const_add _ );
        · exact fun x hx y hy hxy => by simpa using hxy;
      -- Since these shifted fundamental domains are disjoint and cover the entire space, we can apply the linearity of the integral.
      have h_integral_union : ∫ x, f x * cexp (-2 * Real.pi * Complex.I * (inner ℝ x (w : 𝓔 n))) = ∑' v : L.carrier, ∫ x in Set.image (fun y => (v : 𝓔 n) + y) L.basis.fundamentalDomain, f x * cexp (-2 * Real.pi * Complex.I * (inner ℝ x (w : 𝓔 n))) := by
        rw [ ← MeasureTheory.integral_iUnion ];
        · rw [ MeasureTheory.Measure.restrict_eq_self_of_ae_mem ];
          have := EuclideanLattice.partition_by_fundamentalDomain L;
          filter_upwards [ ] with x using by obtain ⟨ y, hy₁, hy₂ ⟩ := this x; exact Set.mem_iUnion.mpr ⟨ y, by simpa [ Set.mem_vadd_set_iff_neg_vadd_mem ] using hy₁ ⟩ ;
        · -- The fundamental domain is measurable, and translations are measurable functions, so the image of the fundamental domain under translation is measurable.
          have h_measurable : MeasurableSet (L.basis.fundamentalDomain) := by
            exact LatticeBasis.fundamentalDomain_measurableSet L.basis;
          intro v; rw [ Set.image_add_left ] ; exact h_measurable.preimage ( measurable_const.add measurable_id' ) ;
        · -- Since the fundamental domain is a fundamental domain for L, shifting it by different lattice points should give disjoint sets.
          have h_disjoint : ∀ v w : L.carrier, v ≠ w → Disjoint (Set.image (fun y => (v : 𝓔 n) + y) L.basis.fundamentalDomain) (Set.image (fun y => (w : 𝓔 n) + y) L.basis.fundamentalDomain) := by
            intros v w hvw;
            have := L.partition_by_fundamentalDomain;
            exact Set.disjoint_left.mpr fun x hxv hxw => hvw <| ExistsUnique.unique ( this x ) ( by simpa [ Set.mem_vadd_set_iff_neg_vadd_mem ] using hxv ) ( by simpa [ Set.mem_vadd_set_iff_neg_vadd_mem ] using hxw );
          exact fun v w hvw => h_disjoint v w hvw;
        · refine' MeasureTheory.Integrable.integrableOn _;
          refine' hf.norm.mono' _ _;
          · fun_prop;
          · norm_num [ Complex.norm_exp ];
      convert congr_arg ( fun x : ℂ => ( 1 / L.det : ℂ ) * x ) h_integral_union using 1;
      · unfold fourierCoefficient; aesop;
      · rw [ ← h_integral_union, Real.fourierIntegral ];
        unfold VectorFourier.fourierIntegral; norm_num [ innerₗ ] ;
        simp +decide [ mul_comm, innerₛₗ, Circle.smul_def ];
        norm_num [ Real.fourierChar, mul_assoc, mul_comm, mul_left_comm ];
        exact Or.inl ( by congr; ext; rw [ ← Complex.exp_neg ] )

/-- Specialization of the periodization theorem for real-value `f` -/
lemma fourierCoefficient_of_periodization_eq_fourierTransform_real (L : EuclideanLattice n n) (f : 𝓔 n → ℝ) (hf : MeasureTheory.Integrable f) (w : L.dual.carrier) :
    fourierCoefficientReal L (fun x => periodize f L x) w = (1 / L.det : ℂ) * 𝓕 (fun v => (f v : ℂ)) (w : 𝓔 n) := by
  -- Apply the periodization theorem to the real function `f` by converting it to a complex function.
  have h_complex_periodization : fourierCoefficient L (fun x => periodize (fun v => (f v : ℂ)) L x) w = (1 / L.det : ℂ) * 𝓕 (fun v => (f v : ℂ)) (w : 𝓔 n) := by
    -- Apply the periodization theorem to the complex function `f` by converting it to a complex function.
    apply fourierCoefficient_of_periodization_eq_fourierTransform L (fun v => (f v : ℂ)) (by
    exact hf.ofReal) w;
  convert h_complex_periodization using 2;
  -- The periodization of f as a real function is the same as the periodization of f as a complex function because the real function is just the real part of the complex function.
  simp [Gaussian.periodize];
  unfold Gaussian.fourierCoefficientReal Gaussian.fourierCoefficient; norm_num;
  congr!;
  unfold EuclideanLattice.latticeSum; norm_num;
  rw [ Complex.ofReal_tsum ]


/-- The periodization theorem for the scaled-tilted Gaussian -/
theorem fourierCoefficient_of_rhoST_periodize_eq_fourierTransform_rhoST
  (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (w : L.dual.carrier) :
    fourierCoefficient L (fun x => (rhoST_periodize s T L x : ℂ)) w = (1 / L.det : ℂ) * 𝓕 (fun v => (rhoST s T v : ℂ)) (w : 𝓔 n) := by
  convert fourierCoefficient_of_periodization_eq_fourierTransform L _ _ _
  · convert Complex.ofReal_tsum _
  · convert rhoST.integrable s hs.ne' T

end fourier_series

/-
 ## Proving the Inversion Formula for the Fourier Series on Z^n.
-/
section fourier_series_inversion_on_Zn


/-
  ### Relating Fourier coefficients on UnitAddTorus to that on R^n / Z^n.
-/
section Zn_equiv_UnitAddTorus

open scoped Real Complex MeasureTheory
open LatticeCrypto.Foundations.Lattice LatticeCrypto.Utils.Vec LatticeCrypto.Foundations.Gaussian
open scoped FourierTransform


variable {n : ℕ+}
private noncomputable abbrev Zn : EuclideanLattice n n := Z n

/-
Isomorphism between R^n / Z^n and the torus (R/Z)^n.
-/
/-- The map from R^n to the torus R^n/Z^n -/
def mapToTorus : (𝓔 n) →+ UnitAddTorus (Fin n) where
  toFun x i := QuotientAddGroup.mk (x i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- The canonical isomorphism between the quotient of Euclidean space by Z^n and the UnitAddTorus -/
noncomputable def quotientZnIsoUnitAddTorus : (𝓔 n) ⧸ Zn.carrier ≃+ UnitAddTorus (Fin n) := by
  let f := mapToTorus (n := n)
  have h_surj : Function.Surjective f := by
    intro x;
    use fun i => Classical.choose (Quotient.exists_rep (x i));
    ext i; exact Classical.choose_spec ( Quotient.exists_rep ( x i ) ) ;
  have h_ker : f.ker = Zn.carrier.toAddSubgroup := by
    -- The kernel of the mapToTorus function is the set of vectors where each component is an integer.
    ext x
    simp [f, mapToTorus];
    constructor <;> intro h <;> simp_all +decide [ funext_iff, Submodule.mem_span_range_iff_exists_fun ];
    · choose c hc using fun i => h i;
      use c; ext i; simp +decide [ Zn ] ;
      have h_comp : (∑ x : Fin n, c x • (EuclideanSpace.single x 1 : 𝓔 n)) i = c i := by
        rw [Finset.sum_apply, Finset.sum_eq_single i] <;> aesop
      have hsum : (∑ y : Fin n, c y • (Z n).basis.basis y) i = (c i : ℝ) := by
        simpa [Z, stdBasisZ, LatticeBasis.toLattice, stdBasis] using h_comp
      have hci : (c i : ℝ) = x i := by simpa using hc i
      exact hsum.trans hci
    · obtain ⟨ c, rfl ⟩ := h; simp_all +decide [ Zn ] ;
      intro x
      refine ⟨c x, ?_⟩
      have h_ortho : ∀ a : Fin n → ℤ,
          (∑ j : Fin n, a j • (EuclideanSpace.single j 1 : 𝓔 n)) x = a x := by
        intro a
        rw [Finset.sum_apply, Finset.sum_eq_single x] <;> aesop
      have hsum : (∑ y : Fin n, c y • (Z n).basis.basis y) x = (c x : ℝ) := by
        simpa [Z, stdBasisZ, LatticeBasis.toLattice, stdBasis] using h_ortho c
      have hzsmul : (fun z : ℤ => z • (1 : ℝ)) (c x) = (c x : ℝ) := by
        norm_num
      exact hzsmul.trans hsum.symm
  let iso := QuotientAddGroup.quotientKerEquivOfSurjective f h_surj
  -- We need to cast the domain from (𝓔 n) ⧸ f.ker to (𝓔 n) ⧸ Zn.carrier
  -- Since f.ker = Zn.carrier.toAddSubgroup, the quotients are the same.
  -- However, Zn.carrier is a Submodule, so we need to be careful with instances.
  -- We can construct the equiv manually to avoid instance hell if cast fails.
  refine AddEquiv.trans ?_ iso
  apply QuotientAddGroup.quotientAddEquivOfEq
  exact h_ker.symm

/--
The isomorphism applied to the projection of x is equal to the mapToTorus applied to x.
-/
lemma quotientZnIsoUnitAddTorus_mk_eq_mapToTorus (x : 𝓔 n) :
    quotientZnIsoUnitAddTorus (QuotientAddGroup.mk x) = mapToTorus x := by
      unfold quotientZnIsoUnitAddTorus;
      simp;
      rfl

/--
The periodization of a function f on Z^n, viewed as a function on UnitAddTorus.
-/
noncomputable def periodizeZnToTorus (f : 𝓔 n → ℂ) : UnitAddTorus (Fin n) → ℂ :=
  periodizeQuotient f Zn ∘ quotientZnIsoUnitAddTorus.symm

/-- The fourier polynomials from UnitAddTorus is essentially a simple exponential -/
theorem mFourier_eq_cexp (w : Fin n → ℤ) (x : 𝓔 n) :
  UnitAddTorus.mFourier (-w) (quotientZnIsoUnitAddTorus (QuotientAddGroup.mk x)) =
  cexp (-2 * π * Complex.I * inner ℝ x (piToEuc (fun i => (w i : ℝ)))) := by
    unfold UnitAddTorus.mFourier;
    -- By definition of quotientZnIsoUnitAddTorus, we have that quotientZnIsoUnitAddTorus x is the equivalence class of x in the quotient space.
    have h_quot : quotientZnIsoUnitAddTorus (QuotientAddGroup.mk x) = fun i => QuotientAddGroup.mk (x i) := by
      exact rfl;
    simp_all +decide [ fourier, piToEuc ];
    norm_num [ Complex.exp_neg, Complex.inner, Complex.conj_ofReal ];
    norm_num [ Complex.inv_def, Complex.normSq_eq_norm_sq, Complex.norm_exp, inner ];
    norm_num [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Complex.exp_sum ]

/--
The volume measure on the unit circle is the pushforward of the Lebesgue measure restricted to [0,1).
-/
lemma volume_unitAddCircle_eq_map :
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) =
    MeasureTheory.Measure.map QuotientAddGroup.mk (MeasureTheory.volume.restrict (Set.Ico 0 1)) := by
      have := @AddCircle.measurePreserving_mk ( 1 : ℝ );
      -- Apply the measure-preserving property of the quotient map.
      have := @this (by exact ⟨by norm_num⟩) 0;
      simp_all +decide ;
      exact Eq.symm ( by rw [ MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ico_ae_eq_Ioc ] ; exact this.map_eq )


/--
The product of quotient maps is measure preserving from the unit cube to the torus.
-/
lemma measurePreserving_pi_quotient :
    MeasureTheory.MeasurePreserving (fun (x : Fin n → ℝ) i => QuotientAddGroup.mk (x i))
      (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ico 0 1)))
      (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin n))) := by
        -- The quotient map from ℝ to ℝ/ℤ is measure-preserving.
        have h_quot : MeasureTheory.MeasurePreserving (fun x : ℝ => QuotientAddGroup.mk x : ℝ → UnitAddCircle) (MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (Set.Ico 0 1)) MeasureTheory.MeasureSpace.volume := by
          refine' ⟨ _, _ ⟩;
          · exact fun ⦃t⦄ a => a;
          · exact Eq.symm volume_unitAddCircle_eq_map;
        -- Apply the fact that the product of measure-preserving maps is measure-preserving.
        have h_prod : ∀ (f : Fin n → ℝ → UnitAddCircle), (∀ i, MeasureTheory.MeasurePreserving (f i) (MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (Set.Ico 0 1)) MeasureTheory.MeasureSpace.volume) → MeasureTheory.MeasurePreserving (fun x : Fin n → ℝ => fun i => f i (x i)) (MeasureTheory.Measure.pi fun _ => MeasureTheory.Measure.restrict MeasureTheory.MeasureSpace.volume (Set.Ico 0 1)) (MeasureTheory.Measure.pi fun _ => MeasureTheory.MeasureSpace.volume) := by
          exact fun f a =>
            MeasureTheory.measurePreserving_pi (fun x => MeasureTheory.volume.restrict (Set.Ico 0 1)) (fun x => MeasureTheory.volume) a;
        convert h_prod ( fun _ => fun x => QuotientAddGroup.mk x ) fun _ => h_quot using 1


/--
The map `mapToTorus` is measure preserving from the fundamental domain of `Zn` to the torus.
-/
lemma mapToTorus_measurePreserving :
    MeasureTheory.MeasurePreserving (mapToTorus (n := n)) (MeasureTheory.volume.restrict (Zn.basis.fundamentalDomain)) (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin n))) := by
      have h_map_to_torus : MeasureTheory.MeasurePreserving (fun (x : Fin n → ℝ) i => QuotientAddGroup.mk (x i)) (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ico 0 1))) (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin n))) := by
        exact measurePreserving_pi_quotient;
      have h_comb : MeasureTheory.MeasurePreserving (fun (x : Fin n → ℝ) i => ↑(x i)) (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ico 0 1))) (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin n))) ∧ MeasureTheory.MeasurePreserving (fun x : (EuclideanSpace ℝ (Fin n)) => eucToPi x) (MeasureTheory.volume.restrict (Set.pi Set.univ (fun _ : Fin n => Set.Ico (0 : ℝ) 1))) (MeasureTheory.Measure.pi (fun _ : Fin n => (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ico 0 1))) := by
        refine' ⟨ h_map_to_torus, _ ⟩;
        convert eucToPi_measurePreserving.restrict_preimage _;
        any_goals exact Set.pi Set.univ fun _ => Set.Ico 0 1;
        · ext; simp [eucToPi];
        · erw [ MeasureTheory.Measure.pi_eq ];
          intro s hs; erw [ MeasureTheory.Measure.restrict_apply ];
          · erw [ show ( Set.univ.pi s ∩ Set.univ.pi fun x => Set.Ico 0 1 : Set ( Fin n → ℝ ) ) = Set.pi Set.univ fun i => s i ∩ Set.Ico 0 1 by ext; aesop ] ; erw [ MeasureTheory.Measure.pi_pi ] ; aesop;
          · exact MeasurableSet.univ_pi hs;
        · exact MeasurableSet.univ_pi fun _ => measurableSet_Ico;
      convert h_comb.1.comp h_comb.2 using 1;
      rw [ Zn_fundamentalDomain_eq_pi_Ico ]

/--
The vector `ZVec.toZnDual w` viewed as an element of `𝓔 n` is equal to `zToE w`.
-/
lemma coe_toZnDual_eq_zToE (w : Fin n → ℤ) :
    (ZVec.toZnDual w : 𝓔 n) = zToE w := by
      -- By definition of `ZVec.toZnDual`, we have `(ZVec.toZnDual w : 𝓔 n) = (ZVec.toZn w : 𝓔 n)`.
      have hZn : (ZVec.toZnDual w : 𝓔 n) = (ZVec.toZn w : 𝓔 n) := by
        congr;
        · ext; simp [Zn_dual_eq_Zn];
        · -- By definition of `ZVec.toZnDual`, we have `(ZVec.toZnDual w : (Zn (n := n)).dual.carrier) = (ZVec.toZn w : (Zn (n := n)).carrier)`.
          simp [ZVec.toZnDual];
      unfold zToE; aesop;

-- Abbrev to shorten your integrand
noncomputable def torusIntegrand (f : 𝓔 n → ℂ) (w : ZVec n) (t : UnitAddTorus (Fin n)) : ℂ :=
  (UnitAddTorus.mFourier (-w)) t * periodizeZnToTorus (n:=n) f t

/--
The Fourier coefficient is the integral of the function against the Fourier basis element.
-/
lemma torusFourierCoeff_torusIntegrand (f : 𝓔 n → ℂ) (w : Fin n → ℤ) :
  UnitAddTorus.mFourierCoeff (periodizeZnToTorus f) w = ∫ t : UnitAddTorus (Fin n), torusIntegrand f w t := by
    unfold UnitAddTorus.mFourierCoeff torusIntegrand;
    convert rfl;
    · -- The measure space on the unit additive circle is defined as the quotient measure of the real numbers with the Lebesgue measure.
      simp [AddCircle.measureSpace, instMeasureSpaceUnitAddCircle];
      congr;
    · -- By definition of `AddCircle.measureSpace`, it is equal to `instMeasureSpaceUnitAddCircle`.
      simp [AddCircle.measureSpace];
      congr

/--
The map from Euclidean space to the torus is continuous.
-/
lemma mapToTorus_continuous : Continuous (mapToTorus (n := n)) := by
  exact continuous_pi_iff.mpr fun i => continuous_quot_mk.comp <| continuous_apply i

/--
The Fourier basis function on the torus evaluated at the projection of x is equal to the complex exponential of the inner product of x and the integer vector w.
-/
lemma mFourier_mapToTorus_eq (w : Fin n → ℤ) (x : 𝓔 n) :
    UnitAddTorus.mFourier (-w) (mapToTorus x) =
    cexp (-2 * π * Complex.I * inner ℝ x (zToE w)) := by
      convert mFourier_eq_cexp w x using 1

/--
The periodization on the torus evaluated at the projection of x is equal to the periodization on the lattice evaluated at x.
-/
lemma periodizeZnToTorus_eq_periodize (f : 𝓔 n → ℂ) (x : 𝓔 n) :
    periodizeZnToTorus f (mapToTorus x) = periodize f Zn x := by
  unfold periodizeZnToTorus
  simp only [Function.comp_apply]
  rw [← quotientZnIsoUnitAddTorus_mk_eq_mapToTorus]
  simp only [AddEquiv.symm_apply_apply]
  rw [periodizeQuotient_mk]

/--
The integrand on the torus, pulled back to the fundamental domain, is equal to the integrand on the lattice.
-/
lemma integrand_eq (f : 𝓔 n → ℂ) (w : Fin n → ℤ) (x : 𝓔 n) :
    torusIntegrand f w (mapToTorus x) =
    periodize f Zn x * cexp (-2 * π * Complex.I * inner ℝ x (ZVec.toZnDual w : 𝓔 n)) := by
      have h_periodize : periodizeZnToTorus f (mapToTorus x) = periodize f Zn x := by
        exact periodizeZnToTorus_eq_periodize f x;
      unfold torusIntegrand;
      rw [ mul_comm, h_periodize, mFourier_mapToTorus_eq ];
      rw [ coe_toZnDual_eq_zToE ]

/-
Definition of the inverse map from torus to fundamental domain.
-/
noncomputable def torusToFundamentalDomain (u : UnitAddTorus (Fin n)) : 𝓔 n :=
  piToEuc (fun i => AddCircle.liftIco 1 0 (id : ℝ → ℝ) (u i))

/--
The inverse map maps into the fundamental domain.
-/
lemma torusToFundamentalDomain_mem (u : UnitAddTorus (Fin n)) :
    torusToFundamentalDomain u ∈ Zn.basis.fundamentalDomain := by
  rw [Zn_fundamentalDomain_eq_pi_Ico]
  simp [torusToFundamentalDomain]
  intro i
  -- We need to show that liftIco returns a value in [0, 1).
  -- liftIco f x = f (equivIco x)
  -- equivIco maps to Ico 0 1.
  -- f is id.
  -- So it maps to Ico 0 1.
  -- We need to unfold liftIco or use a property.
  unfold AddCircle.liftIco
  simp
  have := (AddCircle.equivIco (1 : ℝ) 0 (u i)).2
  simp at this
  exact this

/--
The inverse map from torus to fundamental domain is measurable.
-/
lemma torusToFundamentalDomain_measurable : Measurable (torusToFundamentalDomain (n := n)) := by
  -- The function `torusToFundamentalDomain` is a composition of measurable functions: `piToEuc` and `liftIco`.
  have h_measurable : Measurable (fun u : UnitAddTorus (Fin n) => (fun i => AddCircle.liftIco 1 0 (fun x => x) (u i))) := by
    apply_rules [ measurable_pi_lambda ];
    intro a; apply_rules [ Measurable.comp, measurable_const ];
    all_goals try fun_prop;
    exact ( AddCircle.measurableEquivIco 1 0 ).measurable.comp ( measurable_pi_apply a );
  exact h_measurable

/--
The map to torus is a left inverse of the map to fundamental domain.
-/
lemma mapToTorus_torusToFundamentalDomain (u : UnitAddTorus (Fin n)) :
    mapToTorus (torusToFundamentalDomain u) = u := by
      unfold mapToTorus torusToFundamentalDomain
      ext i
      simp [AddCircle.liftIco];
      exact ( AddCircle.equivIco _ _ ).symm_apply_apply _

/--
The inverse map is a left inverse on the fundamental domain.
-/
lemma torusToFundamentalDomain_mapToTorus (x : 𝓔 n) (hx : x ∈ Zn.basis.fundamentalDomain) :
    torusToFundamentalDomain (mapToTorus x) = x := by
      -- By definition of `mapToTorus`, we know that `mapToTorus x` is the equivalence class of `x` in the torus.
      -- The `torusToFundamentalDomain` function mapToTorus` is the inverse, so it should map `mapToTorus x` back to `x`.
      unfold torusToFundamentalDomain mapToTorus
      simp [Zn_fundamentalDomain_eq_pi_Ico] at *;
      -- By definition of `piToEuc`, we know that `piToEuc (fun i => AddCircle.liftIco 1 0 id (x i))` is the same as `x`.
      funext i; exact (by
      simp +decide [ AddCircle.liftIco ];
      simp +decide [ piToEuc ];
      exact hx i ( Set.mem_univ i ))

/--
The inverse map is measure preserving.
-/
lemma torusToFundamentalDomain_measurePreserving :
    MeasureTheory.MeasurePreserving (torusToFundamentalDomain (n := n)) MeasureTheory.volume (MeasureTheory.volume.restrict Zn.basis.fundamentalDomain) := by
      -- The map `torusToFundamentalDomain` is a right inverse of `mapToTorus` on the fundamental domain.
      have h_right_inv : ∀ x : 𝓔 n, x ∈ Zn.basis.fundamentalDomain → torusToFundamentalDomain (mapToTorus x) = x := by
        exact fun x a => torusToFundamentalDomain_mapToTorus x a;
      -- Since `mapToTorus` is measure preserving and surjective, and `torusToFundamentalDomain` is its right inverse on the fundamental domain, `torusToFundamentalDomain` is also measure preserving.
      have h_measure_preserving : MeasureTheory.MeasurePreserving torusToFundamentalDomain (MeasureTheory.Measure.map (mapToTorus (n := n)) (MeasureTheory.volume.restrict (Zn.basis.fundamentalDomain))) (MeasureTheory.volume.restrict (Zn.basis.fundamentalDomain)) := by
        refine' ⟨ _, _ ⟩;
        · exact torusToFundamentalDomain_measurable;
        · rw [ MeasureTheory.Measure.map_map ];
          · rw [ MeasureTheory.Measure.map_congr, MeasureTheory.Measure.map_id ];
            filter_upwards [ MeasureTheory.ae_restrict_mem ( show MeasurableSet ( Zn.basis.fundamentalDomain ) from by exact
              Zn.basis.fundamentalDomain_measurableSet ) ] with x hx using h_right_inv x hx;
          · exact torusToFundamentalDomain_measurable;
          · exact mapToTorus_continuous.measurable;
      -- Since `mapToTorus` is measure preserving and surjective, the pushforward measure is equal to the volume measure on the torus.
      have h_pushforward : MeasureTheory.Measure.map (mapToTorus (n := n)) (MeasureTheory.volume.restrict (Zn.basis.fundamentalDomain)) = MeasureTheory.volume := by
        apply mapToTorus_measurePreserving.map_eq;
      aesop

/--
A function on the torus is AEStronglyMeasurable iff its pullback to the fundamental domain is.
-/
lemma aestronglyMeasurable_comp_mapToTorus_iff (g : UnitAddTorus (Fin n) → ℂ) :
    MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume ↔ MeasureTheory.AEStronglyMeasurable (g ∘ mapToTorus) (MeasureTheory.volume.restrict Zn.basis.fundamentalDomain) := by
  constructor
  · intro h
    exact h.comp_measurePreserving (LatticeCrypto.Foundations.Gaussian.mapToTorus_measurePreserving (n := n))
  · intro h
    have h_eq : g = (g ∘ mapToTorus) ∘ torusToFundamentalDomain := by
      ext u
      simp only [Function.comp_apply]
      rw [mapToTorus_torusToFundamentalDomain]
    rw [h_eq]
    exact h.comp_measurePreserving (torusToFundamentalDomain_measurePreserving (n := n))

/--
The integral over the torus is equal to the integral over the fundamental domain of the pullback, unconditionally.
-/
lemma integral_torus_eq_integral_fundamentalDomain_final (g : UnitAddTorus (Fin n) → ℂ) :
    ∫ t : UnitAddTorus (Fin n), g t =
    ∫ x in Zn.basis.fundamentalDomain, g (mapToTorus x) := by
      by_contra h;
      -- By definition of integrals, if the integrals are not equal, then the functions must be equal almost everywhere.
      have h_eq : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (UnitAddTorus (Fin n))) := by
        contrapose! h;
        -- If $g$ is not almost everywhere strongly measurable, then the integral of $g$ over the torus is zero.
        have h_zero : ∫ t : UnitAddTorus (Fin n), g t = 0 := by
          rw [ MeasureTheory.integral_undef ];
          exact fun H => h <| H.1;
        rw [ h_zero, MeasureTheory.integral_undef ];
        intro H;
        -- If $g$ is integrable, then it must be almost everywhere strongly measurable.
        have h_aestronglymeasurable : MeasureTheory.AEStronglyMeasurable (fun x => g (mapToTorus x)) (MeasureTheory.volume.restrict (Zn.basis.fundamentalDomain)) := by
          exact H.1;
        exact h ( by simpa using aestronglyMeasurable_comp_mapToTorus_iff g |>.2 h_aestronglymeasurable );
      apply h;
      rw [ ← MeasureTheory.integral_map ];
      · -- Apply the measure-preserving property and the equivalence of AEStronglyMeasurable to handle both integrable and non-integrable cases.
        have h_eq : MeasureTheory.MeasurePreserving (mapToTorus (n := n)) (MeasureTheory.volume.restrict (Zn.basis.fundamentalDomain)) (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (UnitAddTorus (Fin n))) := by
          exact mapToTorus_measurePreserving;
        rw [ ← h_eq.map_eq ];
        rw [ MeasureTheory.Measure.map_id', MeasureTheory.integral_map ];
        · exact h_eq.aemeasurable;
        · rw [ h_eq.map_eq ] ; assumption;
      · exact aemeasurable_id;
      · rwa [ MeasureTheory.Measure.map_id' ]

/--
The Fourier coefficient on the torus is equal to the Fourier coefficient on the lattice.
-/
theorem mFourierCoeff_eq_fourierCoefficient_for_periodization (f : 𝓔 n → ℂ) (w : Fin n → ℤ) :
  UnitAddTorus.mFourierCoeff ( periodizeZnToTorus f ) w =
  fourierCoefficient Zn ( periodize f Zn ) (ZVec.toZnDual w) := by
    rw [ torusFourierCoeff_torusIntegrand, integral_torus_eq_integral_fundamentalDomain_final ];
    unfold torusIntegrand fourierCoefficient;
    rw [ Zn_det_one ] ; norm_num [ mul_comm ] ;
    refine' MeasureTheory.setIntegral_congr_fun ( by exact LatticeBasis.fundamentalDomain_measurableSet _ ) fun x hx => _;
    convert integrand_eq f w x using 1;
    ring_nf

end Zn_equiv_UnitAddTorus

/-
  ### Prove the Fourier inversion theorem on Zn via the isomorphism to UnitAddTorus.
-/
section fourier_inverse_Zn_via_UnitAddTorus

open scoped Real Complex MeasureTheory
open LatticeCrypto.Foundations.Lattice LatticeCrypto.Utils.Vec LatticeCrypto.Foundations.Gaussian
open scoped FourierTransform


variable {n : ℕ+}


/--
If the periodization of a function is continuous, then the induced function on the quotient space is continuous.
-/
lemma continuous_periodizeQuotient {f : 𝓔 n → ℂ} (L : EuclideanLattice n n)
  (h : Continuous (periodize f L)) :
  Continuous (periodizeQuotient f L) := by
    exact continuous_coinduced_dom.mpr h

/--
The inverse of the isomorphism maps the projection of x in the torus to the projection of piToEuc x in the quotient of Euclidean space.
-/
lemma quotientZnIsoUnitAddTorus_symm_comp_mk (x : Fin n → ℝ) :
  quotientZnIsoUnitAddTorus.symm (fun i => QuotientAddGroup.mk (x i)) = QuotientAddGroup.mk (piToEuc x) := by
    exact (AddEquiv.symm_apply_eq quotientZnIsoUnitAddTorus).mpr rfl

/-- Ensure the instance is available -/
instance : TopologicalSpace UnitAddCircle := QuotientAddGroup.instTopologicalSpace (AddSubgroup.zmultiples 1)

/-- The projection map to the torus is open. -/
lemma isOpenMap_pi_quotient_mk : IsOpenMap (fun (x : Fin n → ℝ) i => QuotientAddGroup.mk (x i) : (Fin n → ℝ) → (Fin n → UnitAddCircle)) := by
  have h_proj_open : IsOpenMap (fun x : Fin n → ℝ => fun i => QuotientAddGroup.mk (x i) : (Fin n → ℝ) → (Fin n → UnitAddCircle)) := by
    have h_proj_open_comp : ∀ i : Fin n, IsOpenMap (fun x : ℝ => QuotientAddGroup.mk x : ℝ → UnitAddCircle) := by
      exact fun i => QuotientAddGroup.isOpenMap_coe
    -- The product of open maps is open. Since each component map is open, their product is open.
    apply IsOpenMap.piMap;
    · exact fun i => h_proj_open_comp i;
    · exact Filter.Eventually.of_forall fun i => Quot.mk_surjective;
  exact h_proj_open

/--
The inverse of the isomorphism between the quotient of Euclidean space by Zn and the torus is continuous.
-/
lemma continuous_quotientZnIsoUnitAddTorus_symm :
  Continuous (quotientZnIsoUnitAddTorus (n := n)).symm := by
    -- Let `P : (Fin n → ℝ) → (Fin n → UnitAddCircle)` be `fun x i => QuotientAddGroup.mk (x i)`.
    set P : (Fin n → ℝ) → (Fin n → UnitAddCircle) := fun x i => QuotientAddGroup.mk (x i);
    -- By definition of `quotientZnIsoUnitAddTorus`, we know that `quotientZnIsoUnitAddTorus.symm ∘ P = QuotientAddGroup.mk ∘ piToEuc`.
    have h_comp : quotientZnIsoUnitAddTorus.symm ∘ P = QuotientAddGroup.mk ∘ piToEuc := by
      exact funext fun x => quotientZnIsoUnitAddTorus_symm_comp_mk x;
    -- Since `P` is a quotient map, `quotientZnIsoUnitAddTorus.symm` is continuous if `quotientZnIsoUnitAddTorus.symm ∘ P` is continuous.
    have h_cont : Continuous (quotientZnIsoUnitAddTorus.symm ∘ P) := by
      rw [h_comp];
      exact Continuous.comp ( continuous_quot_mk ) ( continuous_pi fun _ => continuous_apply _ );
    have h_quotient_map : IsOpenQuotientMap P := by
      have h_quotient_map : IsOpenMap P := by
        exact isOpenMap_pi_quotient_mk;
      have h_surjective : Function.Surjective P := by
        exact fun x => ⟨ fun i => Quotient.out ( x i ), by aesop ⟩;
      constructor;
      · exact h_surjective;
      · exact continuous_pi_iff.mpr fun i => continuous_quot_mk.comp ( continuous_apply i );
      · exact h_quotient_map;
    exact (IsOpenQuotientMap.continuous_comp_iff h_quotient_map).mp h_cont

/--
The projection map to the torus is surjective.
-/
lemma surjective_pi_quotient_mk : Function.Surjective (fun (x : Fin n → ℝ) i => QuotientAddGroup.mk (x i) : (Fin n → ℝ) → (Fin n → UnitAddCircle)) := by
  exact fun x => ⟨ fun i => Classical.choose ( Quotient.exists_rep ( x i ) ), funext fun i => Classical.choose_spec ( Quotient.exists_rep ( x i ) ) ⟩

/--
If the periodization of f on Zn is continuous, then the induced function on the torus is continuous.
-/
lemma continuous_periodizeZnToTorus {f : 𝓔 n → ℂ}
  (h : Continuous (periodize f Zn)) :
  Continuous (periodizeZnToTorus f) := by
    convert Continuous.comp ( continuous_periodizeQuotient ( Zn ( n := n ) ) h ) ( continuous_quotientZnIsoUnitAddTorus_symm ) using 1

/--
The Fourier series on Zn is equal to the Fourier series on the torus evaluated at the mapped point.
-/
theorem fourierSeries_Zn_eq_torus_sum (f : 𝓔 n → ℂ) (x : 𝓔 n) :
  fourierSeries Zn (periodize f Zn) x =
  ∑' w : Fin n → ℤ, UnitAddTorus.mFourierCoeff (periodizeZnToTorus f) w * UnitAddTorus.mFourier w (mapToTorus x) := by
    -- By definition of `fourierSeries`, we can rewrite the left-hand side.
    simp [fourierSeries];
    -- By definition of `mFourier`, we know that `mFourier w (mapToTorus x) = cexp (2 * π * Complex.I * inner ℝ x (zToE w))`.
    have h_mFourier : ∀ w : Fin n → ℤ, UnitAddTorus.mFourier w (mapToTorus x) = cexp (2 * Real.pi * Complex.I * inner ℝ x (zToE w)) := by
      simp +decide [ UnitAddTorus.mFourier ];
      unfold zToE mapToTorus; simp +decide [ inner, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Complex.exp_sum ] ;
    -- By definition of `fourierCoefficient`, we know that `fourierCoefficient Zn (periodize f Zn) (ZVec.toZnDual w) = UnitAddTorus.mFourierCoeff (periodizeZnToTorus f) w`.
    have h_fourierCoefficient : ∀ w : Fin n → ℤ, fourierCoefficient Zn (periodize f Zn) (ZVec.toZnDual w) = UnitAddTorus.mFourierCoeff (periodizeZnToTorus f) w := by
      exact fun w => Eq.symm (mFourierCoeff_eq_fourierCoefficient_for_periodization f w);
    have h_bijection : Function.Bijective (fun w : Fin n → ℤ => ZVec.toZnDual w : (Fin n → ℤ) → Zn.dual.carrier) := by
      have h_bijection : Function.Bijective (fun w : Fin n → ℤ => ZVec.toZn w : (Fin n → ℤ) → Zn.carrier) := by
        constructor;
        · intro w₁ w₂ h; simp_all +decide [ funext_iff, ZVec.toZn ] ;
          exact fun i => by simpa using congr_fun h i;
        · intro x;
          -- Since x is in the carrier of Zn, it can be written as a linear combination of the basis vectors with integer coefficients.
          obtain ⟨a, ha⟩ : ∃ a : Fin n → ℤ, x = ∑ i, a i • (Zn.basis.asTopBasis i) := by
            have h_basis : ∀ x : 𝓔 n, x ∈ Zn.carrier → ∃ a : Fin n → ℤ, x = ∑ i, a i • (Zn.basis.asTopBasis i) := by
              intro x hx
              have h_span : x ∈ Submodule.span ℤ (Set.range (Zn.basis.asTopBasis)) := by
                convert hx;
                exact Eq.symm (EuclideanLattice.full_rank_eq_module_span Zn)
              rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_span;
              obtain ⟨ c, hc ⟩ := h_span; use c; simp_all +decide [ Finsupp.sum_fintype ] ;
            exact h_basis x x.2;
          use a; ext i; simp [ha, ZVec.toZn];
          simp +decide [ Zn ];
          have h_proj : ∀ i : Fin n,
              (∑ x : Fin n, a x • (EuclideanSpace.single x 1 : 𝓔 n)) i = a i := by
            intro i
            rw [Finset.sum_apply, Finset.sum_eq_single i] <;> aesop
          have hsum : (∑ x : Fin n, a x • (Z n).basis.basis x) i = (a i : ℝ) := by
            simpa [Z, stdBasisZ, LatticeBasis.toLattice, stdBasis] using h_proj i
          exact hsum.symm
      convert h_bijection using 1;
      · rw [ Zn_dual_eq_Zn ];
      · congr! 1;
        unfold ZVec.toZnDual; aesop;
    have h_sum_eq : ∀ {g : Zn.dual.carrier → ℂ}, ∑' w : Zn.dual.carrier, g w = ∑' w : Fin n → ℤ, g (ZVec.toZnDual w) := by
      intro g; rw [ ← Equiv.tsum_eq ( Equiv.ofBijective _ h_bijection ) ] ; aesop;
    rw [ h_sum_eq ];
    exact tsum_congr fun w => by rw [ h_fourierCoefficient, h_mFourier ] ; rw [ show ( ZVec.toZnDual w : 𝓔 n ) = zToE w from by exact
      (coe_toZnDual_eq_zToE w) ] ;

/--
The Fourier series converges to the periodization.
-/
theorem fourier_series_inversion_Zn_for_periodization {f : 𝓔 n → ℂ}
  -- (hf_int : IntegrableOn (periodize f Zn) Zn.basis.fundamentalDomain)
  (hf_cont : Continuous (periodize f Zn) )
  (h_sum : Summable (fourierCoefficient Zn (periodize f Zn)))
  (x : 𝓔 n):
  fourierSeries Zn (periodize f Zn) x = periodize f Zn x := by
    have := @UnitAddTorus.hasSum_mFourier_series_apply_of_summable;
    specialize @this ( Fin n ) _ ⟨ periodizeZnToTorus f, ?_ ⟩ _ <;> norm_num at *;
    exact continuous_periodizeZnToTorus hf_cont;
    · -- By definition of $Zn$, we know that its dual lattice is also $Zn$.
      have h_dual_eq : ∀ w : Fin n → ℤ, fourierCoefficient Zn (periodize f Zn) (ZVec.toZnDual w) = UnitAddTorus.mFourierCoeff (periodizeZnToTorus f) w := by
        exact fun w => Eq.symm (mFourierCoeff_eq_fourierCoefficient_for_periodization f w);
      convert h_sum.comp_injective ( show Function.Injective ( fun w : Fin n → ℤ => ZVec.toZnDual w ) from ?_ ) using 1;
      · exact funext fun w => h_dual_eq w ▸ rfl;
      · intro w₁ w₂ h_eq; have := congr_arg ( fun x : Zn.dual.carrier => ( x : 𝓔 n ) ) h_eq; simp_all +decide [ ZVec.toZnDual ] ;
        simp_all +decide [ ZVec.toZn, funext_iff ];
        exact fun i => by simpa using congr_fun h_eq i;
    · convert HasSum.tsum_eq ( this ( mapToTorus x ) ) using 1;
      · exact fourierSeries_Zn_eq_torus_sum f x;
      · exact periodizeZnToTorus_eq_periodize f x ▸ rfl

end fourier_inverse_Zn_via_UnitAddTorus

end fourier_series_inversion_on_Zn

end LatticeCrypto.Foundations.Gaussian
