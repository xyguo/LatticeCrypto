import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace LatticeCrypto.Utils.Probability

/-- A lightweight predicate: `f` is a probability density on `S` (nonnegative and integral 1 on `S`). -/
def IsProbabilityDensityOn {α : Type*} [MeasureTheory.MeasureSpace α] (f : α → ℝ) (S : Set α) : Prop :=
  (∀ x ∈ S, 0 ≤ f x) ∧ (∫ x in S, f x = 1)

/-!
  # Density Bridge
  This section provides utilities for bridging our custom probability densities with the probability measure defined in Mathlib.
-/
section density_bridge

variable {α : Type*} [MeasureTheory.MeasureSpace α]

/-- The `withDensity` measure induced by a real-valued density on `volume.restrict S`. -/
noncomputable def measureOfDensityOn (f : α → ℝ) (S : Set α) : MeasureTheory.Measure α :=
  ((MeasureTheory.volume : MeasureTheory.Measure α).restrict S).withDensity
    (fun x => ENNReal.ofReal (f x))

/-- Evaluates `measureOfDensityOn` on a measurable set via `withDensity`. -/
theorem measureOfDensityOn_apply
    (f : α → ℝ) (S T : Set α) (hT : MeasurableSet T) :
    measureOfDensityOn f S T
      = ∫⁻ x in T, ENNReal.ofReal (f x) ∂((MeasureTheory.volume : MeasureTheory.Measure α).restrict S) := by
  simpa [measureOfDensityOn] using
    (MeasureTheory.withDensity_apply
      (μ := ((MeasureTheory.volume : MeasureTheory.Measure α).restrict S))
      (f := fun x => ENNReal.ofReal (f x)) hT)

/--
If `f` is a probability density on `S`, then `f` is integrable on `S`.
-/
theorem IsProbabilityDensityOn.integrableOn
    {f : α → ℝ} {S : Set α}
    (hpdf : IsProbabilityDensityOn f S) (hS : MeasurableSet S) :
    MeasureTheory.IntegrableOn f S := by
  by_contra hInt
  have hInt_ind : ¬ MeasureTheory.Integrable (S.indicator f) := by
    simpa [MeasureTheory.integrable_indicator_iff hS] using hInt
  have hzero : ∫ x, S.indicator f x = 0 := by
    simpa using (MeasureTheory.integral_undef hInt_ind)
  have hset_zero : ∫ x in S, f x = 0 := by
    calc
      ∫ x in S, f x = ∫ x, S.indicator f x := by
        symm
        exact MeasureTheory.integral_indicator hS
      _ = 0 := hzero
  have h01 : (0 : ℝ) = 1 := by
    rw [← hpdf.2]
    exact hset_zero.symm
  exact zero_ne_one h01

/-- The total mass of `measureOfDensityOn f S` is `1` for a probability density on `S`. -/
theorem measureOfDensityOn_univ
    {f : α → ℝ} {S : Set α}
    (hS : MeasurableSet S) (hpdf : IsProbabilityDensityOn f S) :
    measureOfDensityOn f S Set.univ = 1 := by
  let μS : MeasureTheory.Measure α := (MeasureTheory.volume : MeasureTheory.Measure α).restrict S
  have hInt : MeasureTheory.Integrable f μS := by
    simpa [μS] using (hpdf.integrableOn hS)
  have h_nonneg : 0 ≤ᵐ[μS] f := by
    refine (MeasureTheory.ae_restrict_iff' hS).2 ?_
    exact Filter.Eventually.of_forall (fun x hx => hpdf.1 x hx)
  calc
    measureOfDensityOn f S Set.univ
        = ∫⁻ x, ENNReal.ofReal (f x) ∂μS := by
            simpa [μS] using
              (measureOfDensityOn_apply f S Set.univ MeasurableSet.univ)
    _ = ENNReal.ofReal (∫ x, f x ∂μS) := by
          rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt h_nonneg]
    _ = 1 := by
          simpa [μS] using hpdf.2

/-- Any `IsProbabilityDensityOn f S` induces a Mathlib `IsProbabilityMeasure`. -/
theorem measureOfDensityOn_isProbabilityMeasure
    {f : α → ℝ} {S : Set α}
    (hS : MeasurableSet S) (hpdf : IsProbabilityDensityOn f S) :
    MeasureTheory.IsProbabilityMeasure (measureOfDensityOn f S) := by
  refine ⟨measureOfDensityOn_univ hS hpdf⟩

/-- Construct a probability measure from a density `f` on a measurable set `S` -/
noncomputable def probabilityMeasureOfDensity
  {f : α → ℝ} {S : Set α}
  (hS : MeasurableSet S) (hpdf : IsProbabilityDensityOn f S) : MeasureTheory.ProbabilityMeasure α :=
  ⟨(measureOfDensityOn f S), measureOfDensityOn_isProbabilityMeasure hS hpdf⟩

end density_bridge

noncomputable section TV_distance

open MeasureTheory Set

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/--
Total variation distance for probability measures, defined as
`sup_{A measurable} |p(A) - q(A)|` (embedded in `ℝ≥0∞`).
-/
noncomputable def tvDist (p q : ProbabilityMeasure α) : ENNReal :=
  ⨆ (A : Set α) (_ : MeasurableSet A), ENNReal.ofReal |((p A : ℝ) - (q A : ℝ))|

/--
Data processing inequality for total variation distance under measurable pushforward.
-/
lemma tvDist_map_le (p q : ProbabilityMeasure α) (f : α → β) (hf : Measurable f) :
    tvDist (p.map hf.aemeasurable) (q.map hf.aemeasurable) ≤ tvDist p q := by
  unfold tvDist
  refine iSup_le (fun B => ?_)
  refine iSup_le (fun hB => ?_)
  rw [ProbabilityMeasure.map_apply p hf.aemeasurable hB, ProbabilityMeasure.map_apply q hf.aemeasurable hB]
  exact le_iSup_of_le (f ⁻¹' B) <| le_iSup_of_le (hf hB) le_rfl

/--
If two probability laws admit set-integral density representations
`p(A) = ∫_A f dμ`, `q(A) = ∫_A g dμ`, then TV equals half the `L1` distance.
-/
theorem tvDist_eq_half_l1_of_setIntegral_repr
    (μ : Measure α)
    (p q : ProbabilityMeasure α)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (hf_mass : ∫ x, f x ∂μ = 1) (hg_mass : ∫ x, g x ∂μ = 1)
    (hp_apply : ∀ A, MeasurableSet A → (p A : ℝ) = ∫ x in A, f x ∂μ)
    (hq_apply : ∀ A, MeasurableSet A → (q A : ℝ) = ∫ x in A, g x ∂μ) :
    tvDist p q = ENNReal.ofReal ((1 / 2 : ℝ) * ∫ x, |f x - g x| ∂μ) := by
  let h : α → ℝ := fun x => f x - g x
  let P : Set α := h ⁻¹' Set.Ici 0
  let N : Set α := h ⁻¹' Set.Iic 0
  have hh_meas : Measurable h := hf_meas.sub hg_meas
  have hh_int : Integrable h μ := hf_int.sub hg_int
  have hP_meas : MeasurableSet P := by
    simpa [P] using (hh_meas measurableSet_Ici)
  have hN_meas : MeasurableSet N := by
    simpa [N] using (hh_meas measurableSet_Iic)
  have h_h_mass_zero : ∫ x, h x ∂μ = 0 := by
    calc
      ∫ x, h x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ := by
        simpa [h] using (MeasureTheory.integral_sub hf_int hg_int)
      _ = 0 := by rw [hf_mass, hg_mass]; norm_num
  have h_h_nonneg_on_P : ∀ x ∈ P, 0 ≤ h x := by
    intro x hx
    simpa [P] using hx
  have h_h_nonpos_on_N : ∀ x ∈ N, h x ≤ 0 := by
    intro x hx
    simpa [N] using hx
  have h_intP_nonneg : 0 ≤ ∫ x in P, h x ∂μ := by
    exact MeasureTheory.setIntegral_nonneg hP_meas h_h_nonneg_on_P
  have h_compl_eq_lt : Pᶜ = {x | h x < 0} := by
    ext x
    simp [P]
  have h_intN_eq_intComplP : ∫ x in N, h x ∂μ = ∫ x in Pᶜ, h x ∂μ := by
    rw [h_compl_eq_lt]
    simpa [N] using (MeasureTheory.setIntegral_neg_eq_setIntegral_nonpos (μ := μ) (f := h) hh_int.1).symm
  have h_split : ∫ x in P, h x ∂μ + ∫ x in Pᶜ, h x ∂μ = ∫ x, h x ∂μ := by
    simpa using (MeasureTheory.integral_add_compl hP_meas hh_int)
  have h_intN_eq_neg_intP : ∫ x in N, h x ∂μ = - ∫ x in P, h x ∂μ := by
    have h_split' : ∫ x in P, h x ∂μ + ∫ x in N, h x ∂μ = ∫ x, h x ∂μ := by
      simpa [h_intN_eq_intComplP] using h_split
    linarith [h_h_mass_zero, h_split']
  have h_half_l1 :
      ∫ x in P, h x ∂μ = (1 / 2 : ℝ) * ∫ x, |h x| ∂μ := by
    have h_norm :
        ∫ x, |h x| ∂μ = ∫ x in P, h x ∂μ - ∫ x in N, h x ∂μ := by
      simpa [Real.norm_eq_abs, P, N] using
        (MeasureTheory.integral_norm_eq_pos_sub_neg (μ := μ) (f := h) hh_int)
    rw [h_norm, h_intN_eq_neg_intP]
    ring
  have h_upper :
      ∀ A, MeasurableSet A →
        |(p A : ℝ) - (q A : ℝ)| ≤ ∫ x in P, h x ∂μ := by
    intro A hA
    have hAeq : (p A : ℝ) - (q A : ℝ) = ∫ x in A, h x ∂μ := by
      rw [hp_apply A hA, hq_apply A hA]
      have hsubA :
          ∫ x in A, (f x - g x) ∂μ = ∫ x in A, f x ∂μ - ∫ x in A, g x ∂μ := by
        simpa using
          (MeasureTheory.integral_sub (μ := μ.restrict A)
            (hf := hf_int.integrableOn) (hg := hg_int.integrableOn))
      simpa [h] using hsubA.symm
    have hA_le :
        ∫ x in A, h x ∂μ ≤ ∫ x in P, h x ∂μ := by
      exact MeasureTheory.setIntegral_le_nonneg (s := A) (f := h) hA hh_meas.stronglyMeasurable hh_int
    have hN_le_A :
        ∫ x in N, h x ∂μ ≤ ∫ x in A, h x ∂μ := by
      exact MeasureTheory.setIntegral_nonpos_le (s := A) (f := h) hA hh_meas.stronglyMeasurable hh_int
    have hneg_le_A : - (∫ x in P, h x ∂μ) ≤ ∫ x in A, h x ∂μ := by
      simpa [h_intN_eq_neg_intP] using hN_le_A
    rw [hAeq]
    exact abs_le.mpr ⟨hneg_le_A, hA_le⟩
  have h_tv_le : tvDist p q ≤ ENNReal.ofReal (∫ x in P, h x ∂μ) := by
    unfold tvDist
    refine iSup_le (fun A => ?_)
    refine iSup_le (fun hA => ?_)
    exact ENNReal.ofReal_le_ofReal (h_upper A hA)
  have h_tv_ge : ENNReal.ofReal (∫ x in P, h x ∂μ) ≤ tvDist p q := by
    unfold tvDist
    refine le_iSup_of_le P ?_
    refine le_iSup_of_le hP_meas ?_
    have hP_eq : |(p P : ℝ) - (q P : ℝ)| = ∫ x in P, h x ∂μ := by
      have hP_main : (p P : ℝ) - (q P : ℝ) = ∫ x in P, h x ∂μ := by
        rw [hp_apply P hP_meas, hq_apply P hP_meas]
        have hsubP :
            ∫ x in P, (f x - g x) ∂μ = ∫ x in P, f x ∂μ - ∫ x in P, g x ∂μ := by
          simpa using
            (MeasureTheory.integral_sub (μ := μ.restrict P)
              (hf := hf_int.integrableOn) (hg := hg_int.integrableOn))
        simpa [h] using hsubP.symm
      rw [hP_main, abs_of_nonneg h_intP_nonneg]
    simp [hP_eq]
  have h_tv_eq_pos :
      tvDist p q = ENNReal.ofReal (∫ x in P, h x ∂μ) := le_antisymm h_tv_le h_tv_ge
  rw [h_tv_eq_pos, h_half_l1]

/--
If two probability laws admit set-integral representations
`p(A) = ∫_A f dμ`, `q(A) = ∫_A g dμ`, then TV is bounded by the `L1` distance.
-/
theorem tvDist_le_l1_of_setIntegral_repr
    (μ : Measure α)
    (p q : ProbabilityMeasure α)
    (f g : α → ℝ)
    (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (hp_apply : ∀ A, MeasurableSet A → (p A : ℝ) = ∫ x in A, f x ∂μ)
    (hq_apply : ∀ A, MeasurableSet A → (q A : ℝ) = ∫ x in A, g x ∂μ) :
    tvDist p q ≤ ENNReal.ofReal (∫ x, |f x - g x| ∂μ) := by
  have hfg_int : Integrable (fun x => f x - g x) μ := hf_int.sub hg_int
  have habs_int : Integrable (fun x => |f x - g x|) μ := hfg_int.norm
  unfold tvDist
  refine iSup_le (fun A => ?_)
  refine iSup_le (fun hA => ?_)
  have hA_eq : (p A : ℝ) - (q A : ℝ) = ∫ x in A, (f x - g x) ∂μ := by
    rw [hp_apply A hA, hq_apply A hA]
    simpa using
      (MeasureTheory.integral_sub (μ := μ.restrict A)
        (hf := hf_int.integrableOn) (hg := hg_int.integrableOn)).symm
  have hA_norm_le : |(p A : ℝ) - (q A : ℝ)| ≤ ∫ x in A, |f x - g x| ∂μ := by
    rw [hA_eq]
    simpa [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := μ.restrict A) (f := fun x => f x - g x))
  have hA_le_univ :
      ∫ x in A, |f x - g x| ∂μ ≤ ∫ x, |f x - g x| ∂μ := by
    exact MeasureTheory.setIntegral_le_integral habs_int (by
      exact Filter.Eventually.of_forall (fun _ => abs_nonneg _))
  exact ENNReal.ofReal_le_ofReal (hA_norm_le.trans hA_le_univ)

/--
Setwise application formula for a probability measure represented as
`μ.withDensity (ENNReal.ofReal ∘ f)`.
-/
lemma prob_apply_eq_setIntegral_of_toMeasure_eq_withDensity_ofReal
    (μ : Measure α) (p : ProbabilityMeasure α) (f : α → ℝ)
    (hp : (p : Measure α) = μ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf_int : Integrable f μ) (hf_nonneg : 0 ≤ᵐ[μ] f) :
    ∀ A, MeasurableSet A → (p A : ℝ) = ∫ x in A, f x ∂μ := by
  intro A hA
  have hf_intA : Integrable f (μ.restrict A) := hf_int.integrableOn
  have hf_nonnegA : 0 ≤ᵐ[μ.restrict A] f := ae_restrict_of_ae hf_nonneg
  have h_lintegral :
      ENNReal.ofReal (∫ x in A, f x ∂μ) = ∫⁻ x in A, ENNReal.ofReal (f x) ∂μ := by
    simpa using (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_intA hf_nonnegA)
  have h_int_nonneg : 0 ≤ ∫ x in A, f x ∂μ := MeasureTheory.setIntegral_nonneg_of_ae_restrict hf_nonnegA
  calc
    (p A : ℝ) = ((p : Measure α).real A : ℝ) := by
      simp
    _ = ((p : Measure α) A).toReal := by simp [MeasureTheory.Measure.real]
    _ = ((μ.withDensity (fun x => ENNReal.ofReal (f x))) A).toReal := by rw [hp]
    _ = (∫⁻ x in A, ENNReal.ofReal (f x) ∂μ).toReal := by rw [MeasureTheory.withDensity_apply _ hA]
    _ = (ENNReal.ofReal (∫ x in A, f x ∂μ)).toReal := by rw [h_lintegral.symm]
    _ = ∫ x in A, f x ∂μ := ENNReal.toReal_ofReal h_int_nonneg

/--
Convenience form of `tvDist_eq_half_l1_of_setIntegral_repr` for measures
given directly by `withDensity (ENNReal.ofReal ∘ f)`.
-/
theorem tvDist_eq_half_l1_of_withDensity
    (μ : Measure α)
    (p q : ProbabilityMeasure α)
    (f g : α → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hf_mass : ∫ x, f x ∂μ = 1) (hg_mass : ∫ x, g x ∂μ = 1)
    (hp : (p : Measure α) = μ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hq : (q : Measure α) = μ.withDensity (fun x => ENNReal.ofReal (g x))) :
    tvDist p q = ENNReal.ofReal ((1 / 2 : ℝ) * ∫ x, |f x - g x| ∂μ) := by
  refine tvDist_eq_half_l1_of_setIntegral_repr
    (μ := μ) (p := p) (q := q) (f := f) (g := g)
    hf_meas hg_meas hf_int hg_int hf_mass hg_mass ?_ ?_
  · exact prob_apply_eq_setIntegral_of_toMeasure_eq_withDensity_ofReal
      (μ := μ) (p := p) (f := f) hp hf_int hf_nonneg
  · exact prob_apply_eq_setIntegral_of_toMeasure_eq_withDensity_ofReal
      (μ := μ) (p := q) (f := g) hq hg_int hg_nonneg

/--
Convenience `TV ≤ L1` bound for laws represented by `withDensity (ENNReal.ofReal ∘ f)`.
-/
theorem tvDist_le_l1_of_withDensity
    (μ : Measure α)
    (p q : ProbabilityMeasure α)
    (f g : α → ℝ)
    (hf_int : Integrable f μ) (hg_int : Integrable g μ)
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g)
    (hp : (p : Measure α) = μ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hq : (q : Measure α) = μ.withDensity (fun x => ENNReal.ofReal (g x))) :
    tvDist p q ≤ ENNReal.ofReal (∫ x, |f x - g x| ∂μ) := by
  refine tvDist_le_l1_of_setIntegral_repr
    (μ := μ) (p := p) (q := q) (f := f) (g := g) hf_int hg_int ?_ ?_
  · exact prob_apply_eq_setIntegral_of_toMeasure_eq_withDensity_ofReal
      (μ := μ) (p := p) (f := f) hp hf_int hf_nonneg
  · exact prob_apply_eq_setIntegral_of_toMeasure_eq_withDensity_ofReal
      (μ := μ) (p := q) (f := g) hq hg_int hg_nonneg

end TV_distance

end LatticeCrypto.Utils.Probability
