import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic

import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Foundations.Lattice.FundamentalDomain
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec

open scoped Real Complex MeasureTheory ProbabilityTheory
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Foundations.Lattice

namespace LatticeCrypto.Foundations.Gaussian

noncomputable section gaussian

variable {n : ℕ+}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-!
 ## The (continuous) Gaussian functions
 -/
/-- The standard Gaussian function ρ(x) = exp(-π ‖x‖^2) -/
def rho (x : E) : ℝ := Real.exp (-π * ‖x‖^2)

scoped notation "ρ" => rho

/-- The scaled Gaussian ρ_s(x) = ρ(x/s) = exp(-π ‖x‖^2 / s^2) -/
def rhoS (s : ℝ) (x : E) : ℝ := by
  classical
  exact
    if s = 0 then
      if x = 0 then 1 else 0
    else
      Real.exp (-π * ‖s⁻¹ • x‖^2)

scoped notation "ρ[" s "]" => rhoS s

@[simp] theorem rhoS_zero [DecidableEq E] (x : E) : rhoS 0 x = if x = 0 then 1 else 0 := by
  simp [rhoS]

@[simp] theorem rhoS_zero_zero : rhoS 0 (0 : E) = 1 := by
  simp [rhoS]

@[simp] theorem rhoS_zero_of_ne {x : E} (hx : x ≠ 0) : rhoS 0 x = 0 := by
  simp [rhoS, hx]

@[simp] theorem rhoS_of_ne_zero {s : ℝ} (hs : s ≠ 0) (x : E) :
    rhoS s x = Real.exp (-π * ‖s⁻¹ • x‖^2) := by
  simp [rhoS, hs]

/-- Immediate corollary from the definition of `rhoS` -/
theorem rhoS_eq_rho_s_inv_mul_x {s : ℝ} {x : E} (hs : s ≠ 0) :
  rhoS s x = rho (s⁻¹ • x) := by
  simp [rhoS, rho, hs]

/-- The scaled-tilted Gaussian ρ_s ∘ T(x) = ρ(Tx/s) = exp(-π ‖ T x ‖^2 / s^2) -/
def rhoST (s : ℝ) (T : E ≃L[ℝ] E) (x : E) : ℝ := by
  classical
  exact
    if s = 0 then
      if x = 0 then 1 else 0
    else
      Real.exp (-π * ‖s⁻¹ • (T x)‖^2)

@[simp] theorem rhoST_zero [DecidableEq E] (T : E ≃L[ℝ] E) (x : E) : rhoST 0 T x = if x = 0 then 1 else 0 := by
  simp [rhoST]

@[simp] theorem rhoST_zero_zero (T : E ≃L[ℝ] E) : rhoST 0 T (0 : E) = 1 := by
  simp [rhoST]

@[simp] theorem rhoST_zero_of_ne (T : E ≃L[ℝ] E) {x : E} (hx : x ≠ 0) : rhoST 0 T x = 0 := by
  simp [rhoST, hx]

@[simp] theorem rhoST_of_ne_zero {s : ℝ} (hs : s ≠ 0) (T : E ≃L[ℝ] E) (x : E) :
    rhoST s T x = Real.exp (-π * ‖s⁻¹ • (T x)‖^2) := by
  simp [rhoST, hs]

/-- `rhoST` equals `rhoS` composed with the linear equivalence `T` -/
theorem rhoST_eq_rhoS_T_x {s : ℝ} {T : E ≃L[ℝ] E} {x : E} :
  rhoST s T x = rhoS s (T x) := by
  by_cases hs : s = 0
  · subst hs; by_cases hx : x = 0 <;> simp [rhoST, rhoS, hx]
  · simp [rhoST, rhoS, hs]

/-- `rhoST` with the identity equivalence equals `rhoS` -/
lemma rhoST_Id_eq_rhoS (s : ℝ) (x : E) :
  rhoST s (ContinuousLinearEquiv.refl ℝ E) x = rhoS s x := by
  simp [rhoST, rhoS, ContinuousLinearEquiv.refl_apply]

/-- lemma `rhoS_1_eq_rho`: ∀ x : E, rhoS 1 x = rho x. -/
@[simp]
lemma rhoS_1_eq_rho :
  ∀ x : E, rhoS 1 x = rho x :=
  by
    intro x
    simpa using rhoS_eq_rho_s_inv_mul_x (s := 1) (x := x) one_ne_zero

/-- `rhoST` is non-negative -/
lemma rhoST_nonneg (s : ℝ) (T : E ≃L[ℝ] E) (x : E) : 0 ≤ rhoST s T x :=
  by
    by_cases hs : s = 0
    · subst hs; by_cases hx : x = 0 <;> simp [rhoST, hx]
    · simpa [rhoST, hs] using (Real.exp_pos (-(π * ‖s⁻¹ • T x‖^2))).le

/-- `rhoS` is non-negative -/
theorem rhoS_nonneg (s : ℝ) (x : E) : 0 ≤ rhoS s x :=
  by
    by_cases hs : s = 0
    · subst hs; by_cases hx : x = 0 <;> simp [rhoS, hx]
    · simpa [rhoS, hs] using (Real.exp_pos (-(π * ‖s⁻¹ • x‖^2))).le

/-- A linear isometry of Euclidean space preserves the scaled Gaussian `rhoS`. -/
lemma rhoS_map_linearIsometry (R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n) (s : ℝ) (x : 𝓔 n) :
    rhoS s (R x) = rhoS s x := by
  by_cases hs : s = 0
  · subst hs
    by_cases hx : x = 0
    · subst hx
      simp
    · have hRx : R x ≠ 0 := by
        intro hRx
        exact hx (R.injective (by simpa using hRx))
      simp [rhoS, hx, hRx]
  · have hnorm : ‖s⁻¹ • R x‖ = ‖s⁻¹ • x‖ := by
      calc
        ‖s⁻¹ • R x‖ = ‖R (s⁻¹ • x)‖ := by simp [R.map_smul]
        _ = ‖s⁻¹ • x‖ := R.norm_map (s⁻¹ • x)
    simp [rhoS, hs, hnorm]

/-- Larger Gaussian width implies smaller density -/
lemma rhoST_mono {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h : s₁ ≤ s₂) (T : E ≃L[ℝ] E) (x : E) :
    rhoST s₁ T x ≤ rhoST s₂ T x := by
  have hs₁ : s₁ ≠ 0 := h1.ne'
  have hs₂ : s₂ ≠ 0 := ne_of_gt (lt_of_lt_of_le h1 h)
  -- Since the exponential function is decreasing, if the exponent is smaller, the value is larger.
  have h_exp : Real.exp (-(Real.pi * (‖T x‖ / s₁) ^ 2)) ≤ Real.exp (-(Real.pi * (‖T x‖ / s₂) ^ 2)) := by
    gcongr;
    -- Since the norm of T x is non-negative and s₂ is positive, their division is non-negative.
    apply div_nonneg
    exact norm_nonneg _
    exact le_trans h1.le h;
  convert h_exp using 1 <;> norm_num [rhoST_of_ne_zero hs₁, rhoST_of_ne_zero hs₂, rho] ; ring_nf;
  · rw [ norm_smul, Real.norm_of_nonneg ( by positivity ), mul_pow ];
  · rw [ norm_smul, Real.norm_of_nonneg ( inv_nonneg.2 ( by linarith ) ), inv_mul_eq_div ]

/-- Larger Gaussian width implies smaller density -/
theorem rhoS_mono {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h : s₁ ≤ s₂) (x : E) :
    rhoS s₁ x ≤ rhoS s₂ x := by
  simpa [rhoST_Id_eq_rhoS] using rhoST_mono h1 h (ContinuousLinearEquiv.refl ℝ E) x

/-- The Gaussian function ρ is essentially the Gaussian PDF on ℝ -/
theorem rhoS_eq_gaussianPDF (s : ℝ) (x : E) (h: s > 0):
    rhoS s x = s • ProbabilityTheory.gaussianPDFReal 0 ⟨s^2 / (2 * π), by positivity⟩ ‖x‖ := by
  -- Proof involves simple algebra:
  -- rhoS s x
  -- = rho (x / s)
  -- = exp( - π * ‖x / s‖^2 )
  -- = exp( - π * ‖x‖^2 / s^2 )
  -- = s * gaussianPDFReal 0 (s^2 / 2π) ‖x‖
  rw [rhoS_of_ne_zero h.ne']
  unfold ProbabilityTheory.gaussianPDFReal;
  simp +decide [ mul_comm, mul_left_comm, h.ne', Real.pi_pos.ne.symm, div_eq_mul_inv, h.le ] ; ring_nf;
  rw [ norm_smul, Real.norm_of_nonneg ( inv_nonneg.2 h.le ), mul_pow ]

/-- theorem `rhoS_eq_Pi_gaussianPDF`: ℝ) (x : 𝓔 n) (h: s > 0):. -/
theorem rhoS_eq_Pi_gaussianPDF (s : ℝ) (x : 𝓔 n) (h: s > 0):
    rhoS s x = (s ^ (n : ℕ)) • ∏ (i : Fin n), ProbabilityTheory.gaussianPDFReal 0 ⟨s^2 / (2 * π), by positivity⟩ (x i) := by
  convert rhoS_eq_gaussianPDF s x h using 1;
  norm_num [ ProbabilityTheory.gaussianPDFReal, EuclideanSpace.norm_eq ];
  rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ; norm_num [ Finset.prod_mul_distrib, Finset.prod_pow, h.ne', mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, Real.pi_pos.le ] ; ring_nf;
  norm_num [ ← Real.exp_sum, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, h.le ];
  -- Since $s > 0$, we have $s^n * (s^n)^{-1} = 1$ and $s * s^{-1} = 1$.
  field_simp [h.ne']

/-- Handy corollary for ρ=1 -/
corollary rho_eq_gaussianPDF (x : 𝓔 n) :
    rho x = ProbabilityTheory.gaussianPDFReal 0 ⟨1 / (2 * π), by positivity⟩ ‖x‖ := by
    simpa [rhoS_1_eq_rho, rho] using rhoS_eq_gaussianPDF 1 x zero_lt_one

/-- Handy corollary for ρ=1 -/
corollary rho_eq_Pi_gaussianPDF (x : 𝓔 n) :
    rho x = ∏ (i : Fin n), ProbabilityTheory.gaussianPDFReal 0 ⟨1 / (2 * π), by positivity⟩ (x i) := by
    simpa [rhoS_1_eq_rho, rho] using rhoS_eq_Pi_gaussianPDF 1 x zero_lt_one

/-- The Gaussian function ρ_s is integrable -/
lemma rhoS.integrable {n : ℕ+} (s : ℝ) (hs : s ≠ 0) :
    MeasureTheory.Integrable (fun v : 𝓔 n => (rhoS s v : ℂ)) := by
  -- We'll use the fact that the Gaussian function is integrable.
  have h_gauss_integrable : MeasureTheory.Integrable (fun v : 𝓔 n => Real.exp (-Real.pi * ‖v‖^2 / s^2)) MeasureTheory.volume := by
    have h_gauss_integrable : ∫ v : 𝓔 n, Real.exp (-Real.pi * ‖v‖^2 / s^2) = (Real.sqrt (s^2)) ^ (n : ℕ) := by
      have h_gauss_integral : ∫ v : Fin n → ℝ, Real.exp (-Real.pi * (∑ i, v i ^ 2) / s ^ 2) = (Real.sqrt (s ^ 2)) ^ (n : ℕ) := by
        have h_gauss_integral : ∫ v : Fin n → ℝ, Real.exp (-Real.pi * (∑ i, v i ^ 2) / s ^ 2) = (∏ i : Fin n, ∫ v : ℝ, Real.exp (-Real.pi * v ^ 2 / s ^ 2)) := by
          have h_gauss_integral : ∫ v : Fin n → ℝ, Real.exp (-Real.pi * (∑ i, v i ^ 2) / s ^ 2) = (∏ i : Fin n, ∫ v : ℝ, Real.exp (-Real.pi * v ^ 2 / s ^ 2)) := by
            have h_prod : ∀ (f : Fin n → ℝ → ℝ), (∫ v : Fin n → ℝ, ∏ i, f i (v i)) = ∏ i, ∫ v : ℝ, f i v := by
              exact fun f => MeasureTheory.integral_fin_nat_prod_volume_eq_prod f
            convert h_prod ( fun i v => Real.exp ( -Real.pi * v ^ 2 / s ^ 2 ) ) using 3 ; ring_nf;
            rw [ ← Real.exp_sum ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
          convert h_gauss_integral using 1;
        have := integral_gaussian ( Real.pi / s ^ 2 ) ; simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm ] ;
      convert h_gauss_integral using 1;
      rw [ ← MeasureTheory.integral_congr_ae ];
      rw [ ← LatticeCrypto.Utils.Geometry.eucToPi_measurePreserving.integral_comp ];
      congr! 1;
      · exact Measurable.measurableEmbedding (fun ⦃t⦄ a => a) fun ⦃a₁ a₂⦄ a => a;
      · norm_num [ EuclideanSpace.norm_eq ];
        filter_upwards [ ] with v using by rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ; rfl;
    exact ( by contrapose! h_gauss_integrable; rw [ MeasureTheory.integral_undef h_gauss_integrable ] ; positivity );
  norm_num [ div_eq_inv_mul ] at *;
  convert h_gauss_integrable.ofReal using 2;
  ext; simp +decide [rhoS, hs, norm_smul, mul_pow] ; ring_nf

open MeasureTheory.Measure
/-- The composition of an integrable function with a continuous linear equivalence is integrable -/
lemma integrable_comp_continuousLinearEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [MeasurableSpace F]
    (μ : MeasureTheory.Measure E) [IsAddHaarMeasure μ]
    (f : E → F) (T : E ≃L[ℝ] E) (hf : MeasureTheory.Integrable f μ) :
    MeasureTheory.Integrable (f ∘ T) μ := by
      have h_map : MeasureTheory.Integrable f (MeasureTheory.Measure.map T μ) := by
        have h_map : MeasureTheory.Measure.map T μ = ENNReal.ofReal |(LinearMap.det T.toLinearMap)⁻¹| • μ := by
          convert MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar _ _;
          · infer_instance;
          · infer_instance;
          · infer_instance;
          · exact fun h => by simpa [ h ] using T.toLinearEquiv.det.ne_zero;
        rw [ h_map ];
        apply_rules [ MeasureTheory.Integrable.smul_measure ];
        exact ENNReal.ofReal_ne_top;
      convert h_map.comp_measurable T.continuous.measurable

/-- `rhoST` is integrable -/
lemma rhoST.integrable {n : ℕ+} (s : ℝ) (hs : s ≠ 0) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) :
    MeasureTheory.Integrable (fun v : 𝓔 n => (rhoST s T v : ℂ)) := by
  simpa [rhoST_eq_rhoS_T_x] using
    (integrable_comp_continuousLinearEquiv MeasureTheory.MeasureSpace.volume
      (fun v : 𝓔 n => (rhoS s v : ℂ)) T (rhoS.integrable s hs))


open scoped ENNReal
variable {α : Type*}
variable [AddCommMonoid α] [TopologicalSpace α]

/-- Countably summation over lattice points -/
noncomputable def _root_.LatticeCrypto.Foundations.Lattice.EuclideanLattice.latticeSum
  (L : EuclideanLattice n n) (f : 𝓔 n → α) : α :=
  ∑' v : L.carrier, f (v : 𝓔 n)

noncomputable def _root_.LatticeCrypto.Foundations.Lattice.EuclideanLattice.latticeSumOn
  (L : EuclideanLattice n n) (f : L.carrier → α) : α :=
  ∑' v : L.carrier, f v

/-- The Bridge Lemma -/
theorem EuclideanLattice.latticeSum_eq_latticeSumOn (L : EuclideanLattice n n) (f : 𝓔 n → α) :
    L.latticeSum f = L.latticeSumOn (fun v => f (v : 𝓔 n)) :=
  rfl

/-- The tilted and scaled rhoMass -/
noncomputable def rhoSTMass (s : ℝ) (T : (𝓔 n) ≃L[ℝ] (𝓔 n) ) (c : 𝓔 n) (L : EuclideanLattice n n) : ℝ :=
  L.latticeSum (fun v => rhoST s T (v + c))

noncomputable def rhoSTMass.ENNReal (s : ℝ) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (c : 𝓔 n) (L : EuclideanLattice n n) : ENNReal :=
  L.latticeSum (fun v => ENNReal.ofReal (rhoST s T (v + c)))

noncomputable def rhoSTMassOn (s : ℝ) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (c : 𝓔 n) (L : EuclideanLattice n n) (S : Set (𝓔 n)) : ℝ :=
  L.latticeSum (fun v => (S.indicator (rhoST s T)) (v + c))

/-- `rhoSTMassOn` the whole space is by definition equal to `rhoSTMass`. -/
theorem rhoSTMassOn_univ (s : ℝ) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (c : 𝓔 n) (L : EuclideanLattice n n) :
  rhoSTMassOn s T c L Set.univ = rhoSTMass s T c L := by
  classical
  simp [rhoSTMassOn, rhoSTMass]

/-- The untilted but s-scaled rhoMass -/
noncomputable def rhoSMass (s : ℝ) (c : 𝓔 n) (L : EuclideanLattice n n) : ℝ :=
  L.latticeSum (fun v => rhoS s (v + c))

noncomputable def rhoSMassOn
  (s : ℝ) (c : 𝓔 n)
  (L : EuclideanLattice n n)
  (S : Set (𝓔 n)) : ℝ :=
  L.latticeSum (fun v => (S.indicator (rhoS s)) (v + c))

scoped notation "ρMass["s"]" => rhoSMass s
scoped notation "ρMassOn["s"]" => rhoSMassOn s

/-- `rhoSMassOn` the whole space is by definition equal to `rhoSMass`. -/
theorem rhoSMassOn_univ (s : ℝ) (c : 𝓔 n) (L : EuclideanLattice n n) :
  rhoSMassOn s c L Set.univ = rhoSMass s c L := by
  classical
  simp [rhoSMassOn, rhoSMass]

/-- Immediate corollary from `rhoST Id = rhoS` -/
theorem rhoSTMass_Id_eq_rhoSMass (s c L) :
  rhoSTMass s (ContinuousLinearEquiv.refl ℝ (𝓔 n)) c L = rhoSMass s c L :=
  rfl

/-- The unscaled rhoMass -/
noncomputable def rhoMass (c : 𝓔 n) (L : EuclideanLattice n n) : ℝ :=
  L.latticeSum (fun v => rho (v + c))

/-- Filtered rhoMass on subset -/
noncomputable def rhoMassOn
  (c : 𝓔 n)
  (L : EuclideanLattice n n)
  (S : Set (𝓔 n)) : ℝ :=
  L.latticeSum (fun v => (S.indicator rho) (v + c))

scoped notation "ρMass" => rhoMass
scoped notation "ρMassOn" => rhoMassOn

/-- `rhoMassOn` the whole space is by definition equal to `rhoMass` -/
theorem rhoMassOn_univ (c : 𝓔 n) (L : EuclideanLattice n n) :
  rhoMassOn c L Set.univ = rhoMass c L := by
  classical
  simp [rhoMassOn, rhoMass]


/-- Immediate corollary of `rhoS 1 = rho` -/
theorem rhoSMass_one_eq_rhoMass (c : 𝓔 n) L :
   rhoSMass 1 c L = rhoMass c L := by
  unfold rhoSMass rhoMass;
  congr!
  ext x; exact rhoS_1_eq_rho (E := 𝓔 n) x


/-- Immediate corollary of `rhoS 1 = rho` -/
theorem rhoSMassOn_one_eq_rhoMassOn (c : 𝓔 n) L (S : Set (𝓔 n)) :
   rhoSMassOn 1 c L S = rhoMassOn c L S := by
  unfold rhoSMassOn rhoMassOn;
  congr!
  ext x; exact rhoS_1_eq_rho (E := 𝓔 n) x

/-
Scaling the lattice and the set by s is equivalent to scaling the Gaussian parameter by 1/s.
-/
theorem rhoSMass_scale (s : ℝ) (hs : s > 0) (L : EuclideanLattice n n) :
    rhoSMass (1 / s) 0 L = rhoMass 0 (L.smul s hs.ne') := by
  unfold rhoMass rhoSMass;
  unfold EuclideanLattice.latticeSum
  simp [rho, rhoS];
  -- By definition of $L.smul s$, we have that $L.smul s = L.carrier.map (DistribMulAction.toLinearMap ℤ (𝓔 n) s)$.
  have h_smul : (L.smul s (ne_of_gt hs)).carrier = L.carrier.map (DistribMulAction.toLinearMap ℤ (𝓔 n) s) := by
    exact EuclideanLattice.smul_carrier L s (ne_of_gt hs);
  rw [ h_smul ];
  rw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun v : ↥L.carrier => ⟨ s • ( v : LatticeCrypto.Utils.Vec.𝓔 n ), by aesop ⟩ : ↥L.carrier → ↥ ( Submodule.map ( DistribMulAction.toLinearMap ℤ ( LatticeCrypto.Utils.Vec.𝓔 n ) s ) L.carrier ) ) ⟨ fun x => ?_, fun x => ?_ ⟩ ) ];
  all_goals norm_num [ abs_of_pos hs, norm_smul, hs.ne' ];
  · -- Since $s$ is positive, we can divide both sides of the equation $s • x = s • a$ by $s$ to get $x = a$.
    intro a ha h_eq
    have h_eq' : x = a := by
      exact smul_right_injective _ hs.ne' h_eq
    exact h_eq' ▸ rfl;
  · rcases x with ⟨ x, hx ⟩ ; rcases hx with ⟨ y, hy, rfl ⟩ ; use y; aesop;

/-
  The above is true even when we filter by a set S
-/
open scoped Pointwise

/-- Scaling down the Gaussian width for `rhoSMassOn` is equivalent to scaling up the lattice and the set. -/
lemma rhoSMassOn_scale {n : ℕ+} (L : EuclideanLattice n n) (s : ℝ) (hs : s ≠ 0) (S : Set (𝓔 n)) :
    rhoSMassOn (1 / s) 0 L S = rhoMassOn 0 (L.smul s hs) (s • S) := by
      -- By definition of `rhoSMassOn` and `rhoMassOn`, we can rewrite the sums in terms of the scaled lattice.
      rw [←rhoSMassOn_one_eq_rhoMassOn];
      unfold rhoSMassOn;
      unfold EuclideanLattice.latticeSum;
      simp [add_zero]
      -- By definition of `smul`, we know that `L.smul s hs` is the lattice generated by the vectors `s • v_i`.
      have h_smul : (L.smul s hs).carrier = {v : 𝓔 n | ∃ w ∈ L.carrier, v = s • w} := by
        ext; simp [EuclideanLattice.smul];
        simp +decide [ Submodule.mem_span_range_iff_exists_fun, LatticeBasis.smul ];
        simp +decide [ Finset.smul_sum, eq_comm ];
        constructor <;> rintro ⟨ c, hc ⟩;
        · use fun i => c i;
          convert hc using 2 ; ext ; simp +decide ;
          exact mul_left_comm _ _ _;
        · use fun i => c i;
          convert hc using 2 ; simp +decide ;
          rw [ SMulCommClass.smul_comm ];
          rfl;
      -- By definition of `smul`, we know that `L.smul s hs` is the lattice generated by the vectors `s • v_i`. Therefore, we can rewrite the sum over `L.smul s hs` as a sum over `L`.
      have h_sum_smul : ∑' (v : ↥(L.smul s hs).carrier), (fun v => (s • S).indicator (rhoS 1) v) ↑v = ∑' (v : ↥L.carrier), (fun v => (s • S).indicator (rhoS 1) (s • v)) ↑v := by
        have h_sum_smul : ∑' (v : ↥(L.smul s hs).carrier), (fun v => (s • S).indicator (rhoS 1) v) ↑v = ∑' (v : ↥{v : 𝓔 n | ∃ w ∈ L.carrier, v = s • w}), (fun v => (s • S).indicator (rhoS 1) v) ↑v := by
          congr!;
        erw [ h_sum_smul, ← Equiv.tsum_eq ( Equiv.ofBijective ( fun w : L.carrier => ⟨ s • w, w, w.2, rfl ⟩ : L.carrier → { v : 𝓔 n | ∃ w ∈ L.carrier, v = s • w } ) ⟨ fun a => ?_, fun a => ?_ ⟩ ) ];
        all_goals norm_num [ hs ];
        · exact fun x hx hx' => Subtype.ext <| smul_right_injective _ hs hx';
        · rcases a with ⟨ v, ⟨ w, hw, rfl ⟩ ⟩ ; use w; aesop;
      rw [h_sum_smul];
      congr! 2; simp [Set.indicator];
      split_ifs <;> simp_all +decide [ Set.mem_smul_set_iff_inv_smul_mem₀ ];

/-- `rhoSTMass` equals a `rhoSMass` on the lattice mapped by the linear equivalence. -/
theorem rhoSTMass_eq_rhoSMass_map
    (L : EuclideanLattice n n) (T : 𝓔 n ≃L[ℝ] 𝓔 n) (s : ℝ) (c : 𝓔 n) :
    rhoSTMass s T c L = rhoSMass s (T c) (L.map T) := by
  let e : L.carrier ≃ (L.map T).carrier := L.mapCarrierEquiv T
  unfold rhoSTMass rhoSMass EuclideanLattice.latticeSum
  calc
    ∑' v : L.carrier, rhoST s T ((v : 𝓔 n) + c)
      =
    ∑' v : L.carrier, rhoS s (((e v : (L.map T).carrier) : 𝓔 n) + T c) := by
      refine tsum_congr ?_
      intro v
      have hcoe : (((e v : (L.map T).carrier) : 𝓔 n)) = T (v : 𝓔 n) := by
        rfl
      simp [rhoST_eq_rhoS_T_x, hcoe, map_add]
    _ =
    ∑' v' : (L.map T).carrier, rhoS s ((v' : 𝓔 n) + T c) := by
      simpa [e] using
        (e.tsum_eq (fun v' : (L.map T).carrier => rhoS s ((v' : 𝓔 n) + T c)))

end gaussian

open Real LatticeCrypto.Foundations.Lattice

noncomputable section periodization

variable {n : ℕ+}

variable {α : Type*}
variable [AddCommMonoid α] [TopologicalSpace α]

/-!
  ## 1. Analytic Periodization

  The periodization of a function `f` over a lattice `L` is the sum of `f`
  over all lattice points, shifted by `x`.

  g(x) = ∑_{v ∈ L} f(x + v)
-/

/-- The raw periodization of a function f over lattice L. -/
def periodize (f : 𝓔 n → α) (L : EuclideanLattice n n) (x : 𝓔 n) : α :=
  L.latticeSum (fun v => f (x + v))
  -- ∑' v : L.carrier, f (x + v)

/-!
  ## 2. Periodicity Properties

  We need to prove that `periodize f L` is indeed periodic with respect to `L`.
  This requires re-indexing the infinite sum.
-/

/-- General theorem: If f is periodic, the sum is invariant under lattice translation. -/
theorem periodize_add_mem (f : 𝓔 n → α) (L : EuclideanLattice n n)
    (x : 𝓔 n) (u : L.carrier) :
    periodize f L (x + u) = periodize f L x := by
  dsimp [periodize]
  -- We proceed by re-indexing the sum.
  -- We map v ↦ u + v, which is a bijection on the group L.carrier.
  let e : L.carrier ≃ L.carrier :=
    { toFun := fun v => u + v
      invFun := fun v => -u + v
      left_inv := fun v => by simp
      right_inv := fun v => by simp }
  dsimp [EuclideanLattice.latticeSum]
  conv_rhs => rw [ ← Equiv.tsum_eq e ] ;
  simp +decide [ add_assoc, e ]

/-!
  ## 3. Lifting to the Quotient

  Now we define the function on the quotient space `(𝓔 n) ⧸ L`.
  This is the "official" object f(x + L).
-/

/--
  The periodization defined as a function on the quotient group (𝓔 n) / L.
  This maps a coset (x + L) to the value ∑ f(x + v).
-/
noncomputable def periodizeQuotient (f : 𝓔 n → α) (L : EuclideanLattice n n) : L.Quotient → α :=
  Quotient.lift (periodize f L) (by
  intro x y hxy
  obtain ⟨g, hg⟩ : ∃ g : L.carrier, x = y + g := by
    obtain ⟨ g, hg ⟩ := hxy;
    aesop
  rw [ hg, periodize_add_mem ])


/-- The fundamental equivalence: The value on the quotient coset `mk x`
    equals the periodization sum at `x`. -/
@[simp]
theorem periodizeQuotient_mk (f : 𝓔 n → α) (L : EuclideanLattice n n) (x : 𝓔 n) :
    periodizeQuotient f L (QuotientAddGroup.mk x) = periodize f L x := by
      exact rfl

/-- A function is periodic with respect to a lattice L if f(x + v) = f(x) for all v ∈ L. -/
def LatticePeriodic (f : 𝓔 n → α) (L : EuclideanLattice n n) : Prop :=
  ∀ v ∈ L, ∀ x, f (x + v) = f x

/-- The periodization of a function is periodic with respect to the lattice. -/
theorem periodize_is_periodic (f : 𝓔 n → α) (L : EuclideanLattice n n) :
    LatticePeriodic (periodize f L) L := by
  intro v hv x;
  -- Apply the lemma that states the periodization is invariant under lattice translation.
  apply periodize_add_mem f L x ⟨v, by
    -- By definition of L, we know that v is in the carrier of L.
    convert hv using 1⟩

/-- Equivalence between lattice-periodic functions and functions on the quotient. -/
noncomputable def periodicEquivQuotient (L : EuclideanLattice n n) :
    { f : 𝓔 n → α // LatticePeriodic f L } ≃ (L.Quotient → α) where
  toFun f := Quotient.lift f.1 (by
  -- Since `a` and `b` are in the same coset, there exists some `v ∈ L` such that `a = b + v`.
  intro a b h_coset
  obtain ⟨v, hv⟩ : ∃ v ∈ L, a = b + v := by
    obtain ⟨ v, hv ⟩ := h_coset;
    aesop;
  aesop)
  invFun g := ⟨g ∘ QuotientAddGroup.mk, by
    intro v hv x;
    convert congr_arg g ( QuotientAddGroup.eq.mpr _ ) using 1;
    simp +decide [ add_comm ];
    exact L.carrier_eq ▸ hv⟩
  left_inv := by
    intro f; ext; aesop;
  right_inv := by
    intro g; (
    funext x; exact (by
    induction x using Quotient.inductionOn' ; aesop))


/-!
  ## 4. Specialization for Gaussian (rho)

  We apply the above to `rho`. We also add the "Normalized" version
  which divides by the total mass ρ(L).
-/

/-- The Gaussian periodization function: g_s(Tx) = ρ_s(Tx + L) -/
def rhoST_periodize (s : ℝ) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (L : EuclideanLattice n n) : 𝓔 n → ℝ :=
  periodize (fun v => rhoST s T v) L


/--
The series exp(-c * n^2) is summable over the integers for c > 0.
-/
lemma summable_exp_neg_mul_sq_int {c : ℝ} (hc : 0 < c) : Summable (fun n : ℤ => Real.exp (-c * n^2)) := by
  -- We can split the sum into non-negative and negative integers.
  suffices h_split : Summable (fun n : ℕ => Real.exp (-c * n^2)) ∧ Summable (fun n : ℕ => Real.exp (-c * (-n : ℤ) ^ 2)) by
    -- The sum over all integers can be split into the sum over non-negative integers and the sum over negative integers.
    have h_split : Summable (fun n : ℤ => Real.exp (-c * n^2)) ↔ Summable (fun n : ℕ => Real.exp (-c * (n : ℤ)^2)) ∧ Summable (fun n : ℕ => Real.exp (-c * (-n : ℤ)^2)) := by
      have h_split : ∀ {f : ℤ → ℝ}, Summable f ↔ Summable (fun n : ℕ => f n) ∧ Summable (fun n : ℕ => f (-n)) := by
        exact fun {f} => summable_int_iff_summable_nat_and_neg
      convert h_split using 1;
    aesop;
  norm_num +zetaDelta at *;
  have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr ( neg_lt_zero.mpr hc ) );
  exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;

/--
The Gaussian series exp(-c ||v||^2) is summable over any full-rank lattice for c > 0.
-/
lemma summable_exp_neg_mul_sq_lattice {n : ℕ+} (L : EuclideanLattice n n) {c : ℝ} (hc : 0 < c) :
  Summable (fun v : L.carrier => Real.exp (-c * ‖(v : 𝓔 n)‖^2)) := by
    by_contra h;
    -- Since $L$ is a full-rank lattice, the sum $\sum_{v \in L} \exp(-c \|v\|^2)$ is equal to the sum $\sum_{m \in \mathbb{Z}^n} \exp(-c \|Bm\|^2)$ for some basis $B$.
    obtain ⟨B, hB⟩ : ∃ B : SquareLatticeBasis n, L = B.toLattice := by
      cases L ; aesop;
    have h_summable : Summable (fun m : Fin n → ℤ => Real.exp (-c * ‖∑ i, m i • B.basis i‖ ^ 2)) := by
      have h_bound : ∃ k > 0, ∀ m : Fin n → ℤ, ‖∑ i, m i • B.basis i‖ ^ 2 ≥ k * ∑ i, m i ^ 2 := by
        have h_bound : ∃ k > 0, ∀ m : Fin n → ℝ, ‖∑ i, m i • B.basis i‖ ^ 2 ≥ k * ∑ i, m i ^ 2 := by
          have h_pos_def : ∀ m : Fin n → ℝ, m ≠ 0 → ‖∑ i, m i • B.basis i‖ ^ 2 > 0 := by
            intro m hm_ne_zero
            have h_lin_ind : LinearIndependent ℝ B.basis := by
              exact B.li;
            rw [ Fintype.linearIndependent_iff ] at h_lin_ind;
            exact sq_pos_of_pos ( norm_pos_iff.mpr <| show ∑ i, m i • B.basis i ≠ 0 from fun h => hm_ne_zero <| funext fun i => h_lin_ind m h i )
          have h_pos_def : ∃ k > 0, ∀ m : Fin n → ℝ, ‖∑ i, m i • B.basis i‖ ^ 2 ≥ k * ∑ i, m i ^ 2 := by
            have h_pos_def : ∃ k > 0, ∀ m : Fin n → ℝ, ∑ i, m i ^ 2 = 1 → ‖∑ i, m i • B.basis i‖ ^ 2 ≥ k := by
              have h_compact : IsCompact {m : Fin n → ℝ | ∑ i, m i ^ 2 = 1} := by
                refine' ( Metric.isCompact_iff_isClosed_bounded.mpr _ );
                exact ⟨ isClosed_eq ( continuous_finset_sum _ fun _ _ => Continuous.pow ( continuous_apply _ ) _ ) continuous_const, isBounded_iff_forall_norm_le.mpr ⟨ 1, fun m hm => by exact pi_norm_le_iff_of_nonneg ( by norm_num ) |>.2 fun i => by simpa using Real.abs_le_sqrt <| show m i ^ 2 ≤ 1 by exact hm.symm ▸ Finset.single_le_sum ( fun i _ => sq_nonneg ( m i ) ) ( Finset.mem_univ i ) ⟩ ⟩;
              have h_min : ∃ m ∈ {m : Fin n → ℝ | ∑ i, m i ^ 2 = 1}, ∀ x ∈ {m : Fin n → ℝ | ∑ i, m i ^ 2 = 1}, ‖∑ i, m i • B.basis i‖ ^ 2 ≤ ‖∑ i, x i • B.basis i‖ ^ 2 := by
                have h_min : ContinuousOn (fun m : Fin n → ℝ => ‖∑ i, m i • B.basis i‖ ^ 2) {m : Fin n → ℝ | ∑ i, m i ^ 2 = 1} := by
                  fun_prop (disch := norm_num);
                have := h_compact.exists_isMinOn ⟨ fun i => if i = 0 then 1 else 0, by norm_num ⟩ h_min;
                exact ⟨ this.choose, this.choose_spec.1, fun x hx => this.choose_spec.2 hx ⟩;
              obtain ⟨ m, hm₁, hm₂ ⟩ := h_min;
              exact ⟨ ‖∑ i, m i • B.basis i‖ ^ 2, h_pos_def m ( by rintro rfl; norm_num at hm₁ ), fun x hx => hm₂ x hx ⟩
            obtain ⟨ k, hk₀, hk ⟩ := h_pos_def;
            refine' ⟨ k, hk₀, fun m => _ ⟩;
            by_cases hm : m = 0;
            · simp [hm];
            · have := hk ( fun i => m i / Real.sqrt ( ∑ i, m i ^ 2 ) ) ?_;
              · simp_all +decide [ div_eq_inv_mul, Finset.mul_sum _ _ _ ];
                convert mul_le_mul_of_nonneg_right this ( show 0 ≤ ∑ i, m i ^ 2 from Finset.sum_nonneg fun _ _ => sq_nonneg _ ) using 1 ; simp +decide [ ← Finset.mul_sum ];
                rw [ show ( ∑ x : Fin n, m x • B.basis x ) = ( Real.sqrt ( ∑ i : Fin n, m i ^ 2 ) ) • ( ∑ x : Fin n, ( m x * ( Real.sqrt ( ∑ i : Fin n, m i ^ 2 ) ) ⁻¹ ) • B.basis x ) by rw [ Finset.smul_sum ] ; exact Finset.sum_congr rfl fun _ _ => by simp +decide [ mul_left_comm, smul_smul, ne_of_gt ( Real.sqrt_pos.mpr ( show 0 < ∑ i : Fin n, m i ^ 2 from lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( Ne.symm <| by intro H; exact hm <| funext fun i => by simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ) ) ) ] ] ; rw [ norm_smul, Real.norm_of_nonneg <| Real.sqrt_nonneg _ ] ; ring_nf;
                rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] ; ac_rfl;
              · norm_num [ div_pow, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
                rw [ ← Finset.sum_div, div_self <| ne_of_gt <| lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) <| Ne.symm <| by intro H; exact hm <| funext fun i => by simpa [ H ] using Finset.sum_eq_zero_iff_of_nonneg ( fun _ _ => sq_nonneg _ ) |>.1 H i ];
          exact h_pos_def;
        obtain ⟨ k, hk₀, hk ⟩ := h_bound; use k, hk₀; intro m; specialize hk ( fun i => m i ) ; simp_all +decide [ Finset.mul_sum _ _ _ ] ;
        convert hk using 1;
        norm_cast
      obtain ⟨ k, hk₀, hk ⟩ := h_bound;
      -- Since $\exp(-c * k * \sum_{i=1}^n m_i^2)$ is a product of exponentials, we can apply the comparison test.
      have h_prod_exp : Summable (fun m : Fin n → ℤ => ∏ i : Fin n, Real.exp (-c * k * m i ^ 2)) := by
        have h_prod_exp : Summable (fun m : Fin n → ℤ => ∏ i : Fin n, Real.exp (-c * k * m i ^ 2)) := by
          have h_summable : Summable (fun m : ℤ => Real.exp (-c * k * m ^ 2)) := by
            have := summable_exp_neg_mul_sq_int ( show 0 < c * k by positivity );
            simpa only [ neg_mul ] using this
          -- Apply the fact that the product of summable series is summable.
          have h_prod_summable : ∀ {n : ℕ}, (∀ i : Fin n, Summable (fun m : ℤ => Real.exp (-c * k * m ^ 2))) → Summable (fun m : Fin n → ℤ => ∏ i : Fin n, Real.exp (-c * k * m i ^ 2)) := by
            intro n hn; induction n <;> simp_all +decide [ Fin.prod_univ_succ ] ;
            · exact ⟨ _, hasSum_fintype _ ⟩;
            · rename_i n ih;
              have h_prod_summable : Summable (fun m : ℤ × (Fin n → ℤ) => Real.exp (-c * k * m.1 ^ 2) * ∏ i : Fin n, Real.exp (-c * k * m.2 i ^ 2)) := by
                exact .of_norm <| by simpa using Summable.mul_norm ( h_summable.norm ) ( ih.norm ) ;
              convert h_prod_summable.comp_injective ( show Function.Injective ( fun m : Fin ( n + 1 ) → ℤ => ( m 0, fun i => m ( Fin.succ i ) ) ) from fun m m' h => by simpa [ funext_iff, Fin.forall_fin_succ ] using h ) using 1;
              ext; simp [Function.comp];
          exact h_prod_summable fun _ => h_summable;
        convert h_prod_exp using 1;
      refine' h_prod_exp.of_nonneg_of_le ( fun m => Real.exp_nonneg _ ) ( fun m => _ );
      rw [ ← Real.exp_sum ];
      exact Real.exp_le_exp.mpr ( by simpa [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ] using mul_le_mul_of_nonpos_left ( hk m ) ( neg_nonpos.mpr hc.le ) );
    -- Since these two sums are equal, we can conclude that the original sum is also summable.
    have h_eq_sum : ∑' v : L.carrier, Real.exp (-c * ‖(v : 𝓔 n)‖ ^ 2) = ∑' m : Fin n → ℤ, Real.exp (-c * ‖∑ i, m i • B.basis i‖ ^ 2) := by
      rw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun m : Fin n → ℤ => ⟨ ∑ i, m i • B.basis i, ?_ ⟩ : ( Fin n → ℤ ) → L.carrier ) ⟨ ?_, ?_ ⟩ ) ];
      all_goals simp_all +decide [ Function.Injective, Function.Surjective ];
      · have := B.li;
        rw [ Fintype.linearIndependent_iff ] at this;
        intro a₁ a₂ h; ext i; specialize this ( fun j => ( a₁ j : ℝ ) - a₂ j ) ; simp_all +decide [ sub_eq_zero ] ;
        simp_all +decide [ sub_smul, Finset.sum_sub_distrib ];
        exact this ( sub_eq_zero.mpr <| mod_cast h ) i;
      · intro a ha; rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at ha; aesop;
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_range_self _ ) );
    refine' h _;
    contrapose! h_eq_sum;
    rw [ tsum_eq_zero_of_not_summable h_eq_sum ] ; exact ne_of_lt <| lt_of_lt_of_le ( by positivity ) <| Summable.le_tsum ( h_summable ) 0 <| fun _ _ => by positivity;

-- Turn off unused variable linter for the following theorem because the proof actually does use `hs` implicitly in the `positivity` tactic.
set_option linter.unusedVariables false in
/-- The periodized rhoST function is continuous. -/
theorem rhoST_periodize.continuous :
    ∀ (s : ℝ) (hs : 0 ≠ s) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (L : EuclideanLattice n n),
    Continuous (rhoST_periodize s T L) := by
  intro s hs T L;
  -- The series sum of continuous functions is continuous if it converges uniformly.
  have h_sum_cont : Continuous (fun x : 𝓔 n => ∑' v : L.carrier, Real.exp (-Real.pi * ‖T (x + v)‖^2 / s^2)) := by
    have h_uniform : ∀ K : Set (𝓔 n), IsCompact K → Summable (fun v : L.carrier => Real.exp (-Real.pi * ‖T (v : 𝓔 n)‖^2 / (4 * s^2))) → ContinuousOn (fun x => ∑' v : L.carrier, Real.exp (-Real.pi * ‖T (x + v)‖^2 / s^2)) K := by
      intros K hK h_summable
      have h_uniform : ∀ x ∈ K, ∀ v : L.carrier, Real.exp (-Real.pi * ‖T (x + v)‖^2 / s^2) ≤ Real.exp (-Real.pi * ‖T (v : 𝓔 n)‖^2 / (4 * s^2)) * Real.exp (4 * Real.pi * (sSup (Set.image (fun x => ‖T x‖) K))^2 / s^2) := by
        -- Since $T$ is a linear equivalence, we have $\|T(x + v)\| \geq \|Tv\| - \|Tx\|$.
        have h_norm : ∀ x ∈ K, ∀ v : L.carrier, ‖T (x + v)‖ ≥ ‖T (v : 𝓔 n)‖ - ‖T x‖ := by
          intro x hx v; have := norm_sub_le ( T ( x + v ) ) ( T x ) ; aesop;
        intro x hx v
        have h_exp : ‖T (x + v)‖^2 ≥ ‖T (v : 𝓔 n)‖^2 / 2 - 2 * ‖T x‖^2 := by
          by_cases h_case : ‖T (v : 𝓔 n)‖ ≥ 2 * ‖T x‖;
          · nlinarith [ h_norm x hx v, norm_nonneg ( T x ), norm_nonneg ( T ( x + v ) ) ];
          · nlinarith [ norm_nonneg ( T ( x + v ) ), norm_nonneg ( T v ), norm_nonneg ( T x ) ];
        rw [ ← Real.exp_add ];
        refine' Real.exp_le_exp.mpr _;
        have h_exp : ‖T x‖^2 ≤ (sSup (Set.image (fun x => ‖T x‖) K))^2 := by
          exact pow_le_pow_left₀ ( norm_nonneg _ ) ( le_csSup ( IsCompact.bddAbove ( hK.image ( continuous_norm.comp T.continuous ) ) ) ( Set.mem_image_of_mem _ hx ) ) _;
        ring_nf at *;
        nlinarith [ show 0 ≤ Real.pi * s⁻¹ ^ 2 by positivity ];
      refine' continuousOn_tsum _ _ _;
      use fun v => Real.exp ( -Real.pi * ‖T ( v : 𝓔 n )‖ ^ 2 / ( 4 * s ^ 2 ) ) * Real.exp ( 4 * Real.pi * ( SupSet.sSup ( Set.image ( fun x => ‖T x‖ ) K ) ) ^ 2 / s ^ 2 );
      · fun_prop (disch := norm_num);
      · exact h_summable.mul_right _;
      · exact fun v x hx => by rw [ Real.norm_of_nonneg ( Real.exp_nonneg _ ) ] ; exact h_uniform x hx v;
    refine' continuous_iff_continuousAt.mpr fun x => _;
    refine' h_uniform ( Metric.closedBall x 1 ) ( ProperSpace.isCompact_closedBall _ _ ) _ |> ContinuousOn.continuousAt <| Metric.closedBall_mem_nhds _ zero_lt_one;
    have := @summable_exp_neg_mul_sq_lattice;
    -- Since $T$ is a linear equivalence, there exists a constant $C > 0$ such that $\|T(v)\| \geq C \|v\|$ for all $v \in L$.
    obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ v : L.carrier, ‖T (v : 𝓔 n)‖ ≥ C * ‖(v : 𝓔 n)‖ := by
      have h_inv : ∃ C > 0, ∀ v : 𝓔 n, ‖T⁻¹ v‖ ≤ C * ‖v‖ := by
        have := T.symm.toContinuousLinearMap.bound;
        exact this;
      obtain ⟨ C, hC₀, hC ⟩ := h_inv;
      exact ⟨ 1 / C, one_div_pos.mpr hC₀, fun v => by have := hC ( T v ) ; rw [ show T⁻¹ ( T v ) = v from T.symm_apply_apply v ] at this; rw [ div_mul_eq_mul_div, ge_iff_le, div_le_iff₀' hC₀ ] ; linarith ⟩;
    have := @this n L ( Real.pi * C ^ 2 / ( 4 * s ^ 2 ) ) ( by positivity );
    refine' this.of_nonneg_of_le ( fun v => Real.exp_nonneg _ ) ( fun v => Real.exp_le_exp.mpr _ );
    field_simp;
    gcongr ; nlinarith [ hC v, norm_nonneg ( T v ), norm_nonneg ( v : 𝓔 n ), mul_le_mul_of_nonneg_left ( hC v ) hC_pos.le ];
  have hs' : s ≠ 0 := by simpa [eq_comm] using hs
  convert h_sum_cont using 1;
  funext x; exact (by
  simp +decide only [rhoST_periodize, rhoST, hs'];
  ring_nf;
  norm_num; ring_nf;
  simp +decide [ mul_assoc, periodize ];
  simp +decide [ ← smul_add, norm_smul, mul_pow, EuclideanLattice.latticeSum ])

/-- The periodization of rhoST is integrable on the fundamental domain. -/
theorem rhoST_periodize.integrableOn_fundamentalDomain :
    ∀ (s : ℝ) (hs : 0 ≠ s) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (L : EuclideanLattice n n),
    MeasureTheory.IntegrableOn (rhoST_periodize s T L) L.basis.fundamentalDomain := by
  intro s hs T L;
  have h_cont : Continuous (rhoST_periodize s T L) := continuous s hs T L
  -- The fundamental domain is a subset of the space, and since the function is continuous, it's integrable on any bounded set.
  have h_bounded : Bornology.IsBounded L.basis.fundamentalDomain := by
    exact LatticeBasis.fundamentalDomain_isBounded L.basis;
  have h_integrable : MeasureTheory.IntegrableOn (rhoST_periodize s T L) (closure L.basis.fundamentalDomain) MeasureTheory.volume := by
    apply_rules [ ContinuousOn.integrableOn_compact, h_cont.continuousOn ];
    exact h_bounded.isCompact_closure;
  exact h_integrable.mono_set <| subset_closure

/-- The Gaussian periodization on the quotient. -/
noncomputable def rhoST_periodizeQuotient (s : ℝ) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (L : EuclideanLattice n n) : L.Quotient → ℝ :=
  periodizeQuotient (fun v => rhoST s T v) L

/-- The Gaussian periodization function: g_s(x) = ρ_s(x + L) -/
def rhoS_periodize (s : ℝ) (L : EuclideanLattice n n) : 𝓔 n → ℝ :=
  periodize (fun v => ρ[s] v) L

/-- The Gaussian periodization on the quotient. -/
noncomputable def rhoS_periodizeQuotient (s : ℝ) (L : EuclideanLattice n n) : L.Quotient → ℝ :=
  periodizeQuotient (fun v => rhoS s v) L

/-- The periodized rho's value equals that of the rhoMass of a coset-/
theorem rhoS_periodize_eq_rhoSMass_on_coset (s : ℝ) (L : EuclideanLattice n n) (x : 𝓔 n) :
    rhoS_periodize s L x = rhoSMass s x L := by
  dsimp [rhoS_periodize, periodize];
  rw [rhoSMass]
  congr;
  funext v;
  rw [ add_comm ]

/-- The Gaussian periodization function: g_s(x) = ρ_s(x + L) -/
def rho_periodize (L : EuclideanLattice n n) : 𝓔 n → ℝ :=
  rhoS_periodize 1 L

/-- The Gaussian periodization on the quotient. -/
noncomputable def rho_periodizeQuotient (L : EuclideanLattice n n) : L.Quotient → ℝ :=
  rhoS_periodizeQuotient 1 L


end periodization


noncomputable section discrete_gaussian

variable {n : ℕ+}
open scoped ENNReal

/-!
 ## Discrete Gaussian over lattice L with center c and parameter s
 The majority of this section devotes to proving that the discrete Gaussian distribution is well-defined.
 -/

/-- The rhoS function is positive for any `s > 0` and `x ≠ 0`. -/
lemma rhoS_pos {n : ℕ+} (s : ℝ) (hs : s ≠ 0) (x : 𝓔 n) : 0 < rhoS s x := by
  simpa [rhoS, hs] using (Real.exp_pos (-(π * ‖s⁻¹ • x‖^2)))

/-!
 ### Prove that the discrete Gaussian weights sum to a finite value
 -/

/-
The integer coefficients of a lattice vector with respect to the lattice basis.
-/
noncomputable def basisReprCoeff (L : EuclideanLattice n n) (v : L.carrier) : Fin n → ℤ :=
  L.basis.repr (v : 𝓔 n) (by
  cases L ; aesop)

/-
The norm of a lattice vector is bounded below by a constant times the norm of its coefficient vector.
-/
lemma norm_ge_norm_coeffs (L : EuclideanLattice n n) :
  ∃ C > 0, ∀ v : L.carrier, ‖(v : 𝓔 n)‖ ≥ C * ‖(fun i => (basisReprCoeff L v i : ℝ))‖ := by
    -- The map from lattice vectors to their coefficients is bounded.
    obtain ⟨C, hC_pos, hC_bound⟩ : ∃ C > 0, ∀ (c : Fin n → ℝ), ‖∑ i, c i • L.basis.cols i‖ ≥ C * ‖c‖ := by
      -- Let T be the linear map from ℝ^n to ℝ^n given by T(c) = ∑ c_i L.basis.cols i.
      set T : (Fin n → ℝ) →ₗ[ℝ] 𝓔 n := ∑ i, (LinearMap.smulRight (LinearMap.proj i) (L.basis.cols i));
      -- Since T is invertible, we can apply the fact that the norm of the inverse of a linear map is bounded.
      have hT_inv : ∃ T_inv : 𝓔 n →ₗ[ℝ] (Fin n → ℝ), T_inv.comp T = LinearMap.id ∧ T.comp T_inv = LinearMap.id := by
        have hT_inv : Function.Bijective T := by
          have hT_iso : Function.Injective T := by
            have hT_inv : Function.Injective T := by
              have hT_inv : ∀ (c : Fin n → ℝ), T c = 0 → c = 0 := by
                intro c hc; have := Fintype.linearIndependent_iff.mp L.basis.li; aesop;
              exact LinearMap.ker_eq_bot.mp ( LinearMap.ker_eq_bot'.mpr hT_inv );
            exact hT_inv;
          exact ⟨ hT_iso, LinearMap.surjective_of_injective hT_iso ⟩;
        obtain ⟨T_inv, hT_inv⟩ : ∃ T_inv : 𝓔 n →ₗ[ℝ] (Fin n → ℝ), T_inv.comp T = LinearMap.id := by
          exact ⟨ LinearEquiv.symm ( LinearEquiv.ofBijective T hT_inv ), by ext; simp +decide ⟩;
        refine' ⟨ T_inv, hT_inv, _ ⟩;
        exact LinearMap.comp_eq_id_comm.mp hT_inv;
      obtain ⟨T_inv, hT_inv⟩ := hT_inv;
      -- Since T is invertible, we can apply the fact that the norm of the inverse of a linear map is bounded. Specifically, there exists a constant C such that ‖T_inv(v)‖ ≤ C * ‖v‖ for all v.
      obtain ⟨C, hC⟩ : ∃ C > 0, ∀ (v : 𝓔 n), ‖T_inv v‖ ≤ C * ‖v‖ := by
        have hT_inv_bounded : ∃ C > 0, ∀ (v : 𝓔 n), ‖T_inv v‖ ≤ C * ‖v‖ := by
          have hT_inv_cont : Continuous T_inv := by
            exact LinearMap.continuous_of_finiteDimensional T_inv
          exact SemilinearMapClass.bound_of_continuous T_inv hT_inv_cont;
        exact hT_inv_bounded;
      refine' ⟨ 1 / C, one_div_pos.mpr hC.1, fun c => _ ⟩;
      have := hC.2 ( T c ) ; simp_all +decide [ LinearMap.ext_iff ] ;
      rw [ inv_mul_le_iff₀ ] <;> aesop;
    refine' ⟨ C, hC_pos, fun v => le_trans ( mul_le_mul_of_nonneg_left ( _ : ‖fun i => ↑ ( basisReprCoeff L v i )‖ ≤ ‖ ( fun i => ↑ ( basisReprCoeff L v i ) : Fin n → ℝ )‖ ) hC_pos.le ) ( hC_bound _ |> le_trans <| _ ) ⟩;
    · exact Std.IsPreorder.le_refl ‖fun i => basisReprCoeff L v i‖;
    · have := L.basis.repr_spec ( v : 𝓔 n ) ( by aesop );
      exact this ▸ by norm_cast;

/-
The sum of exp(-C * z^2) over all integers z is finite for C > 0.
-/
lemma summable_int_gaussian_1d (C : ℝ) (hC : 0 < C) :
  Summable (fun (z : ℤ) => Real.exp (-C * (z : ℝ)^2)) := by
    -- We'll use the fact that the series $\sum_{z \in \mathbb{Z}} \exp(-C |z|^2)$ is a special case of the Gaussian series, which converges.
    have h_gauss_series : Summable (fun z : ℕ => Real.exp (-C * z^2)) := by
      have := summable_geometric_of_lt_one ( by positivity ) ( Real.exp_lt_one_iff.mpr <| neg_lt_zero.mpr hC );
      exact this.of_nonneg_of_le ( fun n => by positivity ) fun n => by rw [ ← Real.exp_nat_mul ] ; ring_nf; gcongr ; norm_cast ; nlinarith;
    have h_split : ∀ {g : ℤ → ℝ}, Summable (fun z : ℕ => g z) → Summable (fun z : ℕ => g (-z)) → Summable (fun z : ℤ => g z) := by
      intro g hg₁ hg₂; exact Summable.of_nat_of_neg hg₁ hg₂;
    convert h_split _ _ using 1 <;> norm_num [ Real.exp_neg ];
    · simpa [ Real.exp_neg ] using h_gauss_series;
    · simpa [ Real.exp_neg ] using h_gauss_series

/-
The sum of exp(-C * ||c||^2) over integer vectors c is finite for C > 0.
-/
lemma summable_int_gaussian (C : ℝ) (hC : 0 < C) :
  Summable (fun (c : Fin n → ℤ) => Real.exp (-C * ‖(fun i => (c i : ℝ))‖^2)) := by
    -- The sum of exp(-C * z^2) over all integers z is finite for C > 0 by the properties of the Gaussian integral.
    have h_sum_gauss : ∀ C > 0, Summable (fun (z : ℤ) => Real.exp (-C * (z : ℝ)^2)) := by
      exact fun C a => summable_int_gaussian_1d C a;
    specialize h_sum_gauss ( C / n ) ( div_pos hC <| Nat.cast_pos.mpr n.pos );
    -- By the properties of the Gaussian function, we know that $\exp(-C \|c\|^2) \leq \exp(-C / n \|c\|^2)$ for any integer vector $c$.
    have h_le : ∀ c : Fin n → ℤ, Real.exp (-C * ‖(fun i => (c i : ℝ))‖^2) ≤ Real.exp (-C / n * ∑ i, (c i : ℝ)^2) := by
      intro c
      have h_norm_sq : ‖(fun i => (c i : ℝ))‖^2 ≥ (∑ i, (c i : ℝ)^2) / (n : ℝ) := by
        rw [ ge_iff_le, div_le_iff₀ ] <;> norm_num;
        -- Since ‖c‖ is the supremum of |c_i|, we have |c_i| ≤ ‖c‖ for all i.
        have h_abs_le_norm : ∀ i, |(c i : ℝ)| ≤ ‖(fun i => (c i : ℝ))‖ := by
          exact fun i => by simpa using norm_le_pi_norm ( fun i => c i : Fin n → ℝ ) i;
        exact le_trans ( Finset.sum_le_sum fun i _ => show ( c i : ℝ ) ^ 2 ≤ ‖fun i => ( c i : ℝ )‖ ^ 2 by nlinarith only [ abs_le.mp ( h_abs_le_norm i ) ] ) ( by norm_num; linarith );
      exact Real.exp_le_exp.mpr ( by ring_nf at *; nlinarith );
    have h_summable_prod : Summable (fun (c : Fin n → ℤ) => ∏ i, Real.exp (-C / n * (c i : ℝ)^2)) := by
      have h_summable_prod : ∀ m : ℕ, Summable (fun (c : Fin m → ℤ) => ∏ i, Real.exp (-C / n * (c i : ℝ)^2)) := by
        intro m; induction m <;> simp_all +decide [ Fin.prod_univ_succ ] ;
        · exact ⟨ _, hasSum_fintype _ ⟩;
        · rename_i k hk;
          have h_summable_prod : Summable (fun (c : ℤ × (Fin k → ℤ)) => Real.exp (-C / n * (c.1 : ℝ)^2) * ∏ i, Real.exp (-C / n * (c.2 i : ℝ)^2)) := by
            exact .of_norm <| by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using Summable.mul_norm ( h_sum_gauss.norm ) ( hk.norm ) ;
          convert h_summable_prod.comp_injective ( show Function.Injective ( fun c : Fin ( k + 1 ) → ℤ => ( c 0, fun i => c ( Fin.succ i ) ) ) from fun a b h => by simpa [ funext_iff, Fin.forall_fin_succ ] using h ) using 1;
      exact h_summable_prod n;
    exact Summable.of_nonneg_of_le ( fun c => Real.exp_nonneg _ ) ( fun c => le_trans ( h_le c ) ( by rw [ ← Real.exp_sum ] ; exact Real.exp_le_exp.mpr ( by simp [ div_eq_mul_inv, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ) ) ) h_summable_prod

/-
A lower bound on the squared norm of a shifted vector.
-/
lemma norm_sq_shift_bound (v c : 𝓔 n) : ‖v - c‖^2 ≥ 1/2 * ‖v‖^2 - ‖c‖^2 := by
  norm_num [ EuclideanSpace.norm_eq, Real.sq_sqrt ] at *;
  rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ), Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ), Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ];
  rw [ ← Finset.sum_add_distrib ];
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ => by nlinarith only [ sq_nonneg ( v i - 2 * c i ) ] ;

/-- The rhoS function is summable on any `EuclideanLattice` for any `s > 0`. -/
private lemma summable_rhoS_pos_aux (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (c : 𝓔 n) :
  Summable (fun v : L.carrier => rhoS s ((v : 𝓔 n) - c)) := by
    -- Using the bound from `norm_ge_norm_coeffs`, we can show that the sum is summable.
    have h_summable : Summable (fun (v : L.carrier) => Real.exp (-Real.pi / (2 * s^2) * ‖(v : 𝓔 n)‖^2)) := by
      -- Using the bound from `norm_ge_norm_coeffs`, we know that ‖v‖^2 ≥ C^2 * ‖basisReprCoeff L v‖^2 for some C > 0.
      obtain ⟨C, hC_pos, hC_bound⟩ : ∃ C > 0, ∀ v : L.carrier, ‖(v : 𝓔 n)‖^2 ≥ C^2 * ‖(fun i => (basisReprCoeff L v i : ℝ))‖^2 := by
        obtain ⟨ C, hC_pos, hC_bound ⟩ := norm_ge_norm_coeffs L;
        exact ⟨ C, hC_pos, fun v => by nlinarith [ hC_bound v, show 0 ≤ C * ‖fun i => ( basisReprCoeff L v i : ℝ )‖ by positivity ] ⟩;
      have h_summable : Summable (fun (c : Fin n → ℤ) => Real.exp (-Real.pi / (2 * s^2) * C^2 * ‖(fun i => (c i : ℝ))‖^2)) := by
        have h_summable : Summable (fun (c : Fin n → ℤ) => Real.exp (-Real.pi * C^2 / (2 * s^2) * ‖(fun i => (c i : ℝ))‖^2)) := by
          have h_C_pos : 0 < Real.pi * C^2 / (2 * s^2) := by
            positivity
          convert summable_int_gaussian ( Real.pi * C ^ 2 / ( 2 * s ^ 2 ) ) h_C_pos using 2 ; ring_nf;
        convert h_summable using 3 ; ring;
      have h_summable : Summable (fun (v : L.carrier) => Real.exp (-Real.pi / (2 * s^2) * C^2 * ‖(fun i => (basisReprCoeff L v i : ℝ))‖^2)) := by
        convert h_summable.comp_injective ( show Function.Injective ( fun v : L.carrier => basisReprCoeff L v ) from ?_ ) using 1;
        intro v w hvw;
        have h_eq : (v : 𝓔 n) = ∑ i, (basisReprCoeff L v i : ℝ) • L.basis.cols i ∧ (w : 𝓔 n) = ∑ i, (basisReprCoeff L w i : ℝ) • L.basis.cols i := by
          have h_eq : ∀ v : L.carrier, (v : 𝓔 n) = ∑ i, (basisReprCoeff L v i : ℝ) • L.basis.cols i := by
            intro v; exact (by
            convert L.basis.repr_spec ( v : 𝓔 n ) ( by aesop ) using 1;
            congr!;
            ext; simp [basisReprCoeff]);
          exact ⟨ h_eq v, h_eq w ⟩;
        ext; aesop;
      refine' h_summable.of_nonneg_of_le ( fun v => Real.exp_nonneg _ ) ( fun v => Real.exp_le_exp.mpr _ );
      rw [ mul_assoc ] ; exact mul_le_mul_of_nonpos_left ( hC_bound v ) ( div_nonpos_of_nonpos_of_nonneg ( neg_nonpos.mpr Real.pi_pos.le ) ( by positivity ) );
    have h_summable : Summable (fun (v : L.carrier) => Real.exp (-Real.pi / s^2 * ‖(v : 𝓔 n) - c‖^2)) := by
      -- Using the bound from `norm_sq_shift_bound`, we can show that the sum is summable.
      have h_summable : ∀ v : L.carrier, Real.exp (-Real.pi / s^2 * ‖(v : 𝓔 n) - c‖^2) ≤ Real.exp (Real.pi * ‖c‖^2 / s^2) * Real.exp (-Real.pi / (2 * s^2) * ‖(v : 𝓔 n)‖^2) := by
        intro v; rw [ ← Real.exp_add ] ; ring_nf; norm_num;
        have := norm_sq_shift_bound ( v : 𝓔 n ) c;
        nlinarith [ show 0 ≤ Real.pi * ( s ^ 2 ) ⁻¹ by positivity ];
      exact Summable.of_nonneg_of_le ( fun v => Real.exp_nonneg _ ) h_summable ( Summable.mul_left _ ‹_› );
    rw [show (fun v : L.carrier => rhoS s ((v : 𝓔 n) - c)) =
      (fun v : L.carrier => Real.exp (-Real.pi / s^2 * ‖(v : 𝓔 n) - c‖^2)) from by
        funext v
        rw [rhoS_of_ne_zero hs.ne']
        ring_nf
        norm_num [norm_smul, mul_pow, mul_assoc, mul_comm, mul_left_comm]
    ]
    exact h_summable

/-- The rhoS function is summable on any `EuclideanLattice` -/
theorem summable_rhoS (L : EuclideanLattice n n) (s : ℝ) (c : 𝓔 n) :
  Summable (fun v : L.carrier => rhoS s ((v : 𝓔 n) - c)) := by
  by_cases hs0 : s = 0
  · have h_le :
      ∀ v : L.carrier, rhoS s ((v : 𝓔 n) - c) ≤ rhoS 1 ((v : 𝓔 n) - c) := by
        intro v
        subst hs0
        by_cases hv0 : ((v : 𝓔 n) - c) = 0
        · simp [rhoS, hv0]
        · simpa [rhoS, hv0] using (rhoS_nonneg 1 (((v : 𝓔 n) - c)))
    exact Summable.of_nonneg_of_le
      (fun v => rhoS_nonneg s _)
      h_le
      (summable_rhoS_pos_aux L 1 zero_lt_one c)
  · have h_abs_eq :
      (fun v : L.carrier => rhoS s ((v : 𝓔 n) - c)) =
      (fun v : L.carrier => rhoS |s| ((v : 𝓔 n) - c)) := by
      funext v
      rw [rhoS_of_ne_zero hs0, rhoS_of_ne_zero (abs_ne_zero.mpr hs0)]
      congr 1
      congr 1
      rw [norm_smul, norm_smul]
      simp [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg s)]
    exact h_abs_eq.symm ▸ summable_rhoS_pos_aux L |s| (abs_pos.mpr hs0) c

/-- Tilted rhoS is also summable for any `s > 0` -/
private lemma summable_rhoST_pos_aux (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s)
    (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (c : 𝓔 n) :
  Summable (fun v : L.carrier => rhoST s T ((v : 𝓔 n) - c)) := by
  have upper_bounded : ∃ M > 0, ∀ v ∈ L.carrier, ‖T (v - c)‖^2 ≥ ‖v - c‖^2 / M := by
    have h_m_ge_zero : ∃ m > 0, ∀ v : 𝓔 n, ‖v‖ ≤ m * ‖T v‖ := by
      have := T.symm.toContinuousLinearMap.bound;
      obtain ⟨ C, hC₀, hC ⟩ := this; exact ⟨ C, hC₀, fun v => by simpa using hC ( T v ) ⟩ ;
    obtain ⟨ m, hm₀, hm ⟩ := h_m_ge_zero; exact ⟨ m ^ 2, by positivity, fun v hv => by rw [ ge_iff_le ] ; rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ hm ( v - c ), norm_nonneg ( v - c ), norm_nonneg ( T ( v - c ) ) ] ⟩ ;
  -- By combining the results from upper_bounded and summable_rhoS, we can conclude the proof.
  obtain ⟨M, hM_pos, hM⟩ := upper_bounded
  have h_summable : Summable (fun v : L.carrier => Real.exp (-Real.pi * ‖v - c‖^2 / (s^2 * M))) := by
    have h_summable' : Summable (fun v : L.carrier => rhoS (s * Real.sqrt M) ((v : 𝓔 n) - c)) := by
      exact summable_rhoS_pos_aux L (s * Real.sqrt M) (by positivity) c
    have h_eq :
        (fun v : L.carrier => Real.exp (-Real.pi * ‖(v : 𝓔 n) - c‖^2 / (s^2 * M))) =
        (fun v : L.carrier => rhoS (s * Real.sqrt M) ((v : 𝓔 n) - c)) := by
      funext v
      symm
      rw [rhoS_of_ne_zero (by positivity : s * Real.sqrt M ≠ 0)]
      ring_nf
      norm_num [hs.le, hM_pos.le, norm_smul, mul_pow]
      ring
    exact h_eq.symm ▸ h_summable'
  refine' .of_nonneg_of_le ( fun v => _ ) ( fun v => _ ) h_summable;
  · exact rhoST_nonneg s T ((v : 𝓔 n) - c)
  · rw [rhoST_of_ne_zero hs.ne']
    simp_all +decide [ norm_smul, mul_pow, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    exact mul_le_mul_of_nonneg_left ( by have := hM v ( by simpa using v.2 ) ; nlinarith [ inv_pos.mpr hM_pos, inv_pos.mpr ( sq_pos_of_pos hs ), mul_inv_cancel₀ hM_pos.ne', mul_inv_cancel₀ ( ne_of_gt ( sq_pos_of_pos hs ) ) ] ) Real.pi_pos.le

/-- The rhoST function is summable on any `EuclideanLattice`. -/
theorem summable_rhoST (L : EuclideanLattice n n) (s : ℝ) (T : (𝓔 n) ≃L[ℝ] (𝓔 n)) (c : 𝓔 n) :
  Summable (fun v : L.carrier => rhoST s T ((v : 𝓔 n) - c)) := by
  by_cases hs0 : s = 0
  · have h_le :
      ∀ v : L.carrier, rhoST s T ((v : 𝓔 n) - c) ≤ rhoST 1 T ((v : 𝓔 n) - c) := by
        intro v
        subst hs0
        by_cases hv0 : ((v : 𝓔 n) - c) = 0
        · simp [rhoST, hv0]
        · simpa [rhoST, hv0] using (rhoST_nonneg 1 T (((v : 𝓔 n) - c)))
    exact Summable.of_nonneg_of_le
      (fun v => rhoST_nonneg s T _)
      h_le
      (summable_rhoST_pos_aux L 1 zero_lt_one T c)
  · have h_abs_eq :
      (fun v : L.carrier => rhoST s T ((v : 𝓔 n) - c)) =
      (fun v : L.carrier => rhoST |s| T ((v : 𝓔 n) - c)) := by
      funext v
      rw [rhoST_of_ne_zero hs0, rhoST_of_ne_zero (abs_ne_zero.mpr hs0)]
      congr 1
      congr 1
      rw [norm_smul, norm_smul]
      simp [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg s)]
    exact h_abs_eq.symm ▸ summable_rhoST_pos_aux L |s| (abs_pos.mpr hs0) T c

/-
 Handy corollary: The Gaussian mass of a lattice is equal to 1 plus the Gaussian mass of the non-zero lattice vectors.
-/
lemma rhoSMass_eq_one_add_rhoSMassOn_nonzero {n : ℕ+} (L : EuclideanLattice n n) (s : ℝ) :
  rhoSMass s 0 L = 1 + rhoSMassOn s 0 L {0}ᶜ := by
    unfold rhoSMass rhoSMassOn;
    unfold EuclideanLattice.latticeSum;
    rw [ Summable.tsum_eq_add_tsum_ite ];
    congr! 1;
    rotate_right;
    exact ⟨ 0, L.zero_mem ⟩;
    · simp [rhoS]
    · exact tsum_congr fun x => by aesop;
    · have := @LatticeCrypto.Foundations.Gaussian.summable_rhoS ( n := n );
      simpa using this L s 0


/-- Corollary : for a same lattice, a wider Gaussian has larger mass -/
lemma rhoSTMass_mono {s₁ s₂ : ℝ} {T : (𝓔 n) ≃L[ℝ] (𝓔 n)} (h1  : 0 < s₁) (h : s₁ ≤ s₂) (L : EuclideanLattice n n) :
    rhoSTMass s₁ T 0 L ≤ rhoSTMass s₂ T 0 L := by
  have h_sum_ge_s₁ : ∀ v : L.carrier, rhoST s₁ T ((v : 𝓔 n)) ≤ rhoST s₂ T ((v : 𝓔 n)) := by
    intros v; exact (rhoST_mono h1 h T (v : 𝓔 n));
  apply_rules [ Summable.tsum_le_tsum ];
  ·
    have := @summable_rhoST;
    -- Apply the hypothesis `this` with `c = 0` to conclude the summability of the series.
    specialize this L s₁ T 0;
    aesop
  ·
    convert summable_rhoST L s₁ T 0 using 1;
    norm_num [ add_zero]
  .
    convert summable_rhoST L s₂ T 0 using 1;
    norm_num [ add_zero]

/-- Corollary : just apply the above to T = identity map -/
corollary rhoSMass_mono {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h : s₁ ≤ s₂) (L : EuclideanLattice n n) :
    rhoSMass s₁ 0 L ≤ rhoSMass s₂ 0 L := by
    exact rhoSTMass_mono h1 h L (T := ContinuousLinearEquiv.refl _ _)

/-
  rhoSMassOn is summable: because it's just sum of rhoS over a subset of lattice vectors
-/
lemma summable_rhoSMassOn (s : ℝ) (c : 𝓔 n) (L : EuclideanLattice n n) (S : Set (𝓔 n)) :
  Summable (fun v : L.carrier => (S.indicator (rhoS s)) ((v : 𝓔 n) + c)) := by
    -- The series `∑' v : L.carrier, S.indicator (rhoS s) (v + c)` is absolutely convergent because `rhoS` is absolutely integrable.
    have h_abs_conv : Summable (fun v : L.carrier => |(S.indicator (rhoS s)) (v + c)|) := by
      have h_abs_conv : Summable (fun v : L.carrier => rhoS s (v + c)) := by
        -- Apply the lemma that states the summability of the Gaussian function over the lattice.
        simpa [sub_eq_add_neg, add_assoc] using (summable_rhoS L s (-c))
      refine' .of_nonneg_of_le ( fun v => abs_nonneg _ ) ( fun v => _ ) h_abs_conv.norm;
      by_cases hv : ( v : 𝓔 n ) + c ∈ S <;> simp +decide [ hv ];
    exact h_abs_conv.of_abs

/- Handy collorary of the above applied to rhoMassOn -/
corollary summable_rhoMassOn (c : 𝓔 n) (L : EuclideanLattice n n) (S : Set (𝓔 n)) :
  Summable (fun v : L.carrier => (S.indicator rho) ((v : 𝓔 n) + c)) := by
  have h_rhoSMass_summable : Summable (fun v : L.carrier => (S.indicator (rhoS 1)) ((v : 𝓔 n) + c)) := by
    exact summable_rhoSMassOn 1 c L S;
  convert h_rhoSMass_summable using 1
  congr!; ext y; exact (rhoS_1_eq_rho y).symm


/-- Discrete Gaussian weight function for a lattice vector v with center c and parameter s. -/
noncomputable def dGWeight {L: EuclideanLattice n n} (s : ℝ) (c : 𝓔 n) (v : L.carrier) : ℝ :=
  rhoS s ((v : 𝓔 n) - c)

/-- Partition function: The sum of dGWeight over all lattice vectors -/
noncomputable def dGZ (L : EuclideanLattice n n) (s : ℝ) (c : 𝓔 n) : ℝ :=
  ∑' v : L.carrier, dGWeight (L:=L) s c v

/-- lemma `dGZ_eq_rhoSCosetMass`: EuclideanLattice n n) (s : ℝ) (c : 𝓔 n) :. -/
lemma dGZ_eq_rhoSCosetMass (L : EuclideanLattice n n) (s : ℝ) (c : 𝓔 n) :
  dGZ L s c = rhoSMass s (-c) L := by
    dsimp [dGZ, dGWeight, rhoSMass];
    congr;

/-
The partition function dGZ is strictly positive.
-/
theorem dGZ_pos (L : EuclideanLattice n n) (s : ℝ) (h: s > 0) (c : 𝓔 n) : dGZ L s c > 0 := by
  apply_rules [ Summable.tsum_pos ];
  convert summable_rhoS L s c using 1;
  exact fun _ => rhoS_nonneg s _
  exact rhoS_pos s h.ne' _
  exact ⟨ 0, by exact Submodule.zero_mem _ ⟩

/-
The discrete Gaussian weight function converted to ENNReal.
-/
noncomputable def dGWeightENN (L : EuclideanLattice n n) (s : ℝ) (c : 𝓔 n) (v : L.carrier) : ENNReal :=
  ENNReal.ofReal (rhoS s ((v : 𝓔 n) - c))

/-
The ENNReal-valued discrete Gaussian weight function is summable.
-/
lemma dGWeightENN_summable (L : EuclideanLattice n n) (s : ℝ) (c : 𝓔 n) :
  Summable (dGWeightENN L s c) := by
    exact ENNReal.summable

/-
The sum of the ENNReal weights is not infinite.
-/
lemma dGWeightENN_tsum_ne_top (L : EuclideanLattice n n) (s : ℝ) (c : 𝓔 n) :
  tsum (dGWeightENN L s c) ≠ ⊤ := by
    -- Apply the fact that in ENNReal, summability implies that the sum is not top.
    have h_summable : Summable (dGWeightENN L s c) := by
      exact dGWeightENN_summable L s c;
    induction h_summable;
    rename_i w hw;
    apply ne_of_lt; exact (by
    convert ENNReal.ofReal_lt_top;
    rw [ ENNReal.ofReal_tsum_of_nonneg ];
    congr! 1;
    · exact fun _ => rhoS_nonneg _ _;
    · exact summable_rhoS L s c)

/-
The sum of the ENNReal weights is not zero.
-/
lemma dGWeightENN_tsum_ne_zero (L : EuclideanLattice n n) (s : ℝ) (hs : s ≠ 0) (c : 𝓔 n) :
  ∑' v, dGWeightENN L s c v ≠ 0 := by
    -- By definition of `dGWeightENN`, we know that it's a sum of positive terms, so it can't be zero.
    have h_pos : ∀ v : L.carrier, 0 < dGWeightENN L s c v := by
      exact fun v => ENNReal.ofReal_pos.mpr (rhoS_pos s hs _);
    refine' ne_of_gt ( lt_of_lt_of_le _ ( Summable.le_tsum _ 0 fun v _ => le_of_lt ( h_pos v ) ) ) ; aesop;
    exact dGWeightENN_summable L s c

/-
The discrete Gaussian probability mass function on the lattice.
-/
noncomputable def discreteGaussianPMF (L : EuclideanLattice n n) (s : ℝ) (h: s > 0) (c : 𝓔 n) : PMF L.carrier :=
  let f := dGWeightENN L s c
  let Z := ∑' v, f v
  let f_norm := fun v => f v * Z⁻¹
  have h_sum : HasSum f_norm 1 := by
    have h_Z_ne_zero : Z ≠ 0 := dGWeightENN_tsum_ne_zero L s h.ne' c
    have h_Z_ne_top : Z ≠ ⊤ := dGWeightENN_tsum_ne_top L s c
    have h_tsum_eq : ∑' v, f_norm v = 1 := by
      simp only [f_norm]
      rw [ENNReal.tsum_mul_right, ENNReal.mul_inv_cancel h_Z_ne_zero h_Z_ne_top]
    exact ENNReal.summable.hasSum_iff.mpr h_tsum_eq
  ⟨f_norm, h_sum⟩

/-
The real value of the ENNReal weight is the original weight.
-/
lemma dGWeightENN_toReal (L : EuclideanLattice n n) (s : ℝ) (c : 𝓔 n) (v : L.carrier) :
  ENNReal.toReal (dGWeightENN L s c v) = rhoS s ((v : 𝓔 n) - c) := by
    exact ENNReal.toReal_ofReal ( rhoS_nonneg _ _ )

/-
The partition function dGZ is equal to the real value of the sum of the ENNReal weights.
-/
lemma dGZ_eq_tsum_toReal (L : EuclideanLattice n n) (s : ℝ) (c : 𝓔 n) :
  dGZ L s c = (∑' v, dGWeightENN L s c v).toReal := by
    rw [ ENNReal.tsum_toReal_eq ];
    · exact tsum_congr fun _ => dGWeightENN_toReal L s c _ ▸ rfl;
    · exact fun _ => ENNReal.ofReal_ne_top

/-
The real value of the discrete Gaussian PMF at a vector v is equal to the weight of v divided by the partition function.
-/
theorem discreteGaussianPMF_apply_real (L : EuclideanLattice n n) (s : ℝ) (h: s > 0) (c : 𝓔 n) (v : L.carrier) :
  (discreteGaussianPMF L s h c v).toReal = rhoS s ((v : 𝓔 n) - c) / dGZ L s c := by
    erw [ ENNReal.toReal_mul, ENNReal.toReal_inv ];
    rw [ div_eq_mul_inv, ← dGZ_eq_tsum_toReal ];
    · congr;
      exact dGWeightENN_toReal L s c v;


end discrete_gaussian

end LatticeCrypto.Foundations.Gaussian
