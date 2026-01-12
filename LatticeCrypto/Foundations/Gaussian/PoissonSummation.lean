import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Defs.Basic

import LatticeCrypto.Foundations.Gaussian.Defs
import LatticeCrypto.Foundations.Gaussian.Fourier
import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Foundations.Lattice.FundamentalDomain
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec


open Real
open RealInnerProductSpace
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Foundations.Lattice
open scoped FourierTransform

namespace LatticeCrypto.Foundations.Gaussian

/-!
  # Poisson Summation Formula for Gaussian functions over lattices
-/
noncomputable section poisson_summation

open Real Complex MeasureTheory
variable {n : ℕ+}


/-- Poisson Summation Formula on Z^n -/
theorem poisson_summation_Zn (f : 𝔼 n → ℂ)
  (h_int : Integrable f)
  (h_cont : Continuous (periodize f Zn) )
  (h_sum : Summable (fourierCoefficient Zn (periodize f Zn))) :
  Zn.latticeSum (fun v => f v) = Zn.latticeSum (fun w => 𝓕 f w) := by
  have := @fourier_series_inversion_Zn_for_periodization;
  replace := @this n f h_cont h_sum 0; simp_all +decide [ fourierSeries ] ;
  convert this using 1;
  · convert this.symm using 1;
    unfold LatticeCrypto.Foundations.Gaussian.periodize; aesop;
  · have h_fourier_coeff : ∀ w : Zn.dual.carrier, fourierCoefficient Zn (periodize f Zn) w = 𝓕 f w := by
      have := @fourierCoefficient_of_periodization_eq_fourierTransform;
      have := @Zn_det n; aesop;
    convert this using 1;
    rw [ tsum_congr h_fourier_coeff ];
    rw [ Zn_dual_eq_Zn ];
    exact rfl

/-
Composition of an integrable function with the lattice basis linear map is integrable.
-/
lemma integrable_comp_basis (L : GeometricLattice n n) (f : 𝔼 n → ℂ) (h : Integrable f) :
  Integrable (f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) := by
    have := @integrable_comp_continuousLinearEquiv;
    exact this _ _ _ h

/-
Periodization commutes with the basis transformation.
-/
lemma periodize_comp_basis (L : GeometricLattice n n) (f : 𝔼 n → ℂ) (x : 𝔼 n) :
  periodize (f ∘ L.basis.asLinearEquiv) Zn x = periodize f L (L.basis.asLinearEquiv x) := by
    -- By definition of periodization, we can rewrite the left-hand side using the sum over the integers.
    have h_lhs : periodize (f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) Zn x = ∑' z : ZVec n, f (L.basis.asLinearEquiv.toContinuousLinearEquiv (x + zToE z)) := by
      convert tsum_congr fun z => ?_;
      rotate_left;
      use fun z => f ( L.basis.asLinearEquiv.toContinuousLinearEquiv ( x + z ) );
      · rfl;
      · rw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun z : ZVec n => ⟨ zToE z, ?_ ⟩ : ZVec n → Zn.carrier ) ⟨ ?_, ?_ ⟩ ) ];
        all_goals norm_num [ Function.Injective, Function.Surjective ];
        · exact fun a₁ a₂ h => funext fun i => by simpa using congr_fun h i;
        · intro a ha;
          rw [ Submodule.mem_span_range_iff_exists_fun ] at ha;
          obtain ⟨ c, rfl ⟩ := ha;
          use fun i => c i;
          ext i; simp +decide [ Zn ] ;
          simp +decide [ Zn_stdBasis, LatticeBasis.toLattice, LatticeBasis.fromMatrix ];
          simp +decide [ Matrix.col ];
          rw [ Finset.sum_apply, Finset.sum_eq_single i ] <;> aesop;
        · -- Since $z$ is an integer vector, $zToE z$ is a linear combination of the basis vectors with integer coefficients.
          have h_comb : ∃ (c : Fin n → ℤ), zToE z = ∑ i, c i • (Zn.basis.basis i : 𝔼 n) := by
            use fun i => z i;
            ext i; simp +decide [ Zn, Zn_stdBasis ];
            simp +decide [ LatticeBasis.fromMatrix ];
            simp +decide [ LatticeBasis.toLattice, Matrix.col ];
            rw [ Finset.sum_apply, Finset.sum_eq_single i ] <;> aesop;
          exact h_comb.elim fun c hc => hc ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_range_self _ ) );
    -- By definition of periodization, we can rewrite the right-hand side using the sum over the lattice vectors.
    have h_rhs : periodize f L (L.basis.asLinearEquiv x) = ∑' v : L.carrier, f (L.basis.asLinearEquiv x + v) := by
      exact rfl;
    -- Since $L$ is a lattice, the set of lattice vectors $L.carrier$ is in bijection with the set of integer vectors $ZVec n$.
    have h_bij : L.carrier = Set.range (fun z : ZVec n => L.basis.asLinearEquiv.toContinuousLinearEquiv (zToE z)) := by
      ext; simp ;
      constructor <;> intro h <;> simp_all +decide [ Submodule.mem_span_range_iff_exists_fun ];
      · obtain ⟨ c, rfl ⟩ := h;
        simp +decide [ LatticeBasis.asLinearEquiv ];
        simp +decide [ Matrix.toLin_apply, Matrix.mulVec, dotProduct ];
        use fun i => c i; simp +decide [ zToE, stdBasis ] ;
        ext i; simp +decide [ mul_comm ] ;
        rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop;
      · obtain ⟨ y, rfl ⟩ := h;
        use fun i => y i;
        simp +decide [ LatticeBasis.asLinearEquiv ];
        rw [ Matrix.toLin_apply ];
        simp +decide [ Matrix.mulVec, dotProduct ];
        simp +decide [ LatticeBasis.asMatrix, stdBasis ];
        ext i; simp +decide [ mul_comm ] ;
        rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop;
    -- Since $L$ is a lattice, the set of lattice vectors $L.carrier$ is in bijection with the set of integer vectors $ZVec n$. Therefore, we can rewrite the sum over $L.carrier$ as a sum over $ZVec n$.
    have h_sum_eq : ∑' v : L.carrier, f (L.basis.asLinearEquiv x + v) = ∑' z : ZVec n, f (L.basis.asLinearEquiv x + L.basis.asLinearEquiv.toContinuousLinearEquiv (zToE z)) := by
      erw [ ← Equiv.tsum_eq ( Equiv.ofBijective ( fun z : ZVec n => ⟨ L.basis.asLinearEquiv.toContinuousLinearEquiv ( zToE z ), by rw [ Set.ext_iff ] at h_bij; specialize h_bij ( L.basis.asLinearEquiv.toContinuousLinearEquiv ( zToE z ) ) ; aesop ⟩ : ZVec n → L.carrier ) ⟨ fun z => ?_, fun z => ?_ ⟩ ) ];
      all_goals norm_num [ Function.Injective, Function.Surjective ];
      · exact fun w hw => by ext i; simpa using congr_fun hw i;
      · replace h_bij := Set.ext_iff.mp h_bij z; aesop;
    simp_all +decide [ add_comm ]

/-
The representation of a vector transformed by the basis linear equivalence in the lattice basis is equal to the representation of the original vector in the standard basis.
-/
lemma repr_comp_linearEquiv (L : GeometricLattice n n) (x : 𝔼 n) :
  L.basis.asTopBasis.repr (L.basis.asLinearEquiv x) = stdBasis.repr x := by
    unfold LatticeBasis.asTopBasis LatticeBasis.asLinearEquiv;
    simp +decide [ Matrix.toLinearEquiv ];
    simp +decide [ Matrix.toLin_apply, LinearIndependent.repr ];
    erw [ LinearEquiv.symm_apply_eq ];
    ext i; simp +decide [ Matrix.mulVec, Finsupp.linearCombination_apply ] ;
    simp +decide [ Finsupp.sum_fintype, dotProduct ];
    simp +decide [ mul_comm, stdBasis ];
    rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop

/-
The image of the fundamental domain of Zn under the lattice basis map is the fundamental domain of the lattice.
-/
lemma image_fundamentalDomain_eq (L : GeometricLattice n n) :
  L.basis.asLinearEquiv '' Zn.basis.fundamentalDomain = L.basis.fundamentalDomain := by
    ext x;
    constructor <;> intro hx;
    · obtain ⟨ y, hy, rfl ⟩ := hx;
      simp_all +decide [ Zn_basis_eq_stdBasis, LatticeBasis.fundamentalDomain, Set.mem_Ico, forall_and ];
      have := repr_comp_linearEquiv L y; aesop;
    · use L.basis.asLinearEquiv.symm x;
      simp_all +decide ;
      intro i; specialize hx i; simp_all +decide [ Zn_basis_eq_stdBasis ] ;
      convert hx using 1;
      · rw [ ← repr_comp_linearEquiv ];
        rw [ LinearEquiv.apply_symm_apply ];
      · rw [ ← repr_comp_linearEquiv ];
        rw [ LinearEquiv.apply_symm_apply ]

/-
The dual basis linear equivalence maps dual integer vectors to the dual lattice.
-/
lemma dual_basis_map_mem_dual (L : GeometricLattice n n) (k : Zn.dual.carrier) :
  L.basis.dual.asLinearEquiv k.1 ∈ L.dual.carrier := by
    -- Since `k` is in the dual of `Zn`, it is an integer linear combination of the standard basis vectors.
    obtain ⟨a, ha⟩ : ∃ a : Fin n → ℤ, k.val = ∑ i, a i • (Zn.dual.basis.asTopBasis i) := by
      have h_dual_basis : ∀ (k : Zn.dual.carrier), ∃ a : Fin n → ℤ, k.val = ∑ i, a i • (Zn.dual.basis.asTopBasis i) := by
        norm_num +zetaDelta at *;
        intro a ha; rw [ Submodule.mem_span_range_iff_exists_fun ] at ha; tauto;
      exact h_dual_basis k;
    -- Since `L.basis.dual.asLinearEquiv` maps the standard basis vectors to the basis vectors of `L.dual`, the image of `k` is an integer linear combination of the basis vectors of `L.dual`.
    have h_image : L.basis.dual.asLinearEquiv k.val = ∑ i, a i • (L.basis.dual.asTopBasis i) := by
      rw [ ha, map_sum ];
      simp +decide [ Zn_dual_eq_Zn ];
      congr;
      ext i; simp +decide [ Zn ] ;
      simp +decide [ Zn_stdBasis, LatticeBasis.toLattice ];
      simp +decide [ LatticeBasis.fromMatrix, LatticeBasis.asLinearEquiv ];
      simp +decide [ Matrix.toLin_apply, Matrix.col ];
      simp +decide [ Matrix.mulVec, dotProduct, stdBasis ];
      simp +decide [ Matrix.one_apply ];
      rw [ Finset.sum_apply, Finset.sum_eq_single ‹_› ] <;> aesop;
    simp_all +decide [ Submodule.mem_span ];
    exact fun p hp => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( hp <| Set.mem_range_self _ )

/-
The integral of a function composed with the lattice basis map over the standard fundamental domain is equal to the integral of the function over the lattice fundamental domain, scaled by the inverse of the lattice determinant.
-/
lemma integral_comp_basis_eq (L : GeometricLattice n n) (g : 𝔼 n → ℂ) :
  ∫ x in Zn.basis.fundamentalDomain, g (L.basis.asLinearEquiv x) = (L.det⁻¹ : ℂ) * ∫ y in L.basis.fundamentalDomain, g y := by
    -- Using the change of variables formula for integrals, we can rewrite the integral over the fundamental domain.
    have h_change : ∫ x in Zn.basis.fundamentalDomain, g (L.basis.asLinearEquiv x) = (1 / |L.basis.det| : ℝ) * ∫ y in (L.basis.asLinearEquiv '' Zn.basis.fundamentalDomain), g y := by
      rw [ MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul ];
      any_goals intro x hx; exact ContinuousLinearMap.hasFDerivAt ( L.basis.asLinearEquiv.toContinuousLinearMap ) |> HasFDerivAt.hasFDerivWithinAt;
      · simp +decide [ Algebra.smul_def ];
        rw [ MeasureTheory.integral_const_mul ] ; ring_nf;
        simp +decide [ LatticeBasis.det ];
        erw [ LinearMap.det_toLin' ];
        rw [ inv_mul_cancel₀ ( by norm_cast; exact ne_of_gt ( abs_pos.mpr ( show L.basis.asMatrix.det ≠ 0 from by exact L.basis.det_ne_zero ) ) ) ] ; ring;
      · exact LatticeBasis.fundamentalDomain_measurableSet Zn.basis;
      · exact L.basis.asLinearEquiv.injective.injOn;
    rw [ h_change, image_fundamentalDomain_eq ];
    unfold GeometricLattice.det; aesop;

/-
The inner product of the inverse basis transform of y with k is equal to the inner product of y with the dual basis transform of k.
-/
lemma inner_comp_basis_dual (L : GeometricLattice n n) (y : 𝔼 n) (k : 𝔼 n) :
  inner ℝ (L.basis.asLinearEquiv.symm y) k = inner ℝ y (L.basis.dual.asMatrix.mulVec k) := by
    have h_dual_basis : (L.basis.asLinearEquiv.symm y) = (L.basis.asMatrix)⁻¹.mulVec y := by
      unfold LatticeBasis.asMatrix; aesop;
    have h_dual_basis : (L.basis.dual.asMatrix) = (L.basis.asMatrix)⁻¹.transpose := by
      rw [ LatticeBasis.dual_asMatrix ];
      rw [ Matrix.transpose_nonsing_inv ];
    -- By the properties of the transpose and the inner product, we can rewrite the left-hand side as y^T * (L.basis.asMatrix⁻¹.transpose * k).
    have h_transpose : y ⬝ᵥ (L.basis.asMatrix⁻¹.transpose.mulVec k) = (L.basis.asMatrix⁻¹.mulVec y) ⬝ᵥ k := by
      simp +decide [ Matrix.dotProduct_mulVec, Matrix.vecMul_transpose ];
    simp_all +decide [ dotProduct, inner ];
    simp_all +decide [ mul_comm ]

/-
The Fourier coefficient of the composed function on Zn corresponds to the Fourier coefficient of the original function on L, with the dual vector transformed by the dual basis matrix.
-/
lemma fourierCoefficient_comp_basis_eq (L : GeometricLattice n n) (f : 𝔼 n → ℂ) (k : Zn.dual.carrier) :
  fourierCoefficient Zn (periodize (f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) Zn) k =
  fourierCoefficient L (periodize f L) ⟨L.basis.dual.asMatrix.mulVec (k : 𝔼 n), by
    convert dual_basis_map_mem_dual L k⟩ := by
    -- Expand the definition of `fourierCoefficient` on the LHS.
    simp [fourierCoefficient];
    -- Apply the integral_comp_basis_eq lemma with `g(y) = periodize f L y * cexp (-2πi * <B⁻¹ y, k>)`.
    have h_integral : ∫ x in Zn.basis.fundamentalDomain, periodize f L (L.basis.asLinearEquiv x) * cexp (-2 * Real.pi * Complex.I * inner ℝ x k) = (1 / L.det : ℂ) * ∫ y in L.basis.fundamentalDomain, periodize f L y * cexp (-2 * Real.pi * Complex.I * inner ℝ y (L.basis.dual.asMatrix.mulVec k)) := by
      have h_integral : ∫ x in Zn.basis.fundamentalDomain, periodize f L (L.basis.asLinearEquiv x) * cexp (-2 * Real.pi * Complex.I * inner ℝ x k) = (1 / L.det : ℂ) * ∫ y in L.basis.fundamentalDomain, periodize f L y * cexp (-2 * Real.pi * Complex.I * inner ℝ (L.basis.asLinearEquiv.symm y) k) := by
        convert integral_comp_basis_eq L ( fun y => periodize f L y * cexp ( -2 * Real.pi * Complex.I * inner ℝ ( L.basis.asLinearEquiv.symm y ) k ) ) using 1;
        · simp +zetaDelta at *;
        · ring;
      convert h_integral using 4;
      rw [ inner_comp_basis_dual ];
      congr!;
    simp_all +decide [ periodize_comp_basis ];
    erw [ Zn_det ] ; norm_num;
    exact Or.inl rfl

/-
The lattice sum of a function composed with the basis map over Zn is equal to the lattice sum of the function over L.
-/
lemma latticeSum_comp_basis_eq (L : GeometricLattice n n) (f : 𝔼 n → ℂ) :
  Zn.latticeSum (f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) = L.latticeSum f := by
    apply tsum_eq_tsum_of_ne_zero_bij;
    rotate_right;
    use fun x => ⟨ L.basis.asLinearEquiv.symm x, ?_ ⟩;
    all_goals simp +decide [ Function.Injective, Set.subset_def ];
    · -- Since $x$ is in the support of $f$, we have $f(x) \neq 0$. Therefore, $x$ is in the lattice $L$.
      have hx_lattice : (L.basis.asLinearEquiv.symm x : 𝔼 n) ∈ Zn.carrier := by
        -- Since the basis is an equivalence, the inverse of the basis map applied to an element of the lattice should also be in the lattice.
        have h_inv_basis : ∀ y : L.carrier, L.basis.asLinearEquiv.symm y.1 ∈ Zn.carrier := by
          intro y
          obtain ⟨z, hz⟩ : ∃ z : Fin n → ℤ, L.basis.asLinearEquiv.symm y.1 = zToE z := by
            have h_inv_basis : ∀ y : L.carrier, ∃ z : Fin n → ℤ, y.1 = L.basis.asLinearEquiv (zToE z) := by
              intro y
              obtain ⟨z, hz⟩ : ∃ z : Fin n → ℤ, y.1 = ∑ i, z i • (L.basis.asTopBasis i : 𝔼 n) := by
                have h_exists : ∃ z : Fin n → ℤ, y.1 = ∑ i, z i • L.basis.asTopBasis i := by
                  have h_span : y.1 ∈ Submodule.span ℤ (Set.range L.basis.asTopBasis) := by
                    have h_span : L.carrier = Submodule.span ℤ (Set.range L.basis.asTopBasis) := by
                      exact GeometricLattice.full_rank_eq_module_span L;
                    exact h_span ▸ y.2
                  rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_span;
                  obtain ⟨ c, hc ⟩ := h_span; use fun i => c i; simp_all +decide [ Finsupp.sum_fintype ] ;
                exact h_exists;
              use z; simp [hz];
              simp +decide [ LatticeBasis.asLinearEquiv ];
              simp +decide [ Matrix.toLin_apply, LatticeBasis.asMatrix ];
              simp +decide [ Matrix.mulVec, dotProduct, stdBasis ];
              ext i; simp +decide [ mul_comm ] ;
              rw [ Finset.sum_apply, Finset.sum_apply ] ; aesop;
            obtain ⟨ z, hz ⟩ := h_inv_basis y; use z; rw [ hz, LinearEquiv.symm_apply_apply ] ;
          exact hz.symm ▸ zVec_mem_Zn_carrier z;
        exact h_inv_basis x;
      exact hx_lattice;
    · intro a ha hfa;
      refine' ⟨ L.basis.asLinearEquiv a, hfa, _, _ ⟩ <;> simp_all +decide [ Submodule.mem_span_range_iff_exists_fun ];
      rcases ha with ⟨ c, rfl ⟩;
      use fun i => c i;
      simp +decide [ Zn ];
      congr! 2;
      simp +decide [ Zn_stdBasis ];
      simp +decide [ LatticeBasis.toLattice, LatticeBasis.fromMatrix ];
      simp +decide [ Matrix.col, LatticeBasis.asLinearEquiv ];
      simp +decide [ Matrix.toLin_apply, LatticeBasis.asMatrix ];
      simp +decide [ Matrix.mulVec, dotProduct, stdBasis ];
      ext i; simp +decide [ Matrix.one_apply, Finset.sum_ite_eq ] ;
      rw [ Finset.sum_apply, Finset.sum_eq_single i ] <;> aesop

/-
The lattice sum of the Fourier transform of the composed function over Zn is equal to the scaled lattice sum of the Fourier transform of the original function over the dual lattice.
-/
lemma poisson_rhs_eq (L : GeometricLattice n n) (f : 𝔼 n → ℂ) :
  Zn.latticeSum (fun w => 𝓕 (f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) w) =
  (1 / L.det : ℂ) * L.dual.latticeSum (fun w => 𝓕 f w) := by
    have h_fourier_transform_comp_linear_map : ∀ w : 𝔼 n, 𝓕 (f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) w = (1 / L.det : ℂ) * 𝓕 f (L.basis.dual.asMatrix.mulVec w) := by
      intro w;
      convert fourier_transform_comp_linear_map_from_lattice L _ _ using 1;
      aesop;
    -- By `latticeSum_comp_basis_eq` applied to `L.dual`, we have:
    have h_latticeSum_comp_basis_dual : L.dual.latticeSum (fun w => 𝓕 f w) = Zn.latticeSum (fun w => 𝓕 f (L.basis.dual.asMatrix.mulVec w)) := by
      convert latticeSum_comp_basis_eq ( L.dual ) ( fun w => 𝓕 f w ) using 1;
      · exact Eq.symm (latticeSum_comp_basis_eq L.dual fun w => 𝓕 f w);
      · convert latticeSum_comp_basis_eq ( L.dual ) ( fun w => 𝓕 f w ) using 1;
    simp_all +decide [ Zn, GeometricLattice.latticeSum ];
    rw [ tsum_mul_left ]

/-
Poisson Summation Formula for a general lattice L. The sum of f over L equals (1/det L) times the sum of the Fourier transform of f over the dual lattice L*.
-/
theorem poisson_summation (L : GeometricLattice n n) (f : 𝔼 n → ℂ)
  (h_int : Integrable f)
  (h_cont: Continuous (periodize f L))
  (h_sum : Summable (fourierCoefficient L (periodize f L))) :
  L.latticeSum (fun v => f v) = (1 / L.det : ℂ) * L.dual.latticeSum (fun w => 𝓕 f w) := by
    convert poisson_summation_Zn ( f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv ) _ _ _ using 1;
    · exact Eq.symm (latticeSum_comp_basis_eq L f);
    · field_simp;
      -- By definition of the Fourier transform, we have
      have h_fourier_transform : ∀ w : 𝔼 n, 𝓕 (f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) w = (1 / L.det : ℂ) * 𝓕 f (L.basis.dual.asMatrix.mulVec w) := by
        intro w;
        convert fourier_transform_comp_linear_map_from_lattice L ( fun v => f v ) w using 1;
        unfold LatticeBasis.dual; aesop;
      -- By definition of the dual lattice, we know that the sum over the dual lattice is equal to the sum over the original lattice.
      have h_dual_sum : ∀ (g : 𝔼 n → ℂ), L.dual.latticeSum g = Zn.latticeSum (fun w => g (L.basis.dual.asMatrix.mulVec w)) := by
        intro g; exact (by
        have h_dual_sum : ∀ (g : 𝔼 n → ℂ), L.dual.latticeSum g = Zn.latticeSum (fun w => g (L.basis.dual.asLinearEquiv w)) := by
          intro g; exact (by
          convert latticeSum_comp_basis_eq L.dual g using 1;
          · exact Eq.symm (latticeSum_comp_basis_eq L.dual g);
          · convert latticeSum_comp_basis_eq L.dual g using 1);
        convert h_dual_sum g using 1);
      simp_all +decide [ div_eq_inv_mul ];
      erw [ ← tsum_mul_left ];
      exact rfl;
    · exact integrable_comp_basis L f h_int;
    · -- The composition of continuous functions is continuous, so the periodization of f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv is continuous.
      have h_cont_comp : Continuous (periodize f L ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) := by
        exact h_cont.comp <| L.basis.asLinearEquiv.toContinuousLinearEquiv.continuous;
      convert h_cont_comp using 1;
      ext; simp [periodize_comp_basis];
    · have h_fourier_coeff : ∀ k : Zn.dual.carrier, fourierCoefficient Zn (periodize (f ∘ L.basis.asLinearEquiv.toContinuousLinearEquiv) Zn) k = fourierCoefficient L (periodize f L) ⟨L.basis.dual.asMatrix.mulVec (k : 𝔼 n), by
        convert dual_basis_map_mem_dual L k⟩ := by
        exact fun k => fourierCoefficient_comp_basis_eq L f k
      generalize_proofs at *;
      rw [ summable_congr h_fourier_coeff ];
      convert h_sum.comp_injective _;
      intro x y hxy;
      have h_inv : Invertible (L.basis.dual.asMatrix : Matrix (Fin n) (Fin n) ℝ) := by
        convert Matrix.invertibleOfDetInvertible _;
        convert invertibleOfNonzero _;
        exact LatticeBasis.det_ne_zero L.basis.dual;
      exact Subtype.ext <| by simpa using congr_arg ( fun z => h_inv.1.mulVec z ) <| congr_arg Subtype.val hxy;

end poisson_summation

/-!
  ## Corollaries of the Poisson Summation Formula for Gaussian functions over lattices.
-/
noncomputable section poisson_summation_corollaries

open Real Complex MeasureTheory
variable {n : ℕ+}

/-
The Fourier coefficients of the periodized Gaussian function `rhoS` are summable.
-/
lemma summable_fourierCoefficient_of_rhoS_periodize (L : GeometricLattice n n) (s : ℝ) (hs : 0 < s) :
  Summable (fourierCoefficientReal L (rhoS_periodize s L)) := by
    have h_summable : Summable (fun w : L.dual.carrier => rhoS (1 / s) (w : 𝔼 n)) := by
      convert summable_rhoS L.dual ( 1 / s ) ( by positivity ) 0 using 1;
      norm_num +zetaDelta at *;
    have h_fourier_coeff : ∀ w : L.dual.carrier, fourierCoefficientReal L (rhoS_periodize s L) w = (1 / L.det : ℂ) * (s ^ (n : ℕ) : ℂ) * rhoS (1 / s) (w : 𝔼 n) := by
      intro w;
      convert fourierCoefficient_of_periodization_eq_fourierTransform_real L ( fun v => ( rhoS s v : ℝ ) ) _ w using 1;
      · have h_fourier_transform : 𝓕 (fun v : 𝔼 n => (rhoS s v : ℂ)) (w : 𝔼 n) = (s ^ (n : ℕ) : ℂ) * (rhoS (1 / s) (w : 𝔼 n) : ℂ) := by
          convert rhoS_FT_eq s hs ( w : 𝔼 n ) using 1;
        rw [ h_fourier_transform, mul_assoc ];
      · convert ( rhoS.integrable s hs.ne' ) |> MeasureTheory.Integrable.norm using 1 ; norm_num ;
        exact funext fun x => by rw [ abs_of_nonneg ( by exact Real.exp_nonneg _ ) ] ;
    rw [ show fourierCoefficientReal L ( rhoS_periodize s L ) = _ from funext h_fourier_coeff ] ; exact Summable.mul_left _ <| by exact_mod_cast h_summable;

/--
  Poisson Summation Formula for Gaussian functions over lattices.
-/
theorem poisson_summation_rhoS (L : GeometricLattice n n) (s : ℝ) (h_s : 0 < s) :
    rhoSMass s 0 L = (1 / L.det) * (s ^ (n : ℕ)) * rhoSMass (1 / s) 0 L.dual := by
  have h_poisson : L.latticeSum (fun v => (rhoS s v : ℂ)) = (1 / L.det : ℂ) * L.dual.latticeSum (fun w => (rhoS_FT s w : ℂ)) := by
    convert poisson_summation L ( fun v => ( rhoS s v : ℂ ) ) _ _ _ using 1 <;> norm_num [ rhoS.integrable, h_s.ne' ];
    · have h_cont : Continuous (rhoST_periodize s (ContinuousLinearEquiv.refl ℝ (𝔼 n)) L) := by
        apply rhoST_periodize.continuous;
        positivity;
      convert Complex.continuous_ofReal.comp h_cont using 1;
      ext; norm_num [ rhoST_periodize, rhoST, rhoS ] ;
      unfold periodize; norm_num [ Complex.ofReal_tsum ] ;
      unfold GeometricLattice.latticeSum; norm_num [ Complex.ofReal_tsum ] ;
    · have h_summable : Summable (fourierCoefficientReal L (rhoS_periodize s L)) := by
        exact summable_fourierCoefficient_of_rhoS_periodize L s h_s;
      convert h_summable using 1;
      unfold fourierCoefficientReal fourierCoefficient; norm_num [ Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin ] ;
      congr! 3;
      ext; norm_cast;
      erw [ Complex.ofReal_tsum ] ; norm_num [ Complex.ofReal_mul, Complex.ofReal_exp ];
      exact rfl;
  convert congr_arg Complex.re h_poisson using 1;
  · simp [rhoSMass ] ; erw [ Complex.re_tsum ] ; norm_cast;
    convert summable_rhoS L s h_s 0 using 1;
    ext; simp +decide ;
  · -- By definition of `rhoS_FT`, we have `rhoS_FT s w = (s ^ (n : ℕ) : ℂ) * (rhoS (1 / s) w : ℂ)`.
    simp [rhoSMass]
    have h_rhoS_FT : ∀ w : 𝔼 n, rhoS_FT s w = (s ^ (n : ℕ) : ℂ) * (rhoS (1 / s) w : ℂ) := by
      exact fun w => rhoS_FT_eq s h_s w;
    norm_num [ h_rhoS_FT, mul_assoc ];
    norm_cast; norm_num [ tsum_mul_left ] ;
    unfold GeometricLattice.latticeSum; norm_num [ tsum_mul_left ] ;
    norm_cast ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ]

/-
The Fourier transform of the shifted Gaussian `rhoS(· - u)` is `e^{-2πi <u, w>} * rhoS_FT(w)`.
-/
lemma rhoS_shift_FT (s : ℝ) (u : 𝔼 n) (w : 𝔼 n) :
    𝓕 (fun v => (rhoS s (v - u) : ℂ)) w = cexp (-2 * π * I * (inner ℝ u w : ℂ)) * rhoS_FT s w := by
      -- Apply the translation property of the Fourier transform.
      have h_translation : ∀ (f : 𝔼 n → ℂ), 𝓕 (fun v => f (v - u)) w = cexp (-2 * Real.pi * Complex.I * ⟪u, w⟫) * 𝓕 f w := by
        intro f;
        simp +decide [ fourierIntegral, mul_comm ];
        rw [ VectorFourier.fourierIntegral, VectorFourier.fourierIntegral ];
        rw [ ← MeasureTheory.integral_const_mul ] ; rw [ ← MeasureTheory.integral_add_right_eq_self _ u ] ; congr; ext; simp +decide [ ← mul_assoc ] ; ring_nf;
        simp +decide [ sub_eq_add_neg, mul_assoc, mul_comm, mul_left_comm, fourierChar ];
        simp +decide [ mul_comm, mul_left_comm, ← Complex.exp_neg, ← Complex.exp_add, Circle.smul_def ] ; ring_nf;
        norm_num;
      convert h_translation ( fun v => ( rhoS s v : ℂ ) ) using 1

/-
`rhoSCosetMass s L u` is equal to the lattice sum of `rhoS s (v - u)`.
-/
lemma rhoSMass_on_coset_eq_latticeSum_sub (s : ℝ) (L : GeometricLattice n n) (u : 𝔼 n) :
  rhoSMass s u L = L.latticeSum (fun v => rhoS s (v - u)) := by
    have h_reindex : ∑' x : L.carrier, rhoS s (x + u) = ∑' x : L.carrier, rhoS s (-x + u) := by
      -- Since the lattice is closed under negation, the map x ↦ -x is a bijection on the lattice.
      have h_bij : Function.Bijective (fun x : L.carrier => -x : L.carrier → L.carrier) := by
        exact ⟨ neg_injective, neg_surjective ⟩;
      conv_lhs => rw [ ← Equiv.tsum_eq ( Equiv.ofBijective _ h_bij ) ] ;
      norm_num +zetaDelta at *;
    have h_even : ∀ x : 𝔼 n, rhoS s (-x + u) = rhoS s (x - u) := by
      unfold rhoS; intros; ring_nf;
      norm_num [ neg_add_eq_sub, sub_eq_add_neg ] ;
      rw [ ← norm_neg ] ; abel_nf;
    aesop

/-- handy lemmas for the shifted rhoS' Fourier transforms -/
lemma rhoS_sub_FT (s : ℝ) (u : 𝔼 n) (w : 𝔼 n) (hs : 0 < s) :
  𝓕 (fun v => (rhoS s (v - u) : ℂ)) w =
  (s ^ (n : ℕ) : ℂ) * cexp (-2 * π * I * (inner ℝ u w : ℂ)) * (rhoS (1 / s) w : ℂ) := by
  rw [rhoS_shift_FT, rhoS_FT_eq s hs]
  ring

lemma summable_fourier_rhoS_sub (L : GeometricLattice n n) (s : ℝ) (hs : 0 < s) (u : 𝔼 n) :
  Summable (fourierCoefficient L (periodize (fun v => (rhoS s (v - u) : ℂ)) L)) := by
    have := @fourierCoefficient_of_periodization_eq_fourierTransform;
    -- By definition of `rhoS`, we know that `fun v => (rhoS s (v - u) : ℂ)` is integrable.
    have h_integrable : MeasureTheory.Integrable (fun v => (rhoS s (v - u) : ℂ)) MeasureTheory.MeasureSpace.volume := by
      have h_integrable : MeasureTheory.Integrable (fun v => (rhoS s (v - u) : ℝ)) MeasureTheory.MeasureSpace.volume := by
        have := @rhoS.integrable;
        exact MeasureTheory.Integrable.comp_sub_right ( by simpa using Complex.reCLM.integrable_comp ( this s hs.ne' ) ) u;
      exact h_integrable.ofReal;
    have h_fourier_coeff_summable : Summable (fun w : L.dual.carrier => ‖𝓕 (fun v => (rhoS s (v - u) : ℂ)) (w : 𝔼 n)‖) := by
      have h_fourier_coeff_summable : Summable (fun w : L.dual.carrier => ‖(s ^ (n : ℕ) : ℂ) * cexp (-2 * Real.pi * I * (inner ℝ u (w : 𝔼 n) : ℂ)) * (rhoS (1 / s) (w : 𝔼 n))‖) := by
        have h_fourier_coeff_summable : Summable (fun w : L.dual.carrier => ‖(rhoS (1 / s) (w : 𝔼 n))‖) := by
          have h_fourier_coeff_summable : Summable (fun w : L.dual.carrier => (rhoS (1 / s) (w : 𝔼 n))) := by
            have := @summable_rhoS;
            simpa using this L.dual ( 1 / s ) ( one_div_pos.mpr hs ) 0;
          exact h_fourier_coeff_summable.norm;
        simpa [ Complex.norm_exp ] using h_fourier_coeff_summable.mul_left _;
      convert h_fourier_coeff_summable using 2 ; rw [ LatticeCrypto.Foundations.Gaussian.rhoS_sub_FT ] ; aesop;
    rw [ summable_congr fun w => this L _ h_integrable w ];
    exact Summable.mul_left _ <| .of_norm h_fourier_coeff_summable

/-
The shifted Gaussian function is integrable.
-/
lemma rhoS_shifted_integrable (s : ℝ) (hs : s ≠ 0) (u : 𝔼 n) :
  Integrable (fun v => (rhoS s (v - u) : ℂ)) volume := by
    have h_shift : MeasureTheory.Integrable (fun v : 𝔼 n => (rhoS s v : ℂ)) MeasureTheory.MeasureSpace.volume := by
      convert rhoS.integrable s hs using 1;
    exact h_shift.comp_sub_right u


/--
  Poission Summation for rhoS on cosets
-/
theorem poisson_summation_rhoS_coset (L : GeometricLattice n n) (s : ℝ) (h_s : 0 < s) (u : 𝔼 n) :
    (rhoSMass s u L : ℂ) = (1 / L.det) * (s ^ (n : ℕ)) * L.dual.latticeSum (fun v => cexp (-2 * π * I * inner ℝ u (v : 𝔼 n)) * rhoS (1 / s) v) := by
    -- Apply the Poisson summation formula to the shifted Gaussian function.
    have h_poisson : L.latticeSum (fun v => (rhoS s (v - u) : ℝ)) = (1 / L.det : ℝ) * L.dual.latticeSum (fun w => 𝓕 (fun v => (rhoS s (v - u) : ℂ)) w) := by
      have h_poisson : L.latticeSum (fun v => (rhoS s (v - u) : ℝ)) = (1 / L.det : ℂ) * L.dual.latticeSum (fun w => 𝓕 (fun v => (rhoS s (v - u) : ℂ)) w) := by
        have h_integrable : Integrable (fun v => (rhoS s (v - u) : ℂ)) := by
          convert rhoS_shifted_integrable s ( ne_of_gt h_s ) u using 1
        have h_continuous : Continuous (periodize (fun v => (rhoS s (v - u) : ℂ)) L) := by
          have h_continuous : Continuous (fun v => (rhoST_periodize s (ContinuousLinearEquiv.refl ℝ (𝔼 n)) L (v - u) : ℂ)) := by
            exact Complex.continuous_ofReal.comp ( rhoST_periodize.continuous s ( by positivity ) ( ContinuousLinearEquiv.refl ℝ ( 𝔼 n ) ) L |> Continuous.comp <| continuous_sub_right u );
          convert h_continuous using 1;
          ext v; simp +decide [ rhoST_periodize, periodize ] ;
          simp +decide only [sub_add_eq_add_sub];
          convert rfl;
          convert Complex.ofReal_tsum _
        have h_summable : Summable (fourierCoefficient L (periodize (fun v => (rhoS s (v - u) : ℂ)) L)) := by
          exact summable_fourier_rhoS_sub L s h_s u
        convert poisson_summation L _ h_integrable h_continuous h_summable using 1;
        convert Complex.ofReal_tsum _;
      aesop;
    -- Substitute the expression for the Fourier transform of the shifted Gaussian into the Poisson sum formula.
    have h_subst : L.dual.latticeSum (fun w => 𝓕 (fun v => (rhoS s (v - u) : ℂ)) w) = (s ^ (n : ℕ)) * L.dual.latticeSum (fun w => Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ u w : ℂ))) * (rhoS (1 / s) w : ℂ)) := by
      have h_subst : ∀ w : 𝔼 n, 𝓕 (fun v => (rhoS s (v - u) : ℂ)) w = (s ^ (n : ℕ)) * Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ u w : ℂ))) * (rhoS (1 / s) w : ℂ) := by
        apply_rules [ rhoS_sub_FT ];
        funext w; exact (by
        convert rhoS_sub_FT s u w _ using 1 ; norm_num [ h_s ];
        exact h_s);
      simp_all +decide [ mul_assoc ];
      exact tsum_mul_left;
    rw [rhoSMass_on_coset_eq_latticeSum_sub]
    simp_all +decide [ mul_assoc ]


/-- For any lattice L and s ≥ 1, there is rhoS(s, L) ≤ sⁿ * rho(L). -/
theorem rhoSMass_scaling_mono (s : ℝ) (h_s : s ≥ 1) (L : GeometricLattice n n) :
    rhoSMass s 0 L ≤ (s ^ (n : ℕ)) * rhoSMass 1 0 L := by
  -- Proof idea:
  -- rhoS(s, v) = rho(v / s) ≤ rho(v) for s ≥ 1
  -- Therefore, summing over all v ∈ L gives the desired inequality.
  have h_dual_det : L.dual.det = 1 / L.det := by
    exact GeometricLattice.dual_det_eq_inv L;
  have h_poisson : L.latticeSum (fun v => rhoS s v) = (1 / L.det) * s ^ (n : ℕ) * L.dual.latticeSum (fun v => rhoS (1 / s) v) := by
    convert poisson_summation_rhoS L s ( by positivity ) using 1 <;> simp [rhoSMass];
  -- Since $s \geq 1$, we have $s^n \geq 1$ and $1 / s \leq 1$, thus $\rho(1 / s, L^*) \leq \rho(L^*)$.
  have h_rho_bound_1 : L.dual.latticeSum (fun v => rhoS (1 / s) v) ≤ L.dual.latticeSum (fun v => rhoS 1 v) := by
    apply_rules [ Summable.tsum_le_tsum ];
    · unfold LatticeCrypto.Foundations.Gaussian.rhoS;
      norm_num; ring_nf ;
      exact fun x hx => mul_le_mul_of_nonneg_left ( by rw [ norm_smul, Real.norm_of_nonneg ( by positivity ) ] ; exact pow_le_pow_left₀ ( by positivity ) ( le_mul_of_one_le_left ( norm_nonneg _ ) h_s ) _ ) Real.pi_pos.le;
    · have := @LatticeCrypto.Foundations.Gaussian.summable_rhoS;
      simpa using this L.dual ( 1 / s ) ( one_div_pos.mpr ( zero_lt_one.trans_le h_s ) ) 0;
    · have := @LatticeCrypto.Foundations.Gaussian.summable_rhoS n L.dual;
      simpa using this 1 zero_lt_one 0
  have h_rho_bound_2 : L.latticeSum (fun v => rhoS 1 v) = L.det⁻¹ * L.dual.latticeSum (fun v => rhoS 1 v) := by
    have h_poisson := poisson_summation_rhoS L 1 zero_lt_one
    simp at h_poisson; simp [rhoSMass] at h_poisson;
    aesop;
  simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_comm ]; simp [rhoSMass]
  rw [ h_poisson ];
  gcongr;
  rw [ h_rho_bound_2 ];
  gcongr; exact (inv_pos.mpr L.det_pos).le

/-- For any lattice coset L + u, rhoS(s, L + u) ≤ rhoS(s, L).
-/
theorem rhoSMass_shift_mono (L : GeometricLattice n n) (s : ℝ) (hs: 0 < s) (u : 𝔼 n) :
    rhoSMass s u L ≤ rhoSMass s 0 L := by
  -- Proof idea:
  -- Since rhoS is non-negative, shifting by u does not increase the sum.
  have h_rhoSCosetMass_nonneg : 0 ≤ rhoSMass s u L := by
    exact tsum_nonneg fun _ => Real.exp_nonneg _
  have h_rhoSCosetMass_eq_complex : ‖(rhoSMass s u L : ℂ)‖ = rhoSMass s u L := by
    exact_mod_cast abs_of_nonneg h_rhoSCosetMass_nonneg
  rw [ ← h_rhoSCosetMass_eq_complex,  poisson_summation_rhoS_coset L s hs u];
  unfold GeometricLattice.latticeSum;
  have h_le : ∀ (v : L.dual.carrier) (a : ℝ), ‖cexp (-2 * π * I * inner ℝ u (v : 𝔼 n)) * a‖ = ‖a‖ := by
    -- The norm of the product of two complex numbers is the product of their norms.
    simp [Complex.norm_exp]
  have h_abs_tsum_le_tsum_abs : ‖ ∑' (v : L.dual.carrier), (fun v => cexp (-2 * π * I * inner ℝ u (v : 𝔼 n)) * (rhoS (1 / s) v : ℂ)) v‖ ≤ ∑' (v : L.dual.carrier), ‖(rhoS (1 / s) (v : 𝔼 n) : ℂ)‖ := by
    convert norm_tsum_le_tsum_norm _ using 2 ; aesop
    generalize_proofs at *;
    have h_summable : Summable (fun v : L.dual.carrier => rhoS (1 / s) (v : 𝔼 n)) := by
      have := summable_rhoS L.dual ( 1 / s ) ( by positivity ) 0
      generalize_proofs at *;
      aesop;
    convert h_summable.norm using 1 ; aesop

  convert mul_le_mul_of_nonneg_left h_abs_tsum_le_tsum_abs ( show 0 ≤ ‖1 / ( L.det : ℂ ) * ( s : ℂ ) ^ ( n : ℕ )‖ by positivity ) using 1;
  · rw [ norm_mul ];
  · rw [ poisson_summation_rhoS ];
    · norm_num [ abs_of_nonneg, hs.le, L.det_pos ];
      rw [ abs_of_nonneg ( show 0 ≤ L.det from le_of_lt ( L.det_pos ) ) ];
      congr! 2; simp [rhoSMass, GeometricLattice.latticeSum];
      exact tsum_congr fun v => by rw [ abs_of_nonneg ( rhoS_pos _ _ |> le_of_lt ) ] ;
    · positivity

noncomputable section AristotleLemmas

lemma re_tsum_tail_ge_neg_rhoMassOn (L : GeometricLattice n n) (u : 𝔼 n) :
  (∑' v : L.dual.carrier, (if v = 0 then 0 else cexp (-2 * π * I * inner ℝ u (v : 𝔼 n)) * (rho v : ℂ))).re ≥ -rhoMassOn 0 L.dual {0}ᶜ := by
    unfold LatticeCrypto.Foundations.Gaussian.rhoMassOn;
    simp +zetaDelta at *;
    refine' neg_le_of_abs_le _;
    refine' le_trans ( Complex.abs_re_le_norm _ ) _;
    convert norm_tsum_le_tsum_norm _;
    ·
      unfold LatticeCrypto.Foundations.Gaussian.rho; norm_num [ Complex.norm_exp ] ;
      rw [ tsum_congr ] ; aesop;
      intro b; split_ifs <;> simp_all +decide [ Complex.norm_exp ] ;
      norm_cast;
    · -- The series $\sum_{v \in \Lambda^*} \rho(v)$ is summable by the properties of the Gaussian function and the lattice.
      have h_summable : Summable (fun v : L.dual.carrier => (LatticeCrypto.Foundations.Gaussian.rho v : ℝ)) := by
        convert summable_rhoS L.dual 1 zero_lt_one 0 using 1;
        aesop;
      refine' .of_nonneg_of_le ( fun v => norm_nonneg _ ) ( fun v => _ ) h_summable.norm;
      split_ifs <;> norm_num [ Complex.norm_exp ]

lemma summable_rho_exponential (L : GeometricLattice n n) (u : 𝔼 n) :
  Summable (fun v : L.dual.carrier => cexp (-2 * π * I * inner ℝ u (v : 𝔼 n)) * (rho v : ℂ)) := by
    -- Since the Gaussian function is non-negative and its sum is finite, it is summable.
    have h_summable : Summable (fun v : L.dual.carrier => (LatticeCrypto.Foundations.Gaussian.rho v : ℝ)) := by
      -- Apply the lemma `summable_rhoS` with `s = 1` and `c = 0`.
      have := summable_rhoS L.dual 1 (by norm_num) 0;
      aesop;
    exact .of_norm <| by simpa [ Complex.norm_exp ] using h_summable.norm;

open Real Complex MeasureTheory LatticeCrypto.Foundations.Lattice LatticeCrypto.Utils.Vec LatticeCrypto.Foundations.Gaussian

lemma rhoMass_eq_real_part_poisson (L : GeometricLattice n n) (u : 𝔼 n) :
  rhoMass u L = (1 / L.det) * (1 + (∑' v : L.dual.carrier, (if v = 0 then 0 else cexp (-2 * π * I * inner ℝ u (v : 𝔼 n)) * (rho v : ℂ))).re) := by
    have := @LatticeCrypto.Foundations.Gaussian.poisson_summation_rhoS_coset n L 1;
    specialize this zero_lt_one u;
    rw [rhoSMass_one_eq_rhoMass] at this;
    have h_lattice_sum : L.dual.latticeSum (fun v : 𝔼 n => cexp (-2 * Real.pi * I * (inner ℝ u v : ℂ)) * (rho v : ℂ)) = (∑' v : L.dual.carrier, cexp (-2 * Real.pi * I * (inner ℝ u (v : 𝔼 n) : ℂ)) * (rho (v : 𝔼 n) : ℂ)) := by
      exact rfl;
    convert congr_arg Complex.re this using 1;
    rw [ Summable.tsum_eq_add_tsum_ite ] at h_lattice_sum;
    case b => exact ⟨ 0, by simp +decide ⟩;
    · simp_all +decide ;
      unfold LatticeCrypto.Foundations.Gaussian.rho; norm_num;
      exact Or.inl rfl;
    · exact summable_rho_exponential L u

end AristotleLemmas

/-- Corollary : If ρ(L.dual \setminus {0}) ≤ ε for some ε>0, then ρ(x + L) ≥ (1−ε) / (1+ε) * ρ(L) for all x ∈ 𝔼 n -/
theorem rhoMass_almost_uniform_on_dual_if_small_tail (L : GeometricLattice n n) (ε : ℝ) (hε : 0 < ε) (h_tail : rhoMassOn 0 L.dual {0}ᶜ ≤ ε) (u : 𝔼 n) :
  rhoMass u L ≥ (1 - ε) / (1 + ε) * rhoMass 0 L := by

  -- By `rhoMass_eq_real_part_poisson`, `rhoMass u L = (1 / L.det) * (1 + tail.re)` and `rhoMass 0 L = (1 / L.det) * (1 + tail₀.re)`.
  have h_rho_mass_u_L : rhoMass u L = (1 / L.det) * (1 + (∑' v : L.dual.carrier, (if v = 0 then 0 else cexp (-2 * Real.pi * I * inner ℝ u (v : 𝔼 n)) * (rho v : ℂ))).re) := by
    convert rhoMass_eq_real_part_poisson L u using 1
  have h_rho_mass_0_L : rhoMass 0 L = (1 / L.det) * (1 + (∑' v : L.dual.carrier, (if v = 0 then 0 else (rho v : ℂ))).re) := by
    convert rhoMass_eq_real_part_poisson L 0 using 1;
    norm_num [ inner_zero_left ];
  -- By `re_tsum_tail_ge_neg_rhoMassOn`, `tail.re ≥ -rhoMassOn 0 L.dual {0}ᶜ`.
  have h_tail_re_ge_neg_rhoMassOn : (∑' v : L.dual.carrier, (if v = 0 then 0 else cexp (-2 * Real.pi * I * inner ℝ u (v : 𝔼 n)) * (rho v : ℂ))).re ≥ -rhoMassOn 0 L.dual {0}ᶜ := by
    exact re_tsum_tail_ge_neg_rhoMassOn L u;
  -- By `rhoMass_eq_real_part_poisson`, `rhoMass 0 L = (1 + tail₀.re) / det(L)`.
  have h_rho_mass_0_L' : rhoMass 0 L = (1 + rhoMassOn 0 L.dual {0}ᶜ) / L.det := by
    convert h_rho_mass_0_L using 1;
    rw [ div_mul_eq_mul_div, rhoMassOn ];
    rw [ show ( ∑' v : L.dual.carrier, if v = 0 then 0 else ( rho v : ℂ ) ) = ( ∑' v : L.dual.carrier, if v = 0 then 0 else ( rho v : ℝ ) ) from ?_ ];
    ·
      simp +decide ;
      simp ( config := { decide := Bool.true } ) [ Set.indicator ];
      unfold GeometricLattice.latticeSum; aesop;
    · rw [ Complex.ofReal_tsum ];
      exact tsum_congr fun x => by split_ifs <;> simp +decide [ * ] ;
  rw [ ge_iff_le, mul_comm ];
  rw [ h_rho_mass_u_L, h_rho_mass_0_L', div_mul_div_comm ];
  rw [ div_mul_eq_mul_div, div_le_div_iff₀ ] <;> try nlinarith [ show 0 < L.det from L.det_pos ];
  nlinarith [ show 0 < L.det by exact L.det_pos, mul_le_mul_of_nonneg_left h_tail ( show 0 ≤ L.det by exact L.det_pos.le ), mul_le_mul_of_nonneg_left h_tail_re_ge_neg_rhoMassOn ( show 0 ≤ L.det by exact L.det_pos.le ) ]

end poisson_summation_corollaries


end LatticeCrypto.Foundations.Gaussian
