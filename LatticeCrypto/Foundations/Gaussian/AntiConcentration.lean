import Mathlib.Probability.Notation
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.InnerProductSpace.PiL2

import LatticeCrypto.Foundations.Gaussian.Defs
import LatticeCrypto.Foundations.Gaussian.Fourier
import LatticeCrypto.Foundations.Gaussian.PoissonSummation
import LatticeCrypto.Foundations.Gaussian.Sampling
import LatticeCrypto.Foundations.Gaussian.Smoothing
import LatticeCrypto.Foundations.Gaussian.TailBound
import LatticeCrypto.Utils.Probability

namespace LatticeCrypto.Foundations.Gaussian

open scoped RealInnerProductSpace ProbabilityTheory FourierTransform
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Foundations.Lattice

noncomputable section

variable {n : ℕ+}

/-!
  ### Affine hyperplanes and WLOG rotation to the `e₁` hyperplane for anti-concentration
-/
noncomputable section hyperplane_rot

/-- The first standard basis vector in `𝓔 n`. -/
def e1Vec : 𝓔 n := EuclideanSpace.single (0 : Fin n) (1 : ℝ)

/-- Affine hyperplane `{x | ⟪x, u⟫ = c}`. -/
def affineHyperplane (u : 𝓔 n) (c : ℝ) : Set (𝓔 n) :=
  {x | inner ℝ x u = c}

abbrev 𝓗1c (c : ℝ) : Set (𝓔 n) := affineHyperplane e1Vec c

/--
Existence of an orthogonal transformation that rotates a unit vector `u` to `e₁`.
-/
theorem exists_rotation_to_e1
    (u : 𝓔 n) (hu : ‖u‖ = 1) :
    ∃ R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n, R u = e1Vec := by
  classical
  let v : Fin n → 𝓔 n := fun i => if i = 0 then u else 0
  have hv : Orthonormal ℝ ((({(0 : Fin n)} : Set (Fin n)).restrict v)) := by
    classical
    refine (orthonormal_iff_ite.2 ?_)
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    have hi0 : (i : Fin n) = 0 := Set.mem_singleton_iff.mp i.2
    have huInner : inner ℝ u u = 1 := by
      calc
        inner ℝ u u = ‖u‖ ^ 2 := by simp [real_inner_self_eq_norm_sq]
        _ = 1 := by nlinarith [hu]
    simp [Set.restrict, v, hi0, huInner]
  have hcard : Module.finrank ℝ (𝓔 n) = Fintype.card (Fin n) := by
    simp [LatticeCrypto.Utils.Vec.𝓔, finrank_euclideanSpace]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (ι := Fin n) (E := 𝓔 n) (card_ι := hcard)
      (s := ({(0 : Fin n)} : Set (Fin n))) (v := v) hv
  have hb0 : b 0 = u := by
    simpa [v] using hb 0 (by simp : (0 : Fin n) ∈ ({(0 : Fin n)} : Set (Fin n)))
  let R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n :=
    b.equiv (EuclideanSpace.basisFun (Fin n) ℝ) (Equiv.refl (Fin n))
  refine ⟨R, ?_⟩
  calc
    R u = R (b 0) := by simp [hb0]
    _ = EuclideanSpace.basisFun (Fin n) ℝ 0 := by
      have hEq :=
        (OrthonormalBasis.equiv_apply_basis
          (b := b)
          (b' := EuclideanSpace.basisFun (Fin n) ℝ)
          (e := Equiv.refl (Fin n))
          (i := (0 : Fin n)))
      unfold R
      exact hEq.trans (by simp)
    _ = e1Vec := by
      simp [e1Vec, EuclideanSpace.basisFun_apply]

/-- Membership of `affineHyperplane e1Vec c` is equivalent to the first component being `c` -/
lemma mem_affineHyperplane_e1_iff (x : 𝓔 n) (c : ℝ) :
    x ∈ affineHyperplane e1Vec c ↔ x 0 = c := by
  have hinner : inner ℝ x e1Vec = x 0 := by
    calc
      inner ℝ x e1Vec = inner ℝ x (EuclideanSpace.basisFun (Fin n) ℝ 0) := by
        simp [e1Vec, EuclideanSpace.basisFun_apply]
      _ = x 0 := EuclideanSpace.inner_basisFun_real (x := x) (i := (0 : Fin n))
  simp [affineHyperplane, hinner]

/--
WLOG reduction for hyperplanes: after rotating so that `u = e₁`, membership in
`{x | ⟪x,u⟫ = c}` becomes membership in `{x | x₀ = c}`.
-/
theorem hyperplane_mem_rotate_to_e1_wlog
    (u : 𝓔 n) (hu : ‖u‖ = 1) (c : ℝ) :
    ∃ R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n,
      R u = e1Vec ∧
      ∀ x : 𝓔 n,
        x ∈ affineHyperplane u c ↔ R x ∈ affineHyperplane e1Vec c := by
  obtain ⟨R, hR⟩ := exists_rotation_to_e1 (n := n) u hu
  refine ⟨R, hR, ?_⟩
  intro x
  have hRu : R.symm e1Vec = u := by
    exact (by
      have h := congrArg R.symm hR
      simpa using h.symm)
  have hinner :
      inner ℝ (R x) e1Vec = inner ℝ x u := by
    calc
      inner ℝ (R x) e1Vec = inner ℝ x (R.symm e1Vec) := by
        simpa using (LinearIsometryEquiv.inner_map_eq_flip (f := R) x e1Vec)
      _ = inner ℝ x u := by simp [hRu]
  constructor <;> intro hx
  · simpa [affineHyperplane, hinner] using hx
  · simpa [affineHyperplane, hinner] using hx

/-- Hyperplane membership is preserved under a linear isometry after mapping both the point and normal. -/
lemma mem_affineHyperplane_map_linearIsometry_iff
    (R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n) (u x : 𝓔 n) (c : ℝ) :
    x ∈ affineHyperplane u c ↔ R x ∈ affineHyperplane (R u) c := by
  simp [affineHyperplane, LinearIsometryEquiv.inner_map_map]

/-- Hyperplane membership can be pulled back through a linear isometry. -/
lemma mem_affineHyperplane_map_linearIsometry_symm_iff
    (R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n) (u x : 𝓔 n) (c : ℝ) :
    x ∈ affineHyperplane (R u) c ↔ R.symm x ∈ affineHyperplane u c := by
  simpa using
    (mem_affineHyperplane_map_linearIsometry_iff
      (R := R) (u := u) (x := R.symm x) (c := c)).symm

/-- `PMF.toMeasure` on a predicate-set can be rewritten as a lattice tsum with an indicator. -/
lemma discreteGaussian_toMeasure_apply_pred
    (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (center : 𝓔 n)
    (S : Set L.carrier) :
    ((discreteGaussianPMF L s hs center).toMeasure S)
      = ∑' x : L.carrier, S.indicator (discreteGaussianPMF L s hs center) x := by
  simpa using
    (PMF.toMeasure_apply_eq_tsum (p := discreteGaussianPMF L s hs center) S)

/-- Hyperplane membership in ambient space and first-coordinate equality coincide on lattice points. -/
lemma mem_affineHyperplane_e1_iff_subtype
    (L : EuclideanLattice n n) (x : L.carrier) (c : ℝ) :
    ((x : 𝓔 n) ∈ affineHyperplane e1Vec c) ↔ ((x : 𝓔 n) 0 = c) := by
  exact mem_affineHyperplane_e1_iff (x := (x : 𝓔 n)) (c := c)

/-- Event-sets for `x₀ = c` and `x ∈ affineHyperplane e₁ c` are definitionally equivalent on `L.carrier`. -/
lemma subtype_event_eq_firstCoord_eq
    (L : EuclideanLattice n n) (c : ℝ) :
    {x : L.carrier | (x : 𝓔 n) ∈ affineHyperplane e1Vec c}
      = {x : L.carrier | ((x : 𝓔 n) 0 = c)} := by
  ext x
  simp [mem_affineHyperplane_e1_iff_subtype]

/-- Event-set equality induced by the WLOG rotation-to-`e1` equivalence on ambient vectors. -/
lemma subtype_event_eq_rotated_e1
    (L : EuclideanLattice n n) (u : 𝓔 n) (c : ℝ)
    {R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n}
    (hR : ∀ x : 𝓔 n, x ∈ affineHyperplane u c ↔ R x ∈ affineHyperplane e1Vec c) :
    {x : L.carrier | inner ℝ (x : 𝓔 n) u = c}
      =
    {x : L.carrier | (R (x : 𝓔 n)) ∈ affineHyperplane e1Vec c} := by
  ext x
  simpa [affineHyperplane] using (hR (x : 𝓔 n))

--lemma

end hyperplane_rot

/-!
  ### The anti-concentration bound for the special hyperplane `𝓗1c = affineHyperplane e1Vec c`
-/
noncomputable section anti_concentration_H1C

/-- In the smoothing regime, shifted Gaussian mass is bounded below by the `(1-ε)` uniform term. -/
private lemma rhoSMass_lower_bound_of_smoothing
    (L : EuclideanLattice n n) (s ε : ℝ)
    (hs : 0 < s) (hε : 0 < ε) (hη : L.η ε < s) (x : 𝓔 n) :
    L.dual.det * s ^ (n : ℕ) * (1 - ε) ≤ rhoSMass s x L := by
  have hsmooth : s ∈ SmoothingSet L ε :=
    smoothingParameter_thresh (L := L) (ε := ε) hε s hη
  have hMassBound : rhoSMass (1 / s) (0 : 𝓔 n) L.dual ≤ 1 + ε := hsmooth.2
  have hTailLe : rhoSMassOn (1 / s) (0 : 𝓔 n) L.dual {0}ᶜ ≤ ε := by
    have hdecomp := rhoSMass_eq_one_add_rhoSMassOn_nonzero (L := L.dual) (s := 1 / s)
    linarith
  have hPoint := Sampling.modGaussian_vs_uniform_pointwise_le (L := L) (s := s) hs x
  have hScaled :
      |(1 / s ^ (n : ℕ)) * rhoSMass s x L - L.dual.det|
        ≤ L.dual.det * ε := by
    have hdet_nonneg : 0 ≤ L.dual.det := L.dual.det_pos.le
    have hPoint' :
        |(1 / s ^ (n : ℕ)) * rhoSMass s x L - L.dual.det|
          ≤ L.dual.det * rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
      simpa [Sampling.modGaussianDensity, Sampling.uniformDensity] using hPoint
    exact hPoint'.trans (by gcongr)
  have hLowerScaled : L.dual.det * (1 - ε) ≤ (1 / s ^ (n : ℕ)) * rhoSMass s x L := by
    have hAbsLower := (abs_le.mp hScaled).1
    linarith
  have hsPowPos : 0 < s ^ (n : ℕ) := by positivity
  calc
    L.dual.det * s ^ (n : ℕ) * (1 - ε)
      = s ^ (n : ℕ) * (L.dual.det * (1 - ε)) := by ring
    _ ≤ s ^ (n : ℕ) * ((1 / s ^ (n : ℕ)) * rhoSMass s x L) := by
      gcongr
    _ = rhoSMass s x L := by
      field_simp [hs.ne']

/-- The diagonal stretch that scales the first coordinate by `√2` and fixes the others. -/
private def e1StretchCLM : 𝓔 n →L[ℝ] 𝓔 n :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin' (Matrix.diagonal (fun i : Fin n => if i = 0 then Real.sqrt 2 else 1)))

private lemma e1StretchCLM_det_ne_zero :
    (e1StretchCLM (n := n)).det ≠ 0 := by
  rw [show (e1StretchCLM (n := n)).det =
      LinearMap.det
        (Matrix.toLin' (Matrix.diagonal (fun i : Fin n => if i = 0 then Real.sqrt 2 else 1))) by
      rfl]
  rw [LinearMap.det_toLin']
  simp [Matrix.det_diagonal]

/-- The continuous linear equivalence scaling the first coordinate by `√2`. -/
private def e1Stretch : 𝓔 n ≃L[ℝ] 𝓔 n :=
  (e1StretchCLM (n := n)).toContinuousLinearEquivOfDetNeZero
    (e1StretchCLM_det_ne_zero (n := n))

private lemma e1Stretch_apply (x : 𝓔 n) (i : Fin n) :
    e1Stretch (n := n) x i = (if i = 0 then Real.sqrt 2 else 1) * x i := by
  rw [e1Stretch, ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply]
  rw [show (e1StretchCLM (n := n)) x i =
      (Matrix.toLin'
        (Matrix.diagonal (fun j : Fin n => if j = 0 then Real.sqrt 2 else 1)) x) i by
      rfl]
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]

private lemma e1Stretch_symm_apply (x : 𝓔 n) (i : Fin n) :
    e1Stretch (n := n).symm x i = (if i = 0 then 1 / Real.sqrt 2 else 1) * x i := by
  have h :
      e1Stretch (n := n)
          (fun j => (if j = 0 then 1 / Real.sqrt 2 else 1) * x j) = x := by
    ext j
    rw [e1Stretch_apply]
    by_cases hj : j = 0
    · subst hj
      simp
    · simp [hj]
  simpa using
    (congrArg (fun y => y i) ((e1Stretch (n := n)).apply_eq_iff_eq_symm_apply.mp h)).symm

/-- The transpose of the matrix representing the inverse of `e1Stretch` multiplied by a vector equals the inverse of `e1Stretch` applied to the vector -/
private lemma e1Stretch_symm_toMatrix_transpose_mulVec (x : 𝓔 n) :
    ((e1Stretch (n := n).symm.toLinearMap.toMatrix stdBasis stdBasis).transpose.mulVec x)
      = e1Stretch (n := n).symm x := by
  ext i
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · simp [LinearMap.toMatrix_apply, e1Stretch_symm_apply, stdBasis]
  · intro j _ hji
    simp [LinearMap.toMatrix_apply, e1Stretch_symm_apply, stdBasis, hji]
  · intro hi
    simp at hi

/-- The determinant of `e1Stretch` is `√2` -/
private lemma e1Stretch_det :
    LinearMap.det (e1Stretch (n := n)).toLinearMap = Real.sqrt 2 := by
  change
    LinearMap.det
        ((((e1Stretch (n := n)) : 𝓔 n ≃L[ℝ] 𝓔 n) : 𝓔 n →L[ℝ] 𝓔 n) : 𝓔 n →ₗ[ℝ] 𝓔 n)
      = Real.sqrt 2
  rw [e1Stretch, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
  rw [show
      LinearMap.det
          (((e1StretchCLM (n := n) : 𝓔 n →L[ℝ] 𝓔 n) : 𝓔 n →ₗ[ℝ] 𝓔 n))
        =
      LinearMap.det
        (Matrix.toLin' (Matrix.diagonal (fun i : Fin n => if i = 0 then Real.sqrt 2 else 1))) by
      rfl]
  rw [LinearMap.det_toLin']
  simp [Matrix.det_diagonal]

/-- The norm of the inverse of `e1Stretch` is at least `1/√2` -/
private lemma e1Stretch_symm_norm_sq_ge_half (w : 𝓔 n) :
    ‖e1Stretch (n := n).symm w‖ ^ 2 ≥ ‖w‖ ^ 2 / 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n))]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n))]
  simp_rw [e1Stretch_symm_apply, Real.norm_eq_abs, sq_abs]
  have hsum :
      ∑ i ∈ Finset.univ.erase (0 : Fin n), ((if i = 0 then 1 / Real.sqrt 2 else 1) * w i) ^ 2
        = ∑ i ∈ Finset.univ.erase (0 : Fin n), w i ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi0 : i ≠ 0 := by simpa using hi
    simp [hi0]
  rw [hsum]
  simp
  have h0 : ((Real.sqrt 2)⁻¹ * w 0) ^ 2 = w 0 ^ 2 / 2 := by
    have hsqrt : Real.sqrt 2 ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      norm_num
    calc
      ((Real.sqrt 2)⁻¹ * w 0) ^ 2 = (Real.sqrt 2)⁻¹ ^ 2 * (w 0) ^ 2 := by ring
      _ = ((Real.sqrt 2) ^ 2)⁻¹ * (w 0) ^ 2 := by ring
      _ = w 0 ^ 2 / 2 := by rw [hsqrt]; ring
  rw [h0]
  ring_nf
  have hdecomp :
      ∑ i : Fin n, w i ^ 2 = w 0 ^ 2 + ∑ i ∈ Finset.univ.erase (0 : Fin n), w i ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n))]
    simp
  rw [hdecomp]
  nlinarith [sq_nonneg (w 0), show 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin n), w i ^ 2 by positivity]

/-- Relating `rhoS (1/s) e1Stretch` with `rhoS (Real.sqrt 2 / s)` -/
private lemma rhoS_e1Stretch_symm_le
    (s : ℝ) (hs : 0 < s) (w : 𝓔 n) :
    rhoS (1 / s) (e1Stretch (n := n).symm w) ≤ rhoS (Real.sqrt 2 / s) w := by
  rw [rhoS_of_ne_zero (by positivity : (1 / s) ≠ 0)]
  rw [rhoS_of_ne_zero (by positivity : Real.sqrt 2 / s ≠ 0)]
  rw [norm_smul, norm_smul]
  have hs_over : ‖(Real.sqrt 2 / s)⁻¹‖ = s / Real.sqrt 2 := by
    rw [Real.norm_eq_abs, abs_of_pos]
    · field_simp [hs.ne', Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)]
    · positivity
  have hs_inv : ‖(1 / s)⁻¹‖ = s := by
    rw [Real.norm_eq_abs, one_div, inv_inv, abs_of_pos hs]
  rw [hs_inv, hs_over]
  apply Real.exp_le_exp.mpr
  have hnorm := e1Stretch_symm_norm_sq_ge_half (n := n) w
  have hsq :
      (s * ‖e1Stretch (n := n).symm w‖) ^ 2
        ≥
      (s / Real.sqrt 2 * ‖w‖) ^ 2 := by
    have hs2 : 0 ≤ s ^ 2 := by positivity
    have hsqrt : Real.sqrt 2 ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      norm_num
    have hsqrt_ne : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)
    have hs_left : (s * ‖e1Stretch (n := n).symm w‖) ^ 2 = s ^ 2 * ‖e1Stretch (n := n).symm w‖ ^ 2 := by
      ring
    have hs_right : (s / Real.sqrt 2 * ‖w‖) ^ 2 = s ^ 2 * (‖w‖ ^ 2 / 2) := by
      field_simp [hsqrt_ne]
      rw [hsqrt]
      ring
    rw [hs_left, hs_right]
    nlinarith [hnorm]
  have harg :
      -Real.pi * (s * ‖e1Stretch (n := n).symm w‖) ^ 2
        ≤
      -Real.pi * (s / Real.sqrt 2 * ‖w‖) ^ 2 := by
    have hpi_mul :
        Real.pi * (s / Real.sqrt 2 * ‖w‖) ^ 2
          ≤
        Real.pi * (s * ‖e1Stretch (n := n).symm w‖) ^ 2 := by
      gcongr
    linarith
  exact harg

/-- The `rhoST` using `e1Stretch` as the linear map is essentially the same as `rhoS` multiplied by a exponential factor -/
private lemma rhoS_mul_exp_eq_shifted_rhoST
    (s : ℝ) (hs : 0 < s) (center x : 𝓔 n) (c : ℝ) :
    let δ : ℝ := c - center 0
    let u : 𝓔 n := center + (δ / 2) • e1Vec
    rhoS s (x - center) * Real.exp (-Real.pi * ((x 0 - c) / s) ^ 2)
      =
    Real.exp (-Real.pi * (δ ^ 2 / (2 * s ^ 2))) * rhoST s (e1Stretch (n := n)) (x - u) := by
  dsimp
  rw [rhoS_of_ne_zero hs.ne', rhoST_of_ne_zero hs.ne']
  let u : 𝓔 n := center + ((c - center 0) / 2) • e1Vec
  have hnorm :
      ‖x - center‖ ^ 2 + (x 0 - c) ^ 2
        =
      ‖e1Stretch (n := n) (x - u)‖ ^ 2 + (c - center 0) ^ 2 / 2 := by
    change
      ‖x - center‖ ^ 2 + (x 0 - c) ^ 2
        =
      ‖e1Stretch (n := n) (x - u)‖ ^ 2 + (c - center 0) ^ 2 / 2
    have hstretch :
        ‖e1Stretch (n := n) (x - (center + ((c - center 0) / 2) • e1Vec))‖ ^ 2
          =
        2 * (x 0 - (center 0 + c) / 2) ^ 2
          + ∑ i ∈ Finset.univ.erase (0 : Fin n), (x i - center i) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n))]
      simp_rw [e1Stretch_apply, Real.norm_eq_abs, sq_abs]
      have h0 : u 0 = (center 0 + c) / 2 := by
        simp [u, e1Vec]
        ring_nf
      have hsum :
          ∑ i ∈ Finset.univ.erase (0 : Fin n),
            ((if i = 0 then Real.sqrt 2 else 1) * (x i - u i)) ^ 2
            =
          ∑ i ∈ Finset.univ.erase (0 : Fin n), (x i - center i) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi0 : i ≠ 0 := by simpa using hi
        simp [u, hi0, e1Vec]
      have hsum' :
          ∑ i ∈ Finset.univ.erase (0 : Fin n),
            ((if i = 0 then Real.sqrt 2 else 1) * (x - u) i) ^ 2
            =
          ∑ i ∈ Finset.univ.erase (0 : Fin n), (x i - center i) ^ 2 := by
        simpa using hsum
      rw [hsum']
      simp [e1Vec]
      have hsqrt : Real.sqrt 2 ^ 2 = 2 := by
        rw [Real.sq_sqrt]
        norm_num
      ring_nf
      rw [hsqrt]
      ring
    rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n))]
    rw [hstretch]
    simp
    ring_nf
  have hs2 : 0 < s ^ 2 := by positivity
  have hscaled :
      ‖s⁻¹ • (x - center)‖ ^ 2 + ((x 0 - c) / s) ^ 2
        =
      ‖s⁻¹ • e1Stretch (n := n) (x - u)‖ ^ 2 + (c - center 0) ^ 2 / (2 * s ^ 2) := by
    have hs_nonzero : s ≠ 0 := hs.ne'
    have hsmul1 : ‖s⁻¹ • (x - center)‖ ^ 2 = ‖x - center‖ ^ 2 / s ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
      field_simp [hs_nonzero]
    have hsmul2 : ‖s⁻¹ • e1Stretch (n := n) (x - u)‖ ^ 2 = ‖e1Stretch (n := n) (x - u)‖ ^ 2 / s ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
      field_simp [hs_nonzero]
    have hdiv : ((x 0 - c) / s) ^ 2 = (x 0 - c) ^ 2 / s ^ 2 := by
      field_simp [hs_nonzero]
    rw [hsmul1, hsmul2, hdiv]
    have := congrArg (fun t : ℝ => t / s ^ 2) hnorm
    ring_nf at this ⊢
    exact this
  rw [← Real.exp_add, ← Real.exp_add]
  have harg :
      -Real.pi * ‖s⁻¹ • (x - center)‖ ^ 2 + -Real.pi * ((x 0 - c) / s) ^ 2
        =
      -Real.pi * ((c - center 0) ^ 2 / (2 * s ^ 2))
        + -Real.pi * ‖s⁻¹ • e1Stretch (n := n) (x - u)‖ ^ 2 := by
    have harg' := congrArg (fun t : ℝ => -Real.pi * t) hscaled
    ring_nf at harg' ⊢
    exact harg'
  rw [harg]

/-- The Fourier transform of the `rhoST` function composed with a shift -/
private lemma rhoST_shift_FT
    (s : ℝ) (u w : 𝓔 n) :
    𝓕 (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) w
      =
    Complex.exp (-2 * Real.pi * Complex.I * (inner ℝ u w : ℂ)) * rhoST_FT s (e1Stretch (n := n)) w := by
  simpa [rhoST_FT] using
    (fourier_transform_comp_sub_right
      (n := n) (f := fun v => (rhoST s (e1Stretch (n := n)) v : ℂ)) (u := u) (w := w))

/-- The Fourier transform of the stretched Gaussian is bounded by a round Gaussian. -/
private lemma norm_rhoST_FT_e1Stretch_le
    (s : ℝ) (hs : 0 < s) (w : 𝓔 n) :
    ‖rhoST_FT s (e1Stretch (n := n)) w‖
      ≤ (s ^ (n : ℕ) / Real.sqrt 2) * rhoS (Real.sqrt 2 / s) w := by
  have hnorm :
      ‖rhoST_FT s (e1Stretch (n := n)) w‖
        =
      (s ^ (n : ℕ) / Real.sqrt 2) * rhoS (1 / s) (e1Stretch (n := n).symm w) := by
    rw [rhoST_FT_eq_scaled_rhoS, rhoS_FT_eq s hs, e1Stretch_symm_toMatrix_transpose_mulVec]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs]
    have hrho : |rhoS (1 / s) (e1Stretch (n := n).symm w)| = rhoS (1 / s) (e1Stretch (n := n).symm w) := by
      exact abs_of_nonneg (rhoS_nonneg _ _)
    have hdet :
        |LinearMap.det (e1Stretch (n := n)).toLinearMap|⁻¹ = 1 / Real.sqrt 2 := by
      rw [e1Stretch_det, abs_of_nonneg (Real.sqrt_nonneg 2)]
      field_simp [Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)]
    have hsNorm : ‖((s : ℂ) ^ (n : ℕ))‖ = s ^ (n : ℕ) := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hrhoNorm : ‖rhoS (1 / s) (e1Stretch (n := n).symm w)‖ = rhoS (1 / s) (e1Stretch (n := n).symm w) := by
      rw [Real.norm_eq_abs, hrho]
    have hdetNonneg : 0 ≤ |LinearMap.det (e1Stretch (n := n)).toLinearMap|⁻¹ := by
      positivity
    rw [abs_of_nonneg hdetNonneg, hsNorm, hrhoNorm, hdet]
    ring
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left
    (rhoS_e1Stretch_symm_le (n := n) (s := s) hs w)
    (by positivity)

/-- Shifting the stretched Gaussian only introduces a unit-modulus Fourier phase. -/
private lemma norm_rhoST_shift_FT_e1Stretch_le
    (s : ℝ) (hs : 0 < s) (u w : 𝓔 n) :
    ‖𝓕 (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) w‖
      ≤ (s ^ (n : ℕ) / Real.sqrt 2) * rhoS (Real.sqrt 2 / s) w := by
  rw [rhoST_shift_FT]
  have hphase :
      ‖Complex.exp (-2 * Real.pi * Complex.I * (inner ℝ u w : ℂ))‖ = 1 := by
    simp [Complex.norm_exp]
  rw [norm_mul, hphase, one_mul]
  exact norm_rhoST_FT_e1Stretch_le (n := n) (s := s) hs w

/-- Fourier coefficients of the shifted stretched Gaussian are summable. -/
private lemma summable_fourier_shifted_rhoST
    (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (u : 𝓔 n) :
    Summable
      (fourierCoefficient L
        (periodize (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) L)) := by
  have h_integrable :
      MeasureTheory.Integrable
        (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) := by
    have h_base :
        MeasureTheory.Integrable
          (fun v : 𝓔 n => (rhoST s (e1Stretch (n := n)) v : ℂ)) := by
      exact rhoST.integrable s hs.ne' (e1Stretch (n := n))
    exact h_base.comp_sub_right u
  have h_norm_summable :
      Summable
        (fun w : L.dual.carrier =>
          ‖𝓕 (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) (w : 𝓔 n)‖) := by
    have h_bound :
        Summable
          (fun w : L.dual.carrier =>
            (s ^ (n : ℕ) / Real.sqrt 2) * rhoS (Real.sqrt 2 / s) (w : 𝓔 n)) := by
      simpa using
        (summable_rhoS L.dual (Real.sqrt 2 / s) 0).mul_left (s ^ (n : ℕ) / Real.sqrt 2)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_bound
    intro w
    exact norm_rhoST_shift_FT_e1Stretch_le (n := n) (s := s) hs u (w : 𝓔 n)
  rw [summable_congr fun w =>
    fourierCoefficient_of_periodization_eq_fourierTransform L
      (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) h_integrable w]
  exact Summable.mul_left _ <| Summable.of_norm h_norm_summable

/-- Poisson summation bounds the shifted stretched Gaussian sum by dual Gaussian mass. -/
private lemma rhoST_shifted_latticeSum_e1Stretch_le
    (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (u : 𝓔 n) :
    ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u)
      ≤
    (1 / L.det) * (s ^ (n : ℕ) / Real.sqrt 2) * rhoSMass (Real.sqrt 2 / s) 0 L.dual := by
  have h_integrable :
      MeasureTheory.Integrable
        (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) := by
    have h_base :
        MeasureTheory.Integrable
          (fun v : 𝓔 n => (rhoST s (e1Stretch (n := n)) v : ℂ)) := by
      exact rhoST.integrable s hs.ne' (e1Stretch (n := n))
    exact h_base.comp_sub_right u
  have h_continuous :
      Continuous
        (periodize (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) L) := by
    have h_cont :
        Continuous
          (fun v => (rhoST_periodize s (e1Stretch (n := n)) L (v - u) : ℂ)) := by
      exact Complex.continuous_ofReal.comp
        ((rhoST_periodize.continuous s (by positivity) (e1Stretch (n := n)) L).comp
          (continuous_sub_right u))
    convert h_cont using 1
    ext v
    simp +decide [rhoST_periodize, periodize]
    simp +decide only [sub_add_eq_add_sub]
    convert rfl
    convert Complex.ofReal_tsum _
  have h_sum :=
    summable_fourier_shifted_rhoST (n := n) (L := L) (s := s) hs u
  have h_poisson :
      ((∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u)) : ℂ)
        =
      (1 / L.det : ℂ) *
        ∑' w : L.dual.carrier,
          𝓕 (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) (w : 𝓔 n) := by
    convert poisson_summation L
      (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ))
      h_integrable h_continuous h_sum using 1
  have h_norm_summable :
      Summable
        (fun w : L.dual.carrier =>
          ‖𝓕 (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) (w : 𝓔 n)‖) := by
    have h_bound :
        Summable
          (fun w : L.dual.carrier =>
            (s ^ (n : ℕ) / Real.sqrt 2) * rhoS (Real.sqrt 2 / s) (w : 𝓔 n)) := by
      simpa using
        (summable_rhoS L.dual (Real.sqrt 2 / s) 0).mul_left (s ^ (n : ℕ) / Real.sqrt 2)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_bound
    intro w
    exact norm_rhoST_shift_FT_e1Stretch_le (n := n) (s := s) hs u (w : 𝓔 n)
  let G : L.dual.carrier → ℝ := fun w =>
    ‖𝓕 (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) (w : 𝓔 n)‖
  let H : L.dual.carrier → ℝ := fun w =>
    (s ^ (n : ℕ) / Real.sqrt 2) * rhoS (Real.sqrt 2 / s) (w : 𝓔 n)
  have hGsum : Summable G := by
    simpa [G] using h_norm_summable
  have hHsum : Summable H := by
    simpa [H] using
      (summable_rhoS L.dual (Real.sqrt 2 / s) 0).mul_left (s ^ (n : ℕ) / Real.sqrt 2)
  have hGH : ∀ w : L.dual.carrier, G w ≤ H w := by
    intro w
    simpa [G, H] using
      (norm_rhoST_shift_FT_e1Stretch_le (n := n) (s := s) hs u (w : 𝓔 n))
  have h_fourier_tsum_le :
      ∑' w : L.dual.carrier, G w
        ≤ (s ^ (n : ℕ) / Real.sqrt 2) * rhoSMass (Real.sqrt 2 / s) 0 L.dual := by
    calc
      ∑' w : L.dual.carrier, G w ≤ ∑' w : L.dual.carrier, H w := by
        exact hGsum.tsum_le_tsum hGH hHsum
      _ = (s ^ (n : ℕ) / Real.sqrt 2) * rhoSMass (Real.sqrt 2 / s) 0 L.dual := by
        calc
          ∑' w : L.dual.carrier, H w
            = (s ^ (n : ℕ) / Real.sqrt 2) *
                ∑' w : L.dual.carrier, rhoS (Real.sqrt 2 / s) (w : 𝓔 n) := by
                  dsimp [H]
                  rw [tsum_mul_left]
          _ = (s ^ (n : ℕ) / Real.sqrt 2) * rhoSMass (Real.sqrt 2 / s) 0 L.dual := by
                simp only [rhoSMass, EuclideanLattice.latticeSum, add_zero]
  have hsum_nonneg :
      0 ≤ ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) := by
    exact tsum_nonneg fun _ => rhoST_nonneg _ _ _
  have hsumR_summable :
      Summable (fun x : L.carrier => rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u)) := by
    simpa using summable_rhoST L s (e1Stretch (n := n)) u
  have hsum_cast :
      ‖∑' x : L.carrier, (rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) : ℂ)‖
        =
      ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) := by
    rw [← Complex.ofReal_tsum]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
  calc
    ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u)
      =
      ‖∑' x : L.carrier, (rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) : ℂ)‖ := by
        exact hsum_cast.symm
    _ =
      ‖(1 / L.det : ℂ) *
        ∑' w : L.dual.carrier,
          𝓕 (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) (w : 𝓔 n)‖ := by
            rw [h_poisson]
    _ =
      ‖(1 / L.det : ℂ)‖ *
          ‖∑' w : L.dual.carrier,
              𝓕 (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) (w : 𝓔 n)‖ := by
                exact norm_mul _ _
    _ ≤ ‖(1 / L.det : ℂ)‖ *
          ∑' w : L.dual.carrier,
            ‖𝓕 (fun v => (rhoST s (e1Stretch (n := n)) (v - u) : ℂ)) (w : 𝓔 n)‖ := by
              gcongr
              exact norm_tsum_le_tsum_norm h_norm_summable
    _ ≤ ‖(1 / L.det : ℂ)‖ *
          ((s ^ (n : ℕ) / Real.sqrt 2) * rhoSMass (Real.sqrt 2 / s) 0 L.dual) := by
            have hdetcoeff_nonneg : 0 ≤ ‖(1 / L.det : ℂ)‖ := norm_nonneg _
            simpa [G] using mul_le_mul_of_nonneg_left h_fourier_tsum_le hdetcoeff_nonneg
    _ = (1 / L.det) * (s ^ (n : ℕ) / Real.sqrt 2) * rhoSMass (Real.sqrt 2 / s) 0 L.dual := by
          have hdetnorm : ‖(1 / L.det : ℂ)‖ = 1 / L.det := by
            rw [one_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos L.det_pos]
            rw [one_div]
          rw [hdetnorm]
          ring

/-- The point event is bounded by the exponential-weighted discrete-Gaussian expectation. -/
private lemma discreteGaussian_firstCoord_eq_le_exp_tsum
    (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) (center : 𝓔 n) (c : ℝ) :
    (discreteGaussianPMF L s hs center).toMeasure {x : L.carrier | ((x : 𝓔 n) 0 = c)}
      ≤
    ENNReal.ofReal
      (∑' x : L.carrier,
        Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) *
          (discreteGaussianPMF L s hs center x).toReal) := by
  let p : PMF L.carrier := discreteGaussianPMF L s hs center
  let S : Set L.carrier := {x : L.carrier | ((x : 𝓔 n) 0 = c)}
  have hterm_summable :
      Summable
        (fun x : L.carrier =>
          Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) * (p x).toReal) := by
    have h_le :
        ∀ x : L.carrier,
          Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) * (p x).toReal ≤ (p x).toReal := by
      intro x
      have hexp_le : Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have hsq : 0 ≤ (((x : 𝓔 n) 0 - c) / s) ^ 2 := sq_nonneg _
        nlinarith [Real.pi_pos, hsq]
      nlinarith [show 0 ≤ (p x).toReal from ENNReal.toReal_nonneg]
    have h_p_summable :
        Summable (fun x : L.carrier => (p x).toReal) := by
      have h_eq :
          (fun x : L.carrier => (p x).toReal)
            =
          (fun x : L.carrier => rhoS s ((x : 𝓔 n) - center) / dGZ L s center) := by
        funext x
        exact discreteGaussianPMF_apply_real L s hs center x
      rw [h_eq]
      simpa [div_eq_mul_inv] using
        (summable_rhoS L s center).mul_right ((dGZ L s center)⁻¹)
    refine Summable.of_nonneg_of_le ?_ h_le h_p_summable
    intro x
    exact mul_nonneg (by positivity) (show 0 ≤ (p x).toReal from ENNReal.toReal_nonneg)
  calc
    (discreteGaussianPMF L s hs center).toMeasure {x : L.carrier | ((x : 𝓔 n) 0 = c)}
      =
    ∑' x : L.carrier, S.indicator p x := by
      simpa [p, S] using
        (discreteGaussian_toMeasure_apply_pred
          (L := L) (s := s) (hs := hs) (center := center) (S := S))
    _ ≤
      ∑' x : L.carrier,
        ENNReal.ofReal
          (Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) * (p x).toReal) := by
            apply ENNReal.tsum_le_tsum
            intro x
            by_cases hx : ((x : 𝓔 n) 0 = c)
            · rw [Set.indicator_of_mem (s := S) hx]
              have hexp :
                  Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) = 1 := by
                simp [hx]
              have hp : p x = ENNReal.ofReal ((p x).toReal) := by
                symm
                exact ENNReal.ofReal_toReal (p.apply_ne_top x)
              rw [hexp, one_mul]
              exact hp.le
            · rw [Set.indicator_of_notMem (s := S) hx]
              exact bot_le
    _ =
      ENNReal.ofReal
        (∑' x : L.carrier,
          Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) * (p x).toReal) := by
            symm
            exact ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hterm_summable

/-- The probability that a discrete Gaussian vector is in ``affineHyperplane e1Vec c` is bounded when the Gaussian's
scale factor is large enough relative to the smoothing parameter.
-/
theorem discrete_gaussian_hyperplane_anti_concentration_e1_bound
  (L : EuclideanLattice n n) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) (hε1 : ε < 1)
  (hS : Real.sqrt 2 * L.η ε < s) (center : 𝓔 n) (c : ℝ) :
  letI : MeasureTheory.MeasureSpace L.carrier :=
    ⟨(discreteGaussianPMF L s hs center).toMeasure⟩
  ℙ {x : L.carrier | ((x : 𝓔 n) 0 = c)} ≤
    ENNReal.ofReal ((1 + ε) / ((1 - ε) * Real.sqrt 2)) :=
  by
    change
      (discreteGaussianPMF L s hs center).toMeasure
        {x : L.carrier | ((x : 𝓔 n) 0 = c)}
        ≤ ENNReal.ofReal ((1 + ε) / ((1 - ε) * Real.sqrt 2))
    let p : PMF L.carrier := discreteGaussianPMF L s hs center
    let δ : ℝ := c - center 0
    let u : 𝓔 n := center + (δ / 2) • e1Vec
    have hdGZ_pos : 0 < dGZ L s center := dGZ_pos L s hs center
    have hdGZ_ne : dGZ L s center ≠ 0 := hdGZ_pos.ne'
    have hterm_eq :
        (∑' x : L.carrier,
          Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) * (p x).toReal)
          =
        (Real.exp (-Real.pi * (δ ^ 2 / (2 * s ^ 2))) / dGZ L s center) *
          ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) := by
      calc
        ∑' x : L.carrier,
            Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) * (p x).toReal
          =
        ∑' x : L.carrier,
            (Real.exp (-Real.pi * (δ ^ 2 / (2 * s ^ 2))) / dGZ L s center) *
              rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) := by
                refine tsum_congr ?_
                intro x
                have hpReal :
                    (p x).toReal = rhoS s ((x : 𝓔 n) - center) / dGZ L s center := by
                  simpa [p] using discreteGaussianPMF_apply_real L s hs center x
                rw [hpReal]
                calc
                  Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) *
                      (rhoS s ((x : 𝓔 n) - center) / dGZ L s center)
                    =
                  (rhoS s ((x : 𝓔 n) - center) *
                      Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2))) / dGZ L s center := by
                        field_simp [hdGZ_ne]
                  _ =
                  (Real.exp (-Real.pi * (δ ^ 2 / (2 * s ^ 2))) *
                      rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u)) / dGZ L s center := by
                        rw [rhoS_mul_exp_eq_shifted_rhoST (n := n) (s := s) hs center (x : 𝓔 n) c]
                  _ =
                  (Real.exp (-Real.pi * (δ ^ 2 / (2 * s ^ 2))) / dGZ L s center) *
                      rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) := by
                        field_simp [hdGZ_ne]
        _ =
          (Real.exp (-Real.pi * (δ ^ 2 / (2 * s ^ 2))) / dGZ L s center) *
            ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) := by
              rw [tsum_mul_left]
    have hnum_le :
        ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u)
          ≤
        (1 / L.det) * (s ^ (n : ℕ) / Real.sqrt 2) * rhoSMass (Real.sqrt 2 / s) 0 L.dual := by
      exact rhoST_shifted_latticeSum_e1Stretch_le (n := n) (L := L) (s := s) hs u
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
    have hη_div : L.η ε < s / Real.sqrt 2 := by
      have htmp : L.η ε * Real.sqrt 2 < s := by
        simpa [mul_comm] using hS
      exact (lt_div_iff₀ hsqrt2_pos).2 htmp
    have hMassUpper : rhoSMass (Real.sqrt 2 / s) 0 L.dual ≤ 1 + ε := by
      have hsmooth :
          s / Real.sqrt 2 ∈ SmoothingSet L ε :=
        smoothingParameter_thresh (L := L) (ε := ε) hε (s / Real.sqrt 2) hη_div
      simpa [div_eq_mul_inv, hs.ne', Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2),
        mul_comm, mul_left_comm, mul_assoc] using hsmooth.2
    have hs_div_lt_s : s / Real.sqrt 2 < s := by
      have hsqrt2_gt_one : 1 < Real.sqrt 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      exact (_root_.div_lt_iff₀ hsqrt2_pos).2 (by nlinarith)
    have hη_lt_s : L.η ε < s := lt_trans hη_div hs_div_lt_s
    have hden_lower :
        L.dual.det * s ^ (n : ℕ) * (1 - ε) ≤ dGZ L s center := by
      simpa [dGZ_eq_rhoSCosetMass] using
        (rhoSMass_lower_bound_of_smoothing
          (n := n) (L := L) (s := s) (ε := ε) hs hε hη_lt_s (-center))
    have hden_lower' :
        (1 / L.det) * s ^ (n : ℕ) * (1 - ε) ≤ dGZ L s center := by
      simpa [EuclideanLattice.dual_det_eq_inv, mul_assoc, mul_left_comm, mul_comm] using hden_lower
    have hcoeff_le_one :
        Real.exp (-Real.pi * (δ ^ 2 / (2 * s ^ 2))) / dGZ L s center
          ≤ 1 / dGZ L s center := by
      have hexp_le_one : Real.exp (-Real.pi * (δ ^ 2 / (2 * s ^ 2))) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        have hsq : 0 ≤ δ ^ 2 / (2 * s ^ 2) := by positivity
        nlinarith [Real.pi_pos, hsq]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hexp_le_one (by positivity)
    have hsum_nonneg :
        0 ≤ ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) := by
      exact tsum_nonneg fun _ => rhoST_nonneg _ _ _
    have hmain_real :
        (∑' x : L.carrier,
          Real.exp (-Real.pi * ((((x : 𝓔 n) 0 - c) / s) ^ 2)) * (p x).toReal)
          ≤
        (1 + ε) / ((1 - ε) * Real.sqrt 2) := by
      rw [hterm_eq]
      have hstep1 :
          (Real.exp (-Real.pi * (δ ^ 2 / (2 * s ^ 2))) / dGZ L s center) *
              ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u)
            ≤
          (1 / dGZ L s center) *
              ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) := by
        exact mul_le_mul_of_nonneg_right hcoeff_le_one hsum_nonneg
      have hstep2 :
          (1 / dGZ L s center) *
              ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u)
            ≤
          (1 / dGZ L s center) *
              ((1 / L.det) * (s ^ (n : ℕ) / Real.sqrt 2) * rhoSMass (Real.sqrt 2 / s) 0 L.dual) := by
        exact mul_le_mul_of_nonneg_left hnum_le (by positivity)
      have h1mε_pos : 0 < 1 - ε := by linarith
      have hCdiv :
          (((1 / L.det) * s ^ (n : ℕ)) / dGZ L s center) ≤ 1 / (1 - ε) := by
        rw [_root_.div_le_iff₀ hdGZ_pos]
        have htmp :
            (1 / L.det) * s ^ (n : ℕ) ≤ dGZ L s center / (1 - ε) :=
          (le_div_iff₀ h1mε_pos).2 hden_lower'
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htmp
      have hAdiv :
          rhoSMass (Real.sqrt 2 / s) 0 L.dual / Real.sqrt 2 ≤ (1 + ε) / Real.sqrt 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hMassUpper (by positivity)
      have hexpr :
          (1 / dGZ L s center) *
              ((1 / L.det) * (s ^ (n : ℕ) / Real.sqrt 2) * rhoSMass (Real.sqrt 2 / s) 0 L.dual)
            =
          (((1 / L.det) * s ^ (n : ℕ)) / dGZ L s center) *
            (rhoSMass (Real.sqrt 2 / s) 0 L.dual / Real.sqrt 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      calc
        (Real.exp (-Real.pi * (δ ^ 2 / (2 * s ^ 2))) / dGZ L s center) *
            ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u)
          ≤
        (1 / dGZ L s center) *
            ∑' x : L.carrier, rhoST s (e1Stretch (n := n)) ((x : 𝓔 n) - u) := hstep1
        _ ≤
          (1 / dGZ L s center) *
            ((1 / L.det) * (s ^ (n : ℕ) / Real.sqrt 2) * rhoSMass (Real.sqrt 2 / s) 0 L.dual) := hstep2
        _ =
          (((1 / L.det) * s ^ (n : ℕ)) / dGZ L s center) *
            (rhoSMass (Real.sqrt 2 / s) 0 L.dual / Real.sqrt 2) := hexpr
        _ ≤ (1 / (1 - ε)) * ((1 + ε) / Real.sqrt 2) := by
          have hMassNonneg : 0 ≤ rhoSMass (Real.sqrt 2 / s) 0 L.dual := by
            simp [rhoSMass]
            exact tsum_nonneg fun _ => rhoS_nonneg _ _
          have hA_nonneg : 0 ≤ rhoSMass (Real.sqrt 2 / s) 0 L.dual / Real.sqrt 2 := by
            exact div_nonneg hMassNonneg hsqrt2_pos.le
          have hInv_nonneg : 0 ≤ 1 / (1 - ε) := by
            positivity
          exact mul_le_mul hCdiv hAdiv hA_nonneg hInv_nonneg
        _ = (1 + ε) / ((1 - ε) * Real.sqrt 2) := by
          field_simp [sub_ne_zero.mpr hε1.ne', Real.sqrt_ne_zero'.2 (by norm_num : (0 : ℝ) < 2)]
    exact
      (discreteGaussian_firstCoord_eq_le_exp_tsum
        (n := n) (L := L) (s := s) (hs := hs) (center := center) (c := c)).trans
        (ENNReal.ofReal_le_ofReal hmain_real)

/-- Equivalent `e₁`-bound stated using ambient hyperplane membership. -/
theorem discrete_gaussian_hyperplane_anti_concentration_e1_bound_affine
  (L : EuclideanLattice n n) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) (hε1 : ε < 1)
  (hS : Real.sqrt 2 * L.η ε < s) (center : 𝓔 n) (c : ℝ) :
  letI : MeasureTheory.MeasureSpace L.carrier :=
    ⟨(discreteGaussianPMF L s hs center).toMeasure⟩
  ℙ {x : L.carrier | ((x : 𝓔 n) ∈ affineHyperplane e1Vec c)} ≤
    ENNReal.ofReal ((1 + ε) / ((1 - ε) * Real.sqrt 2)) := by
  simpa [subtype_event_eq_firstCoord_eq] using
    (discrete_gaussian_hyperplane_anti_concentration_e1_bound
      (L := L) (s := s) (ε := ε) (hs := hs) (hε := hε) (hε1 := hε1)
      (hS := hS) (center := center) (c := c))

end anti_concentration_H1C

/-!
  ### WLOG rotation to `e₁` for the anti-concentration bound
-/
noncomputable section wlog_rot_e1

/-- Rotating both lattice and center preserves `dGWeightENN` along the carrier equivalence. -/
private lemma dGWeightENN_mapLinearIsometryCarrierEquiv_eq
    (L : EuclideanLattice n n) (R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n) (s : ℝ) (center : 𝓔 n)
    (x : L.carrier) :
    dGWeightENN L s center x =
      dGWeightENN (L.mapLinearIsometry R) s (R center)
        (EuclideanLattice.mapLinearIsometryCarrierEquiv (L := L) R x) := by
  let e : L.carrier ≃ (L.mapLinearIsometry R).carrier :=
    EuclideanLattice.mapLinearIsometryCarrierEquiv (L := L) R
  have hcoe : (((e x : (L.mapLinearIsometry R).carrier) : 𝓔 n)) = R (x : 𝓔 n) := by
    rfl
  have hrho :
      rhoS s ((x : 𝓔 n) - center) = rhoS s (R ((x : 𝓔 n) - center)) := by
    simpa using
      (rhoS_map_linearIsometry (n := n) (R := R) (s := s) (x := ((x : 𝓔 n) - center))).symm
  simpa [dGWeightENN, e, hcoe, map_sub] using congrArg ENNReal.ofReal hrho

/-- The discrete-Gaussian normalizing `tsum` is invariant under rotating lattice and center. -/
private lemma dGWeightENN_tsum_mapLinearIsometry_eq
    (L : EuclideanLattice n n) (R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n) (s : ℝ) (center : 𝓔 n) :
    (∑' x : L.carrier, dGWeightENN L s center x)
      =
    ∑' x' : (L.mapLinearIsometry R).carrier,
      dGWeightENN (L.mapLinearIsometry R) s (R center) x' := by
  let e : L.carrier ≃ (L.mapLinearIsometry R).carrier :=
    L.mapLinearIsometryCarrierEquiv R
  calc
    (∑' x : L.carrier, dGWeightENN L s center x)
      =
      ∑' x : L.carrier,
        dGWeightENN (L.mapLinearIsometry R) s (R center) (e x) := by
        refine tsum_congr ?_
        intro x
        simpa [e] using
          (dGWeightENN_mapLinearIsometryCarrierEquiv_eq
            (L := L) (R := R) (s := s) (center := center) x)
    _ =
      ∑' x' : (L.mapLinearIsometry R).carrier,
        dGWeightENN (L.mapLinearIsometry R) s (R center) x' := by
      simpa [e] using
        (e.tsum_eq
          (fun x' : (L.mapLinearIsometry R).carrier =>
            dGWeightENN (L.mapLinearIsometry R) s (R center) x'))

/-- Pointwise transport of `discreteGaussianPMF` through the lattice rotation carrier equivalence. -/
private lemma discreteGaussianPMF_mapLinearIsometryCarrierEquiv_eq
    (L : EuclideanLattice n n) (R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n)
    (s : ℝ) (hs : 0 < s) (center : 𝓔 n) (x : L.carrier) :
    discreteGaussianPMF L s hs center x =
      discreteGaussianPMF (L.mapLinearIsometry R) s hs (R center)
        (EuclideanLattice.mapLinearIsometryCarrierEquiv (L := L) R x) := by
  let e : L.carrier ≃ (L.mapLinearIsometry R).carrier :=
    EuclideanLattice.mapLinearIsometryCarrierEquiv (L := L) R
  have hWeight :=
    dGWeightENN_mapLinearIsometryCarrierEquiv_eq
      (L := L) (R := R) (s := s) (center := center) x
  have hZ :=
    dGWeightENN_tsum_mapLinearIsometry_eq
      (L := L) (R := R) (s := s) (center := center)
  have hMul :
      dGWeightENN L s center x *
          (∑' x' : (L.mapLinearIsometry R).carrier,
            dGWeightENN (L.mapLinearIsometry R) s (R center) x')⁻¹
        =
      dGWeightENN (L.mapLinearIsometry R) s (R center) (e x) *
          (∑' x' : (L.mapLinearIsometry R).carrier,
            dGWeightENN (L.mapLinearIsometry R) s (R center) x')⁻¹ := by
    exact congrArg
      (fun t =>
        t * (∑' x' : (L.mapLinearIsometry R).carrier,
          dGWeightENN (L.mapLinearIsometry R) s (R center) x')⁻¹)
      hWeight
  simpa [discreteGaussianPMF, e, hZ] using hMul

/-- Hyperplane membership transports through the lattice rotation carrier equivalence. -/
private lemma mem_affineHyperplane_mapLinearIsometryCarrierEquiv_e1_iff
    (L : EuclideanLattice n n) (R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n)
    (u : 𝓔 n) (c : ℝ) (hRu : R u = e1Vec) (x : L.carrier) :
    ((x : 𝓔 n) ∈ affineHyperplane u c) ↔
      (((EuclideanLattice.mapLinearIsometryCarrierEquiv (L := L) R x :
          (L.mapLinearIsometry R).carrier) : 𝓔 n) ∈ affineHyperplane e1Vec c) := by
  simpa
    [EuclideanLattice.mapLinearIsometryCarrierEquiv, EuclideanLattice.mapCarrierEquiv, hRu]
    using
      (mem_affineHyperplane_map_linearIsometry_iff
        (R := R) (u := u) (x := (x : 𝓔 n)) (c := c))

/--
WLOG transfer statement for hyperplane events under rotation:
there exists a rotation `R` such that hyperplane-event probability for
`x ~ D_{L,s,center}` on `(u,c)` equals hyperplane-event probability for
`x' ~ D_{L',s,R center}` on `(e₁,c)`, where `L' = R(L)`.
-/
theorem discrete_gaussian_hyperplane_measure_transfer_from_e1
  (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s)
  (center u : 𝓔 n) (hu : ‖u‖ = 1) (c : ℝ) :
  ∃ R : 𝓔 n ≃ₗᵢ[ℝ] 𝓔 n,
    let L' : EuclideanLattice n n := L.map R.toContinuousLinearEquiv
    let μ := (discreteGaussianPMF L s hs center).toMeasure
    let μ' := (discreteGaussianPMF L' s hs (R center)).toMeasure
    μ {x : L.carrier | (x : 𝓔 n) ∈ affineHyperplane u c}
      =
    μ' {x' : L'.carrier | (x' : 𝓔 n) ∈ affineHyperplane e1Vec c} := by
  obtain ⟨R, hRu⟩ := exists_rotation_to_e1 (n := n) u hu
  refine ⟨R, ?_⟩
  change
    (discreteGaussianPMF L s hs center).toMeasure
      {x : L.carrier | (x : 𝓔 n) ∈ affineHyperplane u c}
      =
    (discreteGaussianPMF (L.mapLinearIsometry R) s hs (R center)).toMeasure
      {x' : (L.mapLinearIsometry R).carrier | (x' : 𝓔 n) ∈ affineHyperplane e1Vec c}
  let e : L.carrier ≃ (L.mapLinearIsometry R).carrier :=
    L.mapLinearIsometryCarrierEquiv R
  let S : Set L.carrier := {x : L.carrier | (x : 𝓔 n) ∈ affineHyperplane u c}
  let S' : Set (L.mapLinearIsometry R).carrier :=
    {x' : (L.mapLinearIsometry R).carrier | (x' : 𝓔 n) ∈ affineHyperplane e1Vec c}
  have hEvent : ∀ x : L.carrier, S x ↔ S' (e x) := by
    intro x
    simpa [S, S', e] using
      (mem_affineHyperplane_mapLinearIsometryCarrierEquiv_e1_iff
        (L := L) (R := R) (u := u) (c := c) hRu x)
  have hPMF : ∀ x : L.carrier,
      discreteGaussianPMF L s hs center x =
        discreteGaussianPMF (L.mapLinearIsometry R) s hs (R center) (e x) := by
    intro x
    simpa [e] using
      (discreteGaussianPMF_mapLinearIsometryCarrierEquiv_eq
        (L := L) (R := R) (s := s) (hs := hs) (center := center) x)
  calc
    (discreteGaussianPMF L s hs center).toMeasure S
      = ∑' x : L.carrier, S.indicator (discreteGaussianPMF L s hs center) x := by
        simpa [S] using
          (discreteGaussian_toMeasure_apply_pred
            (L := L) (s := s) (hs := hs) (center := center) (S := S))
    _ =
      ∑' x : L.carrier,
        S'.indicator (discreteGaussianPMF (L.mapLinearIsometry R) s hs (R center)) (e x) := by
      refine tsum_congr ?_
      intro x
      by_cases hxS : S x
      · have hxS' : S' (e x) := (hEvent x).1 hxS
        rw [Set.indicator_of_mem (s := S) hxS, Set.indicator_of_mem (s := S') hxS']
        exact hPMF x
      · have hxS' : ¬ S' (e x) := by
          exact mt (fun hxS' => (hEvent x).2 hxS') hxS
        rw [Set.indicator_of_notMem (s := S) hxS, Set.indicator_of_notMem (s := S') hxS']
    _ =
      ∑' x' : (L.mapLinearIsometry R).carrier,
        S'.indicator (discreteGaussianPMF (L.mapLinearIsometry R) s hs (R center)) x' := by
      simpa [e] using
        (e.tsum_eq
          (fun x' : (L.mapLinearIsometry R).carrier =>
            S'.indicator (discreteGaussianPMF (L.mapLinearIsometry R) s hs (R center)) x'))
    _ =
      (discreteGaussianPMF (L.mapLinearIsometry R) s hs (R center)).toMeasure S' := by
      symm
      simpa [S'] using
        (discreteGaussian_toMeasure_apply_pred
          (L := L.mapLinearIsometry R) (s := s) (hs := hs) (center := R center) (S := S'))

end wlog_rot_e1

/-- The probability that a discrete Gaussian vector is in any affine hyperplane is bounded when the Gaussian's
scale factor is large enough relative to the smoothing parameter.
-/
theorem discrete_gaussian_hyperplane_anti_concentration_bound
  (L : EuclideanLattice n n) (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) (hε1 : ε < 1)
  (hS : Real.sqrt 2 * L.η ε < s) (center u : 𝓔 n) (hu : ‖u‖ = 1) (c : ℝ) :
  letI : MeasureTheory.MeasureSpace L.carrier :=
    ⟨(discreteGaussianPMF L s hs center).toMeasure⟩
  ℙ {x : L.carrier | inner ℝ (x : 𝓔 n) u = c} ≤
    ENNReal.ofReal ((1 + ε) / ((1 - ε) * Real.sqrt 2)) :=
  by
    obtain ⟨R, hTransfer⟩ :=
      discrete_gaussian_hyperplane_measure_transfer_from_e1
        (L := L) (s := s) (hs := hs) (center := center) (u := u) (hu := hu) (c := c)
    let L' : EuclideanLattice n n := L.mapLinearIsometry R
    have hMeasureEq :
        (discreteGaussianPMF L s hs center).toMeasure
          ({x : L.carrier | inner ℝ (x : 𝓔 n) u = c})
          =
        (discreteGaussianPMF L' s hs (R center)).toMeasure
          ({x' : L'.carrier | (x' : 𝓔 n) ∈ affineHyperplane e1Vec c}) := by
      simpa [L', EuclideanLattice.mapLinearIsometry, affineHyperplane] using hTransfer
    have hS' : Real.sqrt 2 * L'.η ε < s := by
      have hη : L'.η ε = L.η ε := by
        simpa [L'] using (smoothingParameter_mapLinearIsometry_eq (L := L) (R := R) (ε := ε))
      simpa [hη] using hS
    change
      (discreteGaussianPMF L s hs center).toMeasure
        ({x : L.carrier | inner ℝ (x : 𝓔 n) u = c})
        ≤ ENNReal.ofReal ((1 + ε) / ((1 - ε) * Real.sqrt 2))
    calc
      (discreteGaussianPMF L s hs center).toMeasure
          ({x : L.carrier | inner ℝ (x : 𝓔 n) u = c})
        =
      (discreteGaussianPMF L' s hs (R center)).toMeasure
          ({x' : L'.carrier | (x' : 𝓔 n) ∈ affineHyperplane e1Vec c}) := hMeasureEq
      _ ≤ ENNReal.ofReal ((1 + ε) / ((1 - ε) * Real.sqrt 2)) := by
        simpa [L'] using
          (discrete_gaussian_hyperplane_anti_concentration_e1_bound_affine
            (L := L') (s := s) (ε := ε) (hs := hs) (hε := hε) (hε1 := hε1)
            (hS := hS') (center := R center) (c := c))

end

end LatticeCrypto.Foundations.Gaussian
