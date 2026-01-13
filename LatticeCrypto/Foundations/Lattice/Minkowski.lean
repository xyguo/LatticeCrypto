import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Foundations.Lattice.FundamentalDomain
import LatticeCrypto.Foundations.Lattice.SuccessiveMinima
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Algebra.Order.Field.Basic

open scoped ENNReal NNReal Pointwise
open scoped MeasureTheory
open scoped RealInnerProductSpace
open scoped Classical
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.LinearAlgebra

namespace LatticeCrypto.Foundations.Lattice

variable {n : ℕ+}

/-!
# Minkowski's Theorems

This file states some fundamental theorems relating successive minima to volume bounds.

## Main Theorems

* `GeometricLattice.blichfeldt` - Blichfeldt's theorem
* `GeometricLattice.minkowski_convex_body` - Minkowski's convex body theorem
* `GeometricLattice.minkowski_first` - Minkowski's first theorem (bound on λ₁)
* `GeometricLattice.minkowski_second` - Minkowski's second theorem (bound on ∏ λᵢ)

## References

* [Peikert, *Lecture Notes: Lattices in Cryptography*, 2022]
* [Regev, *Lecture Notes: Lattices in Computer Science*, 2004]
* [Olds-Lax-Davidoff, *The Geometry of Numbers*, 2001]
-/


noncomputable section blichfeldt

/-!
## Blichfeldt's Theorem
-/

/--
  **Blichfeldt's Theorem**: If S is a measurable set with measure greater than
  the covolume of L, then S contains two distinct points whose difference is in L.

  This is a fundamental result in the geometry of numbers.
-/
theorem GeometricLattice.blichfeldt (L : GeometricLattice n n) (S : Set (𝔼 n))
    (hS_meas : MeasurableSet S)
    (hS_vol : L.det < (lebesgueMeasure S).toReal) :
    ∃ x y : 𝔼 n, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧ (x - y) ∈ L := by
  -- Let P be the fundamental parallelepiped of L
  let P := L.basis.fundamentalDomain

  -- For each lattice point x ∈ L, define Sₓ = S ∩ (x + P)
  let S_x := fun (x : L.carrier) => S ∩ ((x : 𝔼 n) +ᵥ P)
  -- Each S_x is measurable
  have h_S_meas : ∀ x : L.carrier, MeasurableSet (S_x x) := by
    intro x
    apply MeasurableSet.inter hS_meas
    -- x + P is measurable
    exact MeasurableSet.const_vadd L.basis.fundamentalDomain_measurableSet (x : 𝔼 n)


  -- The sets {x + P : x ∈ L} partition ℝⁿ
  have h_partition : ∀ v : 𝔼 n, ∃! x : L.carrier, v ∈ ((x : 𝔼 n) +ᵥ P) := by
    exact L.partition_by_fundamentalDomain
  -- Implication The Sₓ are pairwise disjoint
  have h_S_disjoint : Pairwise (Function.onFun Disjoint S_x) := by
    intro x y hxy
    simp only [Function.onFun, Set.disjoint_iff]
    intro v ⟨⟨_, hv_x⟩, ⟨_, hv_y⟩⟩
    -- v ∈ (x + P) ∩ (y + P), but the translates are disjoint for x ≠ y
    have h_unique := h_partition v
    obtain ⟨z, hz, hz_unique⟩ := h_unique
    have hx_eq : x = z := hz_unique x hv_x
    have hy_eq : y = z := hz_unique y hv_y
    exact hxy (hx_eq.trans hy_eq.symm)


  -- Therefore S = ⋃_{x ∈ L} Sₓ (disjoint union)
  have h_union : S = ⋃ (x : L.carrier), S_x x := by
    ext v
    simp only [Set.mem_iUnion]
    constructor
    · intro hv
      obtain ⟨x, hx, _⟩ := h_partition v
      exact ⟨x, hv, hx⟩
    · intro ⟨x, hv, _⟩
      exact hv

  -- Define S̃ₓ = Sₓ - x (translate back to P)
  let S_tilde := fun (x : L.carrier) => (fun v => v - (x : 𝔼 n)) '' (S_x x)

  -- Then S̃ₓ ⊆ P and each S̃ₓ is measurable
  have h_S_tilde_meas : ∀ x : L.carrier, MeasurableSet (S_tilde x) := by
    intro x
    apply MeasurableSet.image_of_continuousOn_injOn
    · exact h_S_meas x
    · exact continuous_sub_right (x : 𝔼 n) |>.continuousOn
    · intro a _ b _ hab
      simpa using hab

  have h_S_tilde_subset : ∀ x : L.carrier, S_tilde x ⊆ P := by
    intro x v hv
    simp only [S_tilde, Set.mem_image] at hv
    obtain ⟨w, ⟨_, hw_P⟩, rfl⟩ := hv
    -- w ∈ x + P means w - x ∈ P
    simp only [Set.mem_vadd_set] at hw_P
    obtain ⟨p, hp, rfl⟩ := hw_P
    simp
    exact hp

  -- vol(S̃ₓ) = vol(Sₓ) (translation preserves measure)
  have h_vol_eq : ∀ x : L.carrier, lebesgueMeasure (S_tilde x) = lebesgueMeasure (S_x x) := by
    intro x
    simp only [S_tilde]
    have : lebesgueMeasure ((fun v => v - (x : 𝔼 n)) '' (S_x x)) =
           lebesgueMeasure (S_x x) := by
      -- Subtracting x is the same as adding -x
      have h_eq : (fun v => v - (x : 𝔼 n)) '' (S_x x) = (fun v => v + (-(x : 𝔼 n))) '' (S_x x) := by
        simp only [sub_eq_add_neg]
      rw [h_eq]
      -- Use translation invariance: μ(A + c) = μ(A)
      rw [Set.image_add_right]
      simp
    exact this

  -- ∑_{x ∈ L} vol(S̃ₓ) = ∑_{x ∈ L} vol(Sₓ) = vol(S) > vol(P) = det(L)
  have h_sum_vol : ∑' (x : L.carrier), (lebesgueMeasure (S_tilde x)).toReal =
                   (lebesgueMeasure S).toReal := by
   -- The Sₓ are disjoint and their union is S
   -- First, show that ∑ vol(S̃ₓ) = ∑ vol(Sₓ) using h_vol_eq
    have h_sum_eq : ∑' (x : L.carrier), (lebesgueMeasure (S_tilde x)).toReal =
                    ∑' (x : L.carrier), (lebesgueMeasure (S_x x)).toReal := by
      congr 1
      ext x
      rw [h_vol_eq x]

    rw [h_sum_eq]

    -- Use countable additivity: vol(⋃ Sₓ) = ∑ vol(Sₓ) for pairwise disjoint sets
    have h_measure_union : lebesgueMeasure (⋃ x : L.carrier, S_x x) =
                           ∑' x : L.carrier, lebesgueMeasure (S_x x) := by
      apply MeasureTheory.measure_iUnion
      · -- Pairwise disjoint
        exact fun x y hxy => h_S_disjoint hxy
      · -- Each set is measurable
        exact h_S_meas

    -- S = ⋃ Sₓ
    rw [← h_union] at h_measure_union

    -- Convert from ENNReal to Real
    have h_finite : lebesgueMeasure S ≠ ⊤ := by
      -- Need to show S has finite measure
      -- This follows from hS_vol (if measure were infinite, toReal would be 0)
      intro h_inf
      simp [h_inf] at hS_vol
      exact (not_lt.mpr (L.det_pos.le)) hS_vol

    rw [h_measure_union]
    -- Now need: (∑' x, μ(S_x x)).toReal = ∑' x, (μ(S_x x)).toReal
    -- This requires that the sum is finite
    have h_sum_finite : ∑' x : L.carrier, lebesgueMeasure (S_x x) ≠ ⊤ := by
      rw [← h_measure_union]
      exact h_finite

    -- Each S_x has finite measure (they're subsets of the finite measure set S)
    have h_each_finite : ∀ x : L.carrier, lebesgueMeasure (S_x x) ≠ ⊤ := by
      intro x
      apply ne_top_of_le_ne_top h_finite
      exact MeasureTheory.measure_mono (Set.inter_subset_left)

    exact (ENNReal.tsum_toReal_eq h_each_finite).symm

  -- Since all S̃ₓ ⊆ P and ∑ vol(S̃ₓ) > vol(P), they cannot be disjoint
  -- By pigeonhole, there exist x ≠ y in L such that S̃ₓ ∩ S̃ᵧ ≠ ∅
  have h_pigeonhole : ∃ (x y : L.carrier), x ≠ y ∧ (S_tilde x ∩ S_tilde y).Nonempty := by
    -- Prove contrapositive
    by_contra h_disjoint
    push_neg at h_disjoint

    -- Immediate implication from the contraposition:
    -- The S̃ₓ are pairwise disjoint
    have h_S_tilde_disjoint : Pairwise (Function.onFun Disjoint S_tilde) := by
      intro x y hxy
      simp only [Function.onFun, Set.disjoint_iff_inter_eq_empty]
      exact h_disjoint x y hxy
    -- ⋃ S̃ₓ ⊆ P
    have h_union_subset : (⋃ x : L.carrier, S_tilde x) ⊆ P := by
      apply Set.iUnion_subset
      exact h_S_tilde_subset

    -- If all S̃ₓ are pairwise disjoint and contained in P
    -- then ∑ vol(S̃ₓ) ≤ vol(P) = det(L)
    have h_sum_le : ∑' (x : L.carrier), (lebesgueMeasure (S_tilde x)).toReal ≤ L.det := by
      -- Disjoint subsets of P have total measure ≤ vol(P)
      -- ⋃ S̃ₓ ⊆ P
      have h_union_subset : (⋃ x : L.carrier, S_tilde x) ⊆ P := by
        apply Set.iUnion_subset
        exact h_S_tilde_subset
      -- vol(⋃ S̃ₓ) = ∑ vol(S̃ₓ) by countable additivity (disjoint)
      have h_measure_union : lebesgueMeasure (⋃ x : L.carrier, S_tilde x) =
                             ∑' x : L.carrier, lebesgueMeasure (S_tilde x) := by
        apply MeasureTheory.measure_iUnion
        · exact fun x y hxy => h_S_tilde_disjoint hxy
        · exact h_S_tilde_meas
      -- vol(⋃ S̃ₓ) ≤ vol(P) since ⋃ S̃ₓ ⊆ P
      have h_le_P : lebesgueMeasure (⋃ x : L.carrier, S_tilde x) ≤ lebesgueMeasure P := by
        exact MeasureTheory.measure_mono h_union_subset
      -- vol(P) = det(L)
      have h_vol_P : (lebesgueMeasure P).toReal = L.det := by
        have h_L_basis_vol_eq := L.det_eq_real_measure_fundamentalDomain
        rw [h_L_basis_vol_eq]

      -- Convert to Real
      have h_P_finite : lebesgueMeasure P ≠ ⊤ := by
        have h_vol_P_pos : (lebesgueMeasure P).toReal > 0 := by
          simp [h_vol_P, L.det_pos]
        have h_ne_zero : (lebesgueMeasure P).toReal ≠ 0 := h_vol_P_pos.ne'
        rw [ENNReal.toReal_ne_zero] at h_ne_zero
        exact h_ne_zero.2

      have h_union_finite : lebesgueMeasure (⋃ x : L.carrier, S_tilde x) ≠ ⊤ := by
        exact ne_top_of_le_ne_top h_P_finite h_le_P

      have h_each_S_tilde_finite : ∀ x : L.carrier, lebesgueMeasure (S_tilde x) ≠ ⊤ := by
        intro x
        apply ne_top_of_le_ne_top h_P_finite
        calc lebesgueMeasure (S_tilde x)
            ≤ lebesgueMeasure (⋃ y : L.carrier, S_tilde y) := MeasureTheory.measure_mono (Set.subset_iUnion S_tilde x)
          _ ≤ lebesgueMeasure P := h_le_P

      calc ∑' (x : L.carrier), (lebesgueMeasure (S_tilde x)).toReal
          = (∑' x : L.carrier, lebesgueMeasure (S_tilde x)).toReal := by
              exact (ENNReal.tsum_toReal_eq h_each_S_tilde_finite).symm
        _ = (lebesgueMeasure (⋃ x : L.carrier, S_tilde x)).toReal := by
              rw [h_measure_union]
        _ ≤ (lebesgueMeasure P).toReal := by
              apply ENNReal.toReal_le_toReal h_union_finite h_P_finite |>.mpr
              exact h_le_P
        _ = L.det := h_vol_P
    -- But we have ∑ vol(S̃ₓ) = vol(S) > det(L), contradiction
    have h_sum_gt : L.det < ∑' (x : L.carrier), (lebesgueMeasure (S_tilde x)).toReal := by
      rw [h_sum_vol]
      exact hS_vol
    linarith

  -- Let z ∈ S̃ₓ ∩ S̃ᵧ
  obtain ⟨x, y, hxy_ne, z, hz_x, hz_y⟩ := h_pigeonhole

  -- z ∈ S̃ₓ means z = w - x for some w ∈ Sₓ, i.e., z + x ∈ S
  obtain ⟨w_x, ⟨hw_x_S, _⟩, hw_x_eq⟩ := hz_x
  -- z ∈ S̃ᵧ means z = v - y for some v ∈ Sᵧ, i.e., z + y ∈ S
  obtain ⟨w_y, ⟨hw_y_S, _⟩, hw_y_eq⟩ := hz_y

  -- So z + x and z + y are both in S
  have h_zx_in_S : z + (x : 𝔼 n) ∈ S := by
    convert hw_x_S using 1
    exact add_eq_of_eq_sub (id (Eq.symm hw_x_eq))

  have h_zy_in_S : z + (y : 𝔼 n) ∈ S := by
    convert hw_y_S using 1
    exact add_eq_of_eq_sub (id (Eq.symm hw_y_eq))

  -- Their difference is (z + x) - (z + y) = x - y ∈ L
  use z + (x : 𝔼 n), z + (y : 𝔼 n)
  refine ⟨h_zx_in_S, h_zy_in_S, ?_, ?_⟩
  · -- z + x ≠ z + y since x ≠ y
    intro h
    apply hxy_ne
    ext
    simp_all only [Subtype.forall, Subtype.coe_eta, ne_eq, Set.mem_iUnion, Subtype.exists,
      add_right_inj, SetLike.coe_eq_coe]
  · -- (z + x) - (z + y) = x - y ∈ L
    simp only [add_sub_add_left_eq_sub]
    -- x - y ∈ L since x, y ∈ L and L is a subgroup
    exact L.sub_mem x.property y.property

/-- Corollary: If vol(S) > det(L), then S - S contains a non-zero lattice point. -/
theorem GeometricLattice.blichfeldt_diff (L : GeometricLattice n n) (S : Set (𝔼 n))
    (hS_meas : MeasurableSet S)
    (hS_vol : L.det < (lebesgueMeasure S).toReal) :
    ∃ v ∈ L.nonzeroVectors, v ∈ S - S := by
  obtain ⟨x, y, hx, hy, hne, hdiff⟩ := L.blichfeldt S hS_meas hS_vol
  use x - y
  refine ⟨⟨hdiff, ?_⟩, ?_⟩
  · -- x - y ≠ 0 since x ≠ y
    intro h
    exact hne (sub_eq_zero.mp h)
  · -- x - y ∈ S - S
    exact Set.sub_mem_sub hx hy

/-!
## Minkowski's Convex Body Theorem
-/

/--
  **Minkowski's Convex Body Theorem**: Let L be a full-rank lattice in ℝⁿ with
  covolume det(L). If S is a convex, centrally symmetric, measurable set with
  vol(S) > 2ⁿ · det(L), then S contains a non-zero lattice point.

  This is one of the most important results in the geometry of numbers.
-/
theorem GeometricLattice.minkowski_convex_body (L : GeometricLattice n n)
    (S : Set (𝔼 n))
    (hS_convex : Convex ℝ S)
    (hS_symm : IsCentrallySymmetric S)
    (hS_meas : MeasurableSet S)
    (hS_vol : (2 : ℝ) ^ (n : ℕ) * L.det < (lebesgueMeasure S).toReal) :
    ∃ v ∈ L.nonzeroVectors, v ∈ S := by
  -- Proof: Apply Blichfeldt to (1/2) • S
  -- vol((1/2) • S) = (1/2)ⁿ * vol(S) > det(L)
  -- So there exist x ≠ y in (1/2) • S with x - y ∈ L
  -- Then 2x, 2y ∈ S and by convexity and symmetry:
  -- (1/2)(2x) + (1/2)(-2y) = x - y ∈ S
  let S' := (2 : ℝ)⁻¹ • S
  have hS'_meas : MeasurableSet S' := by
    exact MeasurableSet.const_smul₀ hS_meas 2⁻¹
  have hS'_vol : L.det < (lebesgueMeasure S').toReal := by
    -- vol(S') = (1/2)ⁿ * vol(S) > (1/2)ⁿ * 2ⁿ * det(L) = det(L)
    have hS'_vol_eq : (lebesgueMeasure S').toReal = ((2 : ℝ)⁻¹) ^ (n : ℕ) * (lebesgueMeasure S).toReal := by
      -- Apply the theorem that scaling a set by a factor of $c$ multiplies its volume by $c^n$.
      have h_scale : ∀ c : ℝ, 0 < c → (lebesgueMeasure (c • S)).toReal = c ^ (n : ℕ) * (lebesgueMeasure S).toReal := by
        intro c hc; erw [ MeasureTheory.Measure.addHaar_smul ] ; aesop;
        exact Or.inl ( by rw [ abs_of_pos hc ] );
      -- Apply the scaling theorem with $c = 2^{-1}$.
      apply h_scale; norm_num
    rw [hS'_vol_eq]
    rw [ inv_pow, inv_mul_eq_div, lt_div_iff₀ ] <;> first | positivity | linarith;


  obtain ⟨x, y, hx, hy, hne, hdiff⟩ := L.blichfeldt S' hS'_meas hS'_vol
  -- x, y ∈ (1/2) • S means 2x, 2y ∈ S
  have h2x : (2 : ℝ) • x ∈ S := by
    exact Set.mem_invOf_smul_set.mp hx
  have h2y : (2 : ℝ) • y ∈ S := by
    exact Set.mem_invOf_smul_set.mp hy
  -- -2y ∈ S by symmetry
  have hn2y : -((2 : ℝ) • y) ∈ S := hS_symm _ h2y
  -- x - y = (1/2)(2x) + (1/2)(-2y) ∈ S by convexity
  have hdiff_in_S : x - y ∈ S := by
    have heq : x - y = (1/2 : ℝ) • ((2 : ℝ) • x) + (1/2 : ℝ) • (-((2 : ℝ) • y)) := by
      simp only [smul_neg, smul_smul]
      ring_nf
      simp
      aesop
    rw [heq]
    exact hS_convex h2x hn2y (by norm_num) (by norm_num) (by norm_num)
  use x - y
  refine ⟨⟨hdiff, sub_ne_zero.mpr hne⟩, hdiff_in_S⟩

end blichfeldt


noncomputable section minkowski_1
/-!
## Minkowski's First Theorem
-/

/--
  **Minkowski's First Theorem**: The shortest non-zero vector in a lattice L
  satisfies:
    λ₁(L) ≤ √n · det(L)^(1/n)

  More precisely, for any full-rank lattice in ℝⁿ:
    λ₁(L) ≤ 2 · (det(L) / vol(Bⁿ))^(1/n)

  where Bⁿ is the unit ball.
-/
theorem GeometricLattice.minkowski_first (L : GeometricLattice n n) :
    L.shortestVectorLength ≤ 2 * (L.det / unitBallVolume n) ^ (1 / (n : ℝ)) := by
  -- By defintion, the open ball B(0, λ₀) contains no nonzero lattice points.
  -- Thus by Minkowski's convex body theorem, vol(B(0,λ₀)) ≤ 2^n det(L)
  -- On the other side, using theorem `ball_volume_eq` we have vol(B(0,λ₀)) = λ₀^n * vol(Bⁿ)
  -- Rearranging: λ₁ ≤ 2 * (det(L) / vol(Bⁿ))^(1/n)

  -- Preliminary positivity facts
  have hdet_pos : 0 < L.det := L.det_pos
  have hlambda_pos : 0 < L.shortestVectorLength := L.shortestVectorLength_pos
  have hvol_pos : 0 < unitBallVolume n := by
    exact unitBallVolume_pos -- The unit ball has positive measure

  -- Step 1: The open ball B(0, λ₁) contains no non-zero lattice points
  have h_empty : ∀ v ∈ L.nonzeroVectors, v ∉ Metric.ball (0 : 𝔼 n) L.shortestVectorLength := by
    intro v ⟨hv_mem, hv_ne⟩ hv_ball
    simp only [Metric.mem_ball, dist_zero_right] at hv_ball
    -- ‖v‖ < λ₁ contradicts the definition of λ₁ as the infimum
    have h_le : L.shortestVectorLength ≤ ‖v‖ := by
      -- The shortest vector length is the infimum of norms of non-zero lattice vectors
      -- By definition of the shortest vector length, it is the infimum of the norms of all non-zero vectors in the lattice.
      have h_inf : L.shortestVectorLength = sInf {r | ∃ v ∈ L.nonzeroVectors, ‖v‖ = r} := by
        exact shortestVectorLength_eq L;
      exact h_inf.symm ▸ csInf_le ⟨ 0, by rintro x ⟨ w, hw, rfl ⟩ ; exact norm_nonneg _ ⟩ ⟨ v, ⟨ hv_mem, hv_ne ⟩, rfl ⟩
    linarith

  -- Step 2: By contrapositive of Minkowski's convex body theorem:
  -- If B(0, r) contains no non-zero lattice points, then vol(B(0, r)) ≤ 2^n * det(L)
  have h_vol_bound : (lebesgueMeasure (Metric.ball (0 : 𝔼 n) L.shortestVectorLength)).toReal ≤
                     (2 : ℝ) ^ (n : ℕ) * L.det := by
    by_contra h_contra
    push_neg at h_contra
    -- If vol(B(0, λ₁)) > 2^n * det(L), then by Minkowski there exists a non-zero lattice point in B(0, λ₁)
    have h_meas : MeasurableSet (Metric.ball (0 : 𝔼 n) L.shortestVectorLength) :=
      Metric.isOpen_ball.measurableSet
    obtain ⟨v, hv, hv_in_ball⟩ := L.minkowski_convex_body
      (Metric.ball 0 L.shortestVectorLength)
      ball_convex
      ball_isCentrallySymmetric
      h_meas
      h_contra
    exact h_empty v hv hv_in_ball

  -- Step 3: Use ball_volume_eq: vol(B(0, λ₁)) = λ₁^n * vol(Bⁿ)
  have h_vol_eq : (lebesgueMeasure (Metric.ball (0 : 𝔼 n) L.shortestVectorLength)).toReal =
                  L.shortestVectorLength ^ (n : ℕ) * unitBallVolume n := by
    exact ball_volume_eq L.shortestVectorLength (le_of_lt hlambda_pos)

  -- Step 4: Combine to get λ₁^n * vol(Bⁿ) ≤ 2^n * det(L)
  have h_pow_bound : L.shortestVectorLength ^ (n : ℕ) * unitBallVolume n ≤
                     (2 : ℝ) ^ (n : ℕ) * L.det := by
    rw [← h_vol_eq]
    exact h_vol_bound

  -- Step 5: Divide by vol(Bⁿ) to get λ₁^n ≤ 2^n * (det(L) / vol(Bⁿ))
  have h_pow_bound' : L.shortestVectorLength ^ (n : ℕ) ≤
                      (2 : ℝ) ^ (n : ℕ) * (L.det / unitBallVolume n) := by
    have h := div_le_div_of_nonneg_right h_pow_bound (le_of_lt hvol_pos)
    rw [mul_div_assoc, mul_div_assoc] at h
    simp only [div_self (ne_of_gt hvol_pos), mul_one] at h
    exact h

  -- Step 6: Take n-th root of both sides
  -- λ₁ ≤ 2 * (det(L) / vol(Bⁿ))^(1/n)
  have h_rpow_bound : L.shortestVectorLength ≤
                      2 * (L.det / unitBallVolume n) ^ (1 / (n : ℝ)) := by
    -- First, rewrite LHS as (λ₁^n)^(1/n)
    have h_lhs : L.shortestVectorLength =
                 (L.shortestVectorLength ^ (n : ℕ)) ^ (1 / (n : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hlambda_pos)]
      simp only [one_div]
      rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (PNat.ne_zero n))]
      exact (Real.rpow_one _).symm

    -- Rewrite RHS as (2^n * (det/vol))^(1/n)
    have h_rhs : 2 * (L.det / unitBallVolume n) ^ (1 / (n : ℝ)) =
                 ((2 : ℝ) ^ (n : ℕ) * (L.det / unitBallVolume n)) ^ (1 / (n : ℝ)) := by
      rw [Real.mul_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
                        (div_nonneg (le_of_lt hdet_pos) (le_of_lt hvol_pos))]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [one_div, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (PNat.ne_zero n) : (n : ℝ) ≠ 0)]
      simp [Real.rpow_one 2]

    rw [h_lhs, h_rhs]
    apply Real.rpow_le_rpow
    · exact pow_nonneg (le_of_lt hlambda_pos) _
    · exact h_pow_bound'
    · exact div_nonneg (by norm_num) (Nat.cast_pos.mpr n.pos).le

  exact h_rpow_bound

/-- Simpler bound using √n. -/
theorem GeometricLattice.minkowski_first_sqrt (L : GeometricLattice n n) :
    L.shortestVectorLength ≤ Real.sqrt n * L.det ^ (1 / (n : ℝ)) := by
 -- This follows from minkowski_first and vol(Bⁿ) ≥ (2/√n)ⁿ
  have : unitBallVolume n ≥ (2 : ℝ) ^ (n : ℕ) / (Real.sqrt n) ^ (n : ℕ) := by
    exact unitBallVolume_lb (n := n)
  -- Taking the nth root of both sides of the inequality, we get the desired result.
  have h_root : (unitBallVolume n) ^ (1 / (n : ℝ)) ≥ 2 / (Real.sqrt n) := by
    exact le_trans ( by rw [ Real.div_rpow ( by positivity ) ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( Real.rpow_le_rpow ( by positivity ) this ( by positivity ) );
  -- Using the inequality from h_root, we can bound the expression from Minkowski's first theorem.
  have h_bound : 2 * (L.det / unitBallVolume n) ^ (1 / (n : ℝ)) ≤ 2 * (L.det) ^ (1 / (n : ℝ)) * (Real.sqrt n / 2) := by
    rw [ Real.div_rpow ];
    · rw [ mul_assoc, div_eq_mul_inv ];
      gcongr;
      · exact Real.rpow_nonneg ( le_of_lt ( L.det_pos ) ) _;
      · simpa using inv_anti₀ ( by positivity ) h_root;
    · exact le_of_lt ( L.det_pos );
    · exact le_trans ( by positivity ) this;
  exact le_trans ( GeometricLattice.minkowski_first L ) ( by linarith )

/-- A simple upper bound on the shortest vector length using the geometric mean of the Gram-Schmidt vectors.
  This is a corollary of Minkowski's First Theorem.
-/
theorem shortestVectorLength_le_gramSchmidt_geometric_mean (L : GeometricLattice n n) (B: SquareLatticeBasis n)
  (h: isBasisFor B L) : L.shortestVectorLength ≤ Real.sqrt n * (∏ i : Fin n, ‖InnerProductSpace.gramSchmidt ℝ B.basis i‖) ^ (1 / (n : ℝ)) := by
  have h_L_det := euc_gramSchmidt_matrix_det_abs L.basis.asMatrix
  have h_B_det := euc_gramSchmidt_matrix_det_abs B.asMatrix

  have h_L_B_det_eq : L.det = B.volume := by
    -- By definition of determinant, we know that `L.det = |det(L.basis.asMatrix)|`.
    have h_L_det : L.det = abs (L.basis.asMatrix.det) := by
      exact rfl;
    -- Since L and B are unimodularly equivalent, their determinants are equal.
    have h_det_eq : L.det = B.toLattice.det := by
      have h_unimod : L ≡ᵤ B.toLattice := by
        exact GeometricLattice.CarrierEquiv.symm h
      exact GeometricLattice.det_eq_of_equiv h_unimod;
    exact h_det_eq

  have mink_1 := GeometricLattice.minkowski_first_sqrt L
  rw [h_L_B_det_eq, LatticeBasis.volume, h_B_det] at mink_1
  convert mink_1

end minkowski_1

noncomputable section minkowski_2
/-!
## Minkowski's Second Theorem

**Minkowski's Second Theorem**: The successive minima of a lattice L satisfy:

    (∏ᵢ λᵢ(L))^(1/n) ≤ √n · det(L)^(1/n)

  More precisely:
    vol(Bⁿ) · ∏ᵢ λᵢ(L) ≤ 2ⁿ · det(L)

  where Bⁿ is the unit ball.
-/

/-
Definition of the ellipsoid T used in Minkowski's Second Theorem.
-/
open LatticeCrypto.Foundations.Lattice
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Utils.Geometry
open InnerProductSpace
open Module

/-
There exists a smallest index `j ≤ k` such that `λ_j = λ_k`. For all `i < j`, `λ_i < λ_k`.
-/
lemma exists_min_index_eq_successiveMinima (L : GeometricLattice n n) (k : Fin n) :
    ∃ j : Fin n, j ≤ k ∧ L.successiveMinima j = L.successiveMinima k ∧
    ∀ i : Fin n, i < j → L.successiveMinima i < L.successiveMinima k := by
      -- Since `L.successiveMinima` is monotonic, the set `S = {i | L.successiveMinima i = L.successiveMinima k}` is nonempty and has a least element.
      obtain ⟨j, hj_mem⟩ : ∃ j : Fin n, j ∈ {i : Fin n | L.successiveMinima i = L.successiveMinima k} ∧ (∀ i : Fin n, i ∈ {i : Fin n | L.successiveMinima i = L.successiveMinima k} → j ≤ i) := by
        exact ⟨ Finset.min' ( Finset.univ.filter fun i => L.successiveMinima i = L.successiveMinima k ) ⟨ k, by aesop ⟩, by simpa using Finset.min'_mem ( Finset.univ.filter fun i => L.successiveMinima i = L.successiveMinima k ) ⟨ k, by aesop ⟩, fun i hi => Finset.min'_le _ _ <| by aesop ⟩;
      use j; aesop;
      exact lt_of_le_of_ne ( left ▸ L.successiveMinima_mono a.le ) fun h => a.not_ge ( right _ h )



/-- The ellipsoid T defined in the proof of Minkowski's Second Theorem. -/
def minkowski_ellipsoid (b : Basis (Fin n) ℝ (𝔼 n)) (lambdas : Fin n → ℝ) : Set (𝔼 n) :=
  let b' := gramSchmidt ℝ b
  { y | ∑ i, (inner ℝ y (b' i) / (‖b' i‖ * lambdas i)) ^ 2 < 1 }

/-
The Minkowski ellipsoid is convex.
-/
theorem minkowski_ellipsoid_convex (b : Basis (Fin n) ℝ (𝔼 n)) (lambdas : Fin n → ℝ) (hlambdas : ∀ i, 0 < lambdas i) :
    Convex ℝ (minkowski_ellipsoid b lambdas) := by
      let b_GS := gramSchmidt ℝ b
      intro x hx y hy a b ha hb hab;
      -- Apply the linearity of the inner product and the triangle inequality.
      have h_inner_triangle : ∀ i, (inner ℝ (a • x + b • y) (b_GS i) / (‖b_GS i‖ * lambdas i)) ^ 2 ≤ a * (inner ℝ x (b_GS i) / (‖b_GS i‖ * lambdas i)) ^ 2 + b * (inner ℝ y (b_GS i) / (‖b_GS i‖ * lambdas i)) ^ 2 := by
        -- Apply the linearity of the inner product and the triangle inequality to each term in the sum.
        intro i
        have h_inner_triangle : (a * ⟪x, b_GS i⟫_ℝ + b * ⟪y, b_GS i⟫_ℝ) ^ 2 ≤ (a + b) * (a * ⟪x, b_GS i⟫_ℝ ^ 2 + b * ⟪y, b_GS i⟫_ℝ ^ 2) := by
          nlinarith [ sq_nonneg ( ⟪x, b_GS i⟫_ℝ - ⟪y, b_GS i⟫_ℝ ), mul_nonneg ha hb ];
        simp_all ( config := { decide := Bool.true } ) [ div_pow, mul_pow, inner_add_left, inner_smul_left ];
        convert div_le_div_of_nonneg_right h_inner_triangle ( mul_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) ) using 1 ; ring;
      -- Apply the triangle inequality to each term in the sum.
      have h_sum_triangle : ∑ i, (inner ℝ (a • x + b • y) (b_GS i) / (‖b_GS i‖ * lambdas i)) ^ 2 ≤ a * ∑ i, (inner ℝ x (b_GS i) / (‖b_GS i‖ * lambdas i)) ^ 2 + b * ∑ i, (inner ℝ y (b_GS i) / (‖b_GS i‖ * lambdas i)) ^ 2 := by
        simpa only [ Finset.mul_sum _ _ _, Finset.sum_add_distrib ] using Finset.sum_le_sum fun i _ => h_inner_triangle i;
      unfold minkowski_ellipsoid at *; aesop;
      cases lt_or_ge a b <;> nlinarith

/-
The Minkowski ellipsoid is centrally symmetric.
-/
theorem minkowski_ellipsoid_symmetric (b : Basis (Fin n) ℝ (𝔼 n)) (lambdas : Fin n → ℝ) :
    IsCentrallySymmetric (minkowski_ellipsoid b lambdas) := by
      intro y hy; simp_all +decide [ minkowski_ellipsoid ];
      simpa only [ neg_div, neg_sq ] using hy

/-
Definition of the scaling linear equivalence for the Minkowski ellipsoid.
-/

/-- The linear equivalence that scales the orthonormal basis vectors by lambdas. -/
noncomputable def minkowski_scaling (b : Basis (Fin n) ℝ (𝔼 n)) (lambdas : Fin n → ℝ) (hlambdas : ∀ i, lambdas i ≠ 0) : (𝔼 n) ≃ₗ[ℝ] (𝔼 n) :=
  let u := Basis_of_gramSchmidtOrthonormalBasis b
  let f := Basis.constr u ℝ (fun i => lambdas i • u i)
  have h_inv : Function.Bijective f := by
    have h_inv : Invertible f := by
      use ( u.constr ℝ ) fun i => ( lambdas i ) ⁻¹ • u i;
      · ext i; aesop;
      · ext x; simp +decide [ f, hlambdas ] ;
    obtain ⟨ g, hg ⟩ := h_inv;
    exact ⟨ LinearMap.injective_of_comp_eq_id _ _ ‹_›, LinearMap.surjective_of_comp_eq_id _ _ ‹_› ⟩
  LinearEquiv.ofBijective f h_inv

/-
The determinant of the scaling map is the product of the scaling factors.
-/

theorem minkowski_scaling_det (b : Basis (Fin n) ℝ (𝔼 n)) (lambdas : Fin n → ℝ) (hlambdas : ∀ i, lambdas i ≠ 0) :
    LinearMap.det (minkowski_scaling b lambdas hlambdas).toLinearMap = ∏ i, lambdas i := by
      -- The determinant of a diagonal matrix is the product of its diagonal entries.
      have h_det_diag : (LinearMap.toMatrix (Basis_of_gramSchmidtOrthonormalBasis b) (Basis_of_gramSchmidtOrthonormalBasis b) (minkowski_scaling b lambdas hlambdas)).det = ∏ i, lambdas i := by
        rw [ Matrix.det_of_upperTriangular ];
        · congr;
          ext i; unfold minkowski_scaling; simp +decide [ LinearMap.toMatrix_apply ] ;
        · intro i j hij; simp at hij;
          unfold minkowski_scaling;
          simp +decide [ LinearMap.toMatrix_apply, hij.ne' ];
      rw [ ← h_det_diag, LinearMap.det_toMatrix ]

theorem minkowski_ellipsoid_mem_iff (b : Basis (Fin n) ℝ (𝔼 n)) (lambdas : Fin n → ℝ) (y : 𝔼 n) :
    y ∈ minkowski_ellipsoid b lambdas ↔ ∑ i, (inner ℝ y (Basis_of_gramSchmidtOrthonormalBasis b i) / lambdas i) ^ 2 < 1 := by
      unfold LatticeCrypto.Foundations.Lattice.minkowski_ellipsoid; aesop;
      · convert a using 3 ; norm_num [ div_mul_eq_div_div ];
        erw [ InnerProductSpace.gramSchmidtOrthonormalBasis_apply ] ; aesop;
        · unfold InnerProductSpace.gramSchmidtNormed; aesop;
          rw [ inner_smul_right ] ; ring!;
        · aesop;
          unfold InnerProductSpace.gramSchmidtNormed at a_1; aesop;
          have := InnerProductSpace.gramSchmidt_ne_zero x b.linearIndependent; aesop;
      · convert a using 2 ; norm_num [ div_mul_eq_div_div ];
        unfold LatticeCrypto.Utils.LinearAlgebra.Basis_of_gramSchmidtOrthonormalBasis; aesop;
        rw [ InnerProductSpace.gramSchmidtOrthonormalBasis_apply ];
        · unfold InnerProductSpace.gramSchmidtNormed; aesop;
          rw [ inner_smul_right ] ; ring;
        · simp +decide [ InnerProductSpace.gramSchmidtNormed ];
          exact gramSchmidt_ne_zero x b.linearIndependent

/-
The Minkowski ellipsoid is the image of the unit ball under the scaling map.
-/

theorem minkowski_ellipsoid_eq_image_ball (b : Basis (Fin n) ℝ (𝔼 n)) (lambdas : Fin n → ℝ) (hlambdas : ∀ i, lambdas i ≠ 0) :
    minkowski_ellipsoid b lambdas = (minkowski_scaling b lambdas hlambdas).toLinearMap '' (Metric.ball 0 1) := by
    by_contra h_contra;
    have h_eq : ∀ x : LatticeCrypto.Utils.Vec.𝔼 n, x ∈ minkowski_ellipsoid b lambdas ↔ ‖(minkowski_scaling b lambdas hlambdas).symm x‖ < 1 := by
      have h_eq : ∀ x : LatticeCrypto.Utils.Vec.𝔼 n, ‖(minkowski_scaling b lambdas hlambdas).symm x‖ ^ 2 = ∑ i, (inner ℝ x (Basis_of_gramSchmidtOrthonormalBasis b i) / lambdas i) ^ 2 := by
        intro x
        have h_expand : (minkowski_scaling b lambdas hlambdas).symm x = ∑ i, (inner ℝ x (Basis_of_gramSchmidtOrthonormalBasis b i) / lambdas i) • Basis_of_gramSchmidtOrthonormalBasis b i := by
          have hT_inv : ∀ i, (minkowski_scaling b lambdas hlambdas).symm (Basis_of_gramSchmidtOrthonormalBasis b i) = (1 / lambdas i) • Basis_of_gramSchmidtOrthonormalBasis b i := by
            intro i;
            have hT_inv : (minkowski_scaling b lambdas hlambdas) ((1 / lambdas i) • Basis_of_gramSchmidtOrthonormalBasis b i) = Basis_of_gramSchmidtOrthonormalBasis b i := by
              unfold LatticeCrypto.Foundations.Lattice.minkowski_scaling; aesop;
            rw [ ← hT_inv, LinearEquiv.symm_apply_apply ];
            rw [ hT_inv ];
          -- By definition of $T$, we know that $x = \sum_{i=1}^n \langle x, u_i \rangle u_i$.
          have hx : x = ∑ i, inner ℝ x (Basis_of_gramSchmidtOrthonormalBasis b i) • Basis_of_gramSchmidtOrthonormalBasis b i := by
            convert ( Basis.sum_repr ( Basis_of_gramSchmidtOrthonormalBasis b ) x ) |> Eq.symm;
            unfold LatticeCrypto.Utils.LinearAlgebra.Basis_of_gramSchmidtOrthonormalBasis; aesop;
            rw [ OrthonormalBasis.repr_apply_apply ];
            rw [ real_inner_comm ];
          conv_lhs => rw [ hx ];
          simp +decide [ div_eq_inv_mul, hT_inv ];
          exact Finset.sum_congr rfl fun _ _ => by rw [ smul_smul, mul_comm ] ;
        rw [ h_expand, ← real_inner_self_eq_norm_sq ];
        simp +decide [ inner_sum, sum_inner, inner_smul_left, inner_smul_right, sq ];
        rw [ Finset.sum_congr rfl ] ; intros ; rw [ Finset.sum_eq_single ‹_› ] <;> aesop;
        · simp +decide [ Basis_of_gramSchmidtOrthonormalBasis ];
        · simp +decide [ Basis_of_gramSchmidtOrthonormalBasis, a_2 ];
      aesop;
      · rw [ ← Real.sqrt_sq ( norm_nonneg _ ) ];
        rw [ Real.sqrt_lt' ] <;> aesop;
        exact?;
      · exact minkowski_ellipsoid_mem_iff b lambdas x |>.2 ( by nlinarith [ h_eq x, norm_nonneg ( ( minkowski_scaling b lambdas hlambdas ).symm x ) ] );
    refine' h_contra _;
    ext x; specialize h_eq x; aesop;

/-
The volume of the Minkowski ellipsoid is the product of the scaling factors times the volume of the unit ball.
-/

theorem minkowski_ellipsoid_volume (b : Basis (Fin n) ℝ (𝔼 n)) (lambdas : Fin n → ℝ) (hlambdas : ∀ i, 0 < lambdas i) :
    (lebesgueMeasure (minkowski_ellipsoid b lambdas)).toReal = (∏ i, lambdas i) * unitBallVolume n := by
      -- By the properties of the scaling map and the unit ball, we can rewrite the volume expression.
      have h_eq : minkowski_ellipsoid b lambdas = (minkowski_scaling b lambdas (fun i => ne_of_gt (hlambdas i))).toLinearMap '' Metric.ball 0 1 := by
        exact minkowski_ellipsoid_eq_image_ball b lambdas fun i => ne_of_gt (hlambdas i);
      rw [ h_eq, MeasureTheory.Measure.addHaar_image_linearMap ] ; aesop;
      rw [ minkowski_scaling_det b lambdas ( fun i => ne_of_gt ( hlambdas i ) ) ] ; norm_num [ abs_of_pos, Finset.abs_prod, hlambdas ] ;
      exact Or.inl rfl

/-
Definition of the extremal basis for a geometric lattice.
-/

/-- The basis of vectors attaining the successive minima. -/
noncomputable def GeometricLattice.extremalBasis (L : GeometricLattice n n) : Basis (Fin n) ℝ (𝔼 n) :=
  let x := Classical.choose L.linearIndependent_successiveMinima_attained
  let h := Classical.choose_spec L.linearIndependent_successiveMinima_attained
  basisOfLinearIndependentOfCardEqFinrank h.2 (by simp [finrank_euclideanSpace])

/-
Inequality for the Minkowski ellipsoid sum for vectors in a subspace.
-/

lemma minkowski_ellipsoid_disjoint_ineq (b : Basis (Fin n) ℝ (𝔼 n)) (lambdas : Fin n → ℝ) (k : Fin n) (v : 𝔼 n)
    (hv_span : v ∈ Submodule.span ℝ (Set.image b (Finset.univ.filter (fun i => i ≤ k))))
    (hlambdas_pos : ∀ i, 0 < lambdas i)
    (hlambdas_mono : ∀ i j, i ≤ j → j ≤ k → lambdas i ≤ lambdas j) :
    ∑ i, (inner ℝ v (gramSchmidt ℝ b i) / (‖gramSchmidt ℝ b i‖ * lambdas i)) ^ 2 ≥ ‖v‖ ^ 2 / (lambdas k) ^ 2 := by
      -- Since v is in the span of the first k basis vectors, its projection onto the Gram-Schmidt vectors b'_i for i > k is zero.
      have h_proj_zero : ∀ i, k < i → ⟪v, gramSchmidt ℝ b i⟫_ℝ = 0 := by
        -- By definition of Gram-Schmidt, each Gram-Schmidt vector is orthogonal to all previous basis vectors.
        have h_orthogonal : ∀ i j : Fin n, i < j → ⟪gramSchmidt ℝ b j, b i⟫_ℝ = 0 := by
          exact fun i j a => gramSchmidt_inv_triangular ℝ (⇑b) a;
        intro i hi; rw [ inner_eq_zero_symm ] ; rw [ Submodule.mem_span ] at hv_span;
        specialize hv_span ( LinearMap.ker ( innerₛₗ ℝ ( gramSchmidt ℝ b i ) ) ) ; simp_all +decide [ Set.subset_def ];
        exact hv_span fun x hx => h_orthogonal x i ( lt_of_le_of_lt hx hi );
      -- Since v is in the span of the first k basis vectors, we can write it as a linear combination of these vectors.
      obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, v = ∑ i, c i • gramSchmidt ℝ b i := by
        have h_gram_schmidt_span : Submodule.span ℝ (Set.range (gramSchmidt ℝ b)) = ⊤ := by
          have h_gram_schmidt_span : Submodule.span ℝ (Set.range (gramSchmidt ℝ b)) = Submodule.span ℝ (Set.range b) := by
            exact span_gramSchmidt ℝ ⇑b;
          rw [ h_gram_schmidt_span, b.span_eq ];
        have := h_gram_schmidt_span.ge ( Submodule.mem_top : v ∈ ⊤ ) ; rw [ Submodule.mem_span_range_iff_exists_fun ] at this; tauto;
      -- Since $v$ is in the span of the first $k$ basis vectors, we have $\|v\|^2 = \sum_{i=0}^{k} c_i^2 \|b'_i\|^2$.
      have hv_norm_sq : ‖v‖^2 = ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), c i^2 * ‖gramSchmidt ℝ b i‖^2 := by
        have hv_norm_sq : ‖v‖^2 = ∑ i, c i^2 * ‖gramSchmidt ℝ b i‖^2 := by
          have hv_norm_sq : ‖v‖^2 = ∑ i, ∑ j, c i * c j * ⟪gramSchmidt ℝ b i, gramSchmidt ℝ b j⟫_ℝ := by
            rw [ hc, ← real_inner_self_eq_norm_sq ];
            simp +decide [ inner_sum, sum_inner, inner_smul_left, inner_smul_right ];
            simp +decide only [Finset.mul_sum _ _ _, mul_assoc];
            simp +decide only [real_inner_comm];
          have hv_norm_sq : ∀ i j, i ≠ j → ⟪gramSchmidt ℝ b i, gramSchmidt ℝ b j⟫_ℝ = 0 := by
            exact fun i j a => gramSchmidt_orthogonal ℝ (⇑b) a;
          simp_all +decide [ sq, mul_assoc ];
          exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_eq_single i ] <;> aesop ; simp ( config := { decide := Bool.true } ) [ ← sq, inner_self_eq_norm_sq_to_K ] ;
        rw [ hv_norm_sq, ← Finset.sum_subset ( Finset.filter_subset ( fun i => i ≤ k ) Finset.univ ) ];
        simp +zetaDelta at *;
        intro i hi; specialize h_proj_zero i hi; rw [ hc ] at h_proj_zero; simp_all +decide ;
        rw [ sum_inner, Finset.sum_eq_single i ] at h_proj_zero;
        . have h := h_proj_zero
          -- Expand the inner product of a scalar multiple
          have h' : (c i) * ⟪gramSchmidt ℝ (⇑b) i, gramSchmidt ℝ (⇑b) i⟫_ℝ = 0 := by
            simpa [inner_smul_left] using h
          -- Split the product = 0
          have h'' := mul_eq_zero.mp h'
          -- Conclude
          rcases h'' with hc0 | hinner0
          · left
            exact hc0
          · right
            -- ⟪v,v⟫ = 0 ⇒ v = 0
            exact inner_self_eq_zero.mp hinner0
        . classical
          intro b₁ hb₁ hb₁_ne
          -- expand scalar multiplication in inner product
          simp [inner_smul_left, hb₁_ne, gramSchmidt_orthogonal]
        . aesop
      -- Since $v$ is in the span of the first $k$ basis vectors, we have $\langle v, b'_i \rangle = c_i \|b'_i\|^2$ for $i \leq k$.
      have hv_inner : ∀ i, i ≤ k → ⟪v, gramSchmidt ℝ b i⟫_ℝ = c i * ‖gramSchmidt ℝ b i‖^2 := by
        intro i hi; rw [ hc, sum_inner ] ; simp ( config := { decide := Bool.true } ) [ inner_smul_left ] ;
        rw [ Finset.sum_eq_single i ] <;> simp ( config := { contextual := Bool.true } ) [ inner_self_eq_norm_sq_to_K, gramSchmidt_orthogonal ];
      -- Substitute hv_inner into the sum.
      have h_sum_subst : ∑ i, (⟪v, gramSchmidt ℝ b i⟫_ℝ / (‖gramSchmidt ℝ b i‖ * lambdas i)) ^ 2 = ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), (c i / lambdas i) ^ 2 * ‖gramSchmidt ℝ b i‖ ^ 2 := by
        rw [ Finset.sum_filter ] ; refine' Finset.sum_congr rfl fun i hi => _ ; by_cases hi' : k < i <;> simp_all ( config := { decide := Bool.true } ) [ div_pow, mul_pow, mul_comm, ne_of_gt ( hlambdas_pos _ ) ] ;
        by_cases hi'' : ‖gramSchmidt ℝ b i‖ = 0 <;> simp_all ( config := { decide := Bool.true } ) [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, sq ];
      -- Since $\lambda_i \leq \lambda_k$ for all $i \leq k$, we have $(c_i / \lambda_i)^2 \geq (c_i / \lambda_k)^2$.
      have h_ineq : ∀ i, i ≤ k → (c i / lambdas i) ^ 2 ≥ (c i / lambdas k) ^ 2 := by
        intro i hi; rw [ div_pow, div_pow ] ; gcongr; -- <;> aesop;
        . nlinarith [hlambdas_pos i]
        . nlinarith [hlambdas_pos i]
        . exact hlambdas_mono i k hi (by rfl)
      simp_all ( config := { decide := Bool.true } ) [ div_pow ];
      simpa only [ Finset.sum_div _ _ _, div_mul_eq_mul_div, Finset.sum_mul ] using Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( h_ineq i <| Finset.mem_filter.mp hi |>.2 ) <| sq_nonneg _

/-
If a lattice vector has norm less than the k-th successive minimum, it is in the span of the first k extremal basis vectors.
-/

lemma mem_span_of_norm_lt (L : GeometricLattice n n) (v : 𝔼 n) (hv : v ∈ L.nonzeroVectors) (k : Fin n)
    (h_lt : ‖v‖ < L.successiveMinima k) :
    v ∈ Submodule.span ℝ (Set.image (GeometricLattice.extremalBasis L) (Finset.Iio k)) := by
      norm_num +zetaDelta at *;
      -- Suppose v is not in the span of x_0, ..., x_{k-1}. Then v is linearly independent of the set {x_i | i < k}.
      by_contra h_not_in_span
      have h_lin_indep : LinearIndependent ℝ (Fin.snoc (fun i : Fin k => Classical.choose L.linearIndependent_successiveMinima_attained (Fin.castLE (by
      exact k.2.le) i)) v) := by
        all_goals generalize_proofs at *;
        rw [ linearIndependent_fin_snoc ] ; aesop
        all_goals generalize_proofs at *;
        · exact Classical.choose_spec ( L.linearIndependent_successiveMinima_attained ) |>.2.comp _ ( fun i => by aesop );
        · rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at a;
          contrapose! h_not_in_span;
          aesop;
          refine' Submodule.sum_mem _ fun i hi => _;
          refine' Submodule.smul_mem _ _ _;
          refine' Submodule.subset_span ⟨ Fin.castLE ( by aesop ) i, _, _ ⟩ <;> aesop
          all_goals generalize_proofs at *;
          · exact Fin.castSucc_lt_last i;
          · unfold GeometricLattice.extremalBasis; aesop;
      generalize_proofs at *;
      exact inductive_step_contradiction L k ( Fin.is_lt k ) ( fun i => Classical.choose ( L.linearIndependent_successiveMinima_attained ) ( Fin.castLE ( Nat.le_of_lt k.2 ) i ) ) ( by
        refine' linearIndependent_fin_snoc.mp h_lin_indep |>.1 ) ( by
        exact fun i => Classical.choose_spec L.linearIndependent_successiveMinima_attained |>.1 _ |>.1 ) ( by
        intro i; have := Classical.choose_spec ( L.linearIndependent_successiveMinima_attained ) ; aesop; ) v hv h_lin_indep h_lt

/-
The Minkowski ellipsoid contains no non-zero lattice points.
-/

theorem minkowski_ellipsoid_disjoint (L : GeometricLattice n n) :
    ∀ v ∈ L.nonzeroVectors, v ∉ minkowski_ellipsoid (GeometricLattice.extremalBasis L) (L.successiveMinima) := by
      -- Let's choose any non-zero lattice vector v and apply the two cases.
      intro v hv_nonzero
      by_cases hv_gt : ‖v‖ ≥ L.successiveMinima (Fin.mk (n - 1) (Nat.sub_lt n.pos one_pos));
      · have h_sum_ge_one : ∑ i, (inner ℝ v (gramSchmidt ℝ (GeometricLattice.extremalBasis L) i) / (‖gramSchmidt ℝ (GeometricLattice.extremalBasis L) i‖ * L.successiveMinima i)) ^ 2 ≥ ‖v‖ ^ 2 / (L.successiveMinima (Fin.mk (n - 1) (Nat.sub_lt n.pos one_pos))) ^ 2 := by
          apply minkowski_ellipsoid_disjoint_ineq;
          · have h_span : v ∈ Submodule.span ℝ (Set.range (GeometricLattice.extremalBasis L)) := by
              simp +zetaDelta at *;
            rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_span;
            rcases h_span with ⟨ c, rfl ⟩ ; rw [ Finsupp.sum ] ; aesop;
            exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ <| Submodule.subset_span <| Set.mem_image_of_mem _ <| Nat.le_sub_one_of_lt <| Fin.is_lt i;
          · exact fun i => GeometricLattice.successiveMinima_pos L i;
          · exact fun i j hij hj => L.successiveMinima_mono hij;
        contrapose! h_sum_ge_one;
        exact lt_of_lt_of_le h_sum_ge_one <| by rw [ le_div_iff₀ ] <;> nlinarith [ show 0 < L.successiveMinima ( Fin.mk ( n - 1 ) ( Nat.sub_lt n.pos one_pos ) ) from GeometricLattice.successiveMinima_pos L _ ] ;
      · obtain ⟨ k, hk₁, hk₂ ⟩ := exists_index_between_norms L ( n - 1 ) ( Nat.sub_lt n.pos zero_lt_one ) v hv_nonzero ( by aesop );
        -- By mem_span_of_norm_lt, v is in the span of {x_i | i < k+1}, i.e., i ≤ k.
        have h_span : v ∈ Submodule.span ℝ (Set.image (GeometricLattice.extremalBasis L) (Finset.Iio (⟨ k + 1, by
          exact Nat.lt_pred_iff.mp k.2 ⟩ : Fin n))) := by
          apply mem_span_of_norm_lt;
          · assumption;
          · exact hk₂
        generalize_proofs at *;
        -- By minkowski_ellipsoid_disjoint_ineq with this k, the sum is ≥ ‖v‖^2 / λ_k^2 ≥ 1.
        have h_sum_ge_one : ∑ i : Fin n, (inner ℝ v (gramSchmidt ℝ (GeometricLattice.extremalBasis L) i) / (‖gramSchmidt ℝ (GeometricLattice.extremalBasis L) i‖ * L.successiveMinima i)) ^ 2 ≥ ‖v‖ ^ 2 / (L.successiveMinima (Fin.castLE (Nat.le_of_lt ‹_›) k)) ^ 2 := by
          apply minkowski_ellipsoid_disjoint_ineq;
          · refine' Submodule.span_mono _ h_span;
            simp +decide ;
            exact fun x hx => ⟨ x, Nat.le_of_lt_succ <| by aesop, rfl ⟩;
          · exact fun i => GeometricLattice.successiveMinima_pos L i;
          · exact fun i j a a_1 => GeometricLattice.successiveMinima_mono L a;
        -- Since ‖v‖ ≥ L.successiveMinima (Fin.castLE (Nat.le_of_lt ‹_›) k), we have ‖v‖^2 / (L.successiveMinima (Fin.castLE (Nat.le_of_lt ‹_›) k))^2 ≥ 1.
        have h_norm_ge_one : ‖v‖ ^ 2 / (L.successiveMinima (Fin.castLE (Nat.le_of_lt ‹_›) k)) ^ 2 ≥ 1 := by
          rw [ ge_iff_le, le_div_iff₀ ] <;> nlinarith [ show 0 < L.successiveMinima ( Fin.castLE ( Nat.le_of_lt ‹_› ) k ) from by exact? ];
        exact fun h => h_norm_ge_one.not_gt <| h_sum_ge_one.trans_lt <| by simpa using h;

/-
Minkowski's Second Theorem: The product of successive minima times the unit ball volume is bounded by 2^n times the lattice determinant.
-/

theorem GeometricLattice.minkowski_second (L : GeometricLattice n n) :
    (∏ i : Fin n, L.successiveMinima i) * unitBallVolume n ≤ (2 : ℝ) ^ (n : ℕ) * L.det := by
      -- By Minkowski's Convex Body Theorem, if the volume of the ellipsoid is greater than $(2^n) \cdot \text{det}(L)$, then it would contain a non-zero lattice point.
      have h_minkowski : ∀ S : Set (𝔼 n), Convex ℝ S → IsCentrallySymmetric S → MeasurableSet S → (2 ^ (n : ℕ) * L.det < (lebesgueMeasure S).toReal) → ∃ v ∈ L.nonzeroVectors, v ∈ S := by
        exact fun S a a_1 a_2 a_3 => minkowski_convex_body L S a a_1 a_2 a_3;
      contrapose! h_minkowski;
      refine' ⟨ minkowski_ellipsoid ( GeometricLattice.extremalBasis L ) ( L.successiveMinima ), minkowski_ellipsoid_convex _ _ _, minkowski_ellipsoid_symmetric _ _, _, _, _ ⟩;
      · exact fun i => successiveMinima_pos L i;
      · exact measurableSet_lt ( by measurability ) ( by measurability );
      · refine' lt_of_lt_of_le h_minkowski _;
        rw [ minkowski_ellipsoid_volume ];
        exact fun i => successiveMinima_pos L i;
      · exact?

/-
Minkowski's Second Theorem (sqrt form): The geometric mean of successive minima is bounded by sqrt(n) times the n-th root of the determinant.
-/

theorem GeometricLattice.minkowski_second_sqrt (L : GeometricLattice n n) :
    (∏ i : Fin n, L.successiveMinima i) ^ (1 / (n : ℝ)) ≤ Real.sqrt n * (L.det) ^ (1 / (n : ℝ)) := by
      rw [ mul_comm ];
      -- Taking the n-th root of both sides of the inequality from Minkowski's second theorem.
      have h_root : (∏ i : Fin n, L.successiveMinima i) ≤ (Real.sqrt n) ^ (n : ℕ) * L.det := by
        have := @GeometricLattice.minkowski_second;
        have := @unitBallVolume_lb n;
        rw [ div_le_iff₀ ( by positivity ) ] at this;
        nlinarith [ show 0 < L.det from L.det_pos, show 0 < ( 2 : ℝ ) ^ ( n : ℕ ) by positivity, show 0 < ( Real.sqrt n ) ^ ( n : ℕ ) by positivity, show 0 < ( ∏ i : Fin n, L.successiveMinima i ) by exact Finset.prod_pos fun i _ => L.successiveMinima_pos i, ‹∀ { n : ℕ+ } ( L : GeometricLattice n n ), ( ∏ i, L.successiveMinima i ) * unitBallVolume n ≤ 2 ^ ( n : ℕ ) * L.det› L ];
      exact le_trans ( Real.rpow_le_rpow ( Finset.prod_nonneg fun _ _ => le_of_lt ( GeometricLattice.successiveMinima_pos L _ ) ) h_root ( by positivity ) ) ( by rw [ Real.mul_rpow ( by positivity ) ( by exact le_of_lt ( L.det_pos ) ), ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), mul_one_div_cancel ( by positivity ), Real.rpow_one ] ; ring_nf; norm_num )

end minkowski_2

end LatticeCrypto.Foundations.Lattice
