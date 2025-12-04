import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Foundations.Lattice.FundamentalDomain
import LatticeCrypto.Foundations.Lattice.SuccessiveMinima
import LatticeCrypto.Utils.Geometry

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

open scoped ENNReal NNReal Pointwise
open MeasureTheory
open RealInnerProductSpace
open Classical
open LatticeCrypto.Utils.Geometry

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

noncomputable section


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
      exact measure_mono (Set.inter_subset_left)

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
        exact measure_mono h_union_subset
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
            ≤ lebesgueMeasure (⋃ y : L.carrier, S_tilde y) := measure_mono (Set.subset_iUnion S_tilde x)
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
  calc L.shortestVectorLength
      ≤ 2 * (L.det / unitBallVolume n) ^ (1 / (n : ℝ)) := L.minkowski_first
    _ = 2 * ((L.det ^ (1 / (n : ℝ))) / (unitBallVolume n) ^ (1 / (n : ℝ))) := by
        rw [Real.div_rpow]
        . exact le_of_lt L.det_pos
        . exact le_of_lt unitBallVolume_pos
    _ ≤ 2 * ((L.det ^ (1 / (n : ℝ))) / ( (2 : ℝ) ^ (n : ℕ) / (Real.sqrt n) ^ (n : ℕ))) ^ (1 / (n : ℝ)) := by
      have : unitBallVolume n ≥ (2 : ℝ) ^ (n : ℕ) / (Real.sqrt n) ^ (n : ℕ) := by
        exact unitBallVolume_lb
      sorry
    _ = 2 * ((L.det ^ (1 / (n : ℝ))) / ( (2 : ℝ) / (Real.sqrt n) )) := by sorry
    _ = Real.sqrt n * L.det ^ (1 / (n : ℝ)) := by sorry


/-!
## Minkowski's Second Theorem
-/

/--
  **Minkowski's Second Theorem**: The successive minima of a lattice L satisfy:

    (∏ᵢ λᵢ(L))^(1/n) ≤ √n · det(L)^(1/n)

  More precisely:
    vol(Bⁿ) · ∏ᵢ λᵢ(L) ≤ 2ⁿ · det(L)

  where Bⁿ is the unit ball.
-/
theorem GeometricLattice.minkowski_second (L : GeometricLattice n n) :
    (∏ i : Fin n, L.successiveMinima i) * unitBallVolume n ≤
    (2 : ℝ) ^ (n : ℕ) * L.det := by
  -- Step 1: Get linearly independent vectors achieving the successive minima
  have h_exists_vectors : ∃ (x : Fin n → 𝔼 n),
      (∀ i : Fin n, x i ∈ L.nonzeroVectors ∧ ‖x i‖ = L.successiveMinima i) ∧
      LinearIndependent ℝ (fun i : Fin n => x i) := by
    -- Use that successive minima are achieved (successiveMinima_attained)
    -- and can be chosen to be linearly independent
    sorry

  obtain ⟨x, ⟨hx_norms, hx_li⟩⟩ := h_exists_vectors

  -- Step 2: Gram-Schmidt orthogonalization
  -- Let x̄₁, ..., x̄ₙ be the Gram-Schmidt orthogonalization of x₁, ..., xₙ
  let gram_schmidt := InnerProductSpace.gramSchmidt ℝ (fun i : Fin n => x i)

  have hgs_orthogonal : Pairwise fun i j => ⟪(gram_schmidt i), (gram_schmidt j)⟫ = 0 := by
    sorry

  have hgs_norms : ∀ i : Fin n, ‖gram_schmidt i‖ > 0 := by
    intro i
    sorry

  -- Step 3: Construct the ellipsoid T with axes gram_schmidt and semi-axes λᵢ
  let T := { y : 𝔼 n | ∑ i : Fin n, (⟪y, (gram_schmidt i)⟫ / (‖gram_schmidt i‖ * L.successiveMinima i)) ^ 2 < 1 }

  -- Step 4: T is centrally symmetric and convex (ellipsoid)
  have hT_convex : Convex ℝ T := by
    -- Ellipsoids defined by quadratic form are convex
    sorry

  have hT_symm : IsCentrallySymmetric T := by
    intro y hy
    simp only [T, Set.mem_setOf] at hy ⊢
    sorry

  have hT_meas : MeasurableSet T := by
    -- Ellipsoid is measurable
    sorry

  -- Step 5: T contains no non-zero lattice points
  have hT_no_lattice : ∀ v ∈ L.nonzeroVectors, v ∉ T := by
    intro v hv_L hv_ne

    -- v can be written as a linear combination of x₁, ..., xₙ
    have h_decomp : v ∈ Submodule.span ℝ (Set.range x) := by
      -- Lattice is generated by x₁, ..., xₙ
      sorry

    sorry

  -- Step 6: Volume of T
  -- vol(T) = (∏ᵢ λᵢ) · vol(Bⁿ) · constant for Gram-Schmidt basis
  have hvol_T : (lebesgueMeasure T).toReal = (∏ i : Fin n, L.successiveMinima i) * unitBallVolume n := by
    -- Volume of ellipsoid with semi-axes λ₁, ..., λₙ
    sorry

  -- Step 7: Apply Minkowski's convex body theorem
  -- Since vol(T) ≤ 2ⁿ det(L) (by convexity and no non-zero lattice points)
  have h_vol_bound : (lebesgueMeasure T).toReal ≤ (2 : ℝ) ^ (n : ℕ) * L.det := by
    -- Would need contrapositive: if vol(T) > 2ⁿ det(L), then T contains non-zero lattice point
    -- But we proved T contains no such points
    by_contra h_contra
    push_neg at h_contra
    obtain ⟨v, hv_L, hv_T⟩ := L.minkowski_convex_body T hT_convex hT_symm hT_meas h_contra
    exact hT_no_lattice v hv_L hv_T

  rw [hvol_T] at h_vol_bound
  exact h_vol_bound


theorem GeometricLattice.minkowski_second_sqrt (L : GeometricLattice n n) :
    (∏ i : Fin n, L.successiveMinima i) ^ (1 / (n : ℝ)) ≤
    Real.sqrt n * (L.det) ^ (1 / (n : ℝ)) := by
  -- From minkowski_second: ∏ λᵢ * vol(Bⁿ) ≤ 2ⁿ * det(L)
  have h_second := L.minkowski_second

  -- Rearrange: ∏ λᵢ ≤ 2ⁿ * det(L) / vol(Bⁿ)
  have h_prod_bound : ∏ i : Fin n, L.successiveMinima i ≤
                      (2 : ℝ) ^ (n : ℕ) * L.det / unitBallVolume n := by
    have hvol_pos : 0 < unitBallVolume n := by
      exact unitBallVolume_pos -- Unit ball has positive volume
    rw [le_div_iff₀ hvol_pos]
    exact h_second

  -- Take 1/n-th power
  have h_prod_pos : 0 < ∏ i : Fin n, L.successiveMinima i := by
    apply Finset.prod_pos
    intro i _
    exact L.successiveMinima_pos i

  have hdet_pos : 0 < L.det := L.det_pos

  -- vol(Bⁿ) ≥ (2/√n)ⁿ for the unit ball
  have hvol_bound : (2 : ℝ) ^ (n : ℕ) / unitBallVolume n ≤ (Real.sqrt n) ^ (n : ℕ) := by
    -- Standard bound on unit ball volume
    sorry

  calc (∏ i : Fin n, L.successiveMinima i) ^ (1 / (n : ℝ))
      ≤ ((2 : ℝ) ^ (n : ℕ) * L.det / unitBallVolume n) ^ (1 / (n : ℝ)) := by
        apply Real.rpow_le_rpow (le_of_lt h_prod_pos)
        exact h_prod_bound
        norm_num
    _ = ((2 : ℝ) ^ (n : ℕ)) ^ (1 / (n : ℝ)) * (L.det) ^ (1 / (n : ℝ)) / (unitBallVolume n) ^ (1 / (n : ℝ)) := by
        have h_inner : (2 : ℝ) ^ (n : ℕ) * (L.det / unitBallVolume n) =
                       (2 : ℝ) ^ (n : ℕ) * L.det / unitBallVolume n := by ring
        rw [← h_inner]
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2 ^ (n : ℕ)) (div_nonneg (le_of_lt hdet_pos) (unitBallVolume_pos.le))]
        sorry
    _ = 2 * (L.det) ^ (1 / (n : ℝ)) / (unitBallVolume n) ^ (1 / (n : ℝ)) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        sorry
    _ ≤ Real.sqrt n * (L.det) ^ (1 / (n : ℝ)) := by
        -- Requires: 2 / (vol(Bⁿ))^(1/n) ≤ √n
        sorry

end

end LatticeCrypto.Foundations.Lattice
