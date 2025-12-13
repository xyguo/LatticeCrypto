import Mathlib.Analysis.Normed.Group.Basic      -- For NormedAddCommGroup
import Mathlib.Analysis.InnerProductSpace.PiL2  -- For EuclideanSpace
import Mathlib.Data.Matrix.Basic                -- for type synonym support
import Mathlib.Analysis.Normed.Group.Subgroup   -- For LinearIndependent.discrete_zspan
import Mathlib.LinearAlgebra.LinearIndependent.Defs  -- For LinearIndependent
import Mathlib.LinearAlgebra.Span.Defs               -- For AddSubgroup.zspan
import Mathlib.Data.Rat.Defs                   -- For ℚ (Rat)
import Mathlib.Data.Real.Basic                  -- For ℝ (Real)
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.PNat.Basic

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.CategoryTheory.Category.Basic  -- For aesop_cat

import LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Vec

open scoped ENNReal NNReal Pointwise
open MeasureTheory
open RealInnerProductSpace
open Classical
open FiniteDimensional


variable {n : ℕ+}

/-!
# Utility Functions

This module provides utility functions for mathematical analysis on lattice.
Many are light wrappers around Mathlib functions.

## Main components
* `Vec` - Defines the space the lattice resides.
* `Geometry` (**This file**) - handy lemmas in Euclidean geometry
* `LinearAlgebra` - handy lemmas in linear algebra
* `Algebra.Ring` - Lemmas in ring theory
* `Algebra.Module` - Lemmas in module theory
* `Algebra.Polynomial` - Lemmas in polynomial rings
-/

namespace LatticeCrypto.Utils.Geometry

noncomputable section

/-- The Lebesgue measure on ℝⁿ. -/
def lebesgueMeasure : Measure (𝔼 n) := volume

/-- The Lebesgue measure on ℝⁿ is left-invariant under addition. -/
instance : (lebesgueMeasure (n := n)).IsAddLeftInvariant :=
  -- Need `inferInstanceAs` because (𝔼 n) is a type synonym for EuclideanSpace ℝ (Fin n)
  -- Can also use `unfold legesgueMeasure`.
  inferInstanceAs (volume : Measure (𝔼 n)).IsAddLeftInvariant

instance : (lebesgueMeasure (n := n)).IsAddHaarMeasure :=
  inferInstanceAs (volume : Measure (𝔼 n)).IsAddHaarMeasure

-- This is measure-preserving for Lebesgue measure
lemma eucToPi_measurePreserving {n : ℕ+}:
  MeasurePreserving eucToPi lebesgueMeasure (volume (α := (Fin n → ℝ))):= by
  -- Note the following theorem will soon be deprecated for a more general
  -- `EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp`
  exact EuclideanSpace.volume_preserving_measurableEquiv (Fin n)

theorem volume_euclideanSpace_eq_pi {S : Set (𝔼 n)}:
  volume S = volume (eucToPi '' S) := by
  have h_volume_eq : (MeasureTheory.Measure.map eucToPi lebesgueMeasure) (eucToPi '' S) = lebesgueMeasure S := by
    have h_volume_eq : ∀ s : Set (𝔼 n), (MeasureTheory.Measure.map (⇑eucToPi) lebesgueMeasure) (eucToPi '' s) = (MeasureTheory.MeasureSpace.volume : Set (Fin n → ℝ) → ℝ≥0∞) (eucToPi '' s) := by
      exact fun s => congr_arg ( fun f => f ( eucToPi '' s ) ) ( eucToPi_measurePreserving.map_eq );
    aesop;
    convert h_volume_eq S |> Eq.symm;
    · -- Since `eucToPi` is measure-preserving, the map of the Lebesgue measure under `eucToPi` is equal to the Lebesgue measure on the target space.
      apply Eq.symm; exact (by
      apply MeasureTheory.Measure.ext;
      intro s hs; rw [ MeasureTheory.Measure.map_apply ] ; aesop;
      · exact fun ⦃t⦄ a => a;
      · exact hs);
    · ext; aesop;
  exact h_volume_eq ▸ by erw [ eucToPi_measurePreserving.map_eq ] ;

theorem volume_pi_eq_euclideanSpace {S : Set (Fin n → ℝ)}:
  volume S = volume (piToEuc '' S) := by
  -- By definition of $eucIdent$, we know that it is a linear isomorphism.
  have h_linear_isomorphism : (eucToPi : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ)) '' S = S := by
    aesop_cat;
  rw [ ← h_linear_isomorphism, volume_euclideanSpace_eq_pi ];
  -- Since the image of the image of S under eucToPi is just S itself, we can simplify the right-hand side of the equation.
  simp [Set.image]

lemma fundamentalDomain_stdBasis {n : ℕ+}:
  ZSpan.fundamentalDomain stdBasis =
    { x : 𝔼 n | ∀ i: Fin n, x i ∈ Set.Ico 0 1 } := by
      bound

lemma volume_fundamentalDomain_stdBasis {n : ℕ+}:
  lebesgueMeasure (ZSpan.fundamentalDomain (stdBasis (n := n))) = 1 :=
  by
    -- The fundamental domain of the standard basis is the unit cube in ℝⁿ, which has volume 1.
    have h_unit_cube : ZSpan.fundamentalDomain stdBasis = Set.pi Set.univ (fun _ : Fin n => Set.Ico 0 1) := by
      exact Set.Subset.antisymm (fun ⦃a⦄ a i a_1 => a i) fun ⦃a⦄ a i => a i trivial;
    rw [ h_unit_cube ];
    -- The volume of the product of intervals [0,1) in ℝⁿ is the product of their lengths, which is 1.
    have h_volume : ∀ (n : ℕ), (MeasureTheory.volume (Set.pi Set.univ fun _ : Fin n => Set.Ico (0 : ℝ) 1)) = 1 := by
      intro n; erw [ MeasureTheory.Measure.pi_pi ] ; norm_num;
    convert h_volume n using 1;
    convert eucToPi_measurePreserving.measure_preimage _;
    · ext; simp [eucToPi];
    · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.univ_pi fun _ => measurableSet_Ico )

/-!
## Central Symmetry
-/

/-- A set is centrally symmetric if x ∈ S implies -x ∈ S. -/
def IsCentrallySymmetric (S : Set (𝔼 n)) : Prop :=
  ∀ x ∈ S, -x ∈ S

/-- Central symmetry is equivalent to S = -S. -/
theorem isCentrallySymmetric_iff_neg_eq (S : Set (𝔼 n)) :
    IsCentrallySymmetric S ↔ S = -S := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      simp only [Set.mem_neg]
      convert h x hx using 1
    · intro hx
      simp only [Set.mem_neg] at hx
      have := h (-x) hx
      simp at this
      exact this
  · intro h x hx
    rw [h] at hx ⊢
    simp only [Set.mem_neg] at hx ⊢
    simp
    rw [ h ] at hx; simpa using hx;

/-- The origin is in every non-empty centrally symmetric set. -/
theorem IsCentrallySymmetric.zero_mem {S : Set (𝔼 n)}
    (hS : IsCentrallySymmetric S) (hne : S.Nonempty) (hConvex : Convex ℝ S) :
    (0 : 𝔼 n) ∈ S := by
  obtain ⟨x, hx⟩ := hne
  have hnx : -x ∈ S := hS x hx
  -- 0 = (1/2) * x + (1/2) * (-x)
  have h0 : (0 : 𝔼 n) = (1/2 : ℝ) • x + (1/2 : ℝ) • (-x) := by simp
  rw [h0]
  apply hConvex hx hnx (by norm_num) (by norm_num) (by norm_num)

/-- The open ball is centrally symmetric. -/
lemma ball_isCentrallySymmetric {r} :
    IsCentrallySymmetric (Metric.ball (0 : 𝔼 n) r) := by
  intro x hx
  simp only [Metric.mem_ball, dist_zero_right] at hx ⊢
  simp [hx]

/-- The open ball is convex. -/
lemma ball_convex {r} :
    Convex ℝ (Metric.ball (0 : 𝔼 n) r) := by
  exact convex_ball 0 r

/-- Helper: equivalence between Metric ball definition and radius-set definition -/
@[simp] lemma metric_ball_def_apply (r : ℝ) (x : 𝔼 n) :
  x ∈ Metric.ball (0 : 𝔼 n) r ↔ ‖x‖ < r := by
  simp [Metric.mem_ball, dist_zero_right]
@[simp] lemma metric_closedBall_def_apply (r : ℝ) (x : 𝔼 n) :
  x ∈ Metric.closedBall (0 : 𝔼 n) r ↔ ‖x‖ ≤ r := by
  simp [Metric.mem_closedBall, dist_zero_right]


/-- The volume of the unit ball in ℝⁿ. -/
noncomputable def unitBallVolume (n : ℕ+) : ℝ :=
  (lebesgueMeasure (Metric.ball (0 : 𝔼 n) 1)).toReal

/-- The volume of a ball of radius r in ℝⁿ is rⁿ times the unit ball volume. -/
theorem ball_volume_eq (r : ℝ) (hr : 0 ≤ r) :
    (lebesgueMeasure (Metric.ball (0 : 𝔼 n) r)).toReal =
    r ^ (n : ℕ) * unitBallVolume n := by
  -- Apply the theorem that states the volume of a ball in Euclidean space scales with the radius raised to the power of the dimension.
  have h_volume_ball : ∀ r : ℝ, 0 ≤ r → (MeasureTheory.volume (Metric.ball (0 : 𝔼 n) r)).toReal = r ^ (n : ℕ) * (MeasureTheory.volume (Metric.ball (0 : 𝔼 n) 1)).toReal := by
    intro r hr;
    have := @MeasureTheory.Measure.addHaar_ball ( EuclideanSpace ℝ ( Fin n ) );
    convert congr_arg ENNReal.toReal ( this MeasureTheory.MeasureSpace.volume 0 hr ) using 1;
    rw [ ENNReal.toReal_mul, ENNReal.toReal_ofReal ( by positivity ) ] ; norm_num;
  exact h_volume_ball r hr

theorem unitBallVolume_pos : 0 < unitBallVolume n := by
  have h_unit_ball_pos : 0 < (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    -- The volume of the unit ball in Euclidean space is positive because it is a non-empty open set.
    have h_unit_ball_pos : 0 < MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
      -- The volume of the unit ball in ℝ^n is positive.
      have h_volume_pos : 0 < MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
        have h_ball_pos : ∀ {r : ℝ}, 0 < r → 0 < MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) := by
          exact fun {r} a => Metric.measure_ball_pos volume 0 a
        exact h_ball_pos zero_lt_one;
      exact h_volume_pos;
    rw [ ENNReal.toReal_pos_iff ] ; aesop;
    exact measure_ball_lt_top;
  exact h_unit_ball_pos

/-- A handy lower bound on the volume of the unit ball in ℝⁿ. -/
theorem unitBallVolume_lb : (2 : ℝ) ^ (n : ℕ) / (Real.sqrt n) ^ (n : ℕ) ≤ unitBallVolume n := by
  -- We'll show that the unit ball contains a cube of side length 2/√n
  -- and use that the volume of this cube is (2/√n)ⁿ

  -- Step 1: Define the cube C = {x ∈ ℝⁿ | ∀i, |xᵢ| < 1/√n}
  let cube_side := 1 / Real.sqrt n
  let C := { x : 𝔼 n | ∀ i : Fin n, |eucToPi x i| < cube_side }

  have h_cube_side_nonneg : 0 ≤ cube_side := by
    have hsq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have : 0 ≤ (1 : ℝ) / Real.sqrt n := one_div_nonneg.mpr hsq
    simp [cube_side]

  -- Step 2: Show that C ⊆ B(0, 1)
  have hC_subset : C ⊆ Metric.ball (0 : 𝔼 n) 1 := by
    intro x hx
    simp only [C, Set.mem_setOf] at hx
    rw [metric_ball_def_apply]
    -- Need to show ‖x‖ < 1
    -- We have |xᵢ| < 1/√n for all i
    -- So ‖x‖² = ∑ᵢ xᵢ² < n · (1/√n)² = n · 1/n = 1
    have h_norm_sq : ‖x‖ ^ 2 < 1 := by
      -- ‖x‖² = ∑ᵢ xᵢ²
      have h_norm_def : ‖x‖ ^ 2 = ∑ i : Fin n, (eucToPi x i) ^ 2 := by
        rw [←real_inner_self_eq_norm_sq]
        simp only [PiLp.inner_apply]
        congr 1
        ext i
        simp [eucToPi]
        exact Eq.symm (pow_two (x i))
      rw [h_norm_def]
      -- Each term satisfies (eucToPi x i)² < (1/√n)²
      calc ∑ i : Fin n, (eucToPi x i) ^ 2
          < ∑ i : Fin n, cube_side ^ 2 := by
            apply Finset.sum_lt_sum
            · intro i _
              have := hx i
              have := abs_lt.mp this
              have := sq_lt_sq' this.left this.right
              gcongr
            · use 0
              constructor
              · exact Finset.mem_univ 0
              · have := hx 0
                have := abs_lt.mp this
                have := sq_lt_sq' this.left this.right
                gcongr
        _ = (n : ℝ) * (1 / Real.sqrt n) ^ 2 := by
            simp [Finset.sum_const]
            aesop
        _ = (n : ℝ) * (1 / n) := by
            rw [div_eq_inv_mul, mul_pow]
            ring
            rw [inv_pow, Real.sq_sqrt]
            exact Nat.cast_nonneg n
        _ = 1 := by
            field_simp
    simp_all only [sq_lt_one_iff_abs_lt_one, abs_norm]

  -- Step 3: C is measurable (as a product of intervals)
  -- The cube is a product of intervals
  have hC_pi :
      C =
        Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-cube_side) cube_side) := by
    ext x; constructor
    · intro hx
      -- `hx : ∀ i, |x i| < cube_side`; rewrite as -cube_side < x i < cube_side
      refine Set.mem_pi.mpr ?_
      intro i hi
      specialize hx i
      have h' : -cube_side < x i ∧ x i < cube_side := by
        -- `abs_lt` is `|x| < cube_side ↔ -cube_side < x ∧ x < cube_side`
        simpa [abs_lt] using hx
      exact h'
    · intro hx
      -- `hx : x ∈ pi univ (λ i, Ioo (-cube_side) cube_side)`, so each coordinate is in that interval.
      have hx' := Set.mem_pi.mp hx
      intro i
      specialize hx' i (by simp)
      -- convert `-cube_side < x i ∧ x i < cube_side` back to `|x i| < cube_side`
      have : |x i| < cube_side := by
        -- from -a < x i ∧ x i < a ⇒ |x i| < a
        have := hx'
        exact (abs_lt.mpr this)
      exact this

  -- From the `pi` formulation, measurability is immediate
  have hC_meas : MeasurableSet C := by
    classical
    -- each coordinate strip is measurable
    have h_singleton :
        ∀ i : Fin n,
          MeasurableSet (Set.Ioo (-cube_side : ℝ) cube_side) := by
      intro i
      exact (measurableSet_Ioo : MeasurableSet (Set.Ioo (-cube_side : ℝ) cube_side))
    -- the product of finitely many measurable sets is measurable
    have h_pi :
        MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-cube_side) cube_side)) := by
      exact MeasurableSet.univ_pi h_singleton
    -- rewrite C to that product
    simpa [hC_pi] using h_pi

  -- Step 4: The volume of C is (2 · cube_side)ⁿ = (2/√n)ⁿ
  have h_cube_side_le : (fun _ : Fin n => -cube_side) ≤ fun _ : Fin n => cube_side := by
    intro i
    have := h_cube_side_nonneg
    linarith
  have hvol_C : (lebesgueMeasure C).toReal = (2 * cube_side) ^ (n : ℕ) := by
    -- C is the product ∏ᵢ (-1/√n, 1/√n)
    -- Each interval has length 2/√n
    -- Volume is (2/√n)ⁿ
    -- rewrite C as the `pi` set, then apply `Real.volume_pi_Ioo_toReal`
    have hvol_pi :
        (volume (Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-cube_side) cube_side))).toReal
          = ∏ i : Fin n, (cube_side - (-cube_side)) := by
      simpa using
        (Real.volume_pi_Ioo_toReal
          (ι := Fin n)
          (a := fun _ => -cube_side)
          (b := fun _ => cube_side)
          h_cube_side_le)
    -- simplify ∏ (cube_side - (-cube_side)) = ∏ (2 * cube_side) = (2 * cube_side)^n
    have hprod :
        ∏ i : Fin n, (cube_side - (-cube_side)) = (2 * cube_side) ^ (n : ℕ) := by
      have : ∏ i : Fin n, (cube_side - (-cube_side))
            = ∏ i : Fin n, (2 * cube_side) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        ring
      -- product of a constant over `Fin n` is that constant^n
      simp_all only [Real.volume_pi_Ioo_toReal, sub_neg_eq_add, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, nonneg_add_self_iff, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, ne_eq,
        PNat.ne_zero, not_false_eq_true, pow_left_inj₀]
    -- now rewrite volume C as volume of the `pi` set
    have h1 :
        (volume C).toReal
          = (volume (Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-cube_side) cube_side))).toReal := by
      congr 1
      -- `volume C` is measure on 𝔼 n, but the rhs is measure on Fin n → ℝ.
      -- Need to convert
      let Cpi : Set (Fin n → ℝ) := eucToPi '' C
      have : Cpi = Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-cube_side) cube_side) := by
        ext; aesop;
        · exact left i ( Set.mem_univ i ) |>.1;
        · exact left i ( Set.mem_univ i ) |>.2;
        · exact ⟨ piToEuc x, fun i _ => a i, by ext i; simp +decide [ eucToPi, piToEuc ] ⟩
      rw [← this]
      exact volume_euclideanSpace_eq_pi

    calc
      (volume C).toReal
        = (volume (Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-cube_side) cube_side))).toReal := by
          exact h1
      _ = ∏ i : Fin n, (cube_side - (-cube_side)) := hvol_pi
      _ = (2 * cube_side) ^ (n : ℕ) := hprod

  -- Step 5: vol(C) ≤ vol(B(0,1)) by monotonicity
  have h_le : (lebesgueMeasure C).toReal ≤ (lebesgueMeasure (Metric.ball (0 : 𝔼 n) 1)).toReal := by
    -- First on ENNReal level:
    have h_vol_C_le_vol_ball : volume C ≤ volume (Metric.ball (0 : 𝔼 n) 1) :=
      measure_mono hC_subset
    -- ball has finite volume
    have h_ball_finite :
        volume (Metric.ball (0 : 𝔼 n) 1) ≠ ∞ :=
      (measure_ball_lt_top : volume (Metric.ball (0 : 𝔼 n) 1) < ∞).ne
    have h_vol_C_finite:
      volume C ≠ ∞ := by
      exact measure_ne_top_of_subset hC_subset h_ball_finite
    -- Monotonicity of `toReal`
    exact (ENNReal.toReal_le_toReal h_vol_C_finite h_ball_finite ).mpr h_vol_C_le_vol_ball

  -- Step 6: Combine to get the bound
  calc (2 : ℝ) ^ (n : ℕ) / (Real.sqrt n) ^ (n : ℕ)
      = (2 / Real.sqrt n) ^ (n : ℕ) := by
        rw [div_pow]
      _ = (2 * cube_side) ^ (n : ℕ) := by
        congr 1
        field_simp [cube_side]
        aesop
      _ = (lebesgueMeasure C).toReal := by
        rw [← hvol_C]
      _ ≤ (lebesgueMeasure (Metric.ball (0 : 𝔼 n) 1)).toReal := h_le
      _ = unitBallVolume n := rfl
end

end LatticeCrypto.Utils.Geometry
