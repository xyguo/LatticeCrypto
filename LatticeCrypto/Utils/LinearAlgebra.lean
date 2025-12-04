import Mathlib.Algebra.Group.Subgroup.Defs     -- For AddSubgroup
import Mathlib.Analysis.Normed.Group.Basic      -- For NormedAddCommGroup
import Mathlib.Topology.Algebra.Group.Basic      -- For the subspace topology on AddSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup
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

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Convex

open scoped ENNReal NNReal Pointwise
open MeasureTheory
open RealInnerProductSpace
open Classical
open Module
open FiniteDimensional


variable {n k : ℕ+}

/-- Notation for n-dimensional Euclidean space over ℝ. -/
private abbrev 𝔼 (n : ℕ+) := EuclideanSpace ℝ (Fin n)


/-!
# Utility Functions

This module provides utility functions for mathematical analysis on lattice.
Many are light wrappers around Mathlib functions.

## Main components
* `Geometry` (**This file**) - handy lemmas in Euclidean geometry
* `LinearAlgebra` - handy lemmas in Euclidean geometry
* `Algebra.Ring` - Lemmas in ring theory
* `Algebra.Module` - Lemmas in module theory
* `Algebra.Polynomial` - Lemmas in polynomial rings
-/

namespace LatticeCrypto.Utils.LinearAlgebra

noncomputable section

lemma Z_linearIndependent_if_R_linearIndependent {v : Fin k → 𝔼 n} (li : LinearIndependent ℝ v) : LinearIndependent ℤ v := by
  have h_int_lin_ind : ∀ (c : Fin k → ℤ), (∑ i, c i • v i = 0) → (∀ i, c i = 0) := by
    intros c hc
    have h_real : ∑ i, (c i : ℝ) • v i = 0 := by
      convert hc using 1
      congr! 2
      ext; simp
    exact fun i => by have := Fintype.linearIndependent_iff.mp li (c ·) h_real i; aesop
  rw [Fintype.linearIndependent_iff]; aesop

lemma Q_linearIndependent_if_R_linearIndependent {v : Fin k → 𝔼 n} (li : LinearIndependent ℝ v) : LinearIndependent ℚ v := by
  have h_int_lin_ind : ∀ (c : Fin k → ℚ), (∑ i, c i • v i = 0) → (∀ i, c i = 0) := by
    intros c hc
    have h_real : ∑ i, (c i : ℝ) • v i = 0 := by
      convert hc using 1
    exact fun i => by have := Fintype.linearIndependent_iff.mp li (c ·) h_real i; aesop
  rw [Fintype.linearIndependent_iff]; aesop

/-!
## Discrete Z-Span Theorem
-/

/-- Proof that any linearly independent set of k (k ≤ n) vectors over ℝⁿ has a discrete Z-span -/
theorem discrete_zspan {v : Fin k → 𝔼 n} (li : LinearIndependent ℝ v) :
    DiscreteTopology (Submodule.span ℤ (Set.range v) : Submodule ℤ (𝔼 n)) := by
  -- 1. Extend v to a basis v' of ℝⁿ
  have hli : LinearIndepOn ℝ id (Set.range v) := LinearIndependent.linearIndepOn_id li
  let v' := Basis.extend hli

  -- 2. Use the previous lemma to show that the z-span of v' is discrete
  have discrete_v' : DiscreteTopology ↥(Submodule.span ℤ (Set.range v')) := inferInstance

  -- 3. Show that the z-span of v is a subset of the z-span of v'
  have h_subset : (Submodule.span ℤ (Set.range v)) ≤ (Submodule.span ℤ (Set.range v')) := by
    apply Submodule.span_mono
    intro x hx
    obtain ⟨i, hi⟩ := hx
    use ⟨v i, by
      apply hli.subset_extend
      use i⟩
    generalize_proofs at *
    simp [v', hi]

  -- 4. Conclude that the z-span of v is discrete
  exact DiscreteTopology.of_subset discrete_v' h_subset

end

end LatticeCrypto.Utils.LinearAlgebra
