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
import Mathlib.Data.Set.Card

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

noncomputable section min_norm

/-- Minimum norm among a finite family of vectors, to be the minimum norm of
assuming the index set is nonempty. -/
def minNorm
    {V : Type*} [Norm V]
    (f : Fin k → V) : ℝ :=
  Finset.min' (Finset.image (fun i => ‖f i‖) Finset.univ) (by
    rw [Finset.image_nonempty]
    exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp k.pos)
  )

/-- One can find an index achieving the minNorm-/
noncomputable def argminNorm
    {V : Type*} [Norm V]
    (f : Fin k → V) : Fin k :=
  let h_nonempty : (Finset.univ : Finset (Fin k)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp k.pos)
  -- Finset.exists_min_image proves there exists an index i minimizing the function
  Classical.choose (Finset.exists_min_image Finset.univ (fun i ↦ ‖f i‖) h_nonempty)

/-- The minNorm among a finite family of vectors is no more than the norm of any vector from the family. -/
lemma minNorm_le
    {V : Type*} [Norm V]
    (f : Fin k → V) (i : Fin k) :
    minNorm f ≤ ‖f i‖ := by
  unfold minNorm
  apply Finset.min'_le
  rw [Finset.mem_image]
  use i
  simp only [Finset.mem_univ, true_and]

/-- The minimum norm among a finite family of vectors is equal to the norm at the argmin of the minNorm. -/
lemma minNorm_eq_norm_argmin
    {V : Type*} [Norm V]
    (f : Fin k → V) :
    minNorm f = ‖f (argminNorm f)‖ := by
  unfold minNorm argminNorm;
  refine' le_antisymm _ _;
  · exact Finset.min'_le _ _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) );
  · have := Classical.choose_spec ( Finset.exists_min_image Finset.univ ( fun i => ‖f i‖ ) ( Finset.univ_nonempty ) );
    aesop

/-- The norm at the argmin is less than or equal to the norm of any other vector. -/
lemma norm_argmin_le
    {V : Type*} [Norm V]
    (f : Fin k → V) (i : Fin k) :
    ‖f (argminNorm f)‖ ≤ ‖f i‖ := by
  unfold argminNorm
  have h_nonempty : (Finset.univ : Finset (Fin k)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp k.pos)
  have h_min := Classical.choose_spec (Finset.exists_min_image Finset.univ (fun i ↦ ‖f i‖) h_nonempty)
  exact h_min.2 i (Finset.mem_univ i)

/-- The minimum column norm of a matrix. -/
def Matrix.minColumnNorm
    (A : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  minNorm (fun j => fun i => A i j)

def Matrix.argminColumn
    (A : Matrix (Fin n) (Fin k) ℝ) : Fin k :=
  argminNorm (fun j => fun i => A i j)

end min_norm

/-!
# Some handy results regarding linear independence
-/
noncomputable section independence

lemma Z_linearIndependent_if_R_linearIndependent {v : Fin k → Fin n → ℝ} (li : LinearIndependent ℝ v) : LinearIndependent ℤ v := by
  have h_int_lin_ind : ∀ (c : Fin k → ℤ), (∑ i, c i • v i = 0) → (∀ i, c i = 0) := by
    intros c hc
    have h_real : ∑ i, (c i : ℝ) • v i = 0 := by
      convert hc using 1
      congr! 2
      ext; simp
    exact fun i => by have := Fintype.linearIndependent_iff.mp li (c ·) h_real i; aesop
  rw [Fintype.linearIndependent_iff]; aesop

lemma Q_linearIndependent_if_R_linearIndependent {v : Fin k → Fin n → ℝ} (li : LinearIndependent ℝ v) : LinearIndependent ℚ v := by
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
    DiscreteTopology (Submodule.span ℤ (Set.range v) : Submodule ℤ (Fin n → ℝ)) := by
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

theorem exists_finset_eq_card {α} {n : ℕ} (h : n ≤ Cardinal.mk α) :
    ∃ s : Finset α, n = s.card := by
  obtain hα|hα := finite_or_infinite α
  · let hα := Fintype.ofFinite α
    obtain ⟨t, -, rfl⟩ := @Finset.exists_subset_card_eq α .univ n <| by simpa using h
    exact ⟨t, rfl⟩
  · obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
    exact ⟨s, hs.symm⟩

/- This is a copy of theorem from Mathlib v2025-11-27 -/
theorem le_rank_iff_exists_finset {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M] [Nontrivial R] {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ s : Finset M, s.card = n ∧ LinearIndepOn R id (s : Set M) where
  mp le := by
    contrapose! le
    obtain _ | n := n; · simp at le
    rw [Module.rank, Cardinal.nat_succ, Order.lt_succ_iff, ciSup_le_iff (Cardinal.bddAbove_range _)]
    intro s
    contrapose! le
    rw [← Order.succ_le_iff, ← Cardinal.nat_succ] at le
    have ⟨t, ht⟩ := exists_finset_eq_card le
    exact ⟨t.map (.subtype _), by simpa using ht.symm, s.2.mono <| by simp⟩
  mpr := fun ⟨s, card_s, ind_s⟩ ↦ ind_s.cardinal_le_rank'.trans_eq' <| by simp [card_s]

/- This is a copy of theorem from Mathlib v2025-11-27 -/
theorem le_rank_iff {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M] [Nontrivial R] {n : ℕ} : n ≤ Module.rank R M ↔ ∃ v : Fin n → M, LinearIndependent R v := by
  refine le_rank_iff_exists_finset.trans ⟨fun ⟨s, s_card, s_ind⟩ ↦ ?_, fun ⟨v, v_ind⟩ ↦ ?_⟩
  · exact ⟨_, s_ind.comp _ (s.equivFinOfCardEq s_card).symm.injective⟩
  · refine ⟨.map ⟨_, v_ind.injective⟩ .univ, by simp, ?_⟩
    simpa using (linearIndepOn_id_range_iff v_ind.injective).mpr v_ind

lemma rank_span_ge_iff_subset {V : Type*} [AddCommGroup V] [Module ℝ V] (s : Set V) (k : ℕ) :
    k ≤ Module.rank ℝ (Submodule.span ℝ s) ↔
    ∃ t : Finset V, t.card = k ∧ ↑t ⊆ s ∧ LinearIndependent ℝ (fun x : t => (x : V)) := by
      bound;
      · -- By definition of rank, there exists a linearly independent subset of s with cardinality equal to the rank.
        obtain ⟨t, ht⟩ : ∃ t : Set V, t ⊆ s ∧ LinearIndependent ℝ (fun x : t => (x : V)) ∧ Cardinal.mk t = Module.rank ℝ (Submodule.span ℝ s) := by
          have := exists_linearIndependent ℝ s;
          obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := this; use t; aesop;
          rw [ ← ht₂, rank_span_set ht₃ ];
        -- Since $k \leq \text{rank}(\text{span}(s))$, there exists a subset $t' \subseteq t$ with $|t'| = k$.
        obtain ⟨t', ht'⟩ : ∃ t' : Set V, t' ⊆ t ∧ Cardinal.mk t' = k := by
          have := ht.2.2 ▸ a;
          exact Cardinal.le_mk_iff_exists_subset.mp this;
        -- Since $t'$ is a subset of $t$ with cardinality $k$, we can convert it to a finset.
        obtain ⟨t_fin, ht_fin⟩ : ∃ t_fin : Finset V, t_fin = t' ∧ t_fin.card = k := by
          have h_finite : Set.Finite t' := by
            exact Set.finite_coe_iff.mp ( Cardinal.lt_aleph0_iff_finite.mp ( ht'.2.symm ▸ Cardinal.nat_lt_aleph0 k ) );
          have := h_finite.exists_finset_coe; aesop;
        refine' ⟨ t_fin, ht_fin.2, _, _ ⟩ <;> aesop;
        · exact Set.Subset.trans left_1 left;
        · convert left_3.comp _ _;
          rotate_left;
          exacts [ fun x => ⟨ x.1, left_1 x.2 ⟩, fun x y h => by simpa [ Subtype.ext_iff ] using h, rfl ];
      · -- Since $w$ is a subset of $s$, the span of $w$ is a subspace of the span of $s$.
        have h_subspace : Submodule.span ℝ w ≤ Submodule.span ℝ s := by
          exact Submodule.span_mono left_1;
        refine' le_trans _ ( Submodule.rank_mono h_subspace );
        rw [ rank_span_set ] ; aesop;
        exact right

end independence

end LatticeCrypto.Utils.LinearAlgebra
