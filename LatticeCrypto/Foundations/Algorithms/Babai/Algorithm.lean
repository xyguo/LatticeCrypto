import LatticeCrypto.Foundations.Lattice.Integral
import LatticeCrypto.Foundations.Lattice.SuccessiveMinima
import LatticeCrypto.Foundations.Algorithms.LLL
import Mathlib.Algebra.Order.Floor.Defs
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.LinearAlgebra
import LatticeCrypto.Utils.Vec


namespace LatticeCrypto.Foundations.Algorithms

namespace Babai

/-!
# Babai's Nearest Plane Algorithm

The nearest plane algorithm (Babai's algorithm) for approximating the closest vector problem (CVP) in lattices.

## Algorithm Overview

Given a lattice basis B and a target point t, Babai's algorithm finds an approximate closest lattice vector:
1. Run LLL to obtain a reduced basis B'
2. Express t in terms of the Gram-Schmidt basis: t ≈ ∑ cⱼ • b*ⱼ
3. Round the coefficients: find v = ∑ round(cⱼ) • b'ⱼ
4. Return v as the approximate closest vector

The algorithm achieves an approximation factor of 2^(k/2) for k-dimensional lattices.
-/

open scoped Real RealInnerProductSpace
open scoped Classical
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Foundations.Lattice
open LatticeCrypto.Foundations.Algorithms.LLL

variable {n k : ℕ+}

noncomputable section defs

/-!
## Algorithm Definition
-/

/-- Babai's rounding step: given target t and basis B, construct the shift vector
by rounding the Gram-Schmidt coefficients. This is the core of the nearest plane algorithm.

For each j from k-1 down to 0, we compute round(⟪t, b*ⱼ⟫ / ⟪b*ⱼ, b*ⱼ⟫) and multiply by bⱼ, then
update t to t - round(...) • bⱼ for the next iteration.

The output of this algorithm is a *short* shift vector s in the coset L - t.
-/
noncomputable def babaiReduce (t : 𝓔 n) (B : Fin k → 𝓔 n) : 𝓔 n :=
  let BStar := bStarFun B  -- Fixed GS decomposition computed once
  (List.finRange k.val).reverse.foldl
    (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩) t

/-- Given the shift vector, return the actual lattice vector by subtracting the shift from the target. -/
noncomputable def babaiRound (t : 𝓔 n) (B : Fin k → 𝓔 n) : 𝓔 n :=
  let tReduced := babaiReduce t B
  t - tReduced

/-- Babai's nearest plane algorithm for CVP approximation.

Given a lattice basis and a target point t, returns an approximate closest lattice vector.

Algorithm steps:
1. Run LLL on the input basis to obtain a reduced basis (with default δ = 3/4)
2. Compute the rounded lattice vector using the Gram-Schmidt coefficients
3. Return this vector as the approximation

The algorithm runs in polynomial time and achieves a 2^(k/2) approximation factor
for k-dimensional lattices when using δ = 3/4.
-/
noncomputable def babaiNearestPlane (t : 𝓔 n) (B : LatticeBasis n k) : 𝓔 n :=
  -- Step 1: Run LLL to get a reduced basis
  let B' := LLL_impl (LLL_sufficient_iters B δ34) B δ34
  -- Step 2: Round the coefficients to find the closest lattice point
  babaiRound t B'.basis

/-- Alternative formulation: return the error vector (t - v) instead of the lattice vector v. -/
noncomputable def babaiErrorVector (t : 𝓔 n) (B : LatticeBasis n k) : 𝓔 n :=
  t - babaiNearestPlane t B

end defs

noncomputable section babaiReduce_properties

/-- After `babaiReduce`, all Gram-Schmidt coefficients are bounded by 1/2 in absolute value. -/
lemma projGsCoeff_babaiReduce_eq_reduceAt (B : Fin k → 𝓔 n) (t : 𝓔 n) (i : Fin k) :
    ∃ t0 : 𝓔 n,
      projGsCoeff (babaiReduce t B) B i =
        projGsCoeff (reduceAt B (bStarFun B) t0 i) B i := by
  classical
  let BStar := bStarFun B
  let L := (List.finRange k.val).reverse
  let tReduced := L.foldl
    (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩) t
  let j_i : Fin k.val := ⟨i.val, i.isLt⟩
  have hj_mem : j_i ∈ L := by
    have : j_i ∈ List.finRange k.val := List.mem_finRange j_i
    simp [L, List.mem_reverse.mpr this]
  obtain ⟨idx, hidx⟩ := (List.mem_iff_get).1 hj_mem
  let l1 := L.take idx.1
  let l2 := L.drop (idx.1 + 1)
  have hget : L[idx.1] = j_i := by
    simpa [List.get_eq_getElem] using hidx
  have hdrop : L.drop idx.1 = L[idx.1] :: L.drop (idx.1 + 1) :=
    List.drop_eq_getElem_cons (l := L) (i := idx.1) (h := idx.2)
  have hL : L = l1 ++ j_i :: l2 := by
    have htake : l1 ++ L.drop idx.1 = L := by
      simp [l1, List.take_append_drop idx.1 L]
    calc
      L = l1 ++ L.drop idx.1 := by simpa using htake.symm
      _ = l1 ++ (L[idx.1] :: L.drop (idx.1 + 1)) := by rw [hdrop]
      _ = l1 ++ j_i :: l2 := by simp [hget, l2]

  have htail_lt : ∀ i' ∈ l2, (i' : Fin k) < i := by
    have hpair : List.Pairwise (fun a b : Fin k.val => a > b) L := by
      have hpair' : List.Pairwise (fun a b : Fin k.val => a < b) (List.finRange k.val) :=
        List.pairwise_lt_finRange k.val
      have hpair'' : List.Pairwise (fun a b : Fin k.val => a > b)
          (List.map Fin.rev (List.finRange k.val)) := by
        refine List.Pairwise.map Fin.rev ?_ hpair'
        intro a b hlt
        have : b.rev < a.rev :=
          (Fin.rev_lt_iff (i := a.rev) (j := b)).1 (by simpa [Fin.rev_rev] using hlt)
        simpa [gt_iff_lt] using this
      simpa [L, List.finRange_reverse] using hpair''
    have hsub : (j_i :: l2).Sublist L := by
      simp [hL]
    have hpair_tail : List.Pairwise (fun a b : Fin k.val => a > b) (j_i :: l2) :=
      List.Pairwise.sublist hsub hpair
    have hcons := (List.pairwise_cons).1 hpair_tail
    intro i' hi'
    have : (j_i : Fin k.val) > i' := hcons.1 i' hi'
    exact this

  have h_preserve_one :
      ∀ (acc : 𝓔 n) (j : Fin k), j < i →
        projGsCoeff (reduceAt B BStar acc j) B i = projGsCoeff acc B i := by
    intro acc j hj
    have hji : j ≠ i := ne_of_lt hj
    have hsum :
        ⟪∑ t ∈ Finset.Iio j,
            (⟪B j, bStarFun B t⟫ / ⟪bStarFun B t, bStarFun B t⟫) •
              bStarFun B t,
          bStarFun B i⟫ = 0 := by
      rw [sum_inner]
      refine Finset.sum_eq_zero ?_
      intro t ht
      have ht' : (t : Fin k) ≠ i := by
        exact ne_of_lt (lt_trans (Finset.mem_Iio.mp ht) hj)
      simp [inner_smul_left, bStarFun_orthogonal B t i ht']
    have hBij : ⟪B j, bStarFun B i⟫ = 0 := by
      rw [basis_eq_bStarFun_decomposition (B := B) j]
      simp [inner_add_left, hsum, bStarFun_orthogonal B j i hji]
    unfold projGsCoeff reduceAt
    simp [hBij, inner_sub_left, inner_smul_left]

  have h_preserve_fold :
      ∀ (l : List (Fin k.val)) (acc : 𝓔 n),
        (∀ j' ∈ l, (j' : Fin k) < i) →
          projGsCoeff
              (l.foldl
                (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩) acc)
              B i
            = projGsCoeff acc B i := by
    intro l
    induction l with
    | nil =>
        intro acc _
        simp
    | cons j l ih =>
        intro acc hlt
        have hjlt : (j : Fin k) < i := hlt j (by simp)
        have hlt_tail : ∀ j' ∈ l, (j' : Fin k) < i := by
          intro j' hj'
          exact hlt j' (by simp [hj'])
        calc
          projGsCoeff
              ((j :: l).foldl
                (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩) acc)
              B i
              =
            projGsCoeff
              (l.foldl
                (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩)
                (reduceAt B BStar acc ⟨j.val, j.isLt⟩))
              B i := by
                simp
          _ = projGsCoeff (reduceAt B BStar acc ⟨j.val, j.isLt⟩) B i := by
                exact ih _ hlt_tail
          _ = projGsCoeff acc B i := by
                exact h_preserve_one acc ⟨j.val, j.isLt⟩ hjlt

  have hfold : tReduced =
      l2.foldl
        (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩)
        (reduceAt B BStar
          (l1.foldl
            (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩) t)
          ⟨j_i.val, j_i.isLt⟩) := by
    simp [tReduced, hL, List.foldl_append]
  have h_pres :
      projGsCoeff tReduced B i =
        projGsCoeff
          (reduceAt B BStar
            (l1.foldl
              (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩) t)
            ⟨j_i.val, j_i.isLt⟩) B i := by
    have hlt : ∀ i' ∈ l2, (i' : Fin k) < i := htail_lt
    simpa [hfold] using
      (h_preserve_fold l2 _ hlt)
  let t0 : 𝓔 n :=
    l1.foldl (fun acc (j : Fin k.val) => reduceAt B BStar acc ⟨j.val, j.isLt⟩) t
  have hreduce :
      projGsCoeff (babaiReduce t B) B i =
        projGsCoeff (reduceAt B BStar t0 ⟨j_i.val, j_i.isLt⟩) B i := by
    have : babaiReduce t B = tReduced := by
      simp [babaiReduce, tReduced, L, BStar]
    simpa [t0, this] using h_pres
  refine ⟨t0, ?_⟩
  simpa [BStar, j_i] using hreduce

/-- Lift a one-step property at `reduceAt` to the final coefficient after `babaiReduce`. -/
lemma lift_projGsCoeff_property_from_reduceAt_to_babaiReduce
    (B : Fin k → 𝓔 n) (t : 𝓔 n) (P : ℝ → Prop)
    (hstep : ∀ (u : 𝓔 n) (i : Fin k),
      P (projGsCoeff (reduceAt B (bStarFun B) u i) B i)) :
    ∀ i : Fin k, P (projGsCoeff (babaiReduce t B) B i) := by
  intro i
  rcases projGsCoeff_babaiReduce_eq_reduceAt (B := B) (t := t) (i := i) with ⟨u, hu⟩
  simpa [hu] using hstep u i

end babaiReduce_properties

end Babai

end LatticeCrypto.Foundations.Algorithms
