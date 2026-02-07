import LatticeCrypto.Foundations.Lattice.Integral
import LatticeCrypto.Foundations.Lattice.SuccessiveMinima
import LatticeCrypto.Foundations.Algorithms.Babai.Algorithm
import LatticeCrypto.Foundations.Lattice.Distance
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Nat.Log
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.LinearAlgebra
import LatticeCrypto.Utils.Vec


namespace LatticeCrypto.Foundations.Algorithms

namespace Babai

open scoped Real RealInnerProductSpace
open scoped Classical
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Foundations.Lattice
open LatticeCrypto.Foundations.Algorithms.LLL

variable {n k : ℕ+}

noncomputable section correctness

/-!
## Correctness Properties

The rounded vector is indeed in the lattice, and we can bound its distance from the target.
-/

/-- The result of babaiRound is a lattice vector (integer combination of basis vectors).

PROVIDED SOLUTION
The idea is that the `reduceAt` function modifies `t` by subtracting integer multiples of basis vectors,
and thus the final result `t - tReduced` is an integer combination of the basis vectors.
-/
theorem babaiRound_in_lattice (B : LatticeBasis n k) (t : 𝓔 n) :
    babaiRound t B.basis ∈ B.toLattice := by
  unfold babaiRound
  -- babaiRound produces ∑ⱼ round(cⱼ) • bⱼ where round(cⱼ) ∈ ℤ
  -- This is an integer combination of basis vectors, hence in the lattice
  classical
  set BStar := bStarFun B.basis
  set L := (List.finRange k.val).reverse
  set tReduced := L.foldl
    (fun acc (j : Fin k.val) => reduceAt B.basis BStar acc ⟨j.val, j.isLt⟩) t
  have h_fold :
      ∀ (L : List (Fin k.val)) (acc : 𝓔 n),
        (t - acc) ∈ Submodule.span ℤ (Set.range B.basis) →
        (t - L.foldl
          (fun acc (j : Fin k.val) => reduceAt B.basis BStar acc ⟨j.val, j.isLt⟩) acc)
          ∈ Submodule.span ℤ (Set.range B.basis) := by
    intro L
    induction L with
    | nil =>
        intro acc h
        simpa using h
    | cons j L ih =>
        intro acc h
        let j' : Fin k := ⟨j.val, j.isLt⟩
        have h_base : B.basis j' ∈ Submodule.span ℤ (Set.range B.basis) :=
          Submodule.subset_span (Set.mem_range_self j')
        have h_coeff :
            (roundZ (⟪acc, BStar j'⟫ / ⟪BStar j', BStar j'⟫) : ℝ) • B.basis j' ∈
              Submodule.span ℤ (Set.range B.basis) := by
          have h_zsmul :
              (roundZ (⟪acc, BStar j'⟫ / ⟪BStar j', BStar j'⟫)) • B.basis j' ∈
                Submodule.span ℤ (Set.range B.basis) :=
            Submodule.smul_mem (Submodule.span ℤ (Set.range B.basis)) _ h_base
          simpa [Int.cast_smul_eq_zsmul] using h_zsmul
        have h_step :
            (t - reduceAt B.basis BStar acc j') ∈ Submodule.span ℤ (Set.range B.basis) := by
          have h_add :
              (t - acc) +
                (roundZ (⟪acc, BStar j'⟫ / ⟪BStar j', BStar j'⟫) : ℝ) • B.basis j' ∈
                  Submodule.span ℤ (Set.range B.basis) :=
            Submodule.add_mem (Submodule.span ℤ (Set.range B.basis)) h h_coeff
          -- rewrite t - reduceAt in terms of the previous remainder and the correction term
          have h_eq :
              t - reduceAt B.basis BStar acc j' =
                (t - acc) +
                  (roundZ (⟪acc, BStar j'⟫ / ⟪BStar j', BStar j'⟫) : ℝ) • B.basis j' := by
            simp [reduceAt, sub_eq_add_neg, add_assoc, add_comm]
          simpa [h_eq] using h_add
        exact ih _ h_step
  have h0 : (t - t) ∈ Submodule.span ℤ (Set.range B.basis) := by
    simp
  have h_span : t - tReduced ∈ Submodule.span ℤ (Set.range B.basis) := by
    simpa [tReduced] using (h_fold L t h0)
  -- convert span membership to lattice membership
  rw [EuclideanLattice.mem_def, B.toLattice.carrier_eq]
  simpa [LatticeBasis.cols] using h_span

/-- The output of Babai's algorithm is a lattice vector. -/
theorem babaiNearestPlane_in_lattice (B : LatticeBasis n k) (t : 𝓔 n) :
    babaiNearestPlane t B ∈ B.toLattice := by
  unfold babaiNearestPlane
  -- LLL preserves the lattice, and babaiRound produces a lattice vector
  let numIters := LLL_sufficient_iters B δ34
  have h_lll : (LLL_impl numIters B δ34).toLattice ≡ᵤ B.toLattice := LLL_equiv B δ34 numIters
  let B' := LLL_impl numIters B δ34
  have h_mem : babaiRound t B'.basis ∈ B'.toLattice := by
    simpa [B'] using (babaiRound_in_lattice (B := B') (t := t))
  have h_carrier : B'.toLattice.carrier = B.toLattice.carrier := by
    simpa [B', EuclideanLattice.CarrierEquiv] using h_lll
  -- rewrite membership via carrier equivalence
  rw [EuclideanLattice.mem_def]
  rw [← h_carrier]
  simpa [EuclideanLattice.mem_def] using h_mem

/-- The `babaiReduce` operation preserves the distance to the lattice.

PROVIDED SOLUTION
The idea is that `babaiReduce` modifies the target `t` by subtracting integer multiples of basis vectors,
which does not change the distance to the lattice by theorem `Lattice.distanceToLattice_translation_invariant`
-/
theorem babaiReduce_preserve_distanceToLattice (B : LatticeBasis n k) (t : 𝓔 n) :
    let L := B.toLattice
    let s := babaiReduce t B.basis
    L.distanceToLattice s = L.distanceToLattice t := by
  dsimp
  let L := B.toLattice
  let s := babaiReduce t B.basis
  have hs : t - s ∈ L := by
    simpa [babaiRound, L, s] using (babaiRound_in_lattice (B := B) (t := t))
  have htrans :
      L.distanceToLattice (s + (t - s)) = L.distanceToLattice s :=
    distanceToLattice_translation_invariant (L := L) (t := s) (v := t - s) hs
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htrans.symm

end correctness

end Babai

end LatticeCrypto.Foundations.Algorithms
