import LatticeCrypto.Foundations.Algorithms.LLL.Defs
import LatticeCrypto.Foundations.Algorithms.LLL.Algorithm

namespace LatticeCrypto.Foundations.Algorithms

open scoped Real RealInnerProductSpace BigOperators
open scoped Classical
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Foundations.Lattice

variable {n k : ℕ+}

namespace LLL

noncomputable section correctness
/-!
## Correctness theorems:
  Theorems stating that the reduced basis is still a basis of the same lattice && satisfies the LLL conditions.
  * Theorem `sizeReduce_sizeReduced`: the `sizeReduce` function produces a size-reduced basis.
  * Theorem `sizeReduce_equiv`: the `sizeReduce` function preserves the lattice.
  * Theorem `swapAdjacent_equiv`: the `swapAdjacent` function preserves the lattice.
  * Theorem `LLL_equiv`: the `LLL` function preserves the lattice.

  Ideally, there should be a theorem `LLL_LLLReduced` stating that the output of `LLL` is indeed LLL-reduced, but that would first require us to show that the algorithm terminates, which is done in `LatticeCrypto.Foundations.Algorithms.LLL.Runtime`.
-/

/- `sizeReduceStep` preserves the Gram-Schmidt of the basis being reduced. -/
noncomputable section AristotleLemmas

lemma span_sizeReduceStep_eq (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i) (m : Fin k) :
    Submodule.span ℝ (sizeReduceStep B BStar i j '' Set.Iio m) = Submodule.span ℝ (B '' Set.Iio m) := by
      refine' le_antisymm ( Submodule.span_le.mpr _ ) ( Submodule.span_le.mpr _ );
      · rintro _ ⟨ x, hx, rfl ⟩;
        unfold LatticeCrypto.Foundations.Algorithms.LLL.sizeReduceStep;
        by_cases h : x = i <;> simp_all +decide [ Function.update_apply ];
        · exact Submodule.sub_mem _ ( Submodule.subset_span ⟨ i, hx, rfl ⟩ ) ( Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ j, lt_trans hij hx, rfl ⟩ ) );
        · exact Submodule.subset_span ⟨ x, hx, rfl ⟩;
      · rintro _ ⟨ x, hx, rfl ⟩ ; by_cases hx' : x = i <;> simp_all +decide [ LatticeCrypto.Foundations.Algorithms.LLL.sizeReduceStep ] ;
        · have h_lin_comb : B i = (LatticeCrypto.Foundations.Algorithms.LLL.reduceAt B BStar (B i) j) + (roundZ (projCoeff (B i) BStar j) : ℝ) • B j := by
            exact Eq.symm (add_eq_of_eq_sub rfl);
          rw [ h_lin_comb ];
          refine' Submodule.add_mem _ _ _;
          · refine' Submodule.subset_span ⟨ i, _, _ ⟩ <;> simp +decide ;
            · exact hx;
            · unfold LatticeCrypto.Foundations.Algorithms.LLL.reduceAt; simp +decide  ;
          · refine' Submodule.smul_mem _ _ _;
            exact Submodule.subset_span ⟨ j, by simpa using hij.trans hx, by simp +decide [ hij.ne ] ⟩;
        · exact Submodule.subset_span ⟨ x, hx, by aesop ⟩

lemma gramSchmidt_step_eq {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : ι → E) (i : ι)
    (h_diff : f i - g i ∈ Submodule.span ℝ (f '' Set.Iio i))
    (h_prev : ∀ j < i, InnerProductSpace.gramSchmidt ℝ f j = InnerProductSpace.gramSchmidt ℝ g j) :
    InnerProductSpace.gramSchmidt ℝ f i = InnerProductSpace.gramSchmidt ℝ g i := by
      -- By definition of Gram-Schmidt orthogonalization, we have:
      have h_gram_schmidt_def : ∀ (f : ι → E), InnerProductSpace.gramSchmidt ℝ f i = f i - ∑ j ∈ Finset.Iio i, (⟪f i, InnerProductSpace.gramSchmidt ℝ f j⟫ / ⟪InnerProductSpace.gramSchmidt ℝ f j, InnerProductSpace.gramSchmidt ℝ f j⟫) • InnerProductSpace.gramSchmidt ℝ f j := by
        intro f
        rw [InnerProductSpace.gramSchmidt];
        refine' congr rfl ( Finset.sum_bij ( fun j _ => j ) _ _ _ _ ) <;> simp +decide;
        intro j hj; rw [ Submodule.starProjection ] ;
        simp +decide [ Submodule.starProjection_singleton ];
        rw [ real_inner_comm, real_inner_self_eq_norm_sq ];
      -- Since $f_i - g_i$ is in the span of $\{f_j \mid j < i\}$, it is also in the span of $\{u_j \mid j < i\}$ where $u_j = \text{gramSchmidt } f j$.
      have h_span : f i - g i ∈ Submodule.span ℝ (Set.image (fun j => InnerProductSpace.gramSchmidt ℝ f j) (Set.Iio i)) := by
        have h_span : Submodule.span ℝ (Set.image f (Set.Iio i)) = Submodule.span ℝ (Set.image (fun j => InnerProductSpace.gramSchmidt ℝ f j) (Set.Iio i)) := by
          exact Eq.symm (InnerProductSpace.span_gramSchmidt_Iio ℝ f i);
        exact h_span ▸ h_diff;
      -- Since $f_i - g_i$ is in the span of $\{u_j \mid j < i\}$, we have $\sum_{j < i} \frac{\langle f_i - g_i, u_j \rangle}{\langle u_j, u_j \rangle} u_j = f_i - g_i$.
      have h_sum : ∑ j ∈ Finset.Iio i, (⟪f i - g i, InnerProductSpace.gramSchmidt ℝ f j⟫ / ⟪InnerProductSpace.gramSchmidt ℝ f j, InnerProductSpace.gramSchmidt ℝ f j⟫) • InnerProductSpace.gramSchmidt ℝ f j = f i - g i := by
        have h_sum : ∀ (v : E), v ∈ Submodule.span ℝ (Set.image (fun j => InnerProductSpace.gramSchmidt ℝ f j) (Set.Iio i)) → ∑ j ∈ Finset.Iio i, (⟪v, InnerProductSpace.gramSchmidt ℝ f j⟫ / ⟪InnerProductSpace.gramSchmidt ℝ f j, InnerProductSpace.gramSchmidt ℝ f j⟫) • InnerProductSpace.gramSchmidt ℝ f j = v := by
          intro v hv;
          -- By definition of span, we can write v as a linear combination of the gramSchmidt vectors.
          obtain ⟨c, hc⟩ : ∃ c : ι → ℝ, v = ∑ j ∈ Finset.Iio i, c j • InnerProductSpace.gramSchmidt ℝ f j := by
            rw [ Finsupp.mem_span_image_iff_linearCombination ] at hv;
            obtain ⟨ l, hl₁, hl₂ ⟩ := hv;
            rw [ ← hl₂, Finsupp.linearCombination_apply ];
            rw [ Finsupp.sum_of_support_subset ] <;> aesop_cat;
          -- By definition of inner product, we can expand the inner product of v with each gramSchmidt vector.
          have h_inner_expand : ∀ j ∈ Finset.Iio i, ⟪v, InnerProductSpace.gramSchmidt ℝ f j⟫ = c j * ⟪InnerProductSpace.gramSchmidt ℝ f j, InnerProductSpace.gramSchmidt ℝ f j⟫ := by
            intro j hj
            rw [hc]
            rw [ sum_inner, Finset.sum_eq_single j ] <;> simp +contextual [ inner_smul_left ];
            · intro k hk hne; rw [ InnerProductSpace.gramSchmidt_orthogonal ] ; aesop;
              exact hne;
            · exact fun h => False.elim <| h.not_gt <| Finset.mem_Iio.mp hj;
          rw [ hc, Finset.sum_congr rfl ];
          intro j hj;
          by_cases h : ⟪InnerProductSpace.gramSchmidt ℝ f j, InnerProductSpace.gramSchmidt ℝ f j⟫ = 0 <;> simp_all +decide [ div_eq_mul_inv ];
        exact h_sum _ h_span;
      simp_all +decide ;
      rw [ show ( ∑ j ∈ Finset.Iio i, ( ⟪f i, InnerProductSpace.gramSchmidt ℝ f j⟫ / ⟪InnerProductSpace.gramSchmidt ℝ f j, InnerProductSpace.gramSchmidt ℝ f j⟫ ) • InnerProductSpace.gramSchmidt ℝ f j ) = ( ∑ j ∈ Finset.Iio i, ( ⟪f i - g i, InnerProductSpace.gramSchmidt ℝ f j⟫ / ⟪InnerProductSpace.gramSchmidt ℝ f j, InnerProductSpace.gramSchmidt ℝ f j⟫ ) • InnerProductSpace.gramSchmidt ℝ f j ) + ( ∑ j ∈ Finset.Iio i, ( ⟪g i, InnerProductSpace.gramSchmidt ℝ f j⟫ / ⟪InnerProductSpace.gramSchmidt ℝ f j, InnerProductSpace.gramSchmidt ℝ f j⟫ ) • InnerProductSpace.gramSchmidt ℝ f j ) from ?_ ];
      · rw [ h_sum ];
        rw [ show ( ∑ j ∈ Finset.Iio i, ( ⟪g i, InnerProductSpace.gramSchmidt ℝ f j⟫ / ⟪InnerProductSpace.gramSchmidt ℝ f j, InnerProductSpace.gramSchmidt ℝ f j⟫ ) • InnerProductSpace.gramSchmidt ℝ f j ) = ∑ j ∈ Finset.Iio i, ( ⟪g i, InnerProductSpace.gramSchmidt ℝ g j⟫ / ⟪InnerProductSpace.gramSchmidt ℝ g j, InnerProductSpace.gramSchmidt ℝ g j⟫ ) • InnerProductSpace.gramSchmidt ℝ g j from Finset.sum_congr rfl fun j hj => ?_ ];
        · abel1;
        · rw [ h_prev j ( Finset.mem_Iio.mp hj ) ];
      · rw [ ← Finset.sum_add_distrib ] ; congr ; ext j ; simp +decide [ sub_eq_add_neg, inner_add_left ] ; ring_nf;
        simp +decide [ sub_smul ]

lemma sizeReduceStep_diff_mem_span (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i) (m : Fin k) :
    sizeReduceStep B BStar i j m - B m ∈ Submodule.span ℝ (sizeReduceStep B BStar i j '' Set.Iio m) := by
      by_cases hm : m = i <;> simp_all +decide [ LatticeCrypto.Foundations.Algorithms.LLL.sizeReduceStep ];
      simp +decide [ hm, Function.update_apply ];
      simp +decide [ LatticeCrypto.Foundations.Algorithms.LLL.reduceAt ];
      refine' Submodule.smul_mem _ _ _;
      refine' Submodule.subset_span ⟨ j, _, _ ⟩ <;> aesop

end AristotleLemmas


/-- `sizeReduceStep` preserves the Gram-Schmidt of the basis being reduced. -/
lemma sizeReduceStep_preserve_GS (B : Fin k → 𝓔 n)
    (i j : Fin k) (hij : j < i) :
    let B' := sizeReduceStep B (bStarFun B) i j
    ∀ m : Fin k, bStarFun B' m = bStarFun B m := by
  -- Apply `gramSchmidt_step_eq` with `f = B'` and `g = B`.
  intros B' m; exact gramSchmidt_step_eq (fun m => B' m) (fun m => B m) m (sizeReduceStep_diff_mem_span B (bStarFun B) i j hij m) (by
  -- Apply `gramSchmidt_step_eq` with `f = B'` and `g = B`, using the conditions we've verified.
  apply Classical.byContradiction
  intro h_contra;
  -- Let `m` be the smallest index such that `gramSchmidt ℝ B' m ≠ gramSchmidt ℝ B m`.
  obtain ⟨m, hm⟩ : ∃ m, ¬(InnerProductSpace.gramSchmidt ℝ (fun m => B' m) m = InnerProductSpace.gramSchmidt ℝ (fun m => B m) m) ∧ ∀ j < m, InnerProductSpace.gramSchmidt ℝ (fun m => B' m) j = InnerProductSpace.gramSchmidt ℝ (fun m => B m) j := by
    obtain ⟨m, hm⟩ : ∃ m, ¬(InnerProductSpace.gramSchmidt ℝ (fun m => B' m) m = InnerProductSpace.gramSchmidt ℝ (fun m => B m) m) := by
      exact not_forall.mp fun h => h_contra fun j hj => h j;
    exact ⟨ Finset.min' ( Finset.univ.filter fun m => ¬InnerProductSpace.gramSchmidt ℝ ( fun m => B' m ) m = InnerProductSpace.gramSchmidt ℝ ( fun m => B m ) m ) ⟨ m, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hm ⟩ ⟩, Finset.mem_filter.mp ( Finset.min'_mem ( Finset.univ.filter fun m => ¬InnerProductSpace.gramSchmidt ℝ ( fun m => B' m ) m = InnerProductSpace.gramSchmidt ℝ ( fun m => B m ) m ) ⟨ m, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hm ⟩ ⟩ ) |>.2, fun j hj => Classical.not_not.1 fun h => hj.not_ge ( Finset.min'_le _ _ <| by aesop ) ⟩;
  apply hm.left;
  apply gramSchmidt_step_eq;
  · exact sizeReduceStep_diff_mem_span B (bStarFun B) i j hij m;
  · exact hm.2)

/-- Corollary of `sizeReduceStep_preserve_GS`-/
theorem sizeReduceVector_preserve_GS (B : Fin k → 𝓔 n) (i : Fin k):
    let B' := sizeReduceVector B (bStarFun B) i
    bStarFun B' = bStarFun B := by
  -- Size reduction is a sequence of sizeReduceStep operations.
  classical
  unfold sizeReduceVector
  -- Prove a stronger statement for any fold list and any starting basis.
  have h_fold : ∀ (l : List (Fin i.val)) (B0 : Fin k → 𝓔 n),
      bStarFun B0 = bStarFun B →
        bStarFun
            (List.foldl
              (fun acc (j : Fin i.val) =>
                have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
                sizeReduceStep acc (bStarFun B) i ⟨j.val, hj⟩)
              B0 l) = bStarFun B := by
    intro l; induction l with
    | nil =>
        intro B0 hB0; simpa using hB0
    | cons j l ih =>
        intro B0 hB0
        have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
        have hij' : (⟨j.val, hj⟩ : Fin k) < i := by
          exact Fin.lt_iff_val_lt_val.mpr (by simp [j.isLt])
        let B1 := sizeReduceStep B0 (bStarFun B) i ⟨j.val, hj⟩
        have hB1 : bStarFun B1 = bStarFun B := by
          have hstep : bStarFun (sizeReduceStep B0 (bStarFun B0) i ⟨j.val, hj⟩) =
              bStarFun B0 := by
            funext m
            exact (sizeReduceStep_preserve_GS (B := B0) (i := i) (j := ⟨j.val, hj⟩) (hij := hij')) m
          have hstep' : bStarFun (sizeReduceStep B0 (bStarFun B) i ⟨j.val, hj⟩) =
              bStarFun B := by
            simpa [hB0] using hstep
          simpa [B1] using hstep'
        simpa [List.foldl, B1] using ih B1 hB1
  simpa using h_fold (List.finRange i.val).reverse B rfl

/-- Corollary of `sizeReduceVector_preserve_GS`-/
theorem sizeReduceBasis_preserve_GS (B : Fin k → 𝓔 n):
    let B' := sizeReduceBasis B (bStarFun B)
    bStarFun B' = bStarFun B := by
  -- Size reduction is a sequence of sizeReduceStep operations.
  classical
  unfold sizeReduceBasis
  -- Prove a stronger statement for any fold list and any starting basis.
  have h_fold : ∀ (l : List (Fin k.val)) (B0 : Fin k → 𝓔 n),
      bStarFun B0 = bStarFun B →
        bStarFun
            (List.foldl
              (fun acc (i : Fin k.val) =>
                sizeReduceVector acc (bStarFun B) ⟨i.val, i.isLt⟩)
              B0 l) = bStarFun B := by
    intro l; induction l with
    | nil =>
        intro B0 hB0; simpa using hB0
    | cons i l ih =>
        intro B0 hB0
        let B1 := sizeReduceVector B0 (bStarFun B) ⟨i.val, i.isLt⟩
        have hB1 : bStarFun B1 = bStarFun B := by
          have hstep : bStarFun (sizeReduceVector B0 (bStarFun B0) ⟨i.val, i.isLt⟩) =
              bStarFun B0 := by
            simpa using (sizeReduceVector_preserve_GS (B := B0) (i := ⟨i.val, i.isLt⟩))
          have hstep' : bStarFun (sizeReduceVector B0 (bStarFun B) ⟨i.val, i.isLt⟩) =
              bStarFun B := by
            simpa [hB0] using hstep
          simpa [B1] using hstep'
        simpa [List.foldl, B1] using ih B1 hB1
  simpa using h_fold (List.finRange k.val) B rfl

/-- Corollary of `sizeReduceBasis_preserve_GS`-/
theorem sizeReduce_preserve_GS (B : LatticeBasis n k) :
    let B' := sizeReduce B
    bStarFun B'.basis = bStarFun B.basis := by
  -- Size reduction is a sequence of sizeReduceStep operations.
  simpa [sizeReduce] using (sizeReduceBasis_preserve_GS (B := B.basis))


/-- Helper: The property that |x - round(x)| ≤ 1/2 for the rounding function. -/
lemma roundZ_abs_sub_le (x : ℝ) : |x - (roundZ x : ℝ)| ≤ 1 / 2 := by
  unfold roundZ
  -- roundZ x = floor(x + 1/2)
  -- Need to show: |x - floor(x + 1/2)| ≤ 1/2
  -- This is a standard property of nearest-integer rounding
  exact abs_le.mpr ⟨ by linarith [ Int.floor_le ( x + 1 / 2 ) ], by linarith [ Int.lt_floor_add_one ( x + 1 / 2 ) ] ⟩


/-- Helper: After sizeReduceStep at (i,j) using fixed GS, the new coefficient μ[i,j] satisfies |μ[i,j]| ≤ 1/2.
This is the core of Lemma 3 from Regev's lecture notes.

PROVIDED SOLUTION
Let μ = ⟪B_i, BStar_j⟫ / ⟪BStar_j, BStar_j⟫
After reduction: B'_i = B_i - round(μ) • B_j.
Also note that bStarFun B' = bStarFun B = BStar by `sizeReduceStep_preserve_GS`.
Thus, The new coefficient: μ' = ⟪B'_i, BStar_j⟫ / ⟪BStar_j, BStar_j⟫
= (⟪B_i, BStar_j⟫ - round(μ) • ⟪B_j, BStar_j⟫) / ⟪BStar_j, BStar_j⟫
Since BStar_j = gramSchmidt(B)_j, we have ⟪B_j, BStar_j⟫ = ⟪BStar_j, BStar_j⟫ j(B_j projects onto its own GS vector with coefficient 1)
Therefore: μ' = μ - round(μ), no more than 1/2 by `roundZ_abs_sub_le`
-/
theorem sizeReduceStep_mu_bound (B : Fin k → 𝓔 n) (i j : Fin k) (hij : j < i) :
    let B' := sizeReduceStep B (bStarFun B) i j
    |projCoeff (B' i) (bStarFun B') j| ≤ 1 / 2 := by
  -- With fixed GS, the proof is clearer:
  classical
  intro B'
  -- Gram-Schmidt is preserved under sizeReduceStep.
  have hGS : bStarFun B' = bStarFun B := by
    funext m
    exact (sizeReduceStep_preserve_GS (B := B) (i := i) (j := j) (hij := hij)) m
  let coeff := projCoeff (B i) (bStarFun B) j
  by_cases h0 : ⟪bStarFun B j, bStarFun B j⟫ = 0
  · -- Degenerate case: denominator is zero, so coefficient is zero.
    have : projCoeff (B' i) (bStarFun B') j = 0 := by
      simp [projCoeff, hGS, h0]
    simp [this]
  · -- Non-degenerate case: compute the updated coefficient.
    have hgs : bStarFun B j =
        B j - ∑ t ∈ Finset.Iio j,
          (⟪B j, bStarFun B t⟫ / ⟪bStarFun B t, bStarFun B t⟫) • bStarFun B t := by
      -- Unfold gramSchmidt and starProjection.
      have h := InnerProductSpace.gramSchmidt_def ℝ B j
      -- Convert starProjection to explicit scalar form.
      simpa [bStarFun, Submodule.starProjection_singleton, real_inner_self_eq_norm_sq, real_inner_comm] using h
    have hsum : ⟪∑ t ∈ Finset.Iio j,
          (⟪B j, bStarFun B t⟫ / ⟪bStarFun B t, bStarFun B t⟫) • bStarFun B t,
        bStarFun B j⟫ = 0 := by
      rw [sum_inner]
      refine Finset.sum_eq_zero ?_
      intro t ht
      have ht' : t ≠ j := by
        exact ne_of_lt (Finset.mem_Iio.mp ht)
      simp [inner_smul_left, bStarFun_orthogonal B t j ht']
    have hBj : B j = bStarFun B j + ∑ t ∈ Finset.Iio j,
          (⟪B j, bStarFun B t⟫ / ⟪bStarFun B t, bStarFun B t⟫) • bStarFun B t := by
      calc
        B j = (B j - ∑ t ∈ Finset.Iio j,
              (⟪B j, bStarFun B t⟫ / ⟪bStarFun B t, bStarFun B t⟫) • bStarFun B t) +
              ∑ t ∈ Finset.Iio j,
                (⟪B j, bStarFun B t⟫ / ⟪bStarFun B t, bStarFun B t⟫) • bStarFun B t := by
              abel1
        _ = bStarFun B j + ∑ t ∈ Finset.Iio j,
              (⟪B j, bStarFun B t⟫ / ⟪bStarFun B t, bStarFun B t⟫) • bStarFun B t := by
              simp [hgs]
    have h_inner : ⟪B j, bStarFun B j⟫ = ⟪bStarFun B j, bStarFun B j⟫ := by
      rw [hBj]
      simp [inner_add_left, hsum]
    have hBi' : B' i = B i - (roundZ coeff : ℝ) • B j := by
      simp [B', sizeReduceStep, reduceAt, coeff]
    have hproj : projCoeff (B' i) (bStarFun B) j = coeff - (roundZ coeff : ℝ) := by
      unfold projCoeff
      -- Expand the inner product of the updated vector and simplify.
      have hnum : ⟪B' i, bStarFun B j⟫ =
          ⟪B i, bStarFun B j⟫ - (roundZ coeff : ℝ) * ⟪B j, bStarFun B j⟫ := by
        calc
          ⟪B' i, bStarFun B j⟫ = ⟪B i - (roundZ coeff : ℝ) • B j, bStarFun B j⟫ := by
            simp [hBi']
          _ = ⟪B i, bStarFun B j⟫ - ⟪(roundZ coeff : ℝ) • B j, bStarFun B j⟫ := by
            simp [inner_sub_left]
          _ = ⟪B i, bStarFun B j⟫ - (roundZ coeff : ℝ) * ⟪B j, bStarFun B j⟫ := by
            simp [inner_smul_left]
      have hnum' : ⟪B' i, bStarFun B j⟫ =
          ⟪B i, bStarFun B j⟫ - (roundZ coeff : ℝ) * ⟪bStarFun B j, bStarFun B j⟫ := by
        simpa [h_inner] using hnum
      -- Use h_inner and clear the denominator.
      have : (⟪B i, bStarFun B j⟫ - (roundZ coeff : ℝ) * ⟪bStarFun B j, bStarFun B j⟫) / ⟪bStarFun B j, bStarFun B j⟫ =
          (⟪B i, bStarFun B j⟫ / ⟪bStarFun B j, bStarFun B j⟫) - (roundZ coeff : ℝ) := by
        field_simp [h0]
      simpa [hnum', coeff] using this
    have hproj' : projCoeff (B' i) (bStarFun B') j = coeff - (roundZ coeff : ℝ) := by
      simpa [hGS] using hproj
    simpa [hproj'] using roundZ_abs_sub_le coeff

/-- Later application of sizeReduceStep does not affect previously reduced coefficients.

PROVIDED SOLUTION
The idea is to note that sizeReduceStep at (i,j') only modifies B_i by subtracting multiples of B_{j'}, which has zero projection along the direction of bStar_j for any j > j'. Therefore it does not affect the Gram-Schmidt coefficient μ[i,j], which is B_i's projection length onto bStar_j direction.
-/
lemma sizeReduceStep_pairs_mu_preserved
  (B : Fin k → 𝓔 n)
  (i j j' : Fin k) (hij : j < i) (hjj' : j' < j) :
    let B1 := sizeReduceStep B (bStarFun B) i j
    let coeff1 := projCoeff (B1 i) (bStarFun B1) j
    let B2 := sizeReduceStep B1 (bStarFun B1) i j'
    let coeff2 := projCoeff (B2 i) (bStarFun B2) j
    coeff1 = coeff2 := by
  classical
  intro B1 coeff1 B2 coeff2
  -- Gram-Schmidt is preserved for the second step.
  have hij' : j' < i := lt_trans hjj' hij
  have hGS2 : bStarFun B2 = bStarFun B1 := by
    funext m
    exact (sizeReduceStep_preserve_GS (B := B1) (i := i) (j := j') (hij := hij')) m
  -- Orthogonality: b*_j is orthogonal to B1 j' when j' < j.
  have h_orth : ⟪B1 j', bStarFun B1 j⟫ = 0 := by
    have h := InnerProductSpace.gramSchmidt_inv_triangular ℝ B1 hjj'
    -- h : ⟪gramSchmidt ℝ B1 j, B1 j'⟫ = 0
    simpa [bStarFun, real_inner_comm] using h
  -- Expand the updated coefficient.
  let coeff' := projCoeff (B1 i) (bStarFun B1) j'
  have hBi' : B2 i = B1 i - (roundZ coeff' : ℝ) • B1 j' := by
    simp [B2, sizeReduceStep, reduceAt, coeff']
  have hproj : projCoeff (B2 i) (bStarFun B1) j = projCoeff (B1 i) (bStarFun B1) j := by
    unfold projCoeff
    calc
      ⟪B2 i, bStarFun B1 j⟫ / ⟪bStarFun B1 j, bStarFun B1 j⟫
          = (⟪B1 i, bStarFun B1 j⟫ - (roundZ coeff' : ℝ) * ⟪B1 j', bStarFun B1 j⟫)
              / ⟪bStarFun B1 j, bStarFun B1 j⟫ := by
                have : ⟪B2 i, bStarFun B1 j⟫ =
                    ⟪B1 i, bStarFun B1 j⟫ - (roundZ coeff' : ℝ) * ⟪B1 j', bStarFun B1 j⟫ := by
                  calc
                    ⟪B2 i, bStarFun B1 j⟫ = ⟪B1 i - (roundZ coeff' : ℝ) • B1 j', bStarFun B1 j⟫ := by
                      simp [hBi']
                    _ = ⟪B1 i, bStarFun B1 j⟫ - ⟪(roundZ coeff' : ℝ) • B1 j', bStarFun B1 j⟫ := by
                      simp [inner_sub_left]
                    _ = ⟪B1 i, bStarFun B1 j⟫ - (roundZ coeff' : ℝ) * ⟪B1 j', bStarFun B1 j⟫ := by
                      simp [inner_smul_left]
                simp [this]
      _ = ⟪B1 i, bStarFun B1 j⟫ / ⟪bStarFun B1 j, bStarFun B1 j⟫ := by
            simp [h_orth]
  -- Finish by unfolding coeff1/coeff2 and using GS preservation.
  simpa [coeff1, coeff2, hGS2] using hproj.symm

/-- Corollary of `sizeReduceStep_pairs_mu_preserved`: Later application of sizeReduceStep does not affect previous coefficients.

PROVIDED SOLUTION
The idea is to note that sizeReduceStep at (i,j') only modifies B_i by subtracting multiples of B_{j'}, which has zero projection along the direction of bStar_j for any j > j'. Therefore it does not affect the Gram-Schmidt coefficient μ[i,j], which is B_i's projection length onto bStar_j direction.
-/
theorem sizeReduceStep_previous_mu_preserved
  (B : Fin k → 𝓔 n)
  (i j : Fin k) (hij : j < i) :
    ∀ j' : Fin k, j' > j ∧ j' < i →
    let coeff0 := projCoeff (B i) (bStarFun B) j'
    let B1 := sizeReduceStep B (bStarFun B) i j
    let coeff1 := projCoeff (B1 i) (bStarFun B1) j'
    coeff0 = coeff1 := by
  classical
  intro j' hj' coeff0 B1 coeff1
  -- Gram-Schmidt is preserved for this step.
  have hGS1 : bStarFun B1 = bStarFun B := by
    funext m
    exact (sizeReduceStep_preserve_GS (B := B) (i := i) (j := j) (hij := hij)) m

  -- Orthogonality: for j < j', the GS vector b*_j' is orthogonal to the original basis vector B j.
  have h_orth : ⟪B j, bStarFun B j'⟫ = 0 := by
    have hj_lt_j' : j < j' := hj'.1
    have h := InnerProductSpace.gramSchmidt_inv_triangular ℝ B hj_lt_j'
    -- h : ⟪gramSchmidt ℝ B j', B j⟫ = 0
    simpa [bStarFun, real_inner_comm] using h

  -- Expand the updated i-th vector.
  let coeff := projCoeff (B i) (bStarFun B) j
  have hBi' : B1 i = B i - (roundZ coeff : ℝ) • B j := by
    -- `sizeReduceStep` updates only at `i` using `reduceAt`.
    simp [B1, sizeReduceStep, reduceAt, projCoeff, coeff]

  -- The projection coefficient onto b*_j' is unchanged by subtracting a multiple of B j.
  have hproj : projCoeff (B1 i) (bStarFun B) j' = projCoeff (B i) (bStarFun B) j' := by
    unfold projCoeff
    have hnum : ⟪B1 i, bStarFun B j'⟫ = ⟪B i, bStarFun B j'⟫ := by
      calc
        ⟪B1 i, bStarFun B j'⟫ = ⟪B i - (roundZ coeff : ℝ) • B j, bStarFun B j'⟫ := by
          simp [hBi']
        _ = ⟪B i, bStarFun B j'⟫ - ⟪(roundZ coeff : ℝ) • B j, bStarFun B j'⟫ := by
          simp [inner_sub_left]
        _ = ⟪B i, bStarFun B j'⟫ - (roundZ coeff : ℝ) * ⟪B j, bStarFun B j'⟫ := by
          simp [inner_smul_left]
        _ = ⟪B i, bStarFun B j'⟫ := by
          simp [h_orth]
    simp [hnum]

  -- Rewrite using GS preservation and unfold the let-bound names.
  have hproj' : projCoeff (B1 i) (bStarFun B1) j' = projCoeff (B i) (bStarFun B) j' := by
    simpa [hGS1] using hproj
  simpa [coeff0, coeff1] using hproj'.symm

/-- Helper: partial application of sizeReduceVector upto m components -/
noncomputable def sizeReduceVector_upto (B : Fin k → 𝓔 n) (BStar : Fin k → 𝓔 n) (i : Fin k) (m : ℕ) : Fin k → 𝓔 n :=
  ((List.finRange i.val).take m).reverse.foldl
      (fun (acc : Fin k → 𝓔 n) (j : Fin i.val) =>
        have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
        sizeReduceStep acc BStar i ⟨j.val, hj⟩)
      B

/-- Corollary : `sizeReduceVector B (bStarFun B) i` produces a reduced `(B i)`

PROVIDED SOLUTION
This is a direct corollary of applying `sizeReduceStep_mu_bound` for each j < i in sequence, noting that each step preserves the previously reduced coefficients by `sizeReduceStep_previous_mu_preserved`.
Possible proof strategy:
1. Use the fact that `sizeReduceVector` folds over (finRange i.val).reverse = [i-1, i-2, ..., 1, 0]
2. Show by induction that after processing each j in the list:
   - Althouth `sizeReduceVector` uses a fixed BStar, but we can also pretend that we are using the GS of the just-reduced basis at each step. This is because GS is preserved throughout by `sizeReduceStep_preserve_GS`
   - |μ[i,j]| ≤ 1/2 by `sizeReduceStep_mu_bound`
   - For previously processed j' > j, μ[i,j'] remains ≤ 1/2 by `sizeReduceStep_previous_mu_preserved`
-/
theorem sizeReduceVector_mu_bound (B : Fin k → 𝓔 n) (i : Fin k) :
    let B' := sizeReduceVector B (bStarFun B) i
    ∀ j : Fin k, j < i →
      |projCoeff (B' i) (bStarFun B') j| ≤ 1 / 2 := by
  classical
  intro B' j hji

  -- GS is preserved after full sizeReduceVector
  have hGS_final : bStarFun B' = bStarFun B := sizeReduceVector_preserve_GS B i
  rw [hGS_final]

  -- Convert j to Fin i.val
  have hj_lt_i : j.val < i.val := Fin.lt_iff_val_lt_val.mp hji
  let j_i : Fin i.val := ⟨j.val, hj_lt_i⟩

  -- The fold processes indices in reverse: [i-1, i-2, ..., 0]
  -- We prove: for any suffix of the reversed list containing j_i,
  -- after processing that suffix, |μ[i,j]| ≤ 1/2
  -- Unfold the definition of sizeReduceVector for later rewriting.
  let l := (List.finRange i.val).reverse
  have hB' : B' =
      l.foldl
        (fun (acc : Fin k → 𝓔 n) (j : Fin i.val) =>
          have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
          sizeReduceStep acc (bStarFun B) i ⟨j.val, hj⟩)
        B := by
      rfl

  -- j_i occurs in the reversed finRange list.
  have hj_mem : j_i ∈ l := by
    -- Membership follows from j < i and finRange enumerating [0, i-1].
    -- The list is reversed but preserves membership.
    -- TODO: finish using List.mem_reverse and List.mem_finRange.
    have : j_i ∈ List.finRange i.val := List.mem_finRange j_i
    have : j_i ∈ (List.finRange i.val).reverse := (List.mem_reverse.mpr this)
    simp [l, this]

  -- Main bound: the step at j_i enforces |μ[i,j]| ≤ 1/2, and later steps preserve it.
  have hmain : |projCoeff (B' i) (bStarFun B) j| ≤ 1 / 2 := by
    -- Sketch: split the foldl list around j_i, apply sizeReduceStep_mu_bound
    -- at the step j_i, then use sizeReduceStep_previous_mu_preserved for
    -- subsequent steps in the fold.
    -- TODO: formalize via List.foldl recursion (or sizeReduceVector_upto).
    -- Define the folding function.
    let f :=
      (fun (acc : Fin k → 𝓔 n) (j : Fin i.val) =>
        have hj : j.val < k := Nat.lt_trans j.isLt i.isLt
        sizeReduceStep acc (bStarFun B) i ⟨j.val, hj⟩)

    -- Split the list around j_i.
    obtain ⟨idx, hidx⟩ := (List.mem_iff_get).1 hj_mem
    let l1 := l.take idx.1
    let l2 := l.drop (idx.1 + 1)
    have hget : l[idx.1] = j_i := by
      simpa [List.get_eq_getElem] using hidx
    have hdrop : l.drop idx.1 = l[idx.1] :: l.drop (idx.1 + 1) :=
      List.drop_eq_getElem_cons (l := l) (i := idx.1) (h := idx.2)
    have hl : l = l1 ++ j_i :: l2 := by
      -- take/drop decomposition with the identified element at position n
      have htake : l1 ++ l.drop idx.1 = l := by
        simp [l1, (List.take_append_drop idx.1 l)]
      calc
        l = l1 ++ l.drop idx.1 := by simpa using htake.symm
        _ = l1 ++ (l[idx.1] :: l.drop (idx.1 + 1)) := by
            rw [hdrop]
        _ = l1 ++ j_i :: l2 := by simp [hget, l2]

    -- The reversed finRange list is strictly decreasing.
    have hpair : List.Pairwise (fun a b : Fin i.val => a > b) l := by
      -- Rewrite using the order-reversing map on finRange.
      have hpair' : List.Pairwise (fun a b : Fin i.val => a < b) (List.finRange i.val) :=
        List.pairwise_lt_finRange i.val
      have hpair'' : List.Pairwise (fun a b : Fin i.val => a > b)
          (List.map Fin.rev (List.finRange i.val)) := by
        refine List.Pairwise.map Fin.rev ?_ hpair'
        intro a b hlt
        -- If a < b then b.rev < a.rev, hence a.rev > b.rev.
        have : b.rev < a.rev :=
          (Fin.rev_lt_iff (i := a.rev) (j := b)).1 (by simpa [Fin.rev_rev] using hlt)
        simpa [gt_iff_lt] using this
      simpa [l, List.finRange_reverse] using hpair''

    -- Elements after j_i are strictly smaller than j_i.
    have htail_lt : ∀ j' ∈ l2, (j' : Fin i.val) < j_i := by
      have hsub : (j_i :: l2).Sublist l := by
        -- j_i :: l2 is a suffix of l1 ++ j_i :: l2 = l.
        simp [hl, (List.sublist_append_right l1 (j_i :: l2))]
      have hpair_tail : List.Pairwise (fun a b : Fin i.val => a > b) (j_i :: l2) :=
        List.Pairwise.sublist hsub hpair
      have hcons := (List.pairwise_cons).1 hpair_tail
      exact hcons.1

    -- Helper: GS is preserved for any fold prefix (same as sizeReduceVector_preserve_GS).
    have hGS_prefix : ∀ (l' : List (Fin i.val)) (B0 : Fin k → 𝓔 n),
        bStarFun B0 = bStarFun B →
          bStarFun (List.foldl f B0 l') = bStarFun B := by
      intro l'; induction l' with
      | nil =>
          intro B0 hB0; simpa using hB0
      | cons a l ih =>
          intro B0 hB0
          have ha : a.val < k := Nat.lt_trans a.isLt i.isLt
          have hij' : (⟨a.val, ha⟩ : Fin k) < i := by
            exact Fin.lt_iff_val_lt_val.mpr (by simp [a.isLt])
          let B1 := sizeReduceStep B0 (bStarFun B) i ⟨a.val, ha⟩
          have hB1 : bStarFun B1 = bStarFun B := by
            have hstep : bStarFun (sizeReduceStep B0 (bStarFun B0) i ⟨a.val, ha⟩) =
                bStarFun B0 := by
              funext m
              exact (sizeReduceStep_preserve_GS (B := B0) (i := i)
                (j := ⟨a.val, ha⟩) (hij := hij')) m
            have hstep' : bStarFun (sizeReduceStep B0 (bStarFun B) i ⟨a.val, ha⟩) =
                bStarFun B := by
              simpa [hB0] using hstep
            simpa [B1] using hstep'
          simpa [List.foldl, B1] using ih B1 hB1

    -- Notation for the basis after prefix and at j_i.
    let B1 := List.foldl f B l1
    let B2 := f B1 j_i

    -- Rewrite B' as folding the suffix l2 starting from B2.
    have hB'fold : B' = List.foldl f B2 l2 := by
      have hfold : List.foldl f B l = List.foldl f (List.foldl f B l1) (j_i :: l2) := by
        simp [hl, (List.foldl_append (f := f) (b := B) (l := l1) (l' := j_i :: l2))]
      have hfold' : List.foldl f (List.foldl f B l1) (j_i :: l2) = List.foldl f B2 l2 := by
        simp [List.foldl, B2, B1]
      simpa [hB', hfold'] using hfold

    -- Bound after the j_i step.
    have hGS_B1 : bStarFun B1 = bStarFun B := hGS_prefix l1 B rfl
    have hjk : j_i.val < k := Nat.lt_trans j_i.isLt i.isLt
    have hjk_eq : (⟨j_i.val, hjk⟩ : Fin k) = j := by
      ext; rfl
    have hbound_step : |projCoeff (B2 i) (bStarFun B) j| ≤ 1 / 2 := by
      -- Apply sizeReduceStep_mu_bound on B1, rewriting B2.
      have hbound' : |projCoeff (B2 i) (bStarFun B2) j| ≤ 1 / 2 := by
        simpa [B2, hGS_B1, hjk_eq] using
          (sizeReduceStep_mu_bound (B := B1) (i := i) (j := j) (hij := hji))
      -- bStarFun is preserved for this step, so rewrite to bStarFun B.
      have hGS_B2 : bStarFun B2 = bStarFun B := by
        -- B2 is a sizeReduceStep from B1 with matching GS.
        have hstep : bStarFun (sizeReduceStep B1 (bStarFun B1) i j) = bStarFun B1 := by
          funext m
          exact (sizeReduceStep_preserve_GS (B := B1) (i := i) (j := j) (hij := hji)) m
        simpa [B2, hGS_B1, hjk_eq] using hstep
      simpa [hGS_B2] using hbound'

    -- Induction: steps at indices j' < j preserve μ[i,j].
    have h_preserve :
        projCoeff ((List.foldl f B2 l2) i) (bStarFun B) j =
          projCoeff (B2 i) (bStarFun B) j := by
      -- Stronger invariant: any basis differing from B only at i preserves the coefficient.
      have h_inv : ∀ (l' : List (Fin i.val)) (Bcur : Fin k → 𝓔 n),
          (∀ j' : Fin k, j' ≠ i → Bcur j' = B j') →
          (∀ j' ∈ l', (j' : Fin i.val) < j_i) →
            projCoeff ((List.foldl f Bcur l') i) (bStarFun B) j =
              projCoeff (Bcur i) (bStarFun B) j := by
        intro l'; induction l' with
        | nil =>
            intro Bcur hfix hlt; simp
        | cons a l ih =>
            intro Bcur hfix hlt
            have ha_lt : (a : Fin i.val) < j_i := hlt a (by simp)
            have hak : a.val < k := Nat.lt_trans a.isLt i.isLt
            let a_k : Fin k := ⟨a.val, hak⟩
            let Bcur1 := sizeReduceStep Bcur (bStarFun B) i a_k

            -- Orthogonality of Bcur a_k and bStarFun B j.
            have h_orth : ⟪Bcur a_k, bStarFun B j⟫ = 0 := by
              have ha_lt' : a_k < j := by
                exact Fin.lt_iff_val_lt_val.mpr (by simpa using ha_lt)
              have h := InnerProductSpace.gramSchmidt_inv_triangular ℝ B ha_lt'
              -- h : ⟪gramSchmidt ℝ B j, B a_k⟫ = 0
              have hfix' : Bcur a_k = B a_k := by
                apply hfix
                exact ne_of_lt (lt_trans ha_lt' hji)
              simpa [bStarFun, real_inner_comm, hfix'] using h

            -- Show this step preserves the coefficient.
            have hproj : projCoeff (Bcur1 i) (bStarFun B) j = projCoeff (Bcur i) (bStarFun B) j := by
              unfold projCoeff
              let coeff := projCoeff (Bcur i) (bStarFun B) a_k
              have hBi' : Bcur1 i = Bcur i - (roundZ coeff : ℝ) • Bcur a_k := by
                simp [Bcur1, sizeReduceStep, reduceAt, coeff]
              have hnum : ⟪Bcur1 i, bStarFun B j⟫ = ⟪Bcur i, bStarFun B j⟫ := by
                calc
                  ⟪Bcur1 i, bStarFun B j⟫ = ⟪Bcur i - (roundZ coeff : ℝ) • Bcur a_k, bStarFun B j⟫ := by
                    simp [hBi']
                  _ = ⟪Bcur i, bStarFun B j⟫ - ⟪(roundZ coeff : ℝ) • Bcur a_k, bStarFun B j⟫ := by
                    simp [inner_sub_left]
                  _ = ⟪Bcur i, bStarFun B j⟫ - (roundZ coeff : ℝ) * ⟪Bcur a_k, bStarFun B j⟫ := by
                    simp [inner_smul_left]
                  _ = ⟪Bcur i, bStarFun B j⟫ := by
                    simp [h_orth]
              simp [hnum]

            -- Invariant preserved by this step.
            have hfix1 : ∀ j' : Fin k, j' ≠ i → Bcur1 j' = B j' := by
              intro j' hj'
              have : (sizeReduceStep Bcur (bStarFun B) i a_k) j' = Bcur j' := by
                simp [sizeReduceStep, hj']
              simpa [Bcur1, this] using hfix j' hj'

            -- Continue with the tail.
            have htail : projCoeff ((List.foldl f Bcur1 l) i) (bStarFun B) j =
                projCoeff (Bcur1 i) (bStarFun B) j := by
              apply ih Bcur1 hfix1
              intro j' hj'
              exact hlt j' (by simp [hj'])
            simpa [List.foldl, Bcur1, hproj] using htail

      -- Apply the invariant to B2 and l2.
      -- First, folds with f only change the i-th entry.
      have hfix_fold : ∀ (l' : List (Fin i.val)) (B0 : Fin k → 𝓔 n),
          (∀ j' : Fin k, j' ≠ i → B0 j' = B j') →
            ∀ j' : Fin k, j' ≠ i → (List.foldl f B0 l') j' = B j' := by
        intro l'; induction l' with
        | nil =>
            intro B0 hfix j' hj'; simpa using hfix j' hj'
        | cons a l ih =>
            intro B0 hfix j' hj'
            have hfix1 : ∀ j' : Fin k, j' ≠ i → (f B0 a) j' = B j' := by
              intro j' hj'
              have : (f B0 a) j' = B0 j' := by
                simp [f, sizeReduceStep, hj']
              simpa [this] using hfix j' hj'
            simpa [List.foldl] using ih (f B0 a) hfix1 j' hj'
      have hfix_B1 : ∀ j' : Fin k, j' ≠ i → B1 j' = B j' := by
        have hfix0 : ∀ j' : Fin k, j' ≠ i → B j' = B j' := by
          intro j' hj'; rfl
        exact hfix_fold l1 B hfix0
      have hfix_B2 : ∀ j' : Fin k, j' ≠ i → B2 j' = B j' := by
        intro j' hj'
        have : B2 j' = B1 j' := by
          simp [B2, f, sizeReduceStep, hj']
        simpa [this] using hfix_B1 j' hj'
      exact h_inv l2 B2 hfix_B2 htail_lt

    have hfinal : |projCoeff ((List.foldl f B2 l2) i) (bStarFun B) j| ≤ 1 / 2 := by
      simpa [h_preserve] using hbound_step
    simpa [hB'fold] using hfinal

  simpa using hmain

/-- Size reduction achieves the size reduction condition.

PROVIDED SOLUTION
Follows directly from `sizeReduceVector_mu_bound` applied for each basis vector in `sizeReduceBasis`, which processes each basis vector in order.
-/
theorem sizeReduce_sizeReduced (B : LatticeBasis n k) :
    SizeReduced (sizeReduce B) := by
  classical
  unfold SizeReduced sizeReduce
  intro i j hij

  -- After sizeReduce, the basis has been processed by sizeReduceBasis
  -- which applies sizeReduceVector to each position i in order
  -- sizeReduceVector i processes all j < i, updating B_i against each B_j
  -- For any given i ≠ i', `sizeReduceVector i` is independent of `sizeReduceVector i'`
  let B0 := B.basis
  let BStar := bStarFun B0
  let f := fun (acc : Fin k → 𝓔 n) (i0 : Fin k.val) =>
    sizeReduceVector acc BStar ⟨i0.val, i0.isLt⟩
  let l : List (Fin k.val) := List.finRange k.val
  have hBfinal : sizeReduceBasis B0 BStar = List.foldl f B0 l := by
    rfl

  -- Split the processing list around index i.
  have hi_mem : (i : Fin k.val) ∈ l := by
    simp [l, (List.mem_finRange i)]
  obtain ⟨idx, hidx⟩ := (List.mem_iff_get).1 hi_mem
  let l1 := l.take idx.1
  let l2 := l.drop (idx.1 + 1)
  have hget : l[idx.1] = i := by
    simpa [List.get_eq_getElem] using hidx
  have hdrop : l.drop idx.1 = l[idx.1] :: l.drop (idx.1 + 1) :=
    List.drop_eq_getElem_cons (l := l) (i := idx.1) (h := idx.2)
  have hl : l = l1 ++ i :: l2 := by
    have htake : l1 ++ l.drop idx.1 = l := by
      simp [l1, (List.take_append_drop idx.1 l)]
    calc
      l = l1 ++ l.drop idx.1 := by simpa using htake.symm
      _ = l1 ++ (l[idx.1] :: l.drop (idx.1 + 1)) := by
          rw [hdrop]
      _ = l1 ++ i :: l2 := by simp [hget, l2]

  -- No duplicates in finRange, so i does not occur in the suffix l2.
  have hnodup : l.Nodup := by
    simpa [l] using (List.nodup_finRange k.val)
  have hnotin_l2 : (i : Fin k.val) ∉ l2 := by
    have hnodup' : (l1 ++ i :: l2).Nodup := by
      simpa [hl] using hnodup
    have htail : (i :: l2).Nodup := (List.nodup_append).1 hnodup' |>.2.1
    exact (List.nodup_cons).1 htail |>.1

  -- sizeReduceVector only changes the i'-th component.
  have sizeReduceVector_apply_ne :
      ∀ (B' : Fin k → 𝓔 n) (i' l' : Fin k), l' ≠ i' →
        sizeReduceVector B' BStar i' l' = B' l' := by
    intro B' i' l' hne
    unfold sizeReduceVector
    induction (List.finRange i'.val).reverse generalizing B' with
    | nil =>
        simp
    | cons a L ih =>
        have hj : a.val < k := Nat.lt_trans a.isLt i'.isLt
        have hstep : (sizeReduceStep B' BStar i' ⟨a.val, hj⟩) l' = B' l' := by
          simp [sizeReduceStep, hne]
        have ih' := ih (B' := sizeReduceStep B' BStar i' ⟨a.val, hj⟩)
        simpa [List.foldl, hstep] using ih'

  -- Folding over a list not containing i leaves the i-th component unchanged.
  have hfold_ne : ∀ (l' : List (Fin k.val)) (B0' : Fin k → 𝓔 n),
      (i : Fin k.val) ∉ l' → (List.foldl f B0' l') i = B0' i := by
    intro l'; induction l' with
    | nil =>
        intro B0' _; simp
    | cons a l ih =>
        intro B0' hnotin
        have hne : (a : Fin k) ≠ i := by
          intro h; apply hnotin; simp [h]
        have hnotin' : (i : Fin k.val) ∉ l := by
          intro h; apply hnotin; simp [h]
        have hstep : (f B0' a) i = B0' i := by
          simpa [f] using (sizeReduceVector_apply_ne (B' := B0') (i' := a) (l' := i) hne.symm)
        have htail := ih (f B0' a) hnotin'
        simpa [List.foldl, hstep] using htail

  -- GS is preserved for any prefix of the outer loop.
  have hGS_prefix : ∀ (l' : List (Fin k.val)) (B0' : Fin k → 𝓔 n),
      bStarFun B0' = BStar → bStarFun (List.foldl f B0' l') = BStar := by
    intro l'; induction l' with
    | nil =>
        intro B0' hB0'; simpa using hB0'
    | cons a l ih =>
        intro B0' hB0'
        let B1 := f B0' a
        have hB1 : bStarFun B1 = BStar := by
          have hstep : bStarFun (sizeReduceVector B0' (bStarFun B0') ⟨a.val, a.isLt⟩) =
              bStarFun B0' := by
            simpa using (sizeReduceVector_preserve_GS (B := B0') (i := ⟨a.val, a.isLt⟩))
          have hstep' : bStarFun (sizeReduceVector B0' BStar ⟨a.val, a.isLt⟩) = BStar := by
            simpa [hB0'] using hstep
          simpa [B1, f] using hstep'
        simpa [List.foldl, B1] using ih B1 hB1

  -- Notation for the basis before and after the i-th size-reduction step.
  let Bprev := List.foldl f B0 l1
  let B2 := f Bprev i

  -- After the i-step, later steps do not change the i-th vector.
  have hBfinal_i : (List.foldl f B0 l) i = B2 i := by
    have hfold : List.foldl f B0 l = List.foldl f (List.foldl f B0 l1) (i :: l2) := by
      simp [hl, (List.foldl_append (f := f) (b := B0) (l := l1) (l' := i :: l2))]
    have hfold' : (List.foldl f (List.foldl f B0 l1) (i :: l2)) i = (List.foldl f B2 l2) i := by
      simp [List.foldl, B2, Bprev]
    have htail : (List.foldl f B2 l2) i = B2 i := hfold_ne l2 B2 hnotin_l2
    simp [hfold, hfold', htail]

  -- Apply sizeReduceVector_mu_bound at the i-step.
  have hGS_Bprev : bStarFun Bprev = BStar := hGS_prefix l1 B0 rfl
  have hbound : |projCoeff (B2 i) (bStarFun B2) j| ≤ 1 / 2 := by
    have h := (sizeReduceVector_mu_bound (B := Bprev) (i := i)) j hij
    simpa [B2, Bprev, f, BStar, hGS_Bprev] using h
  have hGS_B2 : bStarFun B2 = BStar := by
    have hstep : bStarFun (sizeReduceVector Bprev (bStarFun Bprev) i) = bStarFun Bprev := by
      simpa using (sizeReduceVector_preserve_GS (B := Bprev) (i := i))
    simpa [B2, Bprev, f, hGS_Bprev] using hstep
  have hbound' : |projCoeff (B2 i) BStar j| ≤ 1 / 2 := by
    simpa [hGS_B2] using hbound

  -- Rewrite to the final basis and finish.
  have hGS_final : bStarFun (sizeReduceBasis B0 BStar) = BStar := by
    simpa [B0, BStar] using (sizeReduceBasis_preserve_GS (B := B0))
  have hBfinal_i' : (sizeReduceBasis B0 BStar) i = B2 i := by
    simpa [hBfinal] using hBfinal_i
  have hfinal : |projCoeff ((sizeReduceBasis B0 BStar) i) (bStarFun (sizeReduceBasis B0 BStar)) j| ≤ 1 / 2 := by
    simpa [hBfinal_i', hGS_final] using hbound'
  simpa [muFun, projGsCoeff] using hfinal

/-!
  ### Proofs that LLL operations preserve the lattice
-/
noncomputable section preserve_lattice
/-- Size reduction preserves the lattice. -/
theorem sizeReduce_equiv (B : LatticeBasis n k) :
    (sizeReduce B).toLattice ≡ᵤ B.toLattice := by
  -- By definition of `sizeReduce`, the basis of the reduced lattice is obtained by applying an invertible integer matrix to the basis of the original lattice.
  have h_basis_eq : ∃ U : Matrix (Fin k) (Fin k) ℤ, IsUnit U.det ∧ (eucBasisToMatrix (sizeReduce B).basis) = (eucBasisToMatrix B.basis) * (U.map (Int.castRingHom ℝ)) := by
    have h_basis_eq : ∃ U : UnimodularMatrix k, (eucBasisToMatrix (sizeReduce B).basis) = (eucBasisToMatrix B.basis) * U.real := by
      have h_basis_eq : ∃ U : UnimodularMatrix k, (eucBasisToMatrix (sizeReduceBasis B.basis (bStarFun B.basis))) = (eucBasisToMatrix B.basis) * U.real := by
        convert sizeReduceBasisSpec_eq_matrix_mul ( eucBasisToMatrix B.basis ) ( bStarFun B.basis ) using 1;
        ext; simp [sizeReduceBasis_eq_sizeReduceBasisSpec];
      convert h_basis_eq using 1;
    obtain ⟨ U, hU ⟩ := h_basis_eq;
    exact ⟨ U, by simp, hU ⟩;
  obtain ⟨ U, hU₁, hU₂ ⟩ := h_basis_eq;
  -- Since $U$ is invertible, the lattice generated by the basis of the reduced lattice is the same as the lattice generated by the basis of the original lattice.
  have h_lattice_eq : ∀ (v : 𝓔 n), v ∈ Submodule.span ℤ (Set.range (eucBasisToMatrix (sizeReduce B).basis).col) ↔ v ∈ Submodule.span ℤ (Set.range (eucBasisToMatrix B.basis).col) := by
    intro v
    constructor;
    · rw [ Submodule.mem_span_range_iff_exists_fun ] at *;
      rintro ⟨ c, rfl ⟩;
      simp_all +decide ;
      refine' Submodule.sum_mem _ fun i _ => _;
      refine' Submodule.smul_mem _ _ _;
      rw [ Submodule.mem_span_range_iff_exists_fun ];
      use fun j => U j i;
      ext j; simp +decide [ Matrix.mul_apply ] ;
      simp +decide [ Matrix.col, mul_comm ];
      rw [ Finset.sum_apply, Finset.sum_congr rfl ] ; intros ; aesop;
    · intro hv
      obtain ⟨c, hc⟩ : ∃ c : Fin k → ℤ, v = ∑ i, c i • (eucBasisToMatrix B.basis).col i := by
        rw [ Submodule.mem_span_range_iff_exists_fun ] at hv ; tauto;
      -- Since $U$ is invertible, there exists some $d : Fin k → ℤ$ such that $U * d = c$.
      obtain ⟨d, hd⟩ : ∃ d : Fin k → ℤ, U.mulVec d = c := by
        use U⁻¹.mulVec c;
        simp +decide [ hU₁ ];
      -- Since $U$ is invertible, we can express $v$ as a linear combination of the columns of the size-reduced basis.
      have hv_comb : v = ∑ i, d i • (eucBasisToMatrix (sizeReduce B).basis).col i := by
        ext i; simp +decide [ hc, hU₂ ] ;
        simp +decide [ ← hd, Matrix.mulVec, dotProduct, mul_comm ];
        simp +decide [ Matrix.mul_apply, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
        rw [ Finset.sum_comm ];
      exact hv_comb.symm ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( Submodule.subset_span <| Set.mem_range_self _ );
  convert Submodule.ext h_lattice_eq using 1

/-
Swapping adjacent basis vectors preserves the lattice.
-/
theorem swapAdjacent_equiv (B : LatticeBasis n k) (i : Fin k) (hi : i.1 + 1 < k) :
    (swapAdjacent B i hi).toLattice ≡ᵤ B.toLattice := by
      have h_swap_equiv : ∃ U : Matrix.GeneralLinearGroup (Fin k) ℤ, (swapAdjacent B i hi) = B ◾ U := by
        exact ⟨ ⟨ swappingMatrixU i ⟨ i + 1, hi ⟩, ( swappingMatrixU i ⟨ i + 1, hi ⟩ ) ⁻¹, by simp +decide, by simp +decide ⟩, swapAdjacent_eq_mul_unimodular B i hi ⟩;
      have := @LatticeBasis.span_eq_of_UnimodularEquiv;
      exact GeometricLattice.CarrierEquiv.symm (this h_swap_equiv)

/-- LLL step preserves the lattice. -/
theorem LLLStep_equiv (B : LatticeBasis n k) (δ : ℝ) :
    (LLLStep B δ).toLattice ≡ᵤ B.toLattice := by
  unfold LatticeCrypto.Foundations.Algorithms.LLL.LLLStep;
  unfold LatticeCrypto.Foundations.Algorithms.LLL.firstLovaszViolation;
  field_simp;
  split_ifs <;> [ exact ( LatticeCrypto.Foundations.Algorithms.LLL.swapAdjacent_equiv _ _ _ ) |> fun h => h.trans ( LatticeCrypto.Foundations.Algorithms.LLL.sizeReduce_equiv _ ) ; exact ( LatticeCrypto.Foundations.Algorithms.LLL.sizeReduce_equiv _ ) ]

/-- Base case for natural number induction -/
private lemma LLL_equiv_base (B : LatticeBasis n k) (δ : ℝ) :
    (LLL_impl 0 B δ).toLattice ≡ᵤ B.toLattice := by
      exact rfl

/-- Inductive step for natural number induction -/
private lemma LLL_equiv_step (numIters : ℕ) (B : LatticeBasis n k) (δ : ℝ)
    (ih : ∀ (B' : LatticeBasis n k), (LLL_impl numIters B' δ).toLattice ≡ᵤ B'.toLattice) :
    (LLL_impl (numIters + 1) B δ).toLattice ≡ᵤ B.toLattice := by
      classical
      by_cases h : LLLReduced B δ
      · simp [LLL_impl, h]
        exact rfl
      · simp [LLL_impl, h]
        exact (ih (LLLStep B δ)).trans (LLLStep_equiv B δ)

/-- LLL preserves the lattice. -/
theorem LLL_equiv (B : LatticeBasis n k) (δ : ℝ) (numIters : ℕ) :
    (LLL_impl numIters B δ).toLattice ≡ᵤ B.toLattice := by
  apply Nat.rec (motive := fun m => ∀ B : LatticeCrypto.Foundations.Lattice.LatticeBasis n k, (LatticeCrypto.Foundations.Algorithms.LLL.LLL_impl m B δ).toLattice ≡ᵤ B.toLattice) (fun B => LLL_equiv_base B δ) (fun m ih B => LLL_equiv_step m B δ ih) numIters B
end preserve_lattice

end correctness

end LLL

end LatticeCrypto.Foundations.Algorithms
