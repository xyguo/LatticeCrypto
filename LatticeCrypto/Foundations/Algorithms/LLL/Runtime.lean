import LatticeCrypto.Foundations.Algorithms.LLL.Defs
import LatticeCrypto.Foundations.Algorithms.LLL.Algorithm
import LatticeCrypto.Foundations.Algorithms.LLL.Correctness

namespace LatticeCrypto.Foundations.Algorithms

open scoped Real RealInnerProductSpace
open scoped Classical
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Foundations.Lattice

variable {n k : ℕ+}

namespace LLL


noncomputable section runtime_analysis
/-!
## Runtime analysis skeleton
  The algorithm runs in polynomial time for integral bases
-/

/-!
### Prefix Gram determinants and potential function

The LLL potential is the product of the determinants of sublattices spanned by
the first i basis vectors. For a basis B = (b_1, ..., b_k), the i-th prefix
sublattice L_i is spanned by (b_1, ..., b_i), and its determinant equals:
  det(L_i) = ∏_{j=0}^{i-1} ‖b*_j‖
where b*_j are the Gram-Schmidt vectors.

The total potential is Φ(B) = ∏_{i=0}^{k-1} det(L_i).
-/

/-- Determinant of the Gram matrix of the first (i+1) basis vectors.
This equals the product of squared norms of the first (i+1) Gram-Schmidt vectors. -/
noncomputable def prefixGramDet (B : LatticeBasis n k) (i : Fin k) : ℝ :=
  ∏ j : Fin (i.1 + 1), ‖bStarFun B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩‖ ^ 2

/-- Alternative definition: Gram determinant as the determinant of the Gram matrix. -/
noncomputable def prefixGramDet' (B : LatticeBasis n k) (i : Fin k) : ℝ :=
  let vecs : Fin (i.1 + 1) → 𝓔 n := fun j => B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩
  let G : Matrix (Fin (i.1 + 1)) (Fin (i.1 + 1)) ℝ := fun r c => ⟪vecs r, vecs c⟫
  Matrix.det G

/-- The two definitions of prefix Gram determinant coincide.

PROVIDED SOLUTION
The idea is to note that the Gram-Schmidt decomposition can be re-expressed as a QR decomposition B = QR, where Q is an orthonormal matrix (the normalized Gram-Schmidt vectors) and R is upper-triangular with diagonal entries equal to the norms of the Gram-Schmidt vectors.
The Gram matrix G = B^T B can then be expressed as G = R^T Q^T Q R = R^T R, and its determinant is the product of det(R^T) and det(R), which equals the squares of the diagonal entries of R (since R is triangular), which are the norms of the Gram-Schmidt vectors.
-/
theorem prefixGramDet_eq_prefixGramDet' (B : LatticeBasis n k) (i : Fin k) :
    prefixGramDet B i = prefixGramDet' B i := by
  classical
  -- Unfold the Gram matrix of the prefix vectors.
  let m : ℕ+ := ⟨i.1 + 1, Nat.succ_pos _⟩
  let vecs : Fin m → 𝓔 n :=
    fun j => B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩
  -- Linear independence of the prefix vectors follows from the basis.
  have hlin : LinearIndependent ℝ vecs := by
    -- `B.li` composed with the embedding into `Fin k`.
    refine (LinearIndependent.comp B.li (fun j : Fin m =>
      (⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ : Fin k)) ?_)
    intro a b h
    apply Fin.ext
    simpa using congrArg Fin.val h
  -- Apply the Gram determinant lemma.
  have hgram : Matrix.det (Matrix.gram ℝ vecs) =
      ∏ j : Fin m, ‖InnerProductSpace.gramSchmidt ℝ vecs j‖ ^ 2 := by
    simpa using (det_gram_eq_prod_gramSchmidt_norm_sq (v := vecs))
  have hgs : ∀ j : Fin m,
      InnerProductSpace.gramSchmidt ℝ vecs j =
        InnerProductSpace.gramSchmidt ℝ B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩ := by
    simpa [m, vecs] using
      (LatticeCrypto.Utils.LinearAlgebra.gramSchmidt_prefix_eq (B := B.basis) (i := i))
  -- Match definitions.
  have hgram' : Matrix.det (Matrix.gram ℝ vecs) =
      ∏ j : Fin m, ‖InnerProductSpace.gramSchmidt ℝ B.basis
        ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩‖ ^ 2 := by
    simpa [hgs] using hgram
  simpa [prefixGramDet, prefixGramDet', vecs, Matrix.gram, bStarFun, m] using hgram'.symm

/-- For integral bases, the Gram determinants are integers. -/
noncomputable def prefixGramDetInt (B : Integral.IntegralLatticeBasis n k) (i : Fin k) : ℤ :=
  let vecs : Fin (i.1 + 1) → Fin n → ℤ :=
    fun j r => B.matrix r ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩
  let G : Matrix (Fin (i.1 + 1)) (Fin (i.1 + 1)) ℤ := fun r c =>
    ∑ t : Fin n, vecs r t * vecs c t
  Matrix.det G

/-- The integer Gram determinants coerce to the real Gram determinants. -/
theorem prefixGramDetInt_coe (B : Integral.IntegralLatticeBasis n k) (i : Fin k) :
    (prefixGramDetInt B i : ℝ) = prefixGramDet (B : LatticeBasis n k) i := by
  classical
  -- Reduce to the Gram determinant over ℝ.
  have hreal : (prefixGramDetInt B i : ℝ) = prefixGramDet' (B : LatticeBasis n k) i := by
    -- Unfold the integer Gram matrix and compare to the real Gram matrix.
    let m : ℕ+ := ⟨i.1 + 1, Nat.succ_pos _⟩
    let vecsZ : Fin m → Fin n → ℤ :=
      fun j r => B.matrix r ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩
    let Gz : Matrix (Fin m) (Fin m) ℤ := fun r c =>
      ∑ t : Fin n, vecsZ r t * vecsZ c t
    let vecsR : Fin m → 𝓔 n := fun j =>
      (B : LatticeBasis n k).basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩
    have hG : (fun r c => (Gz r c : ℝ)) = fun r c => ⟪vecsR r, vecsR c⟫ := by
      ext r c
      -- Inner product in Euclidean space is the sum of coordinate products.
      simp [vecsR, vecsZ, Gz, PiLp.inner_apply,
        Integral.IntegralLatticeBasis.toRealBasis, mul_comm]
    -- Cast the determinant entrywise.
    have hdet : ((Matrix.det (R := ℤ) Gz) : ℝ) = Matrix.det (fun r c => (Gz r c : ℝ)) := by
      -- Expand determinant as sum over permutations and cast termwise.
      simp [Matrix.det_apply', Int.cast_sum, Int.cast_mul, Int.cast_prod]
    have hdet' : Matrix.det (fun r c => (Gz r c : ℝ)) =
        Matrix.det (fun r c => ⟪vecsR r, vecsR c⟫) := by
      simp [hG]
    have hdet'' : ((Matrix.det (R := ℤ) Gz) : ℝ) =
        Matrix.det (fun r c => ⟪vecsR r, vecsR c⟫) := by
      exact hdet.trans hdet'
    -- Finish by rewriting the real Gram matrix.
    simpa [prefixGramDetInt, prefixGramDet', Gz, vecsZ, vecsR] using hdet''
  -- Use the equality of real Gram determinant and the product form.
  simpa [prefixGramDet_eq_prefixGramDet'] using hreal

/-- LLL potential function: product of prefix Gram determinants.
For general bases, this is a real number. For integral bases, it's an integer. -/
noncomputable def LLLPotential (B : LatticeBasis n k) : ℝ :=
  ∏ i : Fin k, prefixGramDet B i

/-- The LLL potential equals the product of squared norms of Gram-Schmidt vectors over all prefixes. -/
theorem LLLPotential_eq (B : LatticeBasis n k) :
    LLLPotential B =  ∏ i : Fin k, ∏ j : Fin (i.1 + 1), ‖bStarFun B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩‖ ^ 2 :=
    rfl

/-- The LLL potential is positive. -/
theorem LLLPotential_pos (B : LatticeBasis n k) :
    0 < LLLPotential B := by
  classical
  -- Each prefix Gram determinant is a product of positive terms.
  have hprefix : ∀ i : Fin k, 0 < prefixGramDet B i := by
    intro i
    -- Each Gram-Schmidt vector is nonzero by linear independence.
    have hpos : ∀ j : Fin (i.1 + 1),
        0 < ‖bStarFun B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩‖ ^ 2 := by
      intro j
      let j' : Fin k := ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩
      have hne : bStarFun B.basis j' ≠ 0 := by
        simpa [bStarFun] using
          (InnerProductSpace.gramSchmidt_ne_zero (f := B.basis) (n := j') B.li)
      have hnorm : 0 < ‖bStarFun B.basis j'‖ := by
        simpa [norm_pos_iff] using hne
      simpa using (pow_pos hnorm 2)
    -- Product of positive terms is positive.
    have :=
      Finset.prod_pos (s := (Finset.univ : Finset (Fin (i.1 + 1))))
        (f := fun j : Fin (i.1 + 1) =>
          ‖bStarFun B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩‖ ^ 2)
        (by intro j hj; exact hpos j)
    simpa [prefixGramDet] using this

  -- Product of positive prefix determinants is positive.
  have :=
    Finset.prod_pos (s := (Finset.univ : Finset (Fin k)))
      (f := fun i : Fin k => prefixGramDet B i)
      (by intro i hi; exact hprefix i)
  simpa [LLLPotential] using this

/--
  For integral bases, the LLL potential is at least 1.
  This is the only condition we need to prove the number of iterations is bounded.
-/
theorem LLLPotential_pos_of_integral (B : Integral.IntegralLatticeBasis n k) :
    1 ≤ LLLPotential (B : LatticeBasis n k) := by
  classical
  -- Rewrite the potential as an integer-valued product.
  have hcoe : LLLPotential (B : LatticeBasis n k) =
      (∏ i : Fin k, (prefixGramDetInt B i : ℝ)) := by
    simp [LLLPotential, prefixGramDetInt_coe]
  let z : ℤ := ∏ i : Fin k, prefixGramDetInt B i
  have hzposR : (0 : ℝ) < (z : ℝ) := by
    have hpos := LLLPotential_pos (B := (B : LatticeBasis n k))
    simpa [hcoe, z] using hpos
  have hzposZ : (0 : ℤ) < z := by
    exact_mod_cast hzposR
  have hzge1Z : (1 : ℤ) ≤ z := by
    have := (Int.add_one_le_iff).2 hzposZ
    simpa using this
  have hzge1R : (1 : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast hzge1Z
  simpa [hcoe, z] using hzge1R


/-!
### Iteration bounds
-/


/-- Initial potential bound for integral bases in terms of basis norms.

PROVIDED SOLUTION
Note that maxNorm(B.basis) is an upperbound for any ‖ bStarFun B.basis j ‖ (because for every i, ‖ B.basis i ‖ ≥ ‖ bStarFun B.basis i ‖), then use the definition of LLLPotential as the product of ‖ bStarFun B.basis i ‖ by unfolding `prefixGramDet`. Lastly, count the number of times each ‖ bStarFun B.basis j ‖ appears in the total product to get the exponent.
-/
theorem LLLPotential_initial_bound (B : LatticeBasis n k) :
    LLLPotential (B : LatticeBasis n k) ≤
      (maxBasisNorm (B : LatticeBasis n k)) ^ ((k : ℝ) * (k + 1 : ℝ)) := by
  classical
  set M : ℝ := maxBasisNorm (B : LatticeBasis n k)
  have h_bstar_le_basis : ∀ j : Fin k, ‖bStarFun B.basis j‖ ≤ ‖B.basis j‖ := by
    intro j
    -- Decompose `B.basis j` into its Gram-Schmidt component and the orthogonal sum.
    let s : 𝓔 n :=
      ∑ i ∈ Finset.Iio j,
        (⟪bStarFun B.basis i, B.basis j⟫ / ‖bStarFun B.basis i‖ ^ 2) • bStarFun B.basis i
    have hdecomp : B.basis j = bStarFun B.basis j + s := by
      simpa [bStarFun, s] using
        (InnerProductSpace.gramSchmidt_def'' (𝕜 := ℝ) (f := B.basis) j)
    have horth : ⟪bStarFun B.basis j, s⟫ = 0 := by
      -- `bStarFun` is orthogonal to all previous Gram-Schmidt vectors.
      classical
      have hsum :
          ⟪bStarFun B.basis j, s⟫ =
            ∑ x ∈ Finset.Iio j,
              (⟪bStarFun B.basis x, B.basis j⟫ / ‖bStarFun B.basis x‖ ^ 2) *
                ⟪bStarFun B.basis j, bStarFun B.basis x⟫ := by
        simp [s, inner_sum, inner_smul_right]
      rw [hsum]
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hx' : (x : Fin k) ≠ j := by
        exact ne_of_lt (Finset.mem_Iio.mp hx)
      have hinner : ⟪bStarFun B.basis j, bStarFun B.basis x⟫ = 0 := by
        exact bStarFun_orthogonal B.basis j x hx'.symm
      simp [hinner]
    have hpyth : ‖B.basis j‖ ^ 2 = ‖bStarFun B.basis j‖ ^ 2 + ‖s‖ ^ 2 := by
      -- Apply Pythagoras to the orthogonal decomposition.
      have :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := bStarFun B.basis j)
          (y := s) horth
      simpa [hdecomp, pow_two] using this
    have hsq : ‖bStarFun B.basis j‖ ^ 2 ≤ ‖B.basis j‖ ^ 2 := by
      nlinarith [hpyth, sq_nonneg ‖s‖]
    have habs : |‖bStarFun B.basis j‖| ≤ |‖B.basis j‖| := (sq_le_sq).1 hsq
    simpa using habs

  have h_basis_le_M : ∀ j : Fin k, ‖B.basis j‖ ≤ M := by
    intro j
    unfold M maxBasisNorm LatticeCrypto.Utils.LinearAlgebra.maxNorm
    exact Finset.le_max' (Finset.univ.image fun i : Fin k => ‖B.basis i‖) _
      (Finset.mem_image_of_mem _ (Finset.mem_univ j))

  have h_bstar_le_M : ∀ j : Fin k, ‖bStarFun B.basis j‖ ≤ M := by
    intro j
    exact le_trans (h_bstar_le_basis j) (h_basis_le_M j)

  have h_term_le :
      ∀ i : Fin k,
        ∀ j : Fin (i.1 + 1),
          ‖bStarFun B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩‖ ^ 2 ≤ M ^ 2 := by
    intro i j
    have hle :
        ‖bStarFun B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩‖ ≤ M :=
      h_bstar_le_M ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2

  have h_prod_le :
      ∏ i : Fin k,
          ∏ j : Fin (i.1 + 1),
            ‖bStarFun B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩‖ ^ 2
        ≤ ∏ i : Fin k, ∏ j : Fin (i.1 + 1), M ^ 2 := by
    -- Pointwise bound each Gram-Schmidt norm by `M`.
    have h_inner_le :
        ∀ i : Fin k,
          ∏ j : Fin (i.1 + 1),
            ‖bStarFun B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩‖ ^ 2
              ≤ ∏ j : Fin (i.1 + 1), M ^ 2 := by
      intro i
      refine Finset.prod_le_prod ?_ ?_
      · intro j hj
        exact sq_nonneg _
      · intro j hj
        exact h_term_le i j
    -- Combine over prefixes.
    exact
      (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin k)))
        (f := fun i : Fin k =>
          ∏ j : Fin (i.1 + 1),
            ‖bStarFun B.basis ⟨j, Nat.lt_of_lt_of_le j.2 (Nat.succ_le_of_lt i.2)⟩‖ ^ 2)
        (g := fun i : Fin k => ∏ j : Fin (i.1 + 1), M ^ 2)
        (by
          intro i hi
          -- inner products are nonnegative
          refine Finset.prod_nonneg ?_
          intro j hj; exact sq_nonneg _)
        (by
          intro i hi
          exact h_inner_le i))

  have h_prod_le' :
      LLLPotential (B : LatticeBasis n k) ≤
        ∏ i : Fin k, ∏ j : Fin (i.1 + 1), M ^ 2 := by
    simpa [LLLPotential_eq] using h_prod_le

  -- Evaluate the constant product.
  have h_prod_eq :
      (∏ i : Fin k, ∏ j : Fin (i.1 + 1), M ^ 2) =
        M ^ ((k : ℝ) * (k + 1 : ℝ)) := by
    -- Compute the number of factors: there are k(k+1)/2 terms, each contributing a square.
    -- Use `prod_pow_eq_pow_sum` and the closed form of the arithmetic series.
    have hsum_range :
        (∑ i : Fin k, (i.1 + 1)) = Finset.sum (Finset.range (k : ℕ)) (fun i => i + 1) := by
      classical
      simpa using
        (Fin.sum_univ_eq_sum_range (n := (k : ℕ)) (f := fun i : ℕ => i + 1))
    have hsum2 : 2 * (∑ i : Fin k, (i.1 + 1)) = (k : ℕ) * (k + 1 : ℕ) := by
      have hsum_add :
          Finset.sum (Finset.range (k : ℕ)) (fun i => i + 1) =
            Finset.sum (Finset.range (k : ℕ)) (fun i => i) + (k : ℕ) := by
        -- sum of (i + 1) = sum of i + sum of 1
        have h1 :
            Finset.sum (Finset.range (k : ℕ)) (fun i => i + 1) =
              Finset.sum (Finset.range (k : ℕ)) (fun i => i) +
                Finset.sum (Finset.range (k : ℕ)) (fun _ => (1 : ℕ)) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (Finset.sum_add_distrib (s := Finset.range (k : ℕ))
              (f := fun i => i) (g := fun _ => (1 : ℕ)))
        simpa using h1
      calc
        2 * (∑ i : Fin k, (i.1 + 1))
            = 2 * Finset.sum (Finset.range (k : ℕ)) (fun i => i + 1) := by
          simp [hsum_range]
        _ = 2 * (Finset.sum (Finset.range (k : ℕ)) (fun i => i) + (k : ℕ)) := by
          simp [hsum_add]
        _ = 2 * Finset.sum (Finset.range (k : ℕ)) (fun i => i) + 2 * (k : ℕ) := by
                nlinarith
        _ = (k : ℕ) * (k - 1) + 2 * (k : ℕ) := by
          have hmul : 2 * Finset.sum (Finset.range (k : ℕ)) (fun i => i) =
              (k : ℕ) * (k - 1) := by
            simpa [mul_comm] using (Finset.sum_range_id_mul_two (n := (k : ℕ)))
          simp [hmul]
        _ = (k : ℕ) * (k + 1) := by
          have hk : (1 : ℕ) ≤ (k : ℕ) := by exact k.pos
          calc
            (k : ℕ) * (k - 1) + 2 * (k : ℕ)
                = (k : ℕ) * (k - 1) + (k : ℕ) * 2 := by
              simp [Nat.mul_comm]
            _ = (k : ℕ) * ((k - 1) + 2) := by
              simp [Nat.mul_add]
            _ = (k : ℕ) * (k + 1) := by
              have h1 : (k : ℕ) - 1 + 1 = (k : ℕ) := by
                exact Nat.sub_add_cancel hk
              have h : (k : ℕ) - 1 + 2 = (k : ℕ) + 1 := by
                calc
                  (k : ℕ) - 1 + 2 = (k : ℕ) - 1 + (1 + 1) := by rfl
                  _ = ((k : ℕ) - 1 + 1) + 1 := by simp [Nat.add_assoc]
                  _ = (k : ℕ) + 1 := by simp [h1]
              simp [h]
    -- Rewrite the product of constants.
    calc
      (∏ i : Fin k, ∏ j : Fin (i.1 + 1), M ^ 2)
          = ∏ i : Fin k, (M ^ 2) ^ (i.1 + 1) := by
              simp
      _ = (M ^ 2) ^ (∑ i : Fin k, (i.1 + 1)) := by
              simpa using (Finset.prod_pow_eq_pow_sum (s := (Finset.univ : Finset (Fin k)))
                (a := M ^ 2) (f := fun i : Fin k => (i.1 + 1)))
      _ = M ^ (2 * (∑ i : Fin k, (i.1 + 1))) := by
              simp [pow_mul]
                        _ = M ^ ((k : ℕ) * (k + 1 : ℕ)) := by
                          simp [hsum2]
                        _ = M ^ ((k : ℕ) * (k + 1 : ℕ) : ℝ) := by
                          simpa using (Real.rpow_natCast M ((k : ℕ) * (k + 1 : ℕ))).symm
                        _ = M ^ ((k : ℝ) * (k + 1 : ℝ)) := by
                          -- Cast the exponent to ℝ.
                          norm_cast

  exact h_prod_le'.trans (by simpa [M] using (le_of_eq h_prod_eq))

/--
  Size reduction preserves the LLL potential.

PROVIDED SOLUTION
Use the fact that size reduction preserves the Gram-Schmidt vectors, hence the norms of the Gram-Schmidt vectors, hence the prefix Gram determinants, hence the potential.
-/
theorem sizeReduce_preserves_potential (B : LatticeBasis n k) :
    LLLPotential (sizeReduce B) = LLLPotential B := by
  classical
  have hGS : bStarFun (sizeReduce B).basis = bStarFun B.basis := by
    simpa using (sizeReduce_preserve_GS (B := B))
  simp [LLLPotential, prefixGramDet, hGS]

/--
  Swapping adjacent basis vectors preserves prefix Gram determinants
  for all prefixes not involving the swapped indices.

PROVIDED SOLUTION
For j < i this is trivial since the first j basis vectors are unchanged. For j ≥ i + 1, the Gram matrix has its ith and (i+1)th columns and rows swapped. Swapping two rows and the corresponding two columns of a matrix does not change its determinant, hence the prefix Gram determinant remains unchanged.
-/
lemma swapAdjacent_preserve_prefixGramDet
    (B : LatticeBasis n k) (i : Fin k) (hi : i.1 + 1 < k) (j : Fin k) (hj : j ≠ i) :
    prefixGramDet (swapAdjacent B i hi) j = prefixGramDet B j := by
  classical
  -- Work with the Gram determinant formulation.
  have h' : prefixGramDet' (swapAdjacent B i hi) j = prefixGramDet' B j := by
    have hj' : j < i ∨ i < j := lt_or_gt_of_ne hj
    cases hj' with
    | inl hjlt =>
        -- For j < i, the prefix vectors are unchanged.
        let m : ℕ+ := ⟨j.1 + 1, Nat.succ_pos _⟩
        let emb : Fin m → Fin k := fun t =>
          ⟨t.1, Nat.lt_of_lt_of_le t.2 (Nat.succ_le_of_lt j.2)⟩
        let vecs : Fin m → 𝓔 n := fun t => B.basis (emb t)
        let vecs' : Fin m → 𝓔 n := fun t => (swapAdjacent B i hi).basis (emb t)
        have hvec : vecs' = vecs := by
          funext t
          have htle : t.1 ≤ j.1 := Nat.lt_succ_iff.mp t.2
          have hjlt' : j.1 < i.1 := (Fin.lt_iff_val_lt_val.mp hjlt)
          have htlt : (emb t).1 < i.1 := lt_of_le_of_lt htle hjlt'
          let u : Fin k := emb t
          have htne : u ≠ i := by
            exact ne_of_lt (Fin.lt_iff_val_lt_val.mpr htlt)
          have htne2 : u ≠ ⟨i.1 + 1, hi⟩ := by
            have htlt' : u.1 < i.1 + 1 := lt_trans htlt (Nat.lt_succ_self _)
            exact ne_of_lt (Fin.lt_iff_val_lt_val.mpr htlt')
          have : swapAdjacentVectors B.basis i hi u = B.basis u := by
            simp [swapAdjacentVectors, htne, htne2]
          simpa [vecs', vecs, swapAdjacent, u, emb] using this
        -- use the equality of vectors to match determinants
        have hdet : Matrix.det (Matrix.gram ℝ vecs') = Matrix.det (Matrix.gram ℝ vecs) := by
          simp [hvec]
        simpa [prefixGramDet', vecs', vecs, Matrix.gram] using hdet
    | inr hjgt =>
        -- For i < j, the prefix vectors are swapped by a permutation.
        let m : ℕ+ := ⟨j.1 + 1, Nat.succ_pos _⟩
        let emb : Fin m → Fin k := fun t =>
          ⟨t.1, Nat.lt_of_lt_of_le t.2 (Nat.succ_le_of_lt j.2)⟩
        let vecs : Fin m → 𝓔 n := fun t => B.basis (emb t)
        let vecs' : Fin m → 𝓔 n := fun t => (swapAdjacent B i hi).basis (emb t)
        have hji : i.1 < j.1 := by
          exact (Fin.lt_iff_val_lt_val.mp hjgt)
        let i' : Fin m := ⟨i.1, Nat.lt_of_lt_of_le hji (Nat.le_succ _)⟩
        let i1' : Fin m :=
          ⟨i.1 + 1, Nat.succ_lt_succ hji⟩
        let e : Equiv.Perm (Fin m) := Equiv.swap i' i1'
        have hEmb_i : emb i' = i := by
          apply Fin.ext; rfl
        have hEmb_i1 : emb i1' = ⟨i.1 + 1, hi⟩ := by
          apply Fin.ext; rfl
        have hne_i1_i : (⟨i.1 + 1, hi⟩ : Fin k) ≠ i := by
          intro h
          have := congrArg Fin.val h
          linarith
        have hvec : vecs' = vecs ∘ e := by
          funext t
          by_cases ht : t = i'
          · subst ht
            -- e i' = i1'
            simp [vecs', vecs, emb, e, hEmb_i, hEmb_i1, swapAdjacent, swapAdjacentVectors]
          · by_cases ht1 : t = i1'
            · subst ht1
              -- e i1' = i'
              have hv1 : vecs' i1' = B.basis i := by
                simp [vecs', emb, swapAdjacent, swapAdjacentVectors, hEmb_i1, hne_i1_i, i1']
              have hv2 : vecs (e i1') = B.basis i := by
                simp [vecs, e, hEmb_i]
              simp [hv1, hv2]
            · have hti : emb t ≠ i := by
                intro h
                apply ht
                apply Fin.ext
                simpa using congrArg Fin.val h
              have hti1 : emb t ≠ ⟨i.1 + 1, hi⟩ := by
                intro h
                apply ht1
                apply Fin.ext
                simpa using congrArg Fin.val h
              have hv1 : vecs' t = vecs t := by
                have : swapAdjacentVectors B.basis i hi (emb t) = B.basis (emb t) := by
                  simp [swapAdjacentVectors, hti, hti1]
                simpa [vecs', vecs, swapAdjacent] using this
              have hswap : e t = t := by
                simp [e, Equiv.swap_apply_def, ht, ht1]
              have hv2 : vecs (e t) = vecs t := by
                simp [vecs, hswap]
              simp [hv1, hv2]
        have hgram : Matrix.gram ℝ vecs' = (Matrix.gram ℝ vecs).submatrix e e := by
          ext r c
          simp [Matrix.gram, hvec]
        have hdet : Matrix.det (Matrix.gram ℝ vecs') = Matrix.det (Matrix.gram ℝ vecs) := by
          calc
            Matrix.det (Matrix.gram ℝ vecs') =
                Matrix.det ((Matrix.gram ℝ vecs).submatrix e e) := by
                  simp [hgram]
            _ = Matrix.det (Matrix.gram ℝ vecs) := by
                  simp [Matrix.det_submatrix_equiv_self (e := e) (A := Matrix.gram ℝ vecs)]
        simpa [prefixGramDet', vecs', vecs, Matrix.gram] using hdet
  -- Switch back to `prefixGramDet`.
  simpa [prefixGramDet_eq_prefixGramDet'] using h'

/-- `swapAdjacent` does not change the basis vectors before the swapped positions -/
lemma swapAdjacent_basis_eq_of_lt
    (B : LatticeBasis n k) (i : Fin k) (hi : i.1 + 1 < k) (j : Fin k) (hj : j < i) :
    (swapAdjacent B i hi).basis j = B.basis j := by
  have hjne : j ≠ i := by
    exact ne_of_lt hj
  have hjne2 : j ≠ ⟨i.1 + 1, hi⟩ := by
    apply ne_of_lt
    have hj' : j.1 < i.1 := (Fin.lt_iff_val_lt_val.mp hj)
    exact (Fin.lt_iff_val_lt_val.mpr (lt_trans hj' (Nat.lt_succ_self _)))
  simp [swapAdjacent, swapAdjacentVectors, hjne, hjne2]

/-- `swapAdjacent` does not change the Gram-Schmidt basis vectors before the swapped positions -/
lemma swapAdjacent_bStarFun_eq_of_lt
    (B : LatticeBasis n k) (i : Fin k) (hi : i.1 + 1 < k) (j : Fin k) (hj : j < i) :
    bStarFun (swapAdjacent B i hi).basis j = bStarFun B.basis j := by
  classical
  let m : ℕ+ := ⟨j.1 + 1, Nat.succ_pos _⟩
  let emb : Fin m → Fin k := fun t =>
    ⟨t.1, Nat.lt_of_lt_of_le t.2 (Nat.succ_le_of_lt j.2)⟩
  let vecs : Fin m → 𝓔 n := fun t => B.basis (emb t)
  let vecs' : Fin m → 𝓔 n := fun t => (swapAdjacent B i hi).basis (emb t)
  have hvec : vecs' = vecs := by
    funext t
    have htle : t.1 ≤ j.1 := Nat.lt_succ_iff.mp t.2
    have hjlt' : j.1 < i.1 := (Fin.lt_iff_val_lt_val.mp hj)
    have htlt : (emb t).1 < i.1 := lt_of_le_of_lt htle hjlt'
    let u : Fin k := emb t
    have htne : u ≠ i := by
      exact ne_of_lt (Fin.lt_iff_val_lt_val.mpr htlt)
    have htne2 : u ≠ ⟨i.1 + 1, hi⟩ := by
      have htlt' : u.1 < i.1 + 1 := lt_trans htlt (Nat.lt_succ_self _)
      exact ne_of_lt (Fin.lt_iff_val_lt_val.mpr htlt')
    have : swapAdjacentVectors B.basis i hi u = B.basis u := by
      simp [swapAdjacentVectors, htne, htne2]
    simpa [vecs', vecs, swapAdjacent, u, emb] using this
  have hgs' : InnerProductSpace.gramSchmidt ℝ vecs'
      ⟨j.1, Nat.lt_succ_self _⟩ = bStarFun (swapAdjacent B i hi).basis j := by
    simpa [bStarFun, m, vecs', emb] using
      (LatticeCrypto.Utils.LinearAlgebra.gramSchmidt_prefix_eq
        (B := (swapAdjacent B i hi).basis) (i := j) ⟨j.1, Nat.lt_succ_self _⟩)
  have hgs : InnerProductSpace.gramSchmidt ℝ vecs
      ⟨j.1, Nat.lt_succ_self _⟩ = bStarFun B.basis j := by
    simpa [bStarFun, m, vecs, emb] using
      (LatticeCrypto.Utils.LinearAlgebra.gramSchmidt_prefix_eq
        (B := B.basis) (i := j) ⟨j.1, Nat.lt_succ_self _⟩)
  calc
    bStarFun (swapAdjacent B i hi).basis j
        = InnerProductSpace.gramSchmidt ℝ vecs' ⟨j.1, Nat.lt_succ_self _⟩ := by
            simpa using hgs'.symm
    _ = InnerProductSpace.gramSchmidt ℝ vecs ⟨j.1, Nat.lt_succ_self _⟩ := by
            simp [hvec]
    _ = bStarFun B.basis j := by
            simpa using hgs

/-- The Gram-Schmidt vector corresponding to index `i` for an independent basis is nonzero. -/
lemma bStarFun_ne_zero (B : LatticeBasis n k) (i : Fin k) : bStarFun B.basis i ≠ 0 := by
  simpa [bStarFun] using
    (InnerProductSpace.gramSchmidt_ne_zero (f := B.basis) (n := i) B.li)

/-- The Gram-Schmidt vector corresponding to index `i` after swapping adjacent basis vectors is equal to the projection of the original basis vector at `i+1` onto the trailing subspace span{B_i,...,B_k}. -/
lemma bStarFun_swap_eq_proj (B : LatticeBasis n k) (i : Fin k) (hi : i.1 + 1 < k) :
    bStarFun (swapAdjacent B i hi).basis i =
      projTrailingSubspace B i (B.basis ⟨i.1 + 1, hi⟩) := by
  classical
  unfold bStarFun projTrailingSubspace
  have hsum_proj :
      ∑ j ∈ Finset.Iio i, projGsVec (B.basis ⟨i.1 + 1, hi⟩) B.basis j =
        ∑ j ∈ Finset.Iio i,
          (Submodule.span ℝ {bStarFun B.basis j}).starProjection (B.basis ⟨i.1 + 1, hi⟩) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      unfold projGsVec projGsCoeff
      simp [Submodule.starProjection_singleton, real_inner_comm, inner_self_eq_norm_sq_to_K]
  rw [InnerProductSpace.gramSchmidt_def]
  have hbi : (swapAdjacent B i hi).basis i = B.basis ⟨i.1 + 1, hi⟩ := by
    simp [swapAdjacent, swapAdjacentVectors]
  have hsum_swap :
      ∑ j ∈ Finset.Iio i,
        (Submodule.span ℝ {InnerProductSpace.gramSchmidt ℝ (swapAdjacent B i hi).basis j}).starProjection
          (B.basis ⟨i.1 + 1, hi⟩)
        =
      ∑ j ∈ Finset.Iio i,
        (Submodule.span ℝ {bStarFun B.basis j}).starProjection (B.basis ⟨i.1 + 1, hi⟩) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hjlt : j < i := Finset.mem_Iio.mp hj
      have hgs : bStarFun (swapAdjacent B i hi).basis j = bStarFun B.basis j :=
        swapAdjacent_bStarFun_eq_of_lt B i hi j hjlt
      have hgs' : InnerProductSpace.gramSchmidt ℝ (swapAdjacent B i hi).basis j =
          InnerProductSpace.gramSchmidt ℝ B.basis j := by
        simpa [bStarFun] using hgs
      simp [hgs', bStarFun]
  rw [hbi]
  -- Convert the RHS sum over the subtype to a sum over the finset.
  rw [Finset.sum_coe_sort]
  rw [hsum_swap, hsum_proj]

/-- Swapping adjacent basis vectors changes the prefix Gram determinant by scaling it with the ratio of the squared norms of the projected trailing subspace vector and the original Gram-Schmidt vector. -/
lemma prefixGramDet_of_swapAdjacent_eq (B : LatticeBasis n k) (i : Fin k) (hi : i.1 + 1 < k) :
    prefixGramDet (swapAdjacent B i hi) i =
    prefixGramDet B i * (‖projTrailingSubspace B i (B.basis ⟨i.1 + 1, hi⟩)‖ ^ 2 / ‖bStarFun B.basis i‖ ^ 2) := by
      field_simp;
      rw [ eq_div_iff ];
      · -- Apply the definition of `prefixGramDet`
        rw [LatticeCrypto.Foundations.Algorithms.LLL.prefixGramDet, LatticeCrypto.Foundations.Algorithms.LLL.prefixGramDet];
        rw [ Fin.prod_univ_castSucc, Fin.prod_univ_castSucc ];
        rw [ mul_right_comm ];
        congr! 1;
        · congr! 1;
          refine' Finset.prod_congr rfl fun j hj => _;
          rw [ LatticeCrypto.Foundations.Algorithms.LLL.swapAdjacent_bStarFun_eq_of_lt ];
          exact Fin.castSucc_lt_last j;
        · convert congr_arg ( fun x : 𝓔 n => ‖x‖ ^ 2 ) ( bStarFun_swap_eq_proj B i hi ) using 1;
      · exact ne_of_gt ( sq_pos_of_pos ( norm_pos_iff.mpr ( bStarFun_ne_zero B i ) ) )


/--
  Each swap decreases potential by at least the factor δ.
  This way we can show that the LLL step either reduces potential (via swaps) or the basis is already reduced.

PROVIDED SOLUTION
Use the previous lemma `swapAdjacent_preserve_prefixGramDet` we only need to consider the ratio between `‖ b'^*_i‖` vs `‖ b^*_i‖`. Specifically, `b'^*_i` will be the component of b^*_{i+1} that's orthogonal to span{b^*_1, ..., b^*_{i-1}}, which can be expressed as μ[i+1,i]*b^*_i + b^*_{i+1}. Using the Lovasz condition violation, we have that the norm of this vector squared is at least δ times the norm of b^*_i squared.
-/
theorem swapAdjacent_decreases_potential_by_factor
    (B : LatticeBasis n k) (δ : ℝ)
    (i : Fin k) (hi : i.1 + 1 < k) (h_viol : lovaszViolationAt B δ i) :
    LLLPotential (swapAdjacent B i hi) < δ * LLLPotential B := by
  classical
  set r : ℝ := ‖projTrailingSubspace B i (B.basis ⟨i.1 + 1, hi⟩)‖ ^ 2 /
    ‖bStarFun B.basis i‖ ^ 2
  have hpot_eq : LLLPotential (swapAdjacent B i hi) = LLLPotential B * r := by
    unfold LLLPotential
    calc
      Finset.prod (Finset.univ : Finset (Fin k)) (fun j => prefixGramDet (swapAdjacent B i hi) j)
          = (Finset.prod (Finset.erase (Finset.univ : Finset (Fin k)) i)
              (fun j => prefixGramDet (swapAdjacent B i hi) j)) *
              prefixGramDet (swapAdjacent B i hi) i := by
            simp [Finset.prod_erase_mul, Finset.mem_univ]
    _ = (Finset.prod (Finset.erase (Finset.univ : Finset (Fin k)) i)
      (fun j => prefixGramDet B j)) * prefixGramDet (swapAdjacent B i hi) i := by
      refine congrArg₂ _ ?_ rfl
      refine Finset.prod_congr rfl ?_
      intro j hj
      have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
      simpa using swapAdjacent_preserve_prefixGramDet B i hi j hjne
    _ = (Finset.prod (Finset.erase (Finset.univ : Finset (Fin k)) i)
      (fun j => prefixGramDet B j)) * (prefixGramDet B i * r) := by
      simp [prefixGramDet_of_swapAdjacent_eq, r]
    _ = ((Finset.prod (Finset.erase (Finset.univ : Finset (Fin k)) i)
      (fun j => prefixGramDet B j)) * prefixGramDet B i) * r := by
      simp [mul_assoc]
    _ = Finset.prod (Finset.univ : Finset (Fin k)) (fun j => prefixGramDet B j) * r := by
      simp [Finset.prod_erase_mul, Finset.mem_univ]

  obtain ⟨hi', hviol⟩ := h_viol
  have hidx : (⟨i.1 + 1, hi⟩ : Fin k) = ⟨i.1 + 1, hi'⟩ := by
    apply Fin.ext
    rfl
  have hviol' : ‖projTrailingSubspace B i (B.basis ⟨i.1 + 1, hi⟩)‖ ^ 2 <
      δ * ‖projTrailingSubspace B i (B.basis i)‖ ^ 2 := by
    simpa [hidx] using hviol
  have h_proj_i : projTrailingSubspace B i (B.basis i) = bStarFun B.basis i := by
    unfold projTrailingSubspace projGsVec projGsCoeff
    unfold bStarFun
    rw [eq_comm, InnerProductSpace.gramSchmidt_def]
    rw [← Finset.sum_coe_sort]
    congr! 2
    convert Submodule.starProjection_singleton _ _ using 1
    simp +decide [inner_self_eq_norm_sq_to_K]
    rw [real_inner_comm]
  have hviol'' : ‖projTrailingSubspace B i (B.basis ⟨i.1 + 1, hi⟩)‖ ^ 2 <
      δ * ‖bStarFun B.basis i‖ ^ 2 := by
    simpa [h_proj_i] using hviol'
  have hpos : 0 < ‖bStarFun B.basis i‖ ^ 2 := by
    have hne : bStarFun B.basis i ≠ 0 := by
      simpa [bStarFun] using
        (InnerProductSpace.gramSchmidt_ne_zero (f := B.basis) (n := i) B.li)
    have hnorm : 0 < ‖bStarFun B.basis i‖ := by
      simpa [norm_pos_iff] using hne
    simpa using (pow_pos hnorm 2)
  have hratio : r < δ := by
    dsimp [r]
    exact (div_lt_iff₀ hpos).2 hviol''

  calc
    LLLPotential (swapAdjacent B i hi) = LLLPotential B * r := hpot_eq
    _ < LLLPotential B * δ := by
      have hpot_pos : 0 < LLLPotential B := LLLPotential_pos B
      exact mul_lt_mul_of_pos_left hratio hpot_pos
    _ = δ * LLLPotential B := by
      ring

/-- If `firstLovaszViolation` returns `none`, then the basis satisfies the Lovasz condition. -/
lemma lovasz_of_firstLovaszViolation_none (B : LatticeBasis n k) (δ : ℝ)
    (h : firstLovaszViolation B δ = none) : LovaszCondition B δ := by
      -- By definition of `firstLovaszViolation`, if it returns `none`, then there are no Lovasz violations at any index `i`.
      have h_no_violations : ∀ i : Fin k, ¬(∃ hi : i.1 + 1 < k, δ * ‖projTrailingSubspace B i (B.basis i)‖ ^ 2 > ‖projTrailingSubspace B i (B.basis ⟨i.1 + 1, hi⟩)‖ ^ 2) := by
        unfold LatticeCrypto.Foundations.Algorithms.LLL.firstLovaszViolation at h;
        unfold LatticeCrypto.Foundations.Algorithms.LLL.lovaszViolationAt at h; aesop;
      -- By definition of `LovaszCondition'`, if there are no Lovasz violations at any index `i`, then the condition holds.
      have h_lovasz_condition : LovaszCondition' B δ := by
        exact fun i hi => le_of_not_gt fun h => h_no_violations i ⟨ hi, h ⟩;
      apply (LovaszCondition_iff_LovaszCondition' B δ).mpr h_lovasz_condition


/-- Corollary of the above two: One LLL step makes progress: either reduces potential or is already reduced. -/
theorem LLLStep_progress (B : LatticeBasis n k) (δ : ℝ) (hδ : IsDelta δ) :
    LLLReduced (LLLStep B δ) δ ∨ LLLPotential (LLLStep B δ) < δ * LLLPotential B := by
  have _hδ : IsDelta δ := hδ
  unfold LatticeCrypto.Foundations.Algorithms.LLL.LLLStep
  cases h' : firstLovaszViolation (LatticeCrypto.Foundations.Algorithms.LLL.sizeReduce B) δ with
  | none =>
      left
      simpa [LatticeCrypto.Foundations.Algorithms.LLL.LLLStep, h',
        LatticeCrypto.Foundations.Algorithms.LLL.LLLReduced] using
        (And.intro (LatticeCrypto.Foundations.Algorithms.LLL.sizeReduce_sizeReduced B)
          (LatticeCrypto.Foundations.Algorithms.LLL.lovasz_of_firstLovaszViolation_none _ _ h'))
  | some bad =>
      right
      have hdec :=
        LatticeCrypto.Foundations.Algorithms.LLL.swapAdjacent_decreases_potential_by_factor
          (LatticeCrypto.Foundations.Algorithms.LLL.sizeReduce B) δ
          bad.1 (Classical.choose bad.2) bad.2
      have hdec' :
          LLLPotential
              (swapAdjacent (LatticeCrypto.Foundations.Algorithms.LLL.sizeReduce B)
                bad.1 (Classical.choose bad.2))
            < δ * LLLPotential B := by
        simpa [LatticeCrypto.Foundations.Algorithms.LLL.sizeReduce_preserves_potential] using hdec
      simpa [LatticeCrypto.Foundations.Algorithms.LLL.LLLStep, h'] using hdec'

/-- The sizeReduce function preserves integrality of the lattice basis. -/
lemma sizeReduce_preserve_integrality (B : Integral.IntegralLatticeBasis n k) :
    let B' := (sizeReduce (B : LatticeBasis n k))
    ∃ B'' : Integral.IntegralLatticeBasis n k,
      B' = (B'' : LatticeBasis n k) := by
  classical
  dsimp
  -- Work with the real basis associated to the integral one.
  let Breal : LatticeBasis n k := (B : LatticeBasis n k)
  -- Use the size-reduction specification: multiplication by a unimodular matrix.
  rcases (sizeReduceBasisSpec_eq_matrix_mul
    (B := eucBasisToMatrix Breal.basis) (BStar := bStarFun Breal.basis)) with ⟨U, hU⟩
  -- Express the size-reduced basis via matrix multiplication.
  have hbasis : (sizeReduce Breal).basis =
      matrixToEucBasis ((eucBasisToMatrix Breal.basis) * U.real) := by
    have hsize :=
      (sizeReduceBasis_eq_sizeReduceBasisSpec (B := Breal.basis)
        (BStar := bStarFun Breal.basis))
    calc
      (sizeReduce Breal).basis
          = sizeReduceBasis Breal.basis (bStarFun Breal.basis) := by rfl
      _ = matrixToEucBasis (sizeReduceBasisSpec (eucBasisToMatrix Breal.basis) (bStarFun Breal.basis)) := by
            simpa using hsize
      _ = matrixToEucBasis ((eucBasisToMatrix Breal.basis) * U.real) := by
            simp [hU]
  -- Define the swapped integer matrix.
  let Mz : Matrix (Fin n) (Fin k) ℤ := B.matrix * (U : Matrix (Fin k) (Fin k) ℤ)
  -- Build the integral basis and show it matches the size-reduced basis.
  refine ⟨
    { matrix := Mz
      le_dim := B.le_dim
      li := by
        -- Transfer linear independence from the size-reduced basis.
        have hli : LinearIndependent ℝ (sizeReduce Breal).basis := (sizeReduce Breal).li
        -- Show the bases coincide after casting to ℝ.
        have hcast : (sizeReduce Breal).basis =
            (fun c : Fin k => piToEuc (fun r => (Mz r c : ℝ))) := by
          -- Compare via `eucToPi` on each coordinate.
          apply funext; intro c
          apply LatticeCrypto.Utils.Vec.eucToPi.injective
          funext r
          -- Left side via `hbasis`.
          have hleft :
              LatticeCrypto.Utils.Vec.eucToPi ((sizeReduce Breal).basis c) r =
                ((eucBasisToMatrix Breal.basis) * U.real) r c := by
            simp [hbasis, LatticeCrypto.Utils.Vec.eucToPi,
              LatticeCrypto.Utils.Vec.matrixToEucBasis_apply]
          -- Right side is just the cast of the integer product.
          have hright :
              LatticeCrypto.Utils.Vec.eucToPi (piToEuc (fun r => (Mz r c : ℝ))) r =
                (Mz r c : ℝ) := by
            simp [LatticeCrypto.Utils.Vec.piToEuc_apply]
          -- Combine.
          calc
            LatticeCrypto.Utils.Vec.eucToPi ((sizeReduce Breal).basis c) r
                = ((eucBasisToMatrix Breal.basis) * U.real) r c := hleft
            _ = (Mz r c : ℝ) := by
                -- Expand both sides.
                simp [Mz, Breal, Integral.IntegralLatticeBasis.toRealBasis,
                  LatticeCrypto.Utils.Vec.eucBasisToMatrix_apply, Matrix.mul_apply,
                  UnimodularMatrix.real, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
            _ = LatticeCrypto.Utils.Vec.eucToPi (piToEuc (fun r => (Mz r c : ℝ))) r := by
                simp [hright]
        simpa [hcast] using hli
    }, ?_⟩
  -- Final equality of bases.
  apply LatticeBasis.ext
  funext c
  funext r
  -- Reuse the basis equality established above.
  have hcast : (sizeReduce Breal).basis =
      (fun c : Fin k => piToEuc (fun r => (Mz r c : ℝ))) := by
    apply funext; intro c
    apply LatticeCrypto.Utils.Vec.eucToPi.injective
    funext r
    have hleft :
        LatticeCrypto.Utils.Vec.eucToPi ((sizeReduce Breal).basis c) r =
          ((eucBasisToMatrix Breal.basis) * U.real) r c := by
      simp [hbasis, LatticeCrypto.Utils.Vec.eucToPi,
        LatticeCrypto.Utils.Vec.matrixToEucBasis_apply]
    have hright :
        LatticeCrypto.Utils.Vec.eucToPi (piToEuc (fun r => (Mz r c : ℝ))) r =
          (Mz r c : ℝ) := by
      simp [LatticeCrypto.Utils.Vec.piToEuc_apply]
    calc
      LatticeCrypto.Utils.Vec.eucToPi ((sizeReduce Breal).basis c) r
          = ((eucBasisToMatrix Breal.basis) * U.real) r c := hleft
      _ = (Mz r c : ℝ) := by
          simp [Mz, Breal, Integral.IntegralLatticeBasis.toRealBasis,
            LatticeCrypto.Utils.Vec.eucBasisToMatrix_apply, Matrix.mul_apply,
            UnimodularMatrix.real, Matrix.map_apply, Int.cast_sum, Int.cast_mul]
      _ = LatticeCrypto.Utils.Vec.eucToPi (piToEuc (fun r => (Mz r c : ℝ))) r := by
          simp [hright]
  -- Use the pointwise consequence of `hcast`.
  have hcast' := congrArg (fun f => f c r) hcast
  simpa [Breal, Integral.IntegralLatticeBasis.toRealBasis,
    LatticeCrypto.Utils.Vec.piToEuc_apply] using hcast'

/-- The swapAdjacent function preserves integrality of the lattice basis. -/
lemma swapAdjacent_preserve_integrality
    (B : Integral.IntegralLatticeBasis n k) (i : Fin k) (hi : i.1 + 1 < k) :
    let B' := swapAdjacent (B : LatticeBasis n k) i hi
    ∃ B'' : Integral.IntegralLatticeBasis n k,
      B' = (B'' : LatticeBasis n k) := by
    classical
    -- Unfold the `let` and construct the swapped integer basis explicitly.
    dsimp
    let j : Fin k := ⟨i.1 + 1, hi⟩
    let M : Matrix (Fin n) (Fin k) ℤ :=
      fun r c => if c = i then B.matrix r j else if c = j then B.matrix r i else B.matrix r c
    -- Define the swapped integral basis.
    refine ⟨
      { matrix := M
        le_dim := B.le_dim
        li := by
          -- Linear independence is preserved by swapping columns.
          let σ : Equiv.Perm (Fin k) := Equiv.swap i j
          have hliB : LinearIndependent ℝ (fun c : Fin k => piToEuc (fun r => (B.matrix r c : ℝ))) := B.li
          have hcomp : (fun c : Fin k => piToEuc (fun r => (M r c : ℝ))) =
              (fun c : Fin k => piToEuc (fun r => (B.matrix r c : ℝ))) ∘ σ := by
            funext c
            -- `σ` swaps the two adjacent columns.
            -- Compare by applying `eucToPi` and using coordinatewise equality.
            apply (LatticeCrypto.Utils.Vec.eucToPi.injective)
            funext r
            have hji : j ≠ i := by
              intro h
              have := congrArg Fin.val h
              have h' : i.1 + 1 = i.1 := by
                simp [j] at this
              have h'' : Nat.succ i.1 = i.1 := by
                simp at h'
              exact (Nat.succ_ne_self i.1) h''
            by_cases hci : c = i
            · subst hci
              simp [σ, M, j, LatticeCrypto.Utils.Vec.piToEuc_apply]
            · by_cases hcj : c = j
              · subst hcj
                simp [σ, M, j, hji, LatticeCrypto.Utils.Vec.piToEuc_apply]
              · simp [σ, M, j, Equiv.swap_apply_def, hci, hcj, LatticeCrypto.Utils.Vec.piToEuc_apply]
          have hli' : LinearIndependent ℝ ((fun c : Fin k => piToEuc (fun r => (B.matrix r c : ℝ))) ∘ σ) := by
            refine (LinearIndependent.comp hliB σ ?_)
            intro a b h
            exact (Equiv.swap i j).injective h
          simpa [hcomp]
      }, ?_⟩
    -- Show the real basis is exactly the swapped basis.
    apply LatticeBasis.ext
    funext c
    funext r
    have hji : j ≠ i := by
      intro h
      have := congrArg Fin.val h
      have h' : i.1 + 1 = i.1 := by
        simp [j] at this
      have h'' : Nat.succ i.1 = i.1 := by
        simp at h'
      exact (Nat.succ_ne_self i.1) h''
    by_cases hci : c = i
    · subst hci
      simp [Integral.IntegralLatticeBasis.toRealBasis, swapAdjacent, swapAdjacentVectors, M, j]
    · by_cases hcj : c = j
      · subst hcj
        simp [Integral.IntegralLatticeBasis.toRealBasis, swapAdjacent, swapAdjacentVectors, M, j, hji]
      · simp [Integral.IntegralLatticeBasis.toRealBasis, swapAdjacent, swapAdjacentVectors, M, j, hci, hcj]

/-- The LLLStep function preserves integrality of the lattice basis. -/
lemma LLLStep_preserve_integrality
    (B : Integral.IntegralLatticeBasis n k) (δ : ℝ) :
    let B' := LLLStep (B : LatticeBasis n k) δ
    ∃ B'' : Integral.IntegralLatticeBasis n k,
      B' = (B'' : LatticeBasis n k) := by
  classical
  -- Unfold one LLL step and use integrality preservation of its components.
  unfold LLLStep
  -- Name the size-reduced basis.
  set Bsr : LatticeBasis n k := sizeReduce (B : LatticeBasis n k) with hBsr
  -- Size reduction preserves integrality.
  rcases (by
    simpa [hBsr] using (sizeReduce_preserve_integrality (B := B))
  ) with ⟨Bint, hBint⟩
  -- Case split on whether we swap.
  cases h : firstLovaszViolation Bsr δ with
  | none =>
      refine ⟨Bint, ?_⟩
      have h' : firstLovaszViolation (sizeReduce (B : LatticeBasis n k)) δ = none := by
        simpa [hBsr] using h
      -- Reduce the match and use the size-reduction equality.
      simpa [h'] using hBint
  | some bad =>
      -- Swapping also preserves integrality.
      rcases (by
        simpa using
          (swapAdjacent_preserve_integrality (B := Bint) (i := bad.1)
            (hi := Classical.choose bad.2))
      ) with ⟨Bswap, hBswap⟩
      refine ⟨Bswap, ?_⟩
      have h' : firstLovaszViolation (sizeReduce (B : LatticeBasis n k)) δ = some bad := by
        simpa [hBsr] using h
      -- Reduce the match and rewrite the size-reduced basis to `Bint`.
      simpa [h', hBint] using hBswap

/-- The LLLStep function preserves the lower bound of LLLPotential for integral lattice bases. -/
lemma LLLStep_preserve_LLLPotential_lb
    (B : Integral.IntegralLatticeBasis n k) (δ : ℝ) :
    let B' := LLLStep (B : LatticeBasis n k) δ
    LLLPotential B' ≥ 1 := by
  classical
  -- Reduce the `let` and use integrality preservation, then apply the lower bound.
  dsimp
  rcases (by
    simpa using (LLLStep_preserve_integrality (B := B) (δ := δ))
  ) with ⟨B'', hB''⟩
  have hpot : 1 ≤ LLLPotential (B'' : LatticeBasis n k) := by
    simpa using (LLLPotential_pos_of_integral (B := B''))
  -- Rewrite the goal using the integral basis `B''`.
  simpa [hB''] using hpot


/-- Sufficient iterations for LLL to achieve 2^{n/2} approximation. -/
def LLL_sufficient_iters (B : LatticeBasis n k) (δ : ℝ) : ℕ :=
  1 + Nat.ceil (
    ((k : ℝ) * (k + 1 : ℝ)) *
    (Real.logb (1 / δ) (maxBasisNorm B)))

/-- The lattice basis are nonzero vectors -/
lemma maxBasisNorm_pos (B : LatticeBasis n k) : 0 < maxBasisNorm B := by
  classical
  let i : Fin k := ⟨0, k.pos⟩
  have hne : B.basis i ≠ 0 := B.li.ne_zero i
  have hpos : 0 < ‖B.basis i‖ := by
    simpa [norm_pos_iff] using hne
  have hle : ‖B.basis i‖ ≤ maxBasisNorm B := by
    unfold maxBasisNorm LatticeCrypto.Utils.LinearAlgebra.maxNorm
    exact Finset.le_max' (Finset.univ.image (fun j : Fin k => ‖B.basis j‖)) _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact lt_of_lt_of_le hpos hle

/-- Helper: for induction proof -/
private lemma LLL_impl_succ (numIters : ℕ) (B : LatticeBasis n k) (δ : ℝ) :
    LLL_impl (Nat.succ numIters) B δ =
      (if LLLReduced B δ then B else LLL_impl numIters (LLLStep B δ) δ) := by
  simp [LLL_impl]

/-- The LLL_impl function preserves integrality of the lattice basis. -/
lemma LLL_impl_preserve_integrality (δ : ℝ) :
    ∀ numIters (B : Integral.IntegralLatticeBasis n k),
      ∃ B' : Integral.IntegralLatticeBasis n k,
        LLL_impl numIters (B : LatticeBasis n k) δ = (B' : LatticeBasis n k) := by
  intro numIters
  induction numIters with
  | zero =>
      intro B
      refine ⟨B, ?_⟩
      simp [LLL_impl]
  | succ numIters ih =>
      intro B
      classical
      by_cases hred : LLLReduced (B : LatticeBasis n k) δ
      · refine ⟨B, ?_⟩
        simp [LLL_impl_succ, hred]
      ·
        rcases (LLLStep_preserve_integrality (B := B) (δ := δ)) with ⟨B1, hB1⟩
        rcases ih B1 with ⟨B2, hB2⟩
        refine ⟨B2, ?_⟩
        simp [LLL_impl_succ, hred, hB1, hB2]

/-- If the LLL_impl function does not return a reduced basis,
then it decreases the potential by at least a factor of δ per iteration.
-/
lemma LLL_impl_potential_bound (δ : ℝ) (hδ : IsDelta δ) :
    ∀ numIters (B : LatticeBasis n k),
      ¬ LLLReduced (LLL_impl numIters B δ) δ →
      LLLPotential (LLL_impl numIters B δ) ≤ (δ ^ numIters) * LLLPotential B := by
  intro numIters
  induction numIters with
  | zero =>
      intro B hnot
      simp [LLL_impl]
  | succ numIters ih =>
      intro B hnot
      classical
      by_cases hred : LLLReduced B δ
      ·
        have hred' : LLLReduced (LLL_impl (numIters + 1) B δ) δ := by
          simp [LLL_impl_succ, hred]
        exact (False.elim (hnot hred'))
      ·
        have hnot' : ¬ LLLReduced (LLL_impl numIters (LLLStep B δ) δ) δ := by
          simpa [LLL_impl_succ, hred] using hnot
        have hstep_not : ¬ LLLReduced (LLLStep B δ) δ := by
          intro hstep
          have hfixed : LLL_impl numIters (LLLStep B δ) δ = LLLStep B δ := by
            -- If the input is reduced, LLL_impl returns it at any iteration count.
            induction numIters with
            | zero =>
                simp [LLL_impl]
            | succ m ih =>
              simp [LLL_impl_succ, hstep]
          have : LLLReduced (LLL_impl numIters (LLLStep B δ) δ) δ := by
            simpa [hfixed] using hstep
          exact hnot' this
        have hstep_pot : LLLPotential (LLLStep B δ) < δ * LLLPotential B := by
          have hprog := LLLStep_progress (B := B) (δ := δ) hδ
          cases hprog with
          | inl hred' => exact (hstep_not hred').elim
          | inr hlt => exact hlt
        have hrec := ih (B := LLLStep B δ) hnot'
        have hδpos : 0 < δ := by nlinarith [hδ.1]
        have hpow_nonneg : 0 ≤ δ ^ numIters := pow_nonneg (le_of_lt hδpos) _
        have hlt : LLLPotential (LLL_impl (numIters + 1) B δ)
            < (δ ^ (numIters + 1)) * LLLPotential B := by
          calc
            LLLPotential (LLL_impl (numIters + 1) B δ)
                = LLLPotential (LLL_impl numIters (LLLStep B δ) δ) := by
                    simp [LLL_impl, hred]
            _ ≤ (δ ^ numIters) * LLLPotential (LLLStep B δ) := hrec
            _ < (δ ^ numIters) * (δ * LLLPotential B) := by
              have hpow_pos : 0 < δ ^ numIters := pow_pos hδpos _
              exact (mul_lt_mul_of_pos_left hstep_pot hpow_pos)
            _ = (δ ^ (numIters + 1)) * LLLPotential B := by
                    simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
        exact le_of_lt hlt


/-- Upper bound on number of LLL iterations when given an integral lattice as input. -/
theorem LLL_iteration_bound
    (B : Integral.IntegralLatticeBasis n k) (δ : ℝ) (hδ : IsDelta δ) :
    let N := LLL_sufficient_iters (B : LatticeBasis n k) δ
    ∀ numIters ≥ N, LLLReduced (LLL_impl numIters (B : LatticeBasis n k) δ) δ := by
  -- Use the fact that
  -- (1) The LLL potential is at least 1 for integral basis (and the integrality is preserved throughout), while at most `M^{k(k+1)}` where `M` is the maximum basis norm.
  -- (2) Each swap reduces potential by at least a factor of δ
  -- Thus after N swaps, the potential is at most `M^{k(k+1)} * δ^N < 1`, which is impossible.
  classical
  intro N numIters hN
  by_contra hnot
  -- Integrality is preserved, so the potential is at least 1.
  rcases (LLL_impl_preserve_integrality (δ := δ) numIters B) with ⟨B', hB'⟩
  have hpot_lb : 1 ≤ LLLPotential (LLL_impl numIters (B : LatticeBasis n k) δ) := by
    simpa [hB'] using (LLLPotential_pos_of_integral (B := B'))

  -- Upper bound on the potential from the step-wise decrease.
  have hpot_ub :
      LLLPotential (LLL_impl numIters (B : LatticeBasis n k) δ)
        ≤ (δ ^ numIters) * LLLPotential (B : LatticeBasis n k) :=
    LLL_impl_potential_bound (δ := δ) hδ numIters (B := (B : LatticeBasis n k)) hnot
  have hinit :
      LLLPotential (B : LatticeBasis n k)
        ≤ (maxBasisNorm (B : LatticeBasis n k)) ^ ((k : ℝ) * (k + 1 : ℝ)) :=
    LLLPotential_initial_bound (B := (B : LatticeBasis n k))
  have hδpos : 0 < δ := by nlinarith [hδ.1]
  have hpow_nonneg : 0 ≤ δ ^ numIters := pow_nonneg (le_of_lt hδpos) _
  have hpot_ub' :
      LLLPotential (LLL_impl numIters (B : LatticeBasis n k) δ)
        ≤ (δ ^ numIters) * (maxBasisNorm (B : LatticeBasis n k)) ^ ((k : ℝ) * (k + 1 : ℝ)) := by
    exact le_trans hpot_ub (mul_le_mul_of_nonneg_left hinit hpow_nonneg)

  -- Turn the iteration bound into a bound on the power.
  set M : ℝ := maxBasisNorm (B : LatticeBasis n k)
  set p : ℝ := (k : ℝ) * (k + 1 : ℝ)
  have hMpos : 0 < M := by
    simpa [M] using (maxBasisNorm_pos (B := (B : LatticeBasis n k)))
  have hb : 1 < (1 / δ) := by
    have hδlt : δ < 1 := hδ.2
    have h := (one_lt_div_iff (a := (1 : ℝ)) (b := δ)).2 (Or.inl ⟨hδpos, hδlt⟩)
    simpa using h
  set t : ℝ := p * Real.logb (1 / δ) M
  have hN' : (1 + (Nat.ceil t : ℝ)) ≤ (numIters : ℝ) := by
    have hN'' : 1 + Nat.ceil t ≤ numIters := by
      simpa [N, LLL_sufficient_iters, t] using hN
    exact_mod_cast hN''
  have hceil : t ≤ (Nat.ceil t : ℝ) := by
    have h : Nat.ceil t ≤ Nat.ceil t := le_rfl
    exact (Nat.ceil_le (a := t) (n := Nat.ceil t)).1 h
  have ht_le : t ≤ (numIters : ℝ) - 1 := by
    have hceil_le : (Nat.ceil t : ℝ) ≤ (numIters : ℝ) - 1 := by
      nlinarith [hN']
    exact le_trans hceil hceil_le
  have hlogb : Real.logb (1 / δ) (M ^ p) ≤ (numIters : ℝ) - 1 := by
    have : Real.logb (1 / δ) (M ^ p) = t := by
      simpa [t, p] using (Real.logb_rpow_eq_mul_logb_of_pos (b := (1 / δ)) (x := M) (y := p) hMpos)
    rw [this]
    exact ht_le
  have hpow_le : M ^ p ≤ (1 / δ) ^ ((numIters : ℝ) - 1) := by
    have hMpos' : 0 < M ^ p := by
      exact Real.rpow_pos_of_pos hMpos _
    exact (Real.logb_le_iff_le_rpow (b := (1 / δ)) (x := M ^ p)
      (y := (numIters : ℝ) - 1) (hb := hb) hMpos').1 hlogb
  have hpow_le' : M ^ p ≤ (1 / δ) ^ (numIters - 1) := by
    -- Since `numIters` is a natural number, `numIters - 1` is also a natural number. Therefore, the real exponent `(numIters - 1 : ℝ)` is equal to the natural number `numIters - 1`.
    have h_nat_exp : (numIters - 1 : ℝ) = (numIters - 1 : ℕ) := by
      cases numIters <;> norm_num at *;
      linarith;
    convert hpow_le using 1 ; rw [ h_nat_exp ] ; norm_cast
  have hmul_le : (δ ^ (numIters - 1)) * M ^ p ≤ (1 : ℝ) := by
    have hpow_nonneg' : 0 ≤ δ ^ (numIters - 1) := pow_nonneg (le_of_lt hδpos) _
    have hmul := mul_le_mul_of_nonneg_left hpow_le' hpow_nonneg'
    have hmul' : (δ ^ (numIters - 1)) * (1 / δ) ^ (numIters - 1) = (1 : ℝ) := by
      have hδne : δ ≠ 0 := ne_of_gt hδpos
      calc
        (δ ^ (numIters - 1)) * (1 / δ) ^ (numIters - 1)
            = (δ * (1 / δ)) ^ (numIters - 1) := by
                symm
                exact (mul_pow δ (1 / δ) (numIters - 1))
        _ = (1 : ℝ) ^ (numIters - 1) := by
                simp [one_div, hδne]
        _ = (1 : ℝ) := by simp
    exact hmul.trans_eq hmul'

  -- Conclude the potential is < 1, contradiction.
  have hnum_pos : 0 < numIters := by
    have hN1 : (1 : ℕ) ≤ N := by exact Nat.le.intro rfl
    have h1 : (1 : ℕ) ≤ numIters := le_trans hN1 hN
    exact (Nat.succ_le_iff).1 h1
  set m : ℕ := numIters - 1
  have hm : numIters = m + 1 := by
    have : Nat.succ (Nat.pred numIters) = numIters := Nat.succ_pred_eq_of_pos hnum_pos
    omega
  have hlt :
      LLLPotential (LLL_impl numIters (B : LatticeBasis n k) δ) < 1 := by
    have hmul_le' : (δ ^ numIters) * M ^ p ≤ δ := by
      calc
        (δ ^ numIters) * M ^ p
            = (δ ^ m) * δ * M ^ p := by
                rw [hm]; ring
        _ = δ * ((δ ^ m) * M ^ p) := by
                ring
        _ ≤ δ * 1 := by
                exact mul_le_mul_of_nonneg_left hmul_le (le_of_lt hδpos)
        _ = δ := by simp
    have hδlt : δ < 1 := hδ.2
    exact lt_of_le_of_lt (le_trans hpot_ub' hmul_le') hδlt
  exact (not_lt_of_ge hpot_lb) hlt

end runtime_analysis

end LLL

end LatticeCrypto.Foundations.Algorithms
