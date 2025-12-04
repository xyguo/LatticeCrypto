import LatticeCrypto.Foundations.Lattice.Defs
import Mathlib.Tactic.Contrapose
import Mathlib.Topology.Defs.Basic
open RealInnerProductSpace
open Classical

/-!
  This file defines basic lattice operations for `GeometricLattice` and `LatticeBasis`.

  ## GeometricLattice Operations
  - `GeometricLattice.coset` and `GeometricLattice.Quotient`
  - `GeometricLattice.smul`
  - `GeometricLattice.dual`

  ## LatticeBasis Operations
  - `LatticeBasis.smul`
  - `LatticeBasis.dual`
  - `LatticeBasis.dual_inner` (biorthogonality: ⟨B_i, B*_j⟩ = δ_ij)

  ## Bridges
  - `GeometricLattice.dual_carrier_eq` (dual lattice = vectors with integral inner products)
-/

namespace LatticeCrypto.Foundations.Lattice

variable {n k : ℕ+}

/-!
## Membership and Representation
-/

noncomputable section membership

/-- Membership in a geometric lattice. -/
instance : Membership (𝔼 n) (GeometricLattice n k) where
  mem L v := v ∈ L.carrier

/-- A vector is in the lattice iff it is in the carrier. -/
theorem GeometricLattice.mem_def (L : GeometricLattice n k) (v : 𝔼 n) :
    v ∈ L ↔ v ∈ L.carrier := Iff.rfl

/-- A vector is in the lattice iff it can be expressed as an integer linear combination of basis vectors. -/
theorem GeometricLattice.mem_iff_zspan (L : GeometricLattice n k) (v : 𝔼 n) :
    v ∈ L ↔ v ∈ Submodule.span ℤ (Set.range L.basis.cols) := by
  rw [mem_def, L.carrier_eq]

/-- A vector is in the lattice iff there exist integer coefficients such that v = ∑ cᵢ bᵢ. -/
theorem GeometricLattice.mem_iff_exists_coeffs (L : GeometricLattice n k) (v : 𝔼 n) :
    v ∈ L ↔ ∃ c : Fin k → ℤ, v = ∑ i, c i • L.basis.cols i := by
  rw [mem_iff_zspan]
  constructor
  · intro hv
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hv
    obtain ⟨c, hc⟩ := hv
    use c
    bound
  · intro ⟨c, hc⟩
    rw [hc]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- Zero is always in the lattice. -/
theorem GeometricLattice.zero_mem (L : GeometricLattice n k) : (0 : 𝔼 n) ∈ L := by
  rw [mem_def]
  exact L.carrier.zero_mem

/-- The lattice is closed under addition. -/
theorem GeometricLattice.add_mem (L : GeometricLattice n k) {v w : 𝔼 n}
    (hv : v ∈ L) (hw : w ∈ L) : v + w ∈ L := by
  rw [mem_def] at *
  exact L.carrier.add_mem hv hw

/-- The lattice is closed under negation. -/
theorem GeometricLattice.neg_mem (L : GeometricLattice n k) {v : 𝔼 n}
    (hv : v ∈ L) : -v ∈ L := by
  rw [mem_def] at *
  exact L.carrier.neg_mem hv

/-- The lattice is closed under subtraction. -/
theorem GeometricLattice.sub_mem (L : GeometricLattice n k) {v w : 𝔼 n}
    (hv : v ∈ L) (hw : w ∈ L) : v - w ∈ L := by
  rw [mem_def] at *
  exact L.carrier.sub_mem hv hw

/-- The lattice is closed under integer scalar multiplication. -/
theorem GeometricLattice.zsmul_mem (L : GeometricLattice n k) {v : 𝔼 n}
    (hv : v ∈ L) (m : ℤ) : m • v ∈ L := by
  rw [mem_def] at *
  bound

/-- Basis vectors are in the lattice. -/
theorem GeometricLattice.basis_mem (L : GeometricLattice n k) (i : Fin k) :
    L.basis.cols i ∈ L := by
  rw [mem_iff_zspan]
  exact Submodule.subset_span (Set.mem_range_self i)

/-- The representation of a lattice vector as integer coordinates with respect to the basis. -/
noncomputable def GeometricLattice.repr (L : GeometricLattice n k) (v : 𝔼 n)
    (hv : v ∈ L) : Fin k → ℤ :=
  L.basis.asZSpanBasis.repr ⟨v, L.carrier_eq ▸ hv⟩

/-- The representation gives the correct coefficients. -/
theorem GeometricLattice.repr_spec (L : GeometricLattice n k) (v : 𝔼 n)
    (hv : v ∈ L) : v = ∑ i, (L.repr v hv i) • L.basis.cols i := by
  rw [mem_def] at hv
  have hv' : v ∈ Submodule.span ℤ (Set.range L.basis.cols) := L.carrier_eq ▸ hv
  have h := L.basis.asZSpanBasis.sum_repr ⟨v, hv'⟩
  simp only [LatticeBasis.asZSpanBasis] at h
  conv_lhs => rw [← Subtype.coe_mk v hv']
  convert congr_arg Subtype.val h.symm using 1;
  induction ( Finset.univ : Finset ( Fin k ) ) using Finset.induction <;> aesop;
  congr;
  exact Eq.symm (Module.Basis.span_apply (LatticeBasis.asZSpanBasis._proof_1 L.basis) a)

/-- Constructing a lattice vector from coefficients. -/
noncomputable def GeometricLattice.ofCoeffs (L : GeometricLattice n k)
    (c : Fin k → ℤ) : 𝔼 n :=
  ∑ i, c i • L.basis.cols i

/-- A vector constructed from coefficients is in the lattice. -/
theorem GeometricLattice.ofCoeffs_mem (L : GeometricLattice n k)
    (c : Fin k → ℤ) : L.ofCoeffs c ∈ L := by
  rw [mem_iff_exists_coeffs]
  exact ⟨c, rfl⟩

/-- repr is a left inverse of ofCoeffs. -/
theorem GeometricLattice.repr_ofCoeffs (L : GeometricLattice n k)
    (c : Fin k → ℤ) : L.repr (L.ofCoeffs c) (L.ofCoeffs_mem c) = c := by
  have h_li : LinearIndependent ℤ L.basis.cols :=
    Z_linearIndependent_if_R_linearIndependent L.basis.li
  ext i
  have h_eq := L.repr_spec (L.ofCoeffs c) (L.ofCoeffs_mem c)
  simp only [ofCoeffs] at h_eq
  -- The representation is unique due to linear independence
  have h_unique : ∀ (c₁ c₂ : Fin k → ℤ),
      (∑ i, c₁ i • L.basis.cols i) = (∑ i, c₂ i • L.basis.cols i) → c₁ = c₂ := by
    intro c₁ c₂ heq
    have : ∑ i, (c₁ i - c₂ i) • L.basis.cols i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [heq, sub_self]
    rw [Fintype.linearIndependent_iff] at h_li
    ext j
    have := h_li (fun i => c₁ i - c₂ i) this j
    omega
  exact congr_fun (h_unique _ _ h_eq.symm) i

/-- ofCoeffs is a left inverse of repr. -/
theorem GeometricLattice.ofCoeffs_repr (L : GeometricLattice n k) (v : 𝔼 n)
    (hv : v ∈ L) : L.ofCoeffs (L.repr v hv) = v := by
  rw [ofCoeffs, ← repr_spec L v hv]

end membership


/-!
## Cosets and Quotients for GeometricLattice
-/

noncomputable section coset

/-- The coset of a vector v with respect to lattice L: v + L -/
def GeometricLattice.coset (L : GeometricLattice n k) (v : 𝔼 n) : Set (𝔼 n) :=
  { x | ∃ l ∈ L.carrier, x = v + l }

-- Notation for cosets: v +ᶜ L
notation:65 v " +ᶜ " L:65 => GeometricLattice.coset L v

/-- The quotient space ℝⁿ / L -/
def GeometricLattice.Quotient (L : GeometricLattice n k) : Type _ :=
  (𝔼 n) ⧸ L.carrier

/-- The canonical projection map π : ℝⁿ → ℝⁿ/L -/
def GeometricLattice.mk_quotient (L : GeometricLattice n k) (v : 𝔼 n) : L.Quotient :=
  QuotientAddGroup.mk v

/-- Two vectors are in the same coset iff their difference is in the lattice -/
theorem GeometricLattice.coset_eq_iff (L : GeometricLattice n k) (v w : 𝔼 n) :
    (v +ᶜ L) = (w +ᶜ L) ↔ (v - w) ∈ L.carrier := by
  constructor
  · intro h
    have hv : v ∈ (v +ᶜ L) := ⟨0, L.carrier.zero_mem, by simp⟩
    rw [h] at hv
    obtain ⟨l, hl, hv_eq⟩ := hv
    have : v - w = l := by bound
    rw [this]
    exact hl
  · intro h
    ext x
    simp only [GeometricLattice.coset, Set.mem_setOf_eq]
    constructor
    · intro ⟨l, hl, hx⟩
      use l + (v - w)
      constructor
      · exact L.carrier.add_mem hl h
      · grind
    · intro ⟨l, hl, hx⟩
      use l - (v - w)
      constructor
      · exact L.carrier.sub_mem hl h
      · grind

end coset

/-!
## Scalar Multiplication
-/

noncomputable section smul

/-- Scale a lattice basis by a non-zero scalar -/
def LatticeBasis.smul (c : ℝ) (B : LatticeBasis n k) (hc : c ≠ 0) : LatticeBasis n k :=
  { basis := fun i => c • (B.basis i)
    le_dim := B.le_dim
    li := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have h_rewrite : ∑ i, g i • (c • B.basis i) = c • ∑ i, g i • B.basis i := by
        rw [Finset.smul_sum]
        congr 1
        ext i
        rw [smul_comm]
      rw [h_rewrite] at hg
      have h_sum_zero : ∑ i, g i • B.basis i = 0 := by
        rwa [smul_eq_zero, or_iff_right hc] at hg
      exact Fintype.linearIndependent_iff.mp B.li g h_sum_zero }

/-- Scale a geometric lattice by a non-zero scalar -/
def GeometricLattice.smul (L : GeometricLattice n k) (c : ℝ) (hc : c ≠ 0) : GeometricLattice n k :=
  (L.basis.smul c hc).toLattice

/-- Scaling preserves carrier equivalence (basically the theorem ZSpan.smul) -/
theorem GeometricLattice.smul_carrier (L : GeometricLattice n k) (c : ℝ) (hc : c ≠ 0) :
    (L.smul c hc).carrier = L.carrier.map (DistribMulAction.toLinearMap ℤ (𝔼 n) c) := by
  simp only [GeometricLattice.smul, LatticeBasis.toLattice, LatticeBasis.smul]
  simp only [LatticeBasis.cols]
  ext x
  simp only [Submodule.mem_map]
  constructor
  · intro hx
    rw [Submodule.mem_span] at hx
    -- x is in the span of scaled basis vectors
    -- Since x is in the submodule generated by the scaled basis, there exist coefficients a_i such that x = sum a_i * (c • L.basis.basis i).
    obtain ⟨a, ha⟩ : ∃ a : Fin k → ℤ, x = ∑ i, a i • (c • L.basis.basis i) := by
      specialize hx ( Submodule.span ℤ ( Set.range ( fun i => c • L.basis.basis i ) ) ) ( Set.range_subset_iff.mpr fun i => Submodule.subset_span ( Set.mem_range_self i ) );
      rw [ Submodule.mem_span_range_iff_exists_fun ] at hx ; tauto;
    -- Let $y = \sum_{i=0}^{k-1} a_i \cdot L.basis.basis_i$. Then $c \cdot y = x$.
    use ∑ i, a i • L.basis.basis i;
    -- The sum of a_i times the basis vectors is in the carrier of L because it is a linear combination of the basis vectors.
    have h_sum_in_carrier : ∑ i, a i • L.basis.basis i ∈ L.carrier := by
      -- Since the carrier is the span of the basis, any linear combination of the basis vectors with integer coefficients is in the carrier.
      have h_sum_in_carrier : ∀ (a : Fin k → ℤ), ∑ i, a i • L.basis.basis i ∈ Submodule.span ℤ (Set.range L.basis.basis) := by
        exact fun a => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_range_self _ ) );
      exact L.carrier_eq ▸ h_sum_in_carrier a;
    simp_all +decide
  · intro ⟨y, hy, hxy⟩
    rw [L.carrier_eq] at hy
    rw [Submodule.mem_span] at hy ⊢
    intro p hp
    -- Need to show x ∈ p where p contains all scaled basis vectors
    -- Since $y$ is in the submodule spanned by the range of $L.basis.cols$, and the scaled basis is in $p$, then multiplying $y$ by $c$ should keep it in $p$ because $p$ is closed under scalar multiplication by integers.
    have h_mul : ∀ (m : ℤ) (v : 𝔼 n), v ∈ p → m • v ∈ p := by
      exact fun m v hv => p.smul_mem m hv;
    -- Since $y$ is in the submodule spanned by the range of $L.basis.cols$, we can write $y$ as a finite sum of integer multiples of the basis vectors.
    obtain ⟨m, hm⟩ : ∃ m : Fin k → ℤ, y = ∑ i, m i • L.basis.basis i := by
      specialize hy ( Submodule.span ℤ ( Set.range L.basis.cols ) ) ( Submodule.subset_span );
      rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hy;
      obtain ⟨ m, hm ⟩ := hy; use m; simp_all +decide [ Finsupp.sum_fintype ] ;
      exact hm.symm;
    simp_all +decide [ Set.range_subset_iff ];
    exact hxy ▸ Submodule.sum_mem _ fun i _ => h_mul _ _ ( hp i )

end smul

/-- Negation of a geometric lattice -/
def GeometricLattice.neg (L : GeometricLattice n k) : GeometricLattice n k :=
  L.smul (-1) (by norm_num)

/-- -L = L -/
theorem GeometricLattice.neg_eq_self {L: GeometricLattice n n} : L.neg ≡ᵤ L := by
  -- The carrier of the negated lattice is the same as the carrier of the original lattice because negation is an automorphism.
  have h_neg_carrier : ∀ (v : 𝔼 n), v ∈ (L.smul (-1) (by norm_num)).carrier ↔ -v ∈ L.carrier := by
    intro v
    simp [GeometricLattice.smul_carrier];
    aesop;
  ext v; specialize h_neg_carrier v; aesop;

/-!
## Dual Basis and Dual Lattice
-/

noncomputable section dual

/--
  The determinant of a square lattice basis matrix is non-zero.
  This follows from linear independence of the columns.
-/
theorem LatticeBasis.det_ne_zero (B : SquareLatticeBasis n) : B.asMatrix.det ≠ 0 := by
  -- The columns of B.asMatrix are linearly independent
  have h_li : LinearIndependent ℝ (fun j => B.asMatrix.col j) := by
    convert B.li using 1
  -- For a square matrix, linear independence of columns implies det ≠ 0
  contrapose! h_li; aesop;
  rw [ Fintype.linearIndependent_iff ] at a;
  -- Apply the fact that if the determinant is zero, then there exists a non-zero vector `g` such that `A * g = 0`.
  obtain ⟨g, hg⟩ : ∃ g : Fin n → ℝ, g ≠ 0 ∧ B.asMatrix.mulVec g = 0 := by
    convert Matrix.exists_mulVec_eq_zero_iff.mpr h_li;
  exact hg.1 ( funext fun i => a g ( by ext j; simpa [ Matrix.mulVec, dotProduct, mul_comm ] using congr_fun hg.2 j ) i )

/--
  The transpose of an invertible matrix is invertible.
-/
theorem LatticeBasis.det_transpose_ne_zero (B : SquareLatticeBasis n) :
    B.asMatrix.transpose.det ≠ 0 := by
  rw [Matrix.det_transpose]
  exact B.det_ne_zero

/--
  The Dual Basis B* for an n×n basis B.
  Mathematically: B* = (B^T)^{-1}.
  Properties: ⟨b_i, b*_j⟩ = δ_ij.
-/
def LatticeBasis.dual (B : SquareLatticeBasis n) : SquareLatticeBasis n :=
  let dual_mat := B.asMatrix.transpose⁻¹
  have h_li : LinearIndependent ℝ (fun j => dual_mat.col j) := by
    -- Since the determinant of the dual matrix is non-zero, the columns are linearly independent.
    have h_det_nonzero : dual_mat.det ≠ 0 := by
      aesop;
      exact absurd a ( LatticeBasis.det_ne_zero B );
    exact Matrix.linearIndependent_cols_of_det_ne_zero h_det_nonzero
  { basis := fun j => dual_mat.col j
    le_dim := le_refl n
    li := h_li }

/-- The dual basis matrix equals (B^T)^{-1} -/
theorem LatticeBasis.dual_asMatrix (B : SquareLatticeBasis n) :
    B.dual.asMatrix = B.asMatrix.transpose⁻¹ := by
  ext i j
  simp [LatticeBasis.dual, LatticeBasis.asMatrix, Matrix.col]

/--
  Biorthogonality: The inner product of primal and dual basis vectors satisfies
  ⟨B_i, B*_j⟩ = δ_ij (Kronecker delta).
-/
theorem LatticeBasis.dual_inner (B : SquareLatticeBasis n) (i j : Fin n) :
    ⟪B.cols i, B.dual.cols j⟫ = if i = j then 1 else 0 := by
  -- By definition of the dual basis, we know that $B^T \cdot (B^T)^{-1} = I$, the identity matrix.
  have h_dual : B.asMatrix.transpose * (B.asMatrix.transpose)⁻¹ = 1 := by
    apply Matrix.mul_nonsing_inv;
    exact isUnit_iff_ne_zero.mpr ( LatticeCrypto.Foundations.Lattice.LatticeBasis.det_transpose_ne_zero B );
  -- By definition of the dual basis, the inner product of the i-th column of B and the j-th column of the dual basis is the (i,j) entry of the product of the transpose of B's matrix and the inverse of the transpose of B's matrix.
  have h_inner : ⟪B.cols i, (B.dual).cols j⟫ = (B.asMatrix.transpose * (B.asMatrix.transpose)⁻¹) i j := by
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _;
  aesop

/--
  Alternative formulation: B^T * B* = I
-/
theorem LatticeBasis.transpose_mul_dual (B : SquareLatticeBasis n) :
    B.asMatrix.transpose * B.dual.asMatrix = 1 := by
  rw [B.dual_asMatrix]
  rw [ Matrix.mul_nonsing_inv _ _ ];
  exact isUnit_iff_ne_zero.mpr ( by exact det_transpose_ne_zero B )

/--
  Alternative formulation: B* * B^T = I
-/
theorem LatticeBasis.dual_mul_transpose (B : SquareLatticeBasis n) :
    B.dual.asMatrix * B.asMatrix.transpose = 1 := by
  rw [B.dual_asMatrix]
  apply Matrix.nonsing_inv_mul;
  simp +zetaDelta at *;
  exact det_ne_zero B

/--
  The dual of the dual is the original basis.
-/
theorem LatticeBasis.dual_dual (B : SquareLatticeBasis n) : B.dual.dual = B := by
  -- By definition of dual, we have that the dual of the dual of B is the transpose of the inverse of the transpose of B's matrix.
  have h_dual_dual : (B.dual.dual.asMatrix) = (B.asMatrix.transpose⁻¹).transpose⁻¹ := by
    aesop;
  -- Since the transpose of the inverse of the transpose of B's matrix is just B's matrix itself, we can conclude that the dual of the dual of B is B.
  have h_dual_dual_eq : (B.dual.dual.asMatrix) = B.asMatrix := by
    simp_all +decide [ Matrix.transpose_nonsing_inv ];
    -- Since the determinant of B is non-zero, B is invertible, and thus (B⁻¹)⁻¹ = B.
    have h_inv_inv : (B.asMatrix)⁻¹⁻¹ = B.asMatrix := by
      have h_det_ne_zero : B.asMatrix.det ≠ 0 := by
        exact det_ne_zero B
      exact Matrix.nonsing_inv_nonsing_inv _ ( show IsUnit _ from isUnit_iff_ne_zero.mpr h_det_ne_zero );
    exact h_inv_inv;
  -- Since the matrices are equal, the bases must be equal.
  apply LatticeBasis.ext;
  exact funext fun i => by ext j; simpa using congr_fun ( congr_fun h_dual_dual_eq j ) i;

/--
  The dual lattice of a full-rank geometric lattice.
  L* is generated by the dual basis B*.
-/
def GeometricLattice.dual (L : GeometricLattice n n) : GeometricLattice n n :=
  L.basis.dual.toLattice

/--
  The set of vectors with integral inner product against all lattice vectors.
-/
def integralDualSet (L : GeometricLattice n n) : Set (𝔼 n) :=
  { y | ∀ x ∈ L.carrier, ∃ m : ℤ, ⟪x, y⟫ = (m : ℝ) }

/--
  The dual lattice carrier equals the set of vectors with integral inner products.
  This is the key characterization: L* = { y ∈ ℝⁿ | ∀ x ∈ L, ⟨x, y⟩ ∈ ℤ }
-/
theorem GeometricLattice.dual_carrier_eq_integralDual (L : GeometricLattice n n) :
    (L.dual.carrier : Set (𝔼 n)) = integralDualSet L := by
  ext y
  simp only [integralDualSet, Set.mem_setOf_eq]
  constructor
  · -- Direction: y ∈ L.dual.carrier → y has integral inner product with all x ∈ L
    intro hy x hx
    -- y is in the Z-span of dual basis vectors
    rw [L.dual.carrier_eq] at hy
    rw [L.carrier_eq] at hx
    -- x = ∑ aᵢ bᵢ for integers aᵢ and primal basis vectors bᵢ
    -- y = ∑ cⱼ b*ⱼ for integers cⱼ and dual basis vectors b*ⱼ
    -- ⟨x, y⟩ = ∑ᵢⱼ aᵢ cⱼ ⟨bᵢ, b*⟨ = ∑ᵢⱼ aᵢ c⟨ δᵢ⟨ = ∑ᵢ aᵢ cᵢ ∈ ℤ
    -- By definition of the dual basis, we know that ⟨B_j, B*_i⟩ = δ_ij.
    have h_biorthogonal : ∀ j i : Fin n, ⟪L.basis.cols j, L.dual.basis.cols i⟫ = if j = i then 1 else 0 := by
      -- Apply the hypothesis `h_biorthogonal` directly to conclude the proof.
      apply LatticeCrypto.Foundations.Lattice.LatticeBasis.dual_inner;
    -- By definition of the span, we can write x as a linear combination of the basis vectors of L with integer coefficients.
    obtain ⟨c, hc⟩ : ∃ c : Fin n → ℤ, x = ∑ j, (c j : ℝ) • L.basis.cols j := by
      rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hx;
      obtain ⟨ c, hc ⟩ := hx; use c; simp +decide [ ← hc, Finsupp.sum_fintype ] ;
      exact Finset.sum_congr rfl fun _ _ => by norm_cast;
    -- By definition of the dual basis, we can write y as a linear combination of the dual basis vectors with integer coefficients.
    obtain ⟨d, hd⟩ : ∃ d : Fin n → ℤ, y = ∑ j, (d j : ℝ) • L.dual.basis.cols j := by
      -- By definition of span, since y is in the span of the dual basis, there exists a function d : Fin n → ℤ such that y is the sum of d_j times the dual basis vectors.
      have h_span : y ∈ Submodule.span ℤ (Set.range L.dual.basis.cols) := by
        exact hy;
      rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_span;
      obtain ⟨ d, rfl ⟩ := h_span; use fun i => d i; simp ( config := { decide := Bool.true } ) [ Finsupp.sum_fintype ] ;
      norm_cast;
    simp_all ( config := { decide := Bool.true } ) [ inner_sum, inner_smul_right ];
    rw [ Finset.sum_congr rfl fun i hi => by rw [ sum_inner, Finset.sum_congr rfl fun j hj => by rw [ inner_smul_left ] ] ] ; aesop;
    exact ⟨ ∑ x : Fin n, d x * c x, by push_cast; rfl ⟩

  · -- Direction: y has integral inner product with all x ∈ L → y ∈ L.dual.carrier
    intro hy
    -- If ⟨bᵢ, y⟩ ∈ ℤ for all primal basis vectors bᵢ, then y ∈ span_ℤ(B*)
    -- This follows because the coordinates of y in the dual basis are exactly ⟨bᵢ, y⟩
    rw [L.dual.carrier_eq]
    -- y = ∑ⱼ ⟨bⱼ, y⟩ b*ⱼ and each ⟨bⱼ, y⟩ is an integer
    -- y = ∑ⱼ ⟨bⱼ, y⟩ b*ⱼ and each ⟨bⱼ, y⟩ is an integer
    -- Let's express y as a linear combination of the dual basis vectors.
    obtain ⟨a, ha⟩ : ∃ a : Fin n → ℝ, y = ∑ i, a i • L.dual.basis.cols i := by
      -- By definition of dual basis, we know that every element in ℝⁿ can be expressed as a linear combination of the dual basis vectors.
      have h_dual_basis : ∀ v : 𝔼 n, ∃ a : Fin n → ℝ, v = ∑ i, a i • L.dual.basis.cols i := by
        have h_dual_basis : LinearIndependent ℝ (L.dual.basis.cols) := by
          exact L.dual.basis.li;
        have h_dual_basis : Submodule.span ℝ (Set.range L.dual.basis.cols) = ⊤ := by
          refine' Submodule.eq_top_of_finrank_eq _;
          rw [ finrank_span_eq_card ] <;> aesop;
        intro v; replace h_dual_basis := Submodule.mem_span_range_iff_exists_fun ℝ |>.1 ( h_dual_basis.symm ▸ Submodule.mem_top : v ∈ Submodule.span ℝ ( Set.range L.dual.basis.cols ) ) ; tauto;
      exact h_dual_basis y;
    -- Since $a_i$ are integers, we can conclude that $y$ is in the submodule spanned by the dual basis vectors.
    have ha_int : ∀ i, ∃ m : ℤ, a i = m := by
      intro i
      obtain ⟨m, hm⟩ : ∃ m : ℤ, ⟪L.basis.cols i, y⟫ = (m : ℝ) := hy (L.basis.cols i) (by
      exact L.carrier_eq.symm ▸ Submodule.subset_span ( Set.mem_range_self i ));
      -- By definition of the dual basis, we know that ⟪L.basis.cols j, L.dual.basis.cols i⟫ = δ_ji.
      have h_dual_inner : ∀ j i : Fin n, ⟪L.basis.cols j, L.dual.basis.cols i⟫ = if j = i then 1 else 0 := by
        -- By definition of the dual basis, we know that ⟨B_j, B*_i⟩ = δ_ji.
        intros j i
        apply LatticeBasis.dual_inner;
      simp_all ( config := { decide := Bool.true } ) [ inner_sum, inner_smul_right ];
    choose m hm using ha_int;
    simp_all ( config := { decide := Bool.true } ) [ Submodule.mem_span ];
    intro p hp;
    convert p.sum_mem fun i _ => p.smul_mem ( m i ) ( hp <| Set.mem_range_self i ) using 1;
    swap;
    exacts [ Finset.univ, by congr; ext; simp ( config := { decide := Bool.true } ) [ Algebra.smul_def ] ]

/--
  A vector is in the dual lattice iff it has integral inner product with all basis vectors.
-/
theorem GeometricLattice.mem_dual_iff_integral_inner_basis (L : GeometricLattice n n) (y : 𝔼 n) :
    y ∈ L.dual.carrier ↔ ∀ i : Fin n, ∃ m : ℤ, ⟪L.basis.cols i, y⟫ = (m : ℝ) := by
  constructor
  · intro hy i
    have hy' : y ∈ integralDualSet L := by
      rw [← dual_carrier_eq_integralDual]
      exact hy
    apply hy'
    rw [L.carrier_eq]
    exact Submodule.subset_span (Set.mem_range_self i)
  · intro h
    -- By definition of integral dual set, if y has integral inner products with all lattice vectors, then y is in the dual lattice.
    have h_integral_dual : y ∈ integralDualSet L := by
      -- By definition of integral dual set, we need to show that for any x in L.carrier, ⟨x, y⟩ is an integer.
      intro x hx
      -- Since x is in the span of the basis vectors, we can write x as a linear combination of the basis vectors with integer coefficients.
      obtain ⟨c, hc⟩ : ∃ c : Fin n → ℤ, x = ∑ i, c i • L.basis.cols i := by
        have h_comb : x ∈ Submodule.span ℤ (Set.range L.basis.cols) := by
          -- By definition of the carrier, we know that $x \in \text{span}(\text{range}(L.basis.cols))$.
          rw [L.carrier_eq] at hx; exact hx;
        rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_comb;
        exact ⟨ h_comb.choose, by simpa [ Finsupp.sum_fintype ] using h_comb.choose_spec.symm ⟩;
      -- By linearity of the inner product, we can distribute the inner product over the sum.
      have h_inner_dist : ⟪x, y⟫ = ∑ i, c i • ⟪L.basis.cols i, y⟫ := by
        simp +decide [ hc ];
        rw [ sum_inner, Finset.sum_congr rfl ] ; intros ; aesop;
        convert inner_smul_left _ _ _;
        ext;
        erw [ Real.ofCauchy_intCast ] ; norm_num;
      choose m hm using h; use ∑ i, c i * m i; simp_all +decide ;
    exact ( GeometricLattice.dual_carrier_eq_integralDual L ) |>.symm.subset h_integral_dual

/--
  The dual of the dual lattice is the original lattice.
-/
theorem GeometricLattice.dual_dual (L : GeometricLattice n n) : L.dual.dual ≡ᵤ L := by
  rw [GeometricLattice.eq_iff_basis_equiv]
  -- L.dual.dual.basis = L.basis.dual.dual =ᵤ L.basis
  have h : L.dual.dual.basis = L.basis := by
    -- This follows from LatticeBasis.dual_dual
    simp only [GeometricLattice.dual, LatticeBasis.toLattice]
    exact L.basis.dual_dual
  rw [h]
  exact LatticeBasis.UnimodularEquiv.refl L.basis

end dual

/-!
## Fundamental Domain and Determinant
-/

noncomputable section fundamental_domain

/-- The fundamental parallelepiped of a lattice basis. -/
def LatticeBasis.fundamentalDomain (B : SquareLatticeBasis n) : Set (𝔼 n) :=
  ZSpan.fundamentalDomain B.asTopBasis

/-- We define the closure of the fundamental parallelepiped as generated with coefficents from [0, 1] -/
def LatticeBasis.fundamentalDomain_closure (B : SquareLatticeBasis n) : Set (𝔼 n) :=
  {m | ∀ i, B.asTopBasis.repr m i ∈ Set.Icc (0 : ℝ) 1}

/-- The closure defined as above is indeed a topological closure -/
theorem LatticeBasis.fundamentalDomain.closure_apply (B : SquareLatticeBasis n) :
  B.fundamentalDomain_closure = closure B.fundamentalDomain := by
  -- The closure of the fundamental domain is the set of points where each coordinate is in [0, 1], which is exactly the fundamental domain closure.
  ext; simp [LatticeBasis.fundamentalDomain_closure, LatticeBasis.fundamentalDomain];
  rw [ mem_closure_iff_seq_limit ] ; aesop;
  · refine' ⟨ fun n => ( 1 - 1 / ( n + 1 ) : ℝ ) • x, _, _ ⟩ <;> aesop;
    · exact mul_nonneg ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| by linarith ) <| a i |>.1;
    · nlinarith [ a i, inv_mul_cancel₀ ( by linarith : ( n_1 : ℝ ) + 1 ≠ 0 ) ];
    · exact le_trans ( Filter.Tendsto.smul ( tendsto_const_nhds.sub <| tendsto_inv_atTop_zero.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ( by norm_num );
  · -- Since the coordinate function is continuous, the limit of the coordinates of $w_n$ is the coordinate of $x$.
    have h_coord_cont : Filter.Tendsto (fun n => (B.asTopBasis.repr (w n)) i) Filter.atTop (nhds ((B.asTopBasis.repr x) i)) := by
      have h_coord_cont : Continuous (fun x => (B.asTopBasis.repr x) i) := by
        exact Continuous.comp ( continuous_apply i ) ( by exact? );
      exact h_coord_cont.continuousAt.tendsto.comp right;
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_coord_cont fun n => left n i |>.1;
  · have h_closure : Filter.Tendsto (fun n => (B.asTopBasis.repr (w n)) i) Filter.atTop (nhds ((B.asTopBasis.repr x) i)) := by
      have h_coord_cont : Continuous (fun x => (B.asTopBasis.repr x) i) := by
        exact Continuous.comp ( continuous_apply i ) ( by exact? );
      exact h_coord_cont.continuousAt.tendsto.comp right;
    exact le_of_tendsto_of_tendsto' h_closure tendsto_const_nhds fun n => left n i |>.2.le

/-- The fundamental parallelepiped of a lattice basis is convex. -/
theorem LatticeBasis.fundamentalDomain_isBounded (B : SquareLatticeBasis n) : Bornology.IsBounded B.fundamentalDomain := by
  exact ZSpan.fundamentalDomain_isBounded B.asTopBasis

/-- The fundamental parallelepiped of a lattice basis is convex. -/
theorem LatticeBasis.fundamentalDomain_isConvex (B : SquareLatticeBasis n) : Convex ℝ B.fundamentalDomain := by
  refine' convex_iff_forall_pos.mpr _;
  unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.fundamentalDomain; aesop;
  · nlinarith [ a i, a_1 i ];
  · nlinarith [ a i, a_1 i ]

/-- The determinant of a square lattice basis. -/
noncomputable def LatticeBasis.det (B : SquareLatticeBasis n) : ℝ :=
  B.asMatrix.det

/-- The volume of a square lattice basis. -/
noncomputable def LatticeBasis.volume (B : SquareLatticeBasis n) : ℝ :=
  |B.asMatrix.det|

theorem LatticeBasis.volume_pos (B : SquareLatticeBasis n) : 0 < B.volume := by
  rw [volume, abs_pos]
  exact B.det_ne_zero

/-- Determinant is invariant under unimodular equivalence. -/
theorem LatticeBasis.volume_of_unimodularEquiv {B1 B2 : SquareLatticeBasis n}
    (h : B1 =ᵤ B2) : B1.volume = B2.volume := by
  obtain ⟨U, rfl⟩ := h
  rw [ show B1.volume = |Matrix.det ( B1.asMatrix )| by rfl, show ( B1 ◾ U ).volume = |Matrix.det ( ( B1.asMatrix * ( U.val.map ( Int.castRingHom ℝ ) ) ) )| by rfl ] ; simp +decide [ Matrix.det_mul ];
  -- Since U is a unit in the matrix ring over ℤ, its determinant is ±1.
  have h_det_U : IsUnit (Matrix.det U.val) := by
    exact Matrix.isUnits_det_units U;
  -- Since U is a unit in the matrix ring over ℤ, its determinant is ±1. Therefore, the absolute value of the determinant of U is 1.
  have h_det_U_abs : |(U.val.det : ℝ)| = 1 := by
    rcases Int.isUnit_iff.mp h_det_U with ( h | h ) <;> norm_num [ h ];
  simp_all +decide [ Matrix.det_apply' ]

/-- The determinant (covolume) of a geometric lattice. -/
noncomputable def GeometricLattice.det (L : GeometricLattice n n) : ℝ :=
  L.basis.volume

/-- Well-definedness of lattice determinant. -/
theorem GeometricLattice.det_def (L : GeometricLattice n n) :
    L.det = L.basis.volume := by rfl

theorem GeometricLattice.det_eq_of_equiv {L1 L2 : GeometricLattice n n}
    (h : L1 ≡ᵤ L2) : L1.det = L2.det := by
  rw [eq_iff_basis_equiv] at h
  exact LatticeBasis.volume_of_unimodularEquiv h

/-- Reduce a vector modulo the fundamental domain. -/
noncomputable def LatticeBasis.mod (B : SquareLatticeBasis n) (v : 𝔼 n) : 𝔼 n :=
  ZSpan.fract B.asTopBasis v

/-- The reduction of a vector modulo the fundamental domain lies within the fundamental domain. -/
theorem LatticeBasis.mod_mem_fundamentalDomain (B : SquareLatticeBasis n) (v : 𝔼 n) :
    B.mod v ∈ B.fundamentalDomain := by
  exact ZSpan.fract_mem_fundamentalDomain B.asTopBasis v

/-- Any vector minus its module will lie in the lattice. -/
theorem LatticeBasis.sub_mod_mem_lattice (B : SquareLatticeBasis n) (v : 𝔼 n) :
    v - B.mod v ∈ B.toLattice.carrier := by
  rw [toLattice, mod]
  -- v - B.mod v = B * c - B * {c} = B * (c - {c}) = B * floor(c)
  refine' Submodule.mem_span.mpr _;
  bound;
  have := a ( Set.mem_range_self ( ⟨ 0, PNat.pos n ⟩ : Fin n ) ) ; simp_all +decide [ ZSpan.fract ] ;
  -- Since the floor of v is a linear combination of the basis vectors with integer coefficients, and each basis vector is in p, the floor of v is in p.
  have h_floor : ∀ (c : Fin n → ℤ), (∑ i, c i • B.cols i) ∈ p := by
    -- Since p is a submodule, it is closed under addition and scalar multiplication. Each basis vector is in p by hypothesis a, so multiplying each by an integer c_i keeps them in p. Then, adding them up should also keep the result in p.
    intros c
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply a
    simp [LatticeCrypto.Foundations.Lattice.LatticeBasis.cols];
  unfold ZSpan.floor; aesop;
  unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.asTopBasis; aesop;

/-- Any vector v can be decomposed into a lattice point and a point in the fundamental domain. -/
theorem LatticeBasis.eq_lattice_add_mod (B : SquareLatticeBasis n) (v : 𝔼 n) :
    ∃ (u : 𝔼 n) (w : 𝔼 n), u ∈ B.toLattice.carrier ∧ w ∈ B.fundamentalDomain ∧ v = u + w := by
  use v - B.mod v, B.mod v
  refine ⟨B.sub_mod_mem_lattice v, B.mod_mem_fundamentalDomain v, by abel⟩

/-- The fundamental parallelepiped of a lattice basis whose center is shifted to the origin. -/
def LatticeBasis.centeredFundamentalDomain (B : SquareLatticeBasis n) : Set (𝔼 n) :=
  {m | ∀ i, B.asTopBasis.repr m i ∈ Set.Ico (-0.5 : ℝ) 0.5}

/-- We define the closure of the centered fundamental parallelepiped as generated with coefficents
    from [-0.5, 0.5] -/
def LatticeBasis.centeredFundamentalDomain_closure (B : SquareLatticeBasis n) : Set (𝔼 n) :=
  {m | ∀ i, B.asTopBasis.repr m i ∈ Set.Icc (-0.5 : ℝ) 0.5}

/-- The closure defined as above is indeed a topological closure -/
theorem LatticeBasis.centeredFundamentalDomain.closure_apply (B : SquareLatticeBasis n) :
  B.centeredFundamentalDomain_closure = closure B.centeredFundamentalDomain := by
  apply le_antisymm;
  · -- The closure of the centered fundamental domain is a subset of the closure of the fundamental domain because the coordinates of the centered fundamental domain are within the coordinates of the fundamental domain.
    intros x hx
    simp [LatticeCrypto.Foundations.Lattice.LatticeBasis.centeredFundamentalDomain_closure] at hx;
    refine' mem_closure_iff_seq_limit.mpr _;
    use fun m => x - (1 / (m + 1) : ℝ) • ∑ i : Fin n, (B.asTopBasis.repr x i) • B.asTopBasis i;
    aesop;
    · intro i; specialize hx i; norm_num at *;
      constructor <;> nlinarith [ inv_mul_cancel₀ ( by linarith : ( n_1 : ℝ ) + 1 ≠ 0 ) ];
    · exact le_trans ( tendsto_const_nhds.sub ( Filter.Tendsto.smul ( tendsto_inv_atTop_zero.comp ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) tendsto_const_nhds ) ) ( by norm_num );
  · intro m hm; replace hm := mem_closure_iff_seq_limit.mp hm; aesop;
    -- Since the coordinates of $m$ are the limits of the coordinates of $w$, and each coordinate of $w$ is in $[-0.5, 0.5]$, it follows that each coordinate of $m$ is also in $[-0.5, 0.5]$.
    have h_coords : ∀ i, Filter.Tendsto (fun n => (B.asTopBasis.repr (w n) i)) Filter.atTop (nhds (B.asTopBasis.repr m i)) := by
      -- The basis representation is a continuous linear map, so if w converges to m, then the basis representation of w converges to the basis representation of m.
      have h_cont : Continuous (fun v : 𝔼 n => (B.asTopBasis.repr v : Fin n → ℝ)) := by
        exact Module.Basis.continuous_coe_repr (asTopBasis B);
      exact fun i => Filter.Tendsto.comp ( continuous_apply i |> Continuous.tendsto <| _ ) ( h_cont.tendsto m |> Filter.Tendsto.comp <| right );
    exact fun i => ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds ( h_coords i ) fun n => left n i |>.1, le_of_tendsto_of_tendsto' ( h_coords i ) tendsto_const_nhds fun n => left n i |>.2.le ⟩

/-- The shift vector: sum of half of each basis vector -/
noncomputable def LatticeBasis.halfBasisSum (B : SquareLatticeBasis n) : 𝔼 n :=
  ∑ i, (0.5 : ℝ) • B.cols i

/-- The centered fundamental domain equals the fundamental domain shifted by -½ ∑ bᵢ -/
theorem LatticeBasis.centeredFundamentalDomain_eq_shifted (B : SquareLatticeBasis n) :
    B.centeredFundamentalDomain = (fun v => v - B.halfBasisSum) '' B.fundamentalDomain := by
    unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.centeredFundamentalDomain; unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.fundamentalDomain; ext; aesop;
    · refine' ⟨ x + LatticeCrypto.Foundations.Lattice.LatticeBasis.halfBasisSum B, _, _ ⟩ <;> aesop;
      · -- By definition of `halfBasisSum`, we know that its i-th component is 0.5.
        have h_halfBasisSum_i : ((B.asTopBasis.repr (LatticeCrypto.Foundations.Lattice.LatticeBasis.halfBasisSum B)) i) = 0.5 := by
          -- The i-th component of the sum is the sum of the i-th components of each term.
          have h_halfBasisSum_i : ((B.asTopBasis.repr (LatticeCrypto.Foundations.Lattice.LatticeBasis.halfBasisSum B)) i) = ∑ j : Fin n, (0.5 : ℝ) * (B.asTopBasis.repr (B.cols j)) i := by
            unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.halfBasisSum; aesop;
          -- Since the basis is a basis, the representation of each basis vector in the basis is the standard basis vector.
          have h_basis_rep : ∀ x : Fin n, (B.asTopBasis.repr (B.cols x)) = Finsupp.single x 1 := by
            bound;
            convert ( B.asTopBasis.repr_self x_1 ) using 1;
            unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.asTopBasis; aesop;
          simp_all +decide [ Finsupp.single_apply ];
        linarith [ a i ];
      · -- The i-th component of the halfBasisSum is 0.5 times the i-th component of the i-th basis vector, which is 1.
        have h_halfBasisSum_i : (((LatticeCrypto.Foundations.Lattice.LatticeBasis.asTopBasis B).repr (LatticeCrypto.Foundations.Lattice.LatticeBasis.halfBasisSum B)) i) = 0.5 := by
          -- The i-th component of the sum is the sum of the i-th components of each term.
          have h_halfBasisSum_i : ((B.asTopBasis.repr (LatticeCrypto.Foundations.Lattice.LatticeBasis.halfBasisSum B)) i) = ∑ j : Fin n, (0.5 : ℝ) * (B.asTopBasis.repr (B.cols j)) i := by
            unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.halfBasisSum; aesop;
          -- Since the basis is a basis, the representation of each basis vector in the basis is the standard basis vector.
          have h_basis_rep : ∀ x : Fin n, (B.asTopBasis.repr (B.cols x)) = Finsupp.single x 1 := by
            bound;
            convert ( B.asTopBasis.repr_self x_1 ) using 1;
            unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.asTopBasis; aesop;
          simp_all +decide [ Finsupp.single_apply ];
        linarith [ a i ];
    · -- By definition of `halfBasisSum`, we have `halfBasisSum B = ∑ i, (0.5 : ℝ) • B.cols i`.
      have h_halfBasisSum : LatticeCrypto.Foundations.Lattice.LatticeBasis.halfBasisSum B = ∑ i, (0.5 : ℝ) • B.asTopBasis i := by
        unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.asTopBasis; aesop;
      rw [ h_halfBasisSum ] ; norm_num [ left ] ;
    · unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.halfBasisSum; norm_num;
      have h_sum : ∑ x : Fin n, (1 / 2 : ℝ) * (((LatticeCrypto.Foundations.Lattice.LatticeBasis.asTopBasis B).repr : LatticeCrypto.Foundations.Lattice.𝔼 n → Fin (↑n : ℕ) →₀ ℝ) (LatticeCrypto.Foundations.Lattice.LatticeBasis.cols B x) : Fin (↑n : ℕ) → ℝ) i = (1 / 2 : ℝ) := by
        -- Since the basis vectors are linearly independent, their representations in the basis are the standard basis vectors.
        have h_basis_rep : ∀ i : Fin n, (B.asTopBasis.repr (B.cols i)) = Finsupp.single i 1 := by
          aesop;
          convert B.asTopBasis.repr_self i_1 using 1;
          unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.asTopBasis; aesop;
        rw [ Finset.sum_eq_single i ] <;> aesop;
      linarith [ left i ]

/-- The fundamental parallelepiped of a lattice basis whose center is shifted to the origin is symmetric. -/
theorem LatticeBasis.centeredFundamentalDomain_closureIsSymmetric {x : 𝔼 n} (B: SquareLatticeBasis n) : x ∈ B.centeredFundamentalDomain_closure ↔ -x ∈ B.centeredFundamentalDomain_closure := by
  unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.centeredFundamentalDomain_closure; aesop;
  · linarith [ a i ];
  · linarith [ a i ]

/-- The fundamental parallelepiped of a lattice basis is convex. -/
theorem LatticeBasis.centeredFundamentalDomain_isBounded (B : SquareLatticeBasis n) : Bornology.IsBounded B.centeredFundamentalDomain := by
  -- The centered fundamental domain is contained within a ball of radius 0.5 times the sum of the norms of the basis vectors.
  have h_bounded : ∃ C : ℝ, ∀ m ∈ B.centeredFundamentalDomain, ‖m‖ ≤ C := by
    -- The norm of a sum is less than or equal to the sum of the norms.
    have h_norm_sum : ∀ m : 𝔼 n, ‖m‖ ≤ ∑ i, |B.asTopBasis.repr m i| * ‖B.cols i‖ := by
      intros m
      have h_norm_sum : ‖m‖ ≤ ‖∑ i, (B.asTopBasis.repr m i) • B.cols i‖ := by
        rw [ ← B.asTopBasis.sum_repr m ];
        convert le_rfl;
        · exact B.asTopBasis.sum_repr m;
        · ext; simp [LatticeBasis.asTopBasis];
          rfl;
      -- Apply the triangle inequality to the sum.
      have h_triangle : ‖∑ i, (B.asTopBasis.repr m i) • B.cols i‖ ≤ ∑ i, ‖(B.asTopBasis.repr m i) • B.cols i‖ := by
        exact norm_sum_le _ _;
      exact h_norm_sum.trans ( h_triangle.trans_eq ( Finset.sum_congr rfl fun _ _ => by rw [ norm_smul, Real.norm_eq_abs ] ) );
    -- Since each coordinate of m is between -0.5 and 0.5, the absolute value of each coordinate is at most 0.5.
    have h_abs_coord : ∀ m ∈ B.centeredFundamentalDomain, ∀ i, |B.asTopBasis.repr m i| ≤ 0.5 := by
      exact fun m hm i => abs_le.mpr ⟨ by linarith [ Set.mem_Ico.mp ( hm i ) ], by linarith [ Set.mem_Ico.mp ( hm i ) ] ⟩;
    exact ⟨ ∑ i : Fin n, 0.5 * ‖B.cols i‖, fun m hm => le_trans ( h_norm_sum m ) ( Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ( h_abs_coord m hm i ) ( norm_nonneg _ ) ) ⟩;
  -- Since the norm of every element in the set is bounded by C, the set is bounded.
  obtain ⟨C, hC⟩ := h_bounded;
  exact isBounded_iff_forall_norm_le.mpr ⟨C, fun m hm => hC m hm⟩

/-- The fundamental parallelepiped of a lattice basis is convex. -/
theorem LatticeBasis.centeredFundamentalDomain_isConvex (B : SquareLatticeBasis n) : Convex ℝ B.centeredFundamentalDomain := by
  -- To prove convexity, take any two points $x$ and $y$ in the centered fundamental domain and show that any convex combination of $x$ and $y$ is also in the domain.
  intro x hx y hy t ht
  simp [LatticeCrypto.Foundations.Lattice.LatticeBasis.centeredFundamentalDomain] at hx hy ⊢;
  -- By definition of convex combination, we can write the combination as a weighted average of the coordinates of x and y.
  intros ht_nonneg ht_nonneg' ht_sum
  intro i
  have h_coord : -0.5 ≤ t * (B.asTopBasis.repr x) i + (1 - t) * (B.asTopBasis.repr y) i ∧ t * (B.asTopBasis.repr x) i + (1 - t) * (B.asTopBasis.repr y) i < 0.5 := by
    -- By combining the inequalities for x and y, we can show that the convex combination is within the interval [-0.5, 0.5).
    apply And.intro;
    · nlinarith [ hx i, hy i ];
    · cases lt_or_eq_of_le ht_nonneg <;> cases lt_or_eq_of_le ht_nonneg' <;> nlinarith [ hx i, hy i ];
  convert h_coord using 1 <;> rw [ ← ht_sum ] ; ring;
  rw [ add_sub_cancel_left ]


end fundamental_domain

end LatticeCrypto.Foundations.Lattice
