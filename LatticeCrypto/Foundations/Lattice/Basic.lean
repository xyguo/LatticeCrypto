import LatticeCrypto.Foundations.Lattice.Defs
import Mathlib.Tactic.Contrapose
import Mathlib.Topology.Defs.Basic

import LatticeCrypto.Utils.LinearAlgebra
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Utils.Geometry

open scoped ENNReal NNReal
open scoped RealInnerProductSpace

/-!
  This file defines basic lattice operations for `EuclideanLattice` and `LatticeBasis`.

  ## EuclideanLattice Operations
  - `EuclideanLattice.coset` and `EuclideanLattice.Quotient`
  - `EuclideanLattice.smul`
  - `EuclideanLattice.mem`
  - `EuclideanLattice.dual`

  ## LatticeBasis Operations
  - `LatticeBasis.smul`
  - `LatticeBasis.dual`
  - `LatticeBasis.dual_inner` (biorthogonality: ⟨B_i, B*_j⟩ = δ_ij)

  ## Bridges
  - `EuclideanLattice.dual_carrier_eq` (dual lattice = vectors with integral inner products)
-/

namespace LatticeCrypto.Foundations.Lattice

variable {n k : ℕ+}

/-!
## Membership and Representation
-/

noncomputable section membership

/-!
### Membership to a Lattice
-/

/-- Membership in a lattice. -/
instance : Membership (𝓔 n) (EuclideanLattice n k) where
  mem L v := v ∈ L.carrier

/-- A vector is in the lattice iff it is in the carrier. -/
theorem EuclideanLattice.mem_def (L : EuclideanLattice n k) (v : 𝓔 n) :
    v ∈ L ↔ v ∈ L.carrier := Iff.rfl

/-- A vector is in the lattice iff it can be expressed as an integer linear combination of basis vectors. -/
theorem EuclideanLattice.mem_iff_zspan (L : EuclideanLattice n k) (v : 𝓔 n) :
    v ∈ L ↔ v ∈ Submodule.span ℤ (Set.range L.basis.cols) := by
  rw [mem_def, L.carrier_eq]

/-- A vector is in the lattice iff there exist integer coefficients such that v = ∑ cᵢ bᵢ. -/
theorem EuclideanLattice.mem_iff_exists_coeffs (L : EuclideanLattice n k) (v : 𝓔 n) :
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
theorem EuclideanLattice.zero_mem (L : EuclideanLattice n k) : (0 : 𝓔 n) ∈ L := by
  rw [mem_def]
  exact L.carrier.zero_mem

/-- The lattice is closed under addition. -/
theorem EuclideanLattice.add_mem (L : EuclideanLattice n k) {v w : 𝓔 n}
    (hv : v ∈ L) (hw : w ∈ L) : v + w ∈ L := by
  rw [mem_def] at *
  exact L.carrier.add_mem hv hw

/-- The lattice is closed under negation. -/
theorem EuclideanLattice.neg_mem (L : EuclideanLattice n k) {v : 𝓔 n}
    (hv : v ∈ L) : -v ∈ L := by
  rw [mem_def] at *
  exact L.carrier.neg_mem hv

/-- The lattice is closed under subtraction. -/
theorem EuclideanLattice.sub_mem (L : EuclideanLattice n k) {v w : 𝓔 n}
    (hv : v ∈ L) (hw : w ∈ L) : v - w ∈ L := by
  rw [mem_def] at *
  exact L.carrier.sub_mem hv hw

/-- The lattice is closed under integer scalar multiplication. -/
theorem EuclideanLattice.zsmul_mem (L : EuclideanLattice n k) {v : 𝓔 n}
    (hv : v ∈ L) (m : ℤ) : m • v ∈ L := by
  rw [mem_def] at *
  bound

/-- Basis vectors are in the lattice. -/
theorem EuclideanLattice.basis_mem (L : EuclideanLattice n k) (i : Fin k) :
    L.basis.cols i ∈ L := by
  rw [mem_iff_zspan]
  exact Submodule.subset_span (Set.mem_range_self i)

/-!
### Representation by a LatticeBasis
-/

/-- The representation of a lattice vector as integer coordinates with respect to the basis. -/
noncomputable def LatticeBasis.repr (B : LatticeBasis n k) (v : 𝓔 n)
    (hv : v ∈ B.toLattice) : Fin k → ℤ :=
  B.asZSpanBasis.repr ⟨v, B.toLattice.carrier_eq ▸ hv⟩

/-- The representation gives the correct coefficients. -/
theorem LatticeBasis.repr_spec (B : LatticeBasis n k) (v : 𝓔 n)
    (hv : v ∈ B.toLattice) : v = ∑ i, (B.repr v hv i) • B.basis i := by
  rw [EuclideanLattice.mem_def] at hv
  have hv' : v ∈ Submodule.span ℤ (Set.range B.basis) := B.toLattice.carrier_eq ▸ hv
  have h := B.asZSpanBasis.sum_repr ⟨v, hv'⟩
  simp only [LatticeBasis.asZSpanBasis] at h
  conv_lhs => rw [← Subtype.coe_mk v hv']
  convert congr_arg Subtype.val h.symm using 1;
  induction ( Finset.univ : Finset ( Fin k ) ) using Finset.induction <;> aesop (config := { warnOnNonterminal := false });
  congr;
  exact Eq.symm (Module.Basis.span_apply (LatticeBasis.asZSpanBasis._proof_1 B) a)

/-- Constructing a lattice vector from coefficients. -/
noncomputable def LatticeBasis.ofCoeffs (B : LatticeBasis n k)
    (c : Fin k → ℤ) : 𝓔 n :=
  ∑ i, c i • B.basis i

/-- A vector constructed from coefficients is in the lattice. -/
theorem LatticeBasis.ofCoeffs_mem (B : LatticeBasis n k)
    (c : Fin k → ℤ) : B.ofCoeffs c ∈ B.toLattice := by
  rw [EuclideanLattice.mem_iff_exists_coeffs]
  exact ⟨c, rfl⟩

/-- repr is a left inverse of ofCoeffs. -/
theorem LatticeBasis.repr_ofCoeffs (B : LatticeBasis n k)
    (c : Fin k → ℤ) : B.repr (B.ofCoeffs c) (B.ofCoeffs_mem c) = c := by
  have h_li : LinearIndependent ℤ B.basis :=
    Z_linearIndependent_if_R_linearIndependent B.li
  ext i
  have h_eq := B.repr_spec (B.ofCoeffs c) (B.ofCoeffs_mem c)
  simp only [ofCoeffs] at h_eq
  -- The representation is unique due to linear independence
  have h_unique : ∀ (c₁ c₂ : Fin k → ℤ),
      (∑ i, c₁ i • B.basis i) = (∑ i, c₂ i • B.basis i) → c₁ = c₂ := by
    intro c₁ c₂ heq
    have : ∑ i, (c₁ i - c₂ i) • B.basis i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [heq, sub_self]
    rw [Fintype.linearIndependent_iff] at h_li
    ext j
    have := h_li (fun i => c₁ i - c₂ i) this j
    omega
  exact congr_fun (h_unique _ _ h_eq.symm) i

/-- ofCoeffs is a left inverse of repr. -/
theorem LatticeBasis.ofCoeffs_repr (B : LatticeBasis n k) (v : 𝓔 n)
    (hv : v ∈ B.toLattice) : B.ofCoeffs (B.repr v hv) = v := by
  rw [ofCoeffs, ← repr_spec B v hv]

end membership


/-!
## Cosets and Quotients for EuclideanLattice
-/

noncomputable section coset

/-- The coset of a vector v with respect to lattice L: v + L -/
def EuclideanLattice.coset (L : EuclideanLattice n k) (v : 𝓔 n) : Set (𝓔 n) :=
  { x | ∃ l ∈ L.carrier, x = v + l }

-- Notation for cosets: v +ᶜ L
notation:65 v " +ᶜ " L:65 => EuclideanLattice.coset L v

/-- The quotient space ℝⁿ / L -/
def EuclideanLattice.Quotient (L : EuclideanLattice n k) : Type _ :=
  (𝓔 n) ⧸ L.carrier

/-- The canonical projection map π : ℝⁿ → ℝⁿ/L -/
def EuclideanLattice.mk_quotient (L : EuclideanLattice n k) (v : 𝓔 n) : L.Quotient :=
  QuotientAddGroup.mk v

/-- Two vectors are in the same coset iff their difference is in the lattice -/
theorem EuclideanLattice.coset_eq_iff (L : EuclideanLattice n k) (v w : 𝓔 n) :
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
    simp only [EuclideanLattice.coset, Set.mem_setOf_eq]
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

/-- Scale a lattice by a non-zero scalar -/
def EuclideanLattice.smul (L : EuclideanLattice n k) (c : ℝ) (hc : c ≠ 0) : EuclideanLattice n k :=
  (L.basis.smul c hc).toLattice

/-- Scaling preserves carrier equivalence (basically the theorem ZSpan.smul) -/
theorem EuclideanLattice.smul_carrier (L : EuclideanLattice n k) (c : ℝ) (hc : c ≠ 0) :
    (L.smul c hc).carrier = L.carrier.map (DistribMulAction.toLinearMap ℤ (𝓔 n) c) := by
  simp only [EuclideanLattice.smul, LatticeBasis.toLattice, LatticeBasis.smul]
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
    have h_mul : ∀ (m : ℤ) (v : 𝓔 n), v ∈ p → m • v ∈ p := by
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

/-
## Mapping by ambient automorphisms
-/

noncomputable section map

/-- Apply an ambient linear automorphism to each basis vector. -/
def LatticeBasis.map (B : LatticeBasis n k) (f : (𝓔 n) ≃L[ℝ] (𝓔 n)) : LatticeBasis n k :=
  { basis := fun i => f (B.basis i)
    le_dim := B.le_dim
    li := by
      have hker : LinearMap.ker (f.toLinearMap) = ⊥ := by
        exact (LinearEquiv.ker (f.toLinearEquiv))
      simpa [Function.comp] using
        B.li.map' (f.toLinearMap) hker }

/-- Mapping a basis by the identity map leaves it unchanged. -/
theorem LatticeBasis.map_id (B : LatticeBasis n k) :
    B.map (ContinuousLinearEquiv.refl ℝ (𝓔 n)) = B := by
  ext i
  rfl

/-- Mapping by `f` and then `g` equals mapping once by `f.trans g`. -/
theorem LatticeBasis.map_comp (B : LatticeBasis n k)
    (f g : (𝓔 n) ≃L[ℝ] (𝓔 n)) :
    (B.map f).map g = B.map (f.trans g) := by
  ext i
  rfl

/-- Apply an ambient linear automorphism to a lattice. -/
def EuclideanLattice.map (L : EuclideanLattice n k) (f : (𝓔 n) ≃L[ℝ] (𝓔 n)) :
    EuclideanLattice n k :=
  (L.basis.map f).toLattice

/-- Mapping a lattice by the identity map leaves it unchanged. -/
theorem EuclideanLattice.map_id (L : EuclideanLattice n k) :
    L.map (ContinuousLinearEquiv.refl ℝ (𝓔 n)) = L := by
  calc
    L.map (ContinuousLinearEquiv.refl ℝ (𝓔 n))
        = (L.basis.map (ContinuousLinearEquiv.refl ℝ (𝓔 n))).toLattice := rfl
    _ = L.basis.toLattice := by rw [LatticeBasis.map_id]
    _ = L := by simpa using (EuclideanLattice.eq_basis_toLattice (L := L)).symm

/-- Mapping by `f` and then `g` equals mapping once by `f.trans g`. -/
theorem EuclideanLattice.map_comp (L : EuclideanLattice n k)
    (f g : (𝓔 n) ≃L[ℝ] (𝓔 n)) :
    (L.map f).map g = L.map (f.trans g) := by
  simpa [EuclideanLattice.map] using
    congrArg LatticeBasis.toLattice (LatticeBasis.map_comp (B := L.basis) f g)

/-- Carrier description of a mapped lattice. -/
theorem EuclideanLattice.map_carrier (L : EuclideanLattice n k) (f : (𝓔 n) ≃L[ℝ] (𝓔 n)) :
    (L.map f).carrier = Submodule.map (f.toLinearMap.restrictScalars ℤ) L.carrier := by
  calc
    (L.map f).carrier = Submodule.span ℤ (Set.range ((L.basis.map f).cols)) := by
      simpa [EuclideanLattice.map] using (L.map f).carrier_eq
    _ = Submodule.span ℤ ((f.toLinearMap.restrictScalars ℤ) '' Set.range L.basis.cols) := by
      congr
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨L.basis.cols i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    _ = Submodule.map (f.toLinearMap.restrictScalars ℤ) (Submodule.span ℤ (Set.range L.basis.cols)) := by
      symm
      exact Submodule.map_span (f.toLinearMap.restrictScalars ℤ) (Set.range L.basis.cols)
    _ = Submodule.map (f.toLinearMap.restrictScalars ℤ) L.carrier := by
      rw [L.carrier_eq]

/-- Membership in a mapped lattice is equivalent to membership of the preimage point. -/
theorem EuclideanLattice.mem_map_iff (L : EuclideanLattice n k)
    (f : (𝓔 n) ≃L[ℝ] (𝓔 n)) (x : 𝓔 n) :
    x ∈ L.map f ↔ f.symm x ∈ L := by
  rw [EuclideanLattice.mem_def, EuclideanLattice.map_carrier, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy' : y = f.symm x := by
      simpa using congrArg f.symm hyx
    simpa [EuclideanLattice.mem_def, hy'] using hy
  · intro hx
    refine ⟨f.symm x, ?_, by simp⟩
    simpa [EuclideanLattice.mem_def] using hx

/-- Explicit equivalence between carrier types of `L` and `L.map f`. -/
def EuclideanLattice.mapCarrierEquiv (L : EuclideanLattice n k)
    (f : (𝓔 n) ≃L[ℝ] (𝓔 n)) :
    L.carrier ≃ (L.map f).carrier where
  toFun x := ⟨f x, by
    have hx : (x : 𝓔 n) ∈ L := x.2
    simpa [EuclideanLattice.mem_def] using
      (EuclideanLattice.mem_map_iff (L := L) (f := f) (x := f x)).2
        (by simpa using hx)⟩
  invFun x := ⟨f.symm x, by
    simpa [EuclideanLattice.mem_def] using
      (EuclideanLattice.mem_map_iff (L := L) (f := f) (x := x)).1 x.2⟩
  left_inv x := by
    ext
    simp
  right_inv x := by
    ext
    simp

/-- Rotation-specialized lattice map via a linear isometry equivalence. -/
abbrev EuclideanLattice.mapLinearIsometry (L : EuclideanLattice n k)
    (R : (𝓔 n) ≃ₗᵢ[ℝ] (𝓔 n)) : EuclideanLattice n k :=
  L.map R.toContinuousLinearEquiv

/-- Membership in a rotation-mapped lattice is equivalent to membership of the rotated-back point. -/
theorem EuclideanLattice.mem_mapLinearIsometry_iff (L : EuclideanLattice n k)
    (R : (𝓔 n) ≃ₗᵢ[ℝ] (𝓔 n)) (x : 𝓔 n) :
    x ∈ L.mapLinearIsometry R ↔ R.symm x ∈ L := by
  simpa [EuclideanLattice.mapLinearIsometry] using
    EuclideanLattice.mem_map_iff (L := L) (f := R.toContinuousLinearEquiv) (x := x)

/-- Carrier equivalence induced by a lattice rotation map. -/
abbrev EuclideanLattice.mapLinearIsometryCarrierEquiv (L : EuclideanLattice n k)
    (R : (𝓔 n) ≃ₗᵢ[ℝ] (𝓔 n)) :
    L.carrier ≃ (L.mapLinearIsometry R).carrier :=
  L.mapCarrierEquiv R.toContinuousLinearEquiv

end map

/-- Negation of a lattice -/
def EuclideanLattice.neg (L : EuclideanLattice n k) : EuclideanLattice n k :=
  L.smul (-1) (by norm_num)

/-- -L = L -/
theorem EuclideanLattice.neg_eq_self {L: EuclideanLattice n n} : L.neg ≡ᵤ L := by
  -- The carrier of the negated lattice is the same as the carrier of the original lattice because negation is an automorphism.
  apply EuclideanLattice.eq_iff_basis_equiv.mpr;
  -- Since multiplying by -1 is a unimodular transformation, we can construct the unimodular matrix U as -1.
  use -1;
  -- By definition of `L.neg`, we have `L.neg.basis = L.basis.smul (-1)`.
  have h_basis_neg : L.neg.basis = L.basis.smul (-1) (by
  norm_num) := by rfl
  generalize_proofs at *;
  -- By definition of `smul`, we have `L.neg.basis = L.basis.smul (-1)`.
  rw [h_basis_neg];
  unfold LatticeBasis.smul LatticeBasis.mul_unimodular; aesop (config := { warnOnNonterminal := false });
  unfold LatticeBasis.asMatrix; ext i j; simp +decide [ Matrix.mul_apply ] ;
  simp +decide [ Matrix.one_apply ]

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
  contrapose! h_li; aesop (config := { warnOnNonterminal := false });
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
      aesop (config := { warnOnNonterminal := false });
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
  The dual lattice of a full-rank lattice.
  L* is generated by the dual basis B*.
-/
def EuclideanLattice.dual (L : EuclideanLattice n n) : EuclideanLattice n n :=
  L.basis.dual.toLattice

/--
  The set of vectors with integral inner product against all lattice vectors.
-/
def integralDualSet (L : EuclideanLattice n n) : Set (𝓔 n) :=
  { y | ∀ x ∈ L.carrier, ∃ m : ℤ, ⟪x, y⟫ = (m : ℝ) }

/--
  The dual lattice carrier equals the set of vectors with integral inner products.
  This is the key characterization: L* = { y ∈ ℝⁿ | ∀ x ∈ L, ⟨x, y⟩ ∈ ℤ }
-/
theorem EuclideanLattice.dual_carrier_eq_integralDual (L : EuclideanLattice n n) :
    (L.dual.carrier : Set (𝓔 n)) = integralDualSet L := by
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
    rw [ Finset.sum_congr rfl fun i hi => by rw [ sum_inner, Finset.sum_congr rfl fun j hj => by rw [ inner_smul_left ] ] ] ; aesop (config := { warnOnNonterminal := false });
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
      have h_dual_basis : ∀ v : 𝓔 n, ∃ a : Fin n → ℝ, v = ∑ i, a i • L.dual.basis.cols i := by
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
theorem EuclideanLattice.mem_dual_iff_integral_inner_basis (L : EuclideanLattice n n) (y : 𝓔 n) :
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
        rw [ sum_inner, Finset.sum_congr rfl ] ; intros ; aesop (config := { warnOnNonterminal := false });
        convert inner_smul_left _ _ _;
        ext;
        erw [ Real.ofCauchy_intCast ] ; norm_num;
      choose m hm using h; use ∑ i, c i * m i; simp_all +decide ;
    exact ( EuclideanLattice.dual_carrier_eq_integralDual L ) |>.symm.subset h_integral_dual

/--
  If `v ∈ L` and `w ∈ L.dual`, then `⟪v, w⟫` is an integer.
-/
theorem EuclideanLattice.inner_lattice_dual_int (L : EuclideanLattice n n) (v w : 𝓔 n)
    (hv : v ∈ L.carrier) (hw : w ∈ L.dual.carrier) : ∃ k : ℤ, inner ℝ v w = k := by
  have h_dual : w ∈ integralDualSet L := by
    exact (EuclideanLattice.dual_carrier_eq_integralDual L) ▸ hw
  simpa [integralDualSet, Set.mem_setOf_eq] using h_dual v hv

/--
  The dual of the dual lattice is the original lattice.
-/
theorem EuclideanLattice.dual_dual (L : EuclideanLattice n n) : L.dual.dual ≡ᵤ L := by
  rw [EuclideanLattice.eq_iff_basis_equiv]
  -- L.dual.dual.basis = L.basis.dual.dual =ᵤ L.basis
  have h : L.dual.dual.basis = L.basis := by
    -- This follows from LatticeBasis.dual_dual
    simp only [EuclideanLattice.dual, LatticeBasis.toLattice]
    exact L.basis.dual_dual
  rw [h]
  exact LatticeBasis.UnimodularEquiv.refl L.basis

/-
The dual of a lattice scaled by c is equivalent to the dual of the original lattice scaled by 1/c.
-/
theorem EuclideanLattice.dual_of_smul_eq_dual_smul_inv {n : ℕ+} (L : EuclideanLattice n n) (c : ℝ) (hc : c ≠ 0) :
    (L.smul c hc).dual ≡ᵤ L.dual.smul (1 / c) (by simp [hc]) := by
      unfold EuclideanLattice.dual;
      unfold LatticeBasis.dual;
      -- The dual of a diagonal matrix is the diagonal matrix with the reciprocals of the diagonal entries.
      have h_dual_diag : ∀ (d : ℝ), (Matrix.diagonal (fun _ => d) : Matrix (Fin n) (Fin n) ℝ).transpose⁻¹ = Matrix.diagonal (fun _ => 1 / d) := by
        simp +decide [ Matrix.inv_def ];
        intro d; by_cases hd : d = 0 <;> simp +decide [ hd, Matrix.smul_eq_diagonal_mul ] ;
        cases n using PNat.recOn <;> simp +decide [ pow_succ', mul_comm, hd ];
      simp_all +decide ;
      -- By definition of matrix multiplication and the properties of diagonal matrices, we can show that the two lattices are equivalent.
      have h_equiv : (L.smul c hc).basis.asMatrix = c • L.basis.asMatrix := by
        exact rfl;
      -- By definition of matrix multiplication and the properties of diagonal matrices, we can show that the two lattices are equivalent. Specifically, multiplying the basis matrix by c and then taking the inverse is the same as taking the inverse first and then multiplying by 1/c.
      have h_equiv : ((c • L.basis.asMatrix).transpose)⁻¹ = (1 / c) • (L.basis.asMatrix.transpose)⁻¹ := by
        simp +decide [ Matrix.smul_eq_diagonal_mul ];
        rw [ Matrix.mul_inv_rev, h_dual_diag ];
      unfold LatticeBasis.toLattice; aesop;


end dual


end LatticeCrypto.Foundations.Lattice
