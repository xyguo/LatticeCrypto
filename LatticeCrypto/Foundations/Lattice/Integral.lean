import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Foundations.Lattice.FundamentalDomain
import LatticeCrypto.Utils.LinearAlgebra
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec

open LatticeCrypto.Utils.LinearAlgebra
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.Vec

namespace LatticeCrypto.Foundations.Lattice

namespace Integral

variable {n k : ℕ+}

/-!
## Bridge to Euclidean Lattice
-/

/-- The standard integer lattice ℤⁿ inside 𝓔 n = ℝⁿ. -/
def ZnSubmodule (n : ℕ+) : Submodule ℤ (𝓔 n) :=
  Submodule.span ℤ (Set.range (stdBasis : Fin n → 𝓔 n))

/-- Predicate: a real lattice basis is integral iff each basis vector lies in `ℤ^n`. -/
class IsIntegralBasis (B : LatticeBasis n k) : Prop where
  integral : ∀ j : Fin k, B.cols j ∈ ZnSubmodule n

namespace IntegralBasis

theorem exists_col_int (B : LatticeBasis n k) [hb : IsIntegralBasis B] (j : Fin k) :
    ∃ z : Fin n → ℤ, ∀ i : Fin n, (B.cols j : 𝓔 n) i = (z i : ℝ) := by
  have h_int : (B.cols j : 𝓔 n) ∈ Submodule.span ℤ (Set.range (stdBasis : Fin n → 𝓔 n)) := by
    simpa [ZnSubmodule] using hb.integral j
  rw [Submodule.mem_span_range_iff_exists_fun] at h_int
  obtain ⟨c, hc⟩ := h_int
  refine ⟨c, ?_⟩
  intro i
  have hci := congrArg (fun v : 𝓔 n => v i) hc
  have hsum : (∑ x, c x • (stdBasis x : 𝓔 n)) i = (c i : ℝ) := by
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [stdBasis]
    · intro b hb hbne
      have hne : i ≠ b := by intro h; exact hbne h.symm
      simp [stdBasis, hne]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  exact hci.symm.trans hsum

/-- Integer coordinate matrix extracted from an integral basis. -/
noncomputable def toMatrixZ (B : LatticeBasis n k) [hb : IsIntegralBasis B] : Matrix (Fin n) (Fin k) ℤ :=
  fun i j => (Classical.choose (exists_col_int B j)) i

/-- Constructor from an integer matrix plus linear independence over `ℝ`. -/
noncomputable def fromMatrixZ (M : Matrix (Fin n) (Fin k) ℤ) (h_le_dim : k ≤ n)
    (h_li : LinearIndependent ℝ (fun j => piToEuc (fun i => (M i j : ℝ)))) :
    { B : LatticeBasis n k // IsIntegralBasis B } := by
  refine ⟨
    { basis := fun j => piToEuc (fun i => (M i j : ℝ))
      le_dim := h_le_dim
      li := h_li },
    ?_⟩
  refine ⟨?_⟩
  intro j
  change (piToEuc (fun i => (M i j : ℝ))) ∈ Submodule.span ℤ (Set.range (stdBasis : Fin n → 𝓔 n))
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun i => M i j, ?_⟩
  ext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · have hleft : (((fun i => M i j) i : ℤ) • (stdBasis i : 𝓔 n)) i = (M i j : ℝ) := by
      simp [stdBasis]
    have hright : (piToEuc (fun i => (M i j : ℝ))) i = (M i j : ℝ) := rfl
    exact hleft.trans hright.symm
  · intro b hb hbne
    have hne : i ≠ b := by intro h; exact hbne h.symm
    simp [stdBasis, hne]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- `toMatrixZ` preserves column vectors. -/
theorem toMatrixZ_cols (B : LatticeBasis n k) [hb : IsIntegralBasis B] :
    (fun j => piToEuc (fun i => ((toMatrixZ B) i j : ℝ))) = B.cols := by
  funext j
  apply LatticeCrypto.Utils.Vec.eucToPi.injective
  funext i
  have hz := (Classical.choose_spec (exists_col_int B j)) i
  simpa [toMatrixZ, LatticeBasis.cols] using hz.symm

/-- `toMatrixZ` preserves linear independence. -/
theorem toMatrixZ_li (B : LatticeBasis n k) [hb : IsIntegralBasis B] :
    LinearIndependent ℝ (fun j => piToEuc (fun i => ((toMatrixZ B) i j : ℝ))) := by
  simpa [toMatrixZ_cols (B := B)] using B.li

/-- Converting an integer matrix to a basis and back recovers the same matrix. -/
theorem toMatrixZ_fromMatrixZ (M : Matrix (Fin n) (Fin k) ℤ) (h_le_dim : k ≤ n)
    (h_li : LinearIndependent ℝ (fun j => piToEuc (fun i => (M i j : ℝ)))) :
    toMatrixZ (B := (fromMatrixZ M h_le_dim h_li).1) (hb := (fromMatrixZ M h_le_dim h_li).2) = M := by
  ext i j
  have hz := (Classical.choose_spec
    (exists_col_int (B := (fromMatrixZ M h_le_dim h_li).1) (hb := (fromMatrixZ M h_le_dim h_li).2) j)) i
  have hreal :
      ((toMatrixZ (B := (fromMatrixZ M h_le_dim h_li).1) (hb := (fromMatrixZ M h_le_dim h_li).2) i j : ℤ) : ℝ)
        = (M i j : ℝ) := by
    calc
      ((toMatrixZ (B := (fromMatrixZ M h_le_dim h_li).1)
        (hb := (fromMatrixZ M h_le_dim h_li).2) i j : ℤ) : ℝ)
        = (((fromMatrixZ M h_le_dim h_li).1.cols j : 𝓔 n) i) := by
          simpa [toMatrixZ] using hz.symm
      _ = (M i j : ℝ) := by rfl
  exact_mod_cast hreal

/-- Converting an integral basis to an integer matrix and back recovers the same basis. -/
theorem fromMatrixZ_toMatrixZ (B : LatticeBasis n k) [hb : IsIntegralBasis B] :
    (fromMatrixZ (toMatrixZ B) B.le_dim (toMatrixZ_li B)).1 = B := by
  apply LatticeBasis.ext
  funext j
  have hcol := congrArg (fun f : Fin k → 𝓔 n => f j) (toMatrixZ_cols (B := B))
  simpa [LatticeBasis.cols] using hcol

end IntegralBasis

/-- A predicate asserting that a EuclideanLattice is integral. Mathematically, Λ ⊆ ℤⁿ. -/
class IsIntegralLattice {n k : ℕ+} (L : EuclideanLattice n k) : Prop where
  subset_int : L.carrier ≤ ZnSubmodule n

/-- A lattice is integral iff all lattice vectors have integer components. -/
theorem isIntegralLattice_iff_vec_integral (L : EuclideanLattice n k) :
    IsIntegralLattice L ↔ ∀ v ∈ L.carrier, ∃ z : Fin n → ℤ, ∀ i : Fin n, (v : 𝓔 n) i = (z i : ℝ) := by
    simp +decide at *;
    constructor;
    · intro hL v hv;
      have h_int : v ∈ Submodule.span ℤ (Set.range (stdBasis : Fin n → 𝓔 n)) := by
        convert hL.subset_int hv using 1;
      rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_int;
      obtain ⟨ c, rfl ⟩ := h_int;
      simp +decide [ Finsupp.sum_fintype, stdBasis ];
      exact ⟨ c, fun i => by rw [ Finset.sum_apply, Finset.sum_eq_single i ] <;> aesop ⟩;
    · intro h;
      refine' ⟨ fun v hv => _ ⟩;
      obtain ⟨ z, hz ⟩ := h v hv;
      -- Since $v$ is equal to the sum of the standard basis vectors multiplied by the integers $z_i$, it is in the span of the standard basis vectors.
      have h_sum : v = ∑ i, z i • (stdBasis i : 𝓔 n) := by
        ext i; simp +decide [ hz, stdBasis ] ;
        rw [ Finset.sum_apply, Finset.sum_eq_single i ] <;> aesop;
      exact h_sum.symm ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_range_self _ ) )


/-- A Euclidean lattice is integral iff its basis vectors have integer components. -/
theorem isIntegralLattice_iff_isIntegralBasis (L : EuclideanLattice n k) :
  IsIntegralLattice L ↔ IsIntegralBasis L.basis := by
  constructor;
  · -- If the lattice is integral, then the carrier is a subset of ZnSubmodule n.
    intro h_integral
    refine ⟨?_⟩
    intro j
    have h_basis_in_carrier : L.basis.cols j ∈ L.carrier := by
      exact Submodule.subset_span ( Set.mem_range_self j ) |> fun h => L.carrier_eq.symm ▸ h
    exact h_integral.subset_int h_basis_in_carrier
  · intro h_integral
    have h_span : Submodule.span ℤ (Set.range L.basis.cols) ≤ ZnSubmodule n := by
      exact Submodule.span_le.mpr (Set.range_subset_iff.mpr h_integral.integral)
    exact ⟨ fun v hv => h_span <| by simpa [ L.carrier_eq ] using hv ⟩


/-- An integral basis generates an Integral Lattice -/
def IntegralLattice.ofIntegralBasis (B : LatticeBasis n k) [IsIntegralBasis B] : EuclideanLattice n k :=
  B.toLattice

/--
  The integral lattice generated by an integral basis is indeed an integral lattice.
-/
instance (B : LatticeBasis n k) [IsIntegralBasis B] : IsIntegralLattice (IntegralLattice.ofIntegralBasis B) := by
  refine ⟨?_⟩
  simpa [IntegralLattice.ofIntegralBasis] using
    (Submodule.span_le.mpr (Set.range_subset_iff.mpr (IsIntegralBasis.integral (B := B))))

/-- We can extract an integral basis from an IntegralLattice. -/
def IntegralBasis.ofIntegralLattice (L : EuclideanLattice n k) : LatticeBasis n k :=
  L.basis

/--
  The integral basis of an integral lattice is indeed an integral basis.
-/
instance (L : EuclideanLattice n k) [IsIntegralLattice L] : IsIntegralBasis (IntegralBasis.ofIntegralLattice L) := by
  refine ⟨?_⟩
  intro j
  have hBint : IsIntegralBasis L.basis := (isIntegralLattice_iff_isIntegralBasis L).mp (by infer_instance)
  simpa [IntegralBasis.ofIntegralLattice] using
    hBint.integral j


noncomputable section Z_n

/--
  The standard basis of the integer lattice Z^n.
-/
def stdBasisZ (n : ℕ+) : LatticeBasis n n :=
  {
    basis := stdBasis
    le_dim := le_refl n
    li := (stdBasis.linearIndependent : LinearIndependent ℝ (fun j : Fin n => (stdBasis j : 𝓔 n)))
  }

/-- The standard basis is an integral basis -/
instance {n : ℕ+} : IsIntegralBasis (stdBasisZ n) := by
  refine ⟨?_⟩
  intro j
  simpa [stdBasisZ, ZnSubmodule] using
    (Submodule.subset_span (Set.mem_range_self j) :
      (stdBasis j : 𝓔 n) ∈ Submodule.span ℤ (Set.range (stdBasis : Fin n → 𝓔 n)))

/-- The integer lattice Z^n -/
def Z (n : ℕ+) : EuclideanLattice n n :=
  let b := stdBasisZ n
  b.toLattice

/-- Zn is an integral lattice -/
instance {n : ℕ+} : IsIntegralLattice (Z n) := by
  have h : IsIntegralLattice (IntegralLattice.ofIntegralBasis (n := n) (k := n)
      (B := stdBasisZ n)) := by
    infer_instance
  simpa [Z, IntegralLattice.ofIntegralBasis] using h

/-
The determinant of the integer lattice Zn is 1.
-/
theorem Zn_det_one {n : ℕ+}: (Z n).det = 1 := by
  have hA : (Z n).basis.asMatrix =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Z, stdBasisZ, LatticeBasis.toLattice,
      LatticeBasis.asMatrix, stdBasis, Matrix.one_apply]
  show |(Z n).basis.asMatrix.det| = 1
  simp [hA]

/-
The dual of Zn is itself.
-/
theorem Zn_dual_eq_Zn :
    let Zn := Z n
    Zn.dual = Zn := by
  classical
  simp
  let Zn : EuclideanLattice n n := Z n
  have hA : Zn.basis.asMatrix = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Zn, Z, stdBasisZ, LatticeBasis.toLattice, LatticeBasis.asMatrix, stdBasis, Matrix.one_apply]
  have hDualMatrix : Zn.basis.dual.asMatrix = (1 : Matrix (Fin n) (Fin n) ℝ) :=
    calc Zn.basis.dual.asMatrix
        = (Zn.basis.asMatrix.transpose)⁻¹ := by simpa using LatticeBasis.dual_asMatrix Zn.basis
      _ = 1 := by simp [hA]
  have hDualBasis : Zn.basis.dual = Zn.basis := by
    apply LatticeBasis.ext; funext j
    apply LatticeCrypto.Utils.Vec.eucToPi.injective; funext i
    simpa [LatticeBasis.asMatrix] using show Zn.basis.dual.asMatrix i j = Zn.basis.asMatrix i j by
      simp [hDualMatrix, hA]
  have hDual : Zn.dual = Zn := by
    calc Zn.dual = Zn.basis.toLattice := by simp [EuclideanLattice.dual, hDualBasis]
      _ = Zn := (EuclideanLattice.eq_basis_toLattice (L := Zn)).symm
  simpa [Zn] using hDual

/-- Corollary: The dual carrier of Z^n is naturally isomorphic to the carrier of Z^n -/
def Zn_dual_carrier_equiv (n : ℕ+) : (Z n).dual.carrier ≃ (Z n).carrier := by
  refine
  { toFun := fun v =>
      ⟨v.1, by
        have hdual : (Z n).dual = Z n := by
          simpa using (Zn_dual_eq_Zn (n := n))
        simpa [hdual] using (v.2 : v.1 ∈ (Z n).dual.carrier)⟩
    invFun := fun v =>
      ⟨v.1, by
        have hdual : (Z n).dual = Z n := by
          simpa using (Zn_dual_eq_Zn (n := n))
        simp [hdual]⟩
    left_inv := by intro v; ext; rfl
    right_inv := by intro v; ext; rfl }

/-- Explicit map from primal carrier to dual carrier. -/
def ZnToZnDual (v : (Z n).carrier) : (Z n).dual.carrier :=
  (Zn_dual_carrier_equiv n).symm v

/-- Coerce a dual lattice vector into the primal lattice carrier. -/
def ZnDualToZn (v : (Z n).dual.carrier) : (Z n).carrier :=
  (Zn_dual_carrier_equiv n) v

/-- Coercion from dual carrier to carrier. -/
instance {n : ℕ+} : Coe ((Z n).dual.carrier) ((Z n).carrier) := ⟨ZnDualToZn (n := n)⟩

/-
The basis of Zn is the standard basis.
-/
lemma Zn_basis_eq_stdBasis :
  let Zn := Z n
  Zn.basis.asTopBasis = stdBasis (n := n) := by
  -- By definition of $Zn$, its basis is the standard basis.
  ext i j
  simp [Z, stdBasisZ, LatticeBasis.toLattice, stdBasis]

/--
  The columns of the basis of Zn are the standard basis vectors.
-/
lemma Zn_basis_cols_eq_stdBasis (i : Fin n) :
  let Zn := Z n
  Zn.basis.cols i = stdBasis i := by
  ext j
  simp [Z, stdBasisZ, LatticeBasis.toLattice, LatticeBasis.cols, stdBasis]

/-
The fundamental domain of Zn is the unit hypercube.
-/
lemma Zn_fundamentalDomain_eq_pi_Ico :
  let Zn := Z n
  Zn.basis.fundamentalDomain =
      Set.pi Set.univ (fun _ : Fin n => Set.Ico 0 1) := by
      unfold LatticeBasis.fundamentalDomain;
      ext; simp [Zn_basis_eq_stdBasis];
      simp +decide [ Set.pi, stdBasis ];
      rfl

/-
The volume of the fundamental domain of Zn is 1.
-/
lemma volume_Zn_fundamentalDomain_eq_one :
  let Zn := Z n
  MeasureTheory.volume (Zn.basis.fundamentalDomain : Set (𝓔 n)) = 1 := by
  let Zn := Z n
  have h := LatticeBasis.volume_fundamentalDomain Zn.basis
  -- LatticeBasis.volume is definitionally equal to EuclideanLattice.det
  exact h.trans (by
    have hv : Zn.basis.volume = 1 := Zn_det_one
    simp [hv])

/-- Integer vectors -/
abbrev ZVec (n : ℕ) := Fin n → ℤ

/-- Simple wrapper convert a ZVec to an element of 𝓔 n -/
def zToE (z : ZVec n) : 𝓔 n := fun i => (z i : ℝ)

/-- Coercion to 𝓔 n -/
instance {n : ℕ+} : Coe (ZVec n) (𝓔 n) := ⟨zToE⟩

@[simp] lemma zToE_apply (z : ZVec n) (i : Fin n) : zToE (n:=n) z i = (z i : ℝ) := rfl

/-- Any integer vector is in the carrier of Z^n -/
lemma zVec_mem_Zn_carrier (z : ZVec n) :
  let Zn := Z n
  zToE z ∈ Zn.carrier := by
  let Zn := Z n
  have hmem : zToE z ∈ Zn := by
    rw [EuclideanLattice.mem_iff_exists_coeffs]
    refine ⟨z, ?_⟩
    ext i
    change (z i : ℝ) = (∑ x : Fin n, ((z x : ℤ) • (Zn.basis.cols x)) ) i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [Zn, Z, stdBasisZ, LatticeBasis.toLattice, LatticeBasis.cols, stdBasis]
    · intro b hb hbne
      have hne : i ≠ b := by intro h; exact hbne h.symm
      simp [Zn, Z, stdBasisZ, LatticeBasis.toLattice, LatticeBasis.cols, stdBasis, hne]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  simpa [EuclideanLattice.mem_def] using hmem

/-- Convert a ZVec to a vector in the carrier of Z^n -/
def ZVec.toZn (z : ZVec n) : (Z n).carrier :=
  ⟨ zToE z, zVec_mem_Zn_carrier (n:=n) z ⟩

/-- Convert a ZVec to a vector in the dual carrier of Z^n -/
def ZVec.toZnDual (z : ZVec n) : (Z n).dual.carrier := by
  -- rewrite Zn.dual.carrier to Zn.carrier
  simpa [Zn_dual_eq_Zn] using (ZVec.toZn (n:=n) z)

/-- For any vector in the carrier of Z^n, there exists a ZVec that maps to it -/
lemma exists_ZVec_toZn_eq (v : (Z n).carrier) :
    ∃ z : ZVec n, ZVec.toZn (n:=n) z = v := by
  let Zn := Z n
  have hInt : IsIntegralLattice Zn := inferInstance
  have hcoords := (isIntegralLattice_iff_vec_integral (L := Zn)).1 hInt
  obtain ⟨z, hz⟩ := hcoords (v : 𝓔 n) v.2
  refine ⟨z, ?_⟩
  ext i
  simp [ZVec.toZn, zToE, hz i]

/-- Convert a vector in the carrier of Z^n to a ZVec -/
noncomputable def Zn.toZVec (v : (Z n).carrier) : ZVec n :=
  Classical.choose (exists_ZVec_toZn_eq (n:=n) v)

/-- The conversion preserves the vector -/
@[simp]
theorem Zn_toZVec_toZn (v : ((Z n).carrier)) :
    (Zn.toZVec v).toZn = v := by
  exact Classical.choose_spec (exists_ZVec_toZn_eq (n:=n) v)

/-- Converting a carrier element of `Z^n` to `ZVec` and back to `𝓔 n` returns the original vector. -/
@[simp]
theorem zToE_toZVec (v : (Z n).carrier) :
    zToE (Zn.toZVec v) = (v : 𝓔 n) := by
  have h := congrArg (fun w : (Z n).carrier => (w : 𝓔 n)) (Zn_toZVec_toZn (n := n) v)
  simpa [ZVec.toZn] using h

/-- Converting a `ZVec` to `(Z n).carrier` and back with `Zn.toZVec` is the identity. -/
@[simp]
theorem Zn_toZVec_toZn_left (z : ZVec n) :
    Zn.toZVec (ZVec.toZn z) = z := by
  ext i
  have h : zToE (Zn.toZVec (ZVec.toZn z)) = zToE z := by
    calc
      zToE (Zn.toZVec (ZVec.toZn z)) = ((ZVec.toZn z : (Z n).carrier) : 𝓔 n) :=
        zToE_toZVec (n := n) (v := ZVec.toZn z)
      _ = zToE z := rfl
  exact by
    have hi := congrArg (fun f : 𝓔 n => f i) h
    simpa [zToE] using hi

/-- Canonical equivalence between integer vectors and the carrier of Z^n. -/
noncomputable def zVecEquivZnCarrier (n : ℕ+) : ZVec n ≃ (Z n).carrier :=
  { toFun := ZVec.toZn (n := n)
    invFun := Zn.toZVec (n := n)
    left_inv := Zn_toZVec_toZn_left (n := n)
    right_inv := Zn_toZVec_toZn (n := n) }

/-- Canonical equivalence between integer vectors and the dual carrier of Z^n. -/
noncomputable def zVecEquivZnDualCarrier (n : ℕ+) : ZVec n ≃ (Z n).dual.carrier :=
  (zVecEquivZnCarrier n).trans (Zn_dual_carrier_equiv n).symm

/-- Coercing `ZnDualToZn k` to `𝓔 n` preserves the underlying vector. -/
@[simp]
theorem coe_ZnDualToZn (k : (Z n).dual.carrier) :
    ((ZnDualToZn k : (Z n).carrier) : 𝓔 n) = (k : 𝓔 n) := by
  rfl

/-- Converting a dual-carrier vector through `ZnDualToZn` then `Zn.toZVec` recovers the same `𝓔 n` vector. -/
@[simp]
theorem zToE_toZVec_dual (k : (Z n).dual.carrier) :
    zToE (Zn.toZVec (ZnDualToZn k)) = (k : 𝓔 n) := by
  calc
    zToE (Zn.toZVec (ZnDualToZn k)) = ((ZnDualToZn k : (Z n).carrier) : 𝓔 n) :=
      zToE_toZVec (n := n) (v := ZnDualToZn k)
    _ = (k : 𝓔 n) := coe_ZnDualToZn (n := n) k

end Z_n

end Integral

end LatticeCrypto.Foundations.Lattice
