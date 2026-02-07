import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
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
## Integral Lattice Basis

An integral lattice basis is represented strictly by integer coefficients.
This is the standard representation in algorithmic lattice theory (e.g., LLL).
-/

/--
An integral lattice basis: k linearly independent vectors in ℤⁿ (k ≤ n).
Represented as an integer matrix.
-/
structure IntegralLatticeBasis (n k : ℕ+) where
  /-- The basis matrix with integer entries -/
  matrix : Matrix (Fin n) (Fin k) ℤ
  /-- The rank constraint -/
  le_dim : k ≤ n
  /--
  Linearly independent over ℝ when cast.
  Note: We must check independence over ℝ, not just ℤ, to form a valid geometric lattice.
  -/
  li : LinearIndependent ℝ (fun j => piToEuc (fun i => (matrix i j : ℝ)))

/--
Convert an IntegralLatticeBasis to the general real LatticeBasis.
This allows us to reuse all existing theorems for real lattices.
-/
def IntegralLatticeBasis.toRealBasis (B : IntegralLatticeBasis n k) : LatticeBasis n k :=
  { basis := fun j i => (B.matrix i j : ℝ)
    le_dim := B.le_dim
    li := B.li }

-- Set up coercion so you can use an Integral basis anywhere a real basis is expected
instance : Coe (IntegralLatticeBasis n k) (LatticeBasis n k) :=
  ⟨IntegralLatticeBasis.toRealBasis⟩

/-!
## Properties and Determinants
-/


/-!
## Bridge to Geometric Lattice
-/

/-- The standard integer lattice ℤⁿ inside 𝓔 n = ℝⁿ. -/
def ZnSubmodule (n : ℕ+) : Submodule ℤ (𝓔 n) :=
  Submodule.span ℤ (Set.range (stdBasis : Fin n → 𝓔 n))

/-- A predicate asserting that a EuclideanLattice is integral. Mathematically, Λ ⊆ ℤⁿ. -/ class IsIntegral (L : EuclideanLattice n k) : Prop where
  subset_int : L.carrier ≤ ZnSubmodule n

/-- A lattice is integral iff all lattice vectors have integer components. -/
theorem isIntegral_iff_vec_integral (L : EuclideanLattice n k) :
    IsIntegral L ↔ ∀ v ∈ L.carrier, ∃ z : Fin n → ℤ, ∀ i : Fin n, (v : 𝓔 n) i = (z i : ℝ) := by
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

/-- A special lattice that is a subset of ℤⁿ -/
structure IntegralLattice (n k : ℕ+) extends EuclideanLattice n k where
  integral : IsIntegral toEuclideanLattice

instance : Coe (IntegralLattice n k) (EuclideanLattice n k) := ⟨IntegralLattice.toEuclideanLattice⟩

instance (L : IntegralLattice n k) : IsIntegral (L : EuclideanLattice n k) := L.integral

theorem isIntegral_iff_basis_integral (L : EuclideanLattice n k) :
  IsIntegral L ↔ ∀ j, L.basis.cols j ∈ ZnSubmodule n := by
  constructor;
  · -- If the lattice is integral, then the carrier is a subset of ZnSubmodule n.
    intro h_integral j
    have h_basis_in_carrier : L.basis.cols j ∈ L.carrier := by
      exact Submodule.subset_span ( Set.mem_range_self j ) |> fun h => L.carrier_eq.symm ▸ h;
    exact h_integral.subset_int h_basis_in_carrier;
  · intro h_integral
    have h_span : Submodule.span ℤ (Set.range L.basis.cols) ≤ ZnSubmodule n := by
      exact Submodule.span_le.mpr ( Set.range_subset_iff.mpr h_integral );
    exact ⟨ fun v hv => h_span <| by simpa [ L.carrier_eq ] using hv ⟩

/-- An integral basis generates an Integral Lattice -/
def IntegralLatticeBasis.toLattice (B : IntegralLatticeBasis n k) : IntegralLattice n k :=
  { basis := B.toRealBasis
    integral := by
      rw [isIntegral_iff_basis_integral]
      intro j
      simp
      -- Since the j-th column of B is an integer vector, it can be written as a linear combination of the standard basis vectors with integer coefficients.
      have h_col_int : ∃ (c : Fin n → ℤ), B.toRealBasis.cols j = ∑ i, c i • stdBasis i := by
        use fun i => B.matrix i j;
        ext i; simp +decide [ stdBasis ] ;
        rw [ Finset.sum_apply, Finset.sum_eq_single i ] <;> aesop;
      exact h_col_int.elim fun c hc => hc.symm ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_range_self _ ) )
  }

/-- Convert a EuclideanLattice with a proof of integrality into an IntegralLattice. -/
def toIntegralLattice (L : EuclideanLattice n k) (h : IsIntegral L) : IntegralLattice n k :=
  { toEuclideanLattice := L
    integral := h }

/-- We can extract an integral basis from an IntegralLattice. -/
noncomputable def getIntegralBasis (L : IntegralLattice n k) : IntegralLatticeBasis n k :=
  by
    classical
    -- Extract integer coordinates for each basis vector using integrality of the lattice.
    have h_integral :
        ∀ j, ∃ z : Fin n → ℤ, ∀ i : Fin n, (L.basis.cols j : 𝓔 n) i = (z i : ℝ) := by
      have hL : IsIntegral (L : EuclideanLattice n k) := inferInstance
      have h := (isIntegral_iff_vec_integral (L : EuclideanLattice n k)).1 hL
      intro j
      have hmem : (L.basis.cols j : 𝓔 n) ∈ (L : EuclideanLattice n k) := by
        exact EuclideanLattice.basis_mem (L : EuclideanLattice n k) j
      exact h (L.basis.cols j) (by simpa [EuclideanLattice.mem_def] using hmem)
    refine
      { matrix := fun i j => (Classical.choose (h_integral j)) i
        le_dim := L.basis.le_dim
        li := ?_ }
    -- The chosen integer columns recover the original real basis columns.
    have h_cols_eq :
        (fun j => piToEuc (fun i => ((Classical.choose (h_integral j)) i : ℝ))) =
          fun j => L.basis.cols j := by
      funext j
      apply LatticeCrypto.Utils.Vec.eucToPi.injective
      funext i
      have hz := (Classical.choose_spec (h_integral j)) i
      have hz' : (Classical.choose (h_integral j) i : ℝ) = (L.basis.cols j : 𝓔 n) i := by
        simp [hz]
      have h_euc : (LatticeCrypto.Utils.Vec.eucToPi (L.basis.cols j)) i = (L.basis.cols j : 𝓔 n) i := rfl
      simpa [LatticeCrypto.Utils.Vec.piToEuc_apply] using hz'.trans h_euc.symm
    have h_li_real : LinearIndependent ℝ (fun j => L.basis.cols j) := L.basis.li
    simpa [h_cols_eq] using h_li_real

/-- The integral basis obtained from an IntegralLattice indeed spans the original lattice. -/
theorem getIntegralBasis_toLattice (L : IntegralLattice n k) :
    (getIntegralBasis L).toLattice = L := by
  classical
  cases L with
  | mk L hL =>
    -- First show the extracted real basis agrees with the original basis.
    have h_basis_fun : (getIntegralBasis ⟨L, hL⟩).toRealBasis.basis = L.basis.basis := by
      funext j
      apply LatticeCrypto.Utils.Vec.eucToPi.injective
      funext i
      -- Unfold the definition to expose the chosen integer coordinates.
      change (getIntegralBasis ⟨L, hL⟩).toRealBasis.basis j i = (L.basis.basis j) i
      have h_integral :
          ∀ j, ∃ z : Fin n → ℤ, ∀ i : Fin n, (L.basis.basis j : 𝓔 n) i = (z i : ℝ) := by
        have h := (isIntegral_iff_vec_integral (L : EuclideanLattice n k)).1 hL
        intro j
        have hmem : (L.basis.basis j : 𝓔 n) ∈ (L : EuclideanLattice n k) := by
          exact EuclideanLattice.basis_mem (L : EuclideanLattice n k) j
        exact h (L.basis.basis j) (by simpa [EuclideanLattice.mem_def] using hmem)
      have hz := (Classical.choose_spec (h_integral j)) i
      simpa [getIntegralBasis, IntegralLatticeBasis.toRealBasis, h_integral] using hz.symm
    have h_basis : (getIntegralBasis ⟨L, hL⟩).toRealBasis = L.basis := by
      exact LatticeBasis.ext h_basis_fun
    have h_euc : ((getIntegralBasis ⟨L, hL⟩).toLattice : EuclideanLattice n k) = (L.basis).toLattice := by
      simpa using congrArg LatticeBasis.toLattice h_basis
    have h_euc' : (L : EuclideanLattice n k) = (L.basis).toLattice :=
      EuclideanLattice.eq_basis_toLattice (L : EuclideanLattice n k)
    have h_euc_final : (getIntegralBasis ⟨L, hL⟩).toLattice.toEuclideanLattice = L := by
      simpa using h_euc.trans h_euc'.symm
    -- Lift the equality of Euclidean lattices to Integral lattices using proof irrelevance.
    have h_ext :
        ∀ {L1 L2 : IntegralLattice n k},
          L1.toEuclideanLattice = L2.toEuclideanLattice → L1 = L2 := by
      intro L1 L2 h
      cases L1 with
      | mk L1 h1 =>
        cases L2 with
        | mk L2 h2 =>
          cases h
          have : h1 = h2 := Subsingleton.elim _ _
          cases this
          rfl
    apply h_ext
    simpa using h_euc_final

end Integral

end LatticeCrypto.Foundations.Lattice
