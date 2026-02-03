import LatticeCrypto.Foundations.Lattice.Defs
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

/-- A predicate asserting that a GeometricLattice is integral. Mathematically, Λ ⊆ ℤⁿ. -/ class IsIntegral (L : GeometricLattice n k) : Prop where
  subset_int : L.carrier ≤ ZnSubmodule n

/-- A lattice is integral iff all lattice vectors have integer components. -/
theorem isIntegral_iff_vec_integral (L : GeometricLattice n k) :
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
structure IntegralLattice (n k : ℕ+) extends GeometricLattice n k where
  integral : IsIntegral toGeometricLattice

instance : Coe (IntegralLattice n k) (GeometricLattice n k) := ⟨IntegralLattice.toGeometricLattice⟩

instance (L : IntegralLattice n k) : IsIntegral (L : GeometricLattice n k) := L.integral

theorem isIntegral_iff_basis_integral (L : GeometricLattice n k) :
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

end Integral

end LatticeCrypto.Foundations.Lattice
