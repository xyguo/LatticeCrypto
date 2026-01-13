import Mathlib.Analysis.InnerProductSpace.PiL2  -- For EuclideanSpace

namespace LatticeCrypto.Utils.Vec

variable {n : ℕ+}

/-- Notation for n-dimensional Euclidean space over ℝ. -/
abbrev 𝓔 (n : ℕ+) := EuclideanSpace ℝ (Fin n)

noncomputable section

def stdBasis : Module.Basis (Fin n) ℝ (𝓔 n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

lemma toMatrix_on_stdBasis_eq_self (mb: Module.Basis (Fin n) ℝ (𝓔 n)) :
  stdBasis.toMatrix mb = Matrix.of (fun i j => mb j i) := by
 rfl

/-- Helper: Linear equivalence between EuclideanSpace ℝ (Fin n) and the function space (Fin n → ℝ). -/
def eucToPi : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv

def piToEuc : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv

@[simp] lemma piToEuc_apply (f : Fin n → ℝ) (i : Fin n) :
  (eucToPi (piToEuc f)) i = f i := by simp [piToEuc, eucToPi]

@[simp] lemma eucToPi_apply (x : EuclideanSpace ℝ (Fin n)) :
  piToEuc (eucToPi x) = x := by simp [piToEuc, eucToPi]


end

end LatticeCrypto.Utils.Vec
