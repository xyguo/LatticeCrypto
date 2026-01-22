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

/-- Linear equivalence between basis functions and column matrices.
    Each basis vector becomes a column of the matrix. -/
def eucBasisToMatrixₗ {k : ℕ+} : (Fin k → 𝓔 n) ≃ₗ[ℝ] Matrix (Fin n) (Fin k) ℝ where
  toFun B := fun row col => B col row
  map_add' B₁ B₂ := by ext row col; simp [Pi.add_apply]
  map_smul' c B := by ext row col; simp [Pi.smul_apply]
  invFun M := fun col row => M row col
  left_inv B := by ext col row; rfl
  right_inv M := by ext row col; rfl

/-- Convert basis function to matrix (each column is a basis vector) -/
abbrev eucBasisToMatrix {k : ℕ+} : (Fin k → 𝓔 n) → Matrix (Fin n) (Fin k) ℝ :=
  eucBasisToMatrixₗ

/-- Convert matrix back to basis function (extract columns as vectors) -/
abbrev matrixToEucBasis {k : ℕ+} : Matrix (Fin n) (Fin k) ℝ → (Fin k → 𝓔 n) :=
  eucBasisToMatrixₗ.symm

@[simp] lemma eucBasisToMatrix_apply {k : ℕ+} (B : Fin k → 𝓔 n) (row : Fin n) (col : Fin k) :
  eucBasisToMatrix B row col = B col row := rfl

@[simp] lemma matrixToEucBasis_apply {k : ℕ+} (M : Matrix (Fin n) (Fin k) ℝ) (col : Fin k) (row : Fin n) :
  matrixToEucBasis M col row = M row col := rfl

@[simp] lemma matrixToEucBasis_eucBasisToMatrix {k : ℕ+} (B : Fin k → 𝓔 n) :
  matrixToEucBasis (eucBasisToMatrix B) = B := by
  ext col row; rfl

@[simp] lemma eucBasisToMatrix_matrixToEucBasis {k : ℕ+} (M : Matrix (Fin n) (Fin k) ℝ) :
  eucBasisToMatrix (matrixToEucBasis M) = M := by
  ext row col; rfl

end

end LatticeCrypto.Utils.Vec
