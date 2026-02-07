import LatticeCrypto.Foundations.Lattice.SuccessiveMinima
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Foundations.Lattice.Distance


/-!
Definitions of major hard problems in lattice-based cryptography, such as SVP, CVP, SIVP, BDD,
and their approximate/decision variants.
-/

namespace LatticeCrypto.Foundations

namespace Hardness

open scoped RealInnerProductSpace
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Foundations.Lattice

variable {n k : ℕ+}

noncomputable section defs

/-!
## SVP (Shortest Vector Problem)
-/

/-- An SVP instance is just a full-rank lattice. -/
structure SVPInstance (n : ℕ+) where
  L : EuclideanLattice n n

/-- Exact SVP solution: a nonzero lattice vector of minimum norm. -/
def SVPSolution (inst : SVPInstance n) (v : 𝓔 n) : Prop :=
  v ∈ inst.L ∧ v ≠ 0 ∧ ‖v‖ = inst.L.shortestVectorLength

/-- Approximate SVP solution with factor `γ ≥ 1`. -/
def approxSVPSolution (inst : SVPInstance n) (γ : ℝ) (v : 𝓔 n) : Prop :=
  v ∈ inst.L ∧ v ≠ 0 ∧ ‖v‖ ≤ γ * inst.L.shortestVectorLength

/-- GapSVP decision instance with radius `r`. -/
structure GapSVPInstance (n : ℕ+) where
  L : EuclideanLattice n n
  r : ℝ

/-- YES instances for GapSVP: $\lambda_1(L) \le r$. -/
def gapSVPYes (inst : GapSVPInstance n) : Prop :=
  inst.L.shortestVectorLength ≤ inst.r

/-- NO instances for GapSVP with factor `γ`: $\lambda_1(L) > γ \cdot r$. -/
def gapSVPNo (inst : GapSVPInstance n) (γ : ℝ) : Prop :=
  inst.L.shortestVectorLength > γ * inst.r

/-- The GapSVP promise. -/
def gapSVPPromise (inst : GapSVPInstance n) (γ : ℝ) : Prop :=
  gapSVPYes inst ∨ gapSVPNo inst γ

/-!
## CVP (Closest Vector Problem)
-/

/-- A CVP instance is a lattice and a target. -/
structure CVPInstance (n k : ℕ+) where
  L : EuclideanLattice n k
  t : 𝓔 n

/-- Exact CVP solution: a lattice vector at distance `distanceToLattice`. -/
def CVPSolution (inst : CVPInstance n k) (v : 𝓔 n) : Prop :=
  v ∈ inst.L ∧ ‖inst.t - v‖ = inst.L.distanceToLattice inst.t

/-- Approximate CVP solution with factor `γ`. -/
def approxCVPSolution (inst : CVPInstance n k) (γ : ℝ) (v : 𝓔 n) : Prop :=
  v ∈ inst.L ∧ ‖inst.t - v‖ ≤ γ * inst.L.distanceToLattice inst.t

/-- GapCVP decision instance with radius `r`. -/
structure GapCVPInstance (n k : ℕ+) where
  L : EuclideanLattice n k
  t : 𝓔 n
  r : ℝ

/-- YES instances for GapCVP: $\mathrm{dist}(t,L) \le r$. -/
def gapCVPYes (inst : GapCVPInstance n k) : Prop :=
  inst.L.distanceToLattice inst.t ≤ inst.r

/-- NO instances for GapCVP with factor `γ`: $\mathrm{dist}(t,L) > γ \cdot r$. -/
def gapCVPNo (inst : GapCVPInstance n k) (γ : ℝ) : Prop :=
  inst.L.distanceToLattice inst.t > γ * inst.r

/-- The GapCVP promise. -/
def gapCVPPromise (inst : GapCVPInstance n k) (γ : ℝ) : Prop :=
  gapCVPYes inst ∨ gapCVPNo inst γ

/-!
## SIVP (Shortest Independent Vectors Problem)
-/

/-- A SIVP instance is a full-rank lattice. -/
structure SIVPInstance (n : ℕ+) where
  L : EuclideanLattice n n

/-- Exact SIVP solution: `n` independent vectors of length at most $\lambda_n(L)$. -/
def SIVPSolution (inst : SIVPInstance n) (v : Fin n → 𝓔 n) : Prop :=
  LinearIndependent ℝ v ∧
  (∀ i, v i ∈ inst.L) ∧
  (∀ i, ‖v i‖ ≤ inst.L.succMinₙ)

/-- Approximate SIVP solution with factor `γ`. -/
def approxSIVPSolution (inst : SIVPInstance n) (γ : ℝ) (v : Fin n → 𝓔 n) : Prop :=
  LinearIndependent ℝ v ∧
  (∀ i, v i ∈ inst.L) ∧
  (∀ i, ‖v i‖ ≤ γ * inst.L.succMinₙ)

/-!
## BDD (Bounded Distance Decoding)
-/

/-- A BDD instance is a lattice, a target, and a decoding radius. -/
structure BDDInstance (n : ℕ+) where
  L : EuclideanLattice n n
  t : 𝓔 n
  r : ℝ

/-- BDD promise: target is within radius `r` and `r` is below $\lambda_1(L)/2$. -/
def BDDPromise (inst : BDDInstance n) : Prop :=
  inst.L.distanceToLattice inst.t ≤ inst.r ∧ inst.r < inst.L.shortestVectorLength / 2

/-- BDD solution: any lattice vector within radius `r`. -/
def BDDSolution (inst : BDDInstance n) (v : 𝓔 n) : Prop :=
  v ∈ inst.L ∧ ‖inst.t - v‖ ≤ inst.r

end defs

end Hardness

end LatticeCrypto.Foundations
