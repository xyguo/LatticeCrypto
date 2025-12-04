import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Utils.Geometry

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.CompleteLattice.Defs

open scoped ENNReal NNReal Pointwise
open MeasureTheory
open RealInnerProductSpace
open Classical
open LatticeCrypto.Utils.Geometry

namespace LatticeCrypto.Foundations.Lattice

variable {n : ℕ+}

/-!
# Successive Minima definitions

This file defines the successive minima of a geometric lattice and some basic properties they satisfy.

## Main Definitions

* `GeometricLattice.successiveMinima` - The i-th successive minimum λᵢ(L)
* `GeometricLattice.shortestVectorLength` - The length of the shortest non-zero vector λ₁(L)

## References

* [Peikert, *Lecture Notes: Lattices in Cryptography*, 2022]
* [Regev, *Lecture Notes: Lattices in Computer Science*, 2004]
* [Olds-Lax-Davidoff, *The Geometry of Numbers*, 2001]
-/

noncomputable section

/-!
## Successive Minima
-/

/-- The set of non-zero lattice vectors. -/
def GeometricLattice.nonzeroVectors (L : GeometricLattice n n) : Set (𝔼 n) :=
  { v | v ∈ L ∧ v ≠ 0 }

/-- The set of lattice vectors with norm at most r. -/
def GeometricLattice.ballIntersect (L : GeometricLattice n n) (r : ℝ) : Set (𝔼 n) :=
  { v | v ∈ L ∧ ‖v‖ ≤ r }

/-- The set of non-zero lattice vectors with norm at most r. -/
def GeometricLattice.nonzeroBallIntersect (L : GeometricLattice n n) (r : ℝ) : Set (𝔼 n) :=
  { v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r }

/-
Helper lemma: Any non-empty subset of the norms of non-zero lattice vectors has a minimum element.
-/
lemma exists_min_norm_subset (L : GeometricLattice n n) (S : Set ℝ)
    (h_subset : S ⊆ { ‖v‖ | v ∈ L.nonzeroVectors })
    (h_nonempty : S.Nonempty) :
    ∃ m ∈ S, ∀ s ∈ S, m ≤ s := by
      -- Let x be an element of S. Consider the intersection of S with [0, x]. This subset consists of norms of lattice vectors of length at most x.
      obtain ⟨x, hx⟩ : ∃ x ∈ S, True := by
        exact ⟨ _, h_nonempty.choose_spec, trivial ⟩
      set T := S ∩ Set.Icc 0 x with hT_def
      have hT_finite : T.Finite := by
        -- Since the lattice intersection with any ball is finite, the set of such norms is finite.
        have hT_finite : Set.Finite {v : 𝔼 n | v ∈ L.nonzeroVectors ∧ ‖v‖ ≤ x} := by
          have hT_finite : Set.Finite (L.ballIntersect x) := by
            -- Apply the fact that the intersection of a discrete set with a closed ball is finite.
            apply L.finite_intersection_closedBall x
          generalize_proofs at *; (
          exact hT_finite.subset fun v hv => ⟨ hv.1.1, hv.2 ⟩);
        exact Set.Finite.subset ( hT_finite.image fun v => ‖v‖ ) fun y hy => by rcases h_subset hy.1 with ⟨ v, hv₁, rfl ⟩ ; aesop;
      have hT_nonempty : T.Nonempty := by
        exact ⟨ x, hx.1, ⟨ by obtain ⟨ v, hv₁, hv₂ ⟩ := h_subset hx.1; exact hv₂.symm ▸ norm_nonneg _, le_rfl ⟩ ⟩
      obtain ⟨m, hm⟩ : ∃ m ∈ T, ∀ t ∈ T, m ≤ t := by
        exact ⟨ Finset.min' ( Set.Finite.toFinset hT_finite ) ( Finset.nonempty_of_ne_empty <| by aesop ), hT_finite.mem_toFinset.mp <| Finset.min'_mem _ _, fun t ht => Finset.min'_le _ _ <| hT_finite.mem_toFinset.mpr ht ⟩
      use m
      aesop;
      -- Since $s \in S$ and $S \subseteq \{ \|v\| \mid v \in L, v \neq 0 \}$, we have $0 \leq s$.
      have hs_nonneg : 0 ≤ s := by
        obtain ⟨ v, hv₁, hv₂ ⟩ := h_subset a; linarith [ norm_nonneg v ] ;
      exact if hs_le_x : s ≤ x then right s a hs_nonneg hs_le_x else by linarith [ right x hx ( by linarith ) ( by linarith ) ] ;


/-- A lattice has a shortest non-zero vector (discreteness implies this infimum is attained). -/
theorem GeometricLattice.exists_shortest_vector (L : GeometricLattice n n) :
    ∃ v ∈ L.nonzeroVectors, ∀ w ∈ L.nonzeroVectors, ‖v‖ ≤ ‖w‖ := by
  -- Discreteness means there exists ε > 0 such that B(0, ε) ∩ L = {0}
  have hdiscrete := discreteTopology_iff_isOpen_singleton_zero.mp L.discrete
  obtain ⟨t, ht_open, ht_preimage⟩ := hdiscrete
  have h0_mem : (0 : L.carrier) ∈ Subtype.val ⁻¹' t := by rw [ht_preimage]; exact Set.mem_singleton _
  have ht_open' : IsOpen t := ht_open
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp ht_open' (0 : 𝔼 n) h0_mem
  have hε_discrete : ∀ v : L.carrier, ‖(v : 𝔼 n)‖ < ε → v = 0 := fun v hv => by
    have : (v : 𝔼 n) ∈ t := hε_ball (by simp [dist_zero_right, hv])
    have : v ∈ Subtype.val ⁻¹' t := this
    rw [ht_preimage] at this
    exact this

  -- nonzeroVectors is nonempty (any basis vector works)
  have hne : L.nonzeroVectors.Nonempty := by
    use L.basis.cols ⟨0, n.pos⟩
    refine ⟨L.basis_mem ⟨0, n.pos⟩, ?_⟩
    intro h
    have hli := L.basis.li
    rw [Fintype.linearIndependent_iff] at hli
    have := hli (fun i => if i = ⟨0, n.pos⟩ then 1 else 0) ?_ ⟨0, n.pos⟩
    · simp at this
    · aesop

  -- Let λ = inf { ‖v‖ : v ∈ nonzeroVectors }
  let lambda := sInf { ‖v‖ | v ∈ L.nonzeroVectors }

  -- λ ≥ ε > 0 (no non-zero vectors in B(0, ε))
  have h_lambda_pos : ε ≤ lambda := by
    apply le_csInf (hne.image _)
    intro r ⟨v, hv, hvr⟩
    rw [← hvr]
    by_contra h
    push_neg at h
    have hv_in_ball : v ∈ Metric.ball (0 : 𝔼 n) ε := by
      simp [Metric.mem_ball, dist_zero_right, h]
    have hv_norm : ‖(⟨v, hv.1⟩ : L.carrier)‖ < ε := by
      aesop
    have := hε_discrete ⟨v, hv.1⟩ hv_norm
    exact hv.2 (Subtype.ext_iff.mp this)

  -- Pick any v₀ ∈ nonzeroVectors, then search in the compact set B(0, ‖v₀‖) ∩ L \ {0}
  obtain ⟨v₀, hv₀⟩ := hne

  -- The closed ball intersected with lattice minus origin is finite
  let ball₀ := { v ∈ L.carrier | v ≠ 0 ∧ ‖v‖ ≤ ‖v₀‖ }
  have hfinite : Set.Finite ball₀ := by
   -- Apply the hypothesis `finite_intersection_closedBall` with `r = ‖v₀‖`.
   have h_finite : Set.Finite {v ∈ L.carrier | ‖v‖ ≤ ‖v₀‖} := by
     -- Apply the hypothesis `finite_intersection_closedBall` with `r = ‖v₀‖` to conclude that the set is finite.
     apply GeometricLattice.finite_intersection_closedBall L ‖v₀‖;
   -- Since ball₀ is a subset of the finite set {v ∈ L.carrier | ‖v‖ ≤ ‖v₀‖}, it must also be finite.
   apply Set.Finite.subset h_finite; intro v hv; exact ⟨hv.left, hv.right.right⟩

  -- This set is nonempty
  have hnonempty : { v ∈ L.carrier | v ≠ 0 ∧ ‖v‖ ≤ ‖v₀‖ }.Nonempty := by
    use v₀
    exact ⟨hv₀.1, hv₀.2, le_refl _⟩

  -- A finite nonempty set has a minimum element (by norm)
  obtain ⟨v, ⟨hv_mem, hv_ne, hv_bound⟩, hv_min⟩ :=
    hfinite.exists_minimalFor (fun x : (𝔼 n) => ‖x‖) ball₀ hnonempty

  -- v is the shortest vector
  use v
  refine ⟨⟨hv_mem, hv_ne⟩, ?_⟩
  intro w ⟨hw_mem, hw_ne⟩
  by_cases h : ‖w‖ ≤ ‖v₀‖
  · -- w is in our finite set, use minimality
    have hw_in : w ∈ { v ∈ L.carrier | v ≠ 0 ∧ ‖v‖ ≤ ‖v₀‖ } := ⟨hw_mem, hw_ne, h⟩
    by_cases hle : ‖w‖ ≤ ‖v‖
    · exact hv_min hw_in hle
    · push_neg at hle; exact le_of_lt hle
  · -- w is outside the ball, so ‖v‖ ≤ ‖v₀‖ < ‖w‖
    push_neg at h
    exact le_of_lt (calc ‖v‖ ≤ ‖v₀‖ := hv_bound
         _ < ‖w‖ := h)

/-- The length of the shortest non-zero vector in the lattice (first successive minimum). -/
noncomputable def GeometricLattice.shortestVectorLength (L : GeometricLattice n n) : ℝ :=
  iInf (fun v : L.nonzeroVectors => ‖(v : 𝔼 n)‖)

/-- Alternative definition: λ₁(L) = inf { ‖v‖ : v ∈ L, v ≠ 0 } -/
theorem GeometricLattice.shortestVectorLength_eq (L : GeometricLattice n n) :
    L.shortestVectorLength = sInf { r | ∃ v ∈ L.nonzeroVectors, ‖v‖ = r } := by
  simp only [shortestVectorLength]
  -- Both are infima over the same set of values
  apply le_antisymm
  · -- iInf ≤ sInf
    apply le_csInf
    · -- The set is nonempty
      obtain ⟨v, hv⟩ := L.exists_shortest_vector
      exact ⟨‖v‖, v, hv.1, rfl⟩
    · -- If $b$ is in the set, then there exists some $v \in L.nonzeroVectors$ such that $\|v\| = b$.
      intro b hb
      obtain ⟨v, hv⟩ := hb;
      -- Since $v \in L.nonzeroVectors$ and $\|v\| = b$, we have $b \in \{ \|v\| \mid v \in L.nonzeroVectors \}$.
      have h_b_in_set : b ∈ Set.image (fun v : L.nonzeroVectors => ‖(v : 𝔼 n)‖) Set.univ := by
        aesop;
      simp +zetaDelta at *;
      obtain ⟨ a, ha₁, ha₂ ⟩ := h_b_in_set; exact le_trans ( ciInf_le ⟨ 0, Set.forall_mem_range.mpr fun x => norm_nonneg _ ⟩ ⟨ a, ha₁ ⟩ ) ( by simp +decide [ ha₂ ] ) ;
  · -- sInf ≤ iInf
    apply csInf_le
    · -- Bounded below by 0
      exact ⟨0, fun r ⟨v, _, hvr⟩ => hvr ▸ norm_nonneg v⟩
    · -- The infimum value is in the set
      obtain ⟨v, hv, hv_min⟩ := L.exists_shortest_vector
      -- Since the infimum is achieved by some vector in L.nonzeroVectors, we can conclude that there exists a vector v in L.nonzeroVectors such that ‖v‖ is the infimum.
      use v; aesop;
      -- Since $v$ is in the set and for any $w$ in the set, $\|v\| \leq \|w\|$, the infimum must be at least $\|v\|$.
      have h_inf_ge : ⨅ (v : L.nonzeroVectors), ‖(v : 𝔼 n)‖ ≥ ‖v‖ := by
        -- Apply the fact that the infimum is the greatest lower bound.
        apply le_csInf;
        · exact ⟨ _, ⟨ ⟨ v, hv ⟩, rfl ⟩ ⟩;
        · aesop;
      exact le_antisymm h_inf_ge <| ciInf_le_of_le ⟨ 0, Set.forall_mem_range.mpr fun _ => norm_nonneg _ ⟩ ⟨ v, hv ⟩ <| by aesop;

/-- The shortest vector length is positive. -/
theorem GeometricLattice.shortestVectorLength_pos (L : GeometricLattice n n) :
    0 < L.shortestVectorLength := by
  -- Since the lattice is discrete, there exists a shortest non-zero vector. Let's call this vector v. Then ‖v‖ is positive.
  obtain ⟨v, hv⟩ : ∃ v : L.nonzeroVectors, ∀ w : L.nonzeroVectors, ‖(v : 𝔼 n)‖ ≤ ‖(w : 𝔼 n)‖ := by
    have := L.exists_shortest_vector;
    exact ⟨ ⟨ this.choose, this.choose_spec.1 ⟩, fun w => this.choose_spec.2 _ w.2 ⟩;
  exact lt_of_lt_of_le ( norm_pos_iff.mpr v.2.2 ) ( le_csInf ⟨ _, Set.mem_range_self v ⟩ <| Set.forall_mem_range.mpr hv )

/-- Any lattice point in the open ball of radius λ₀ is the origin. -/
lemma GeometricLattice.lattice_point_in_lambda_zero_ball_is_zero (L : GeometricLattice n n)
    (v : 𝔼 n) (hv : v ∈ L) (hr : ‖v‖ < L.shortestVectorLength) :
    v = 0 := by
  by_contra hne
  -- v is a non-zero lattice vector with ‖v‖ < λ₁, contradicting definition of λ₁
  have hv_nonzero : v ∈ L.nonzeroVectors := ⟨hv, hne⟩
  have := ciInf_le (⟨0, fun x ⟨w, hw⟩ => hw ▸ norm_nonneg _⟩ : BddBelow (Set.range fun v : L.nonzeroVectors => ‖(v : 𝔼 n)‖)) ⟨v, hv_nonzero⟩
  convert hr.not_ge _;
  convert this using 1


/--
  The i-th successive minimum λᵢ(L) is the smallest r such that
  the ball of radius r contains i linearly independent lattice vectors.

  Formally: λᵢ(L) = inf { r > 0 : dim(span_ℝ(L ∩ B(0,r))) ≥ i }
-/
noncomputable def GeometricLattice.successiveMinima (L : GeometricLattice n n) (i : Fin n) : ℝ :=
  sInf { r : ℝ | 0 < r ∧
    ∃ (S : Finset (𝔼 n)),
      S.card = i.val + 1 ∧
      (∀ v ∈ S, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r) ∧
      LinearIndependent ℝ (fun v : S => (v : 𝔼 n)) }

notation "λ_[" i "]" => GeometricLattice.successiveMinima · i

theorem GeometricLattice.exists_successiveMinima (L : GeometricLattice n n) (i : Fin n) :
  ∃ (r : ℝ), 0 < r ∧ ∃ (S : Finset (𝔼 n)),
      S.card = i.val + 1 ∧
      (∀ v ∈ S, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r) ∧
      LinearIndependent ℝ (fun v : S => (v : 𝔼 n)) := by
  -- Choose the first i.val+1 basis vectors
  let idx : Finset (Fin n) := (Finset.univ.filter (fun j : Fin n => j.val ≤ i.val))
  have hcard : idx.card = i.val + 1 := by
    -- size of initial segment {0,1,...,i.val}
    simp +zetaDelta at *;
    rw [ show Finset.filter ( fun j => j ≤ i ) Finset.univ = Finset.Iic i by ext; simp +decide ] ; aesop
  let S : Finset (𝔼 n) := idx.image fun j => (L.basis.cols j : 𝔼 n)
  -- Define r as the maximum norm of these chosen basis vectors
  have hnonempty : S.Nonempty := by
    -- since i.val+1 ≥ 1, there is at least one element
    -- Since idx is nonempty, we can pick any element from idx and show that its image under the cols function is in S.
    have hidx_nonempty : idx.Nonempty := by
      -- Since $i$ is a Fin $n$, its value is between $0$ and $n-1$. Therefore, $i$ itself is in $idx$.
      use i; simp [idx];
    -- Since idx is nonempty, we can pick any element from idx and show that its image under the cols function is in S. Therefore, S is nonempty.
    obtain ⟨j, hj⟩ := hidx_nonempty;
    use L.basis.cols j;
    aesop
  let r : ℝ := S.sup' hnonempty (fun v => ‖v‖)
  have hr_pos : 0 < r := by
    -- norms of nonzero basis vectors are positive
    -- Since S is nonempty and consists of non-zero vectors, the supremum of their norms is positive.
    have hr_pos : ∀ v ∈ S, 0 < ‖v‖ := by
      -- Since the basis vectors are non-zero, their norms are positive.
      intros v hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      have h_basis_nonzero : L.basis.cols j ≠ 0 := by
        have := L.basis.li.ne_zero j; aesop;
      exact norm_pos_iff.mpr h_basis_nonzero;
    norm_num +zetaDelta at *;
    exact ⟨ 0, Nat.zero_le _, hr_pos 0 bot_le ⟩
  have h_mem : ∀ v ∈ S, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨j, hj_idx, rfl⟩
    have hjL : (L.basis.cols j : 𝔼 n) ∈ L := L.basis_mem j
    have hj_ne : (L.basis.cols j : 𝔼 n) ≠ 0 := by
      -- basis vectors are nonzero
      have := L.basis.li; aesop;
      -- Since the basis is linearly independent, having a zero vector would contradict that.
      apply this.ne_zero j; aesop
    have hj_le : ‖(L.basis.cols j : 𝔼 n)‖ ≤ r := by
      -- by definition of r = sup' over S
      exact Finset.le_sup' (fun v => ‖v‖) (by simpa [S, idx] using hv)
    exact ⟨hjL, hj_ne, hj_le⟩
  have h_li : LinearIndependent ℝ (fun v : S => (v : 𝔼 n)) := by
    -- a subset of a linearly independent family is linearly independent
    have h_basis_li : LinearIndependent ℝ (fun j : Fin n => (L.basis.cols j : 𝔼 n)) := L.basis.li
    -- use linear independence of image of a subset
    convert h_basis_li.comp _ _;
    rotate_left;
    use fun x => Classical.choose ( Finset.mem_image.mp x.2 );
    · intro x y hxy; have := Classical.choose_spec ( Finset.mem_image.mp x.2 ) ; have := Classical.choose_spec ( Finset.mem_image.mp y.2 ) ; aesop;
    · ext ⟨ x, hx ⟩ ; have := Classical.choose_spec ( Finset.mem_image.mp hx ) ; aesop;
  have hS_card : S.card = i.val + 1 := by
    rw [Finset.card_image_of_injective]
    · exact hcard
    · intro x y hxy
      exact L.basis.li.injective hxy
  refine ⟨r, hr_pos, S, hS_card, h_mem, h_li⟩


/-- The first successive minimum equals the shortest vector length. -/
theorem GeometricLattice.successiveMinima_one (L : GeometricLattice n n) :
    L.successiveMinima ⟨0, n.pos⟩ = L.shortestVectorLength := by
  simp only [successiveMinima, shortestVectorLength]
  apply le_antisymm
  · -- successiveMinima ≤ shortestVectorLength
    apply csInf_le
    · -- Bounded below
      exact ⟨0, fun r ⟨hr, _⟩ => le_of_lt hr⟩
    · -- shortestVectorLength is in the set
      obtain ⟨v, hv, hv_min⟩ := L.exists_shortest_vector
      refine ⟨L.shortestVectorLength_pos, {v}, ?_, ?_, ?_⟩
      · simp
      · intro w hw
        simp at hw
        rw [hw]
        refine ⟨hv.1, hv.2, ?_⟩
        -- Since $v$ is in the set of non-zero vectors, by definition of infimum, the infimum is less than or equal to $v$'s norm.
        apply le_csInf;
        · exact ⟨ _, ⟨ ⟨ v, hv ⟩, rfl ⟩ ⟩;
        · grind
      · simp
        exact hv.2
  · -- shortestVectorLength ≤ successiveMinima
    apply le_csInf
    · -- The set is nonempty
      obtain ⟨v, hv, _⟩ := L.exists_shortest_vector
      exact ⟨‖v‖, norm_pos_iff.mpr hv.2, {v}, by simp, fun w hw => by simp at hw; rw [hw]; exact ⟨hv.1, hv.2, le_refl _⟩, by simp [hv.2]⟩
    · intro r ⟨_, S, hS_card, hS_props, _⟩
      simp at hS_card
      obtain ⟨v, hv_mem⟩ := Finset.card_pos.mp (by rw [hS_card]; exact Nat.one_pos)
      have ⟨hv_L, hv_ne, hv_norm⟩ := hS_props v hv_mem
      refine' le_trans ( ciInf_le _ _ ) _;
      -- The norm is always non-negative, so 0 is a lower bound for the range.
      have h_nonneg : ∀ v : L.nonzeroVectors, 0 ≤ ‖(v : 𝔼 n)‖ := by
        exact fun v => norm_nonneg _;
      exact ⟨ 0, Set.forall_mem_range.mpr h_nonneg ⟩;
      exacts [ ⟨ v, hv_L, hv_ne ⟩, hv_norm ]

/-- Successive minima are non-decreasing: λᵢ ≤ λⱼ for i ≤ j. -/
theorem GeometricLattice.successiveMinima_mono (L : GeometricLattice n n)
    {i j : Fin n} (hij : i ≤ j) :
    L.successiveMinima i ≤ L.successiveMinima j := by
  apply csInf_le_csInf
  · -- Lower bound exists for λᵢ
    exact ⟨0, fun r ⟨hr, _⟩ => le_of_lt hr⟩
  · -- Since $L$ is a geometric lattice, it has a basis $B$ with $n$ elements.
    obtain ⟨B, hB⟩ : ∃ B : SquareLatticeBasis n, L = B.toLattice := by
      cases L ; aesop;
    -- Let $r$ be a positive real number such that $r \geq \max_{i} \|B_i\|$.
    obtain ⟨r, hr⟩ : ∃ r : ℝ, 0 < r ∧ ∀ i : Fin n, ‖B.cols i‖ ≤ r := by
      exact ⟨ ∑ i : Fin n, ‖B.cols i‖ + 1, add_pos_of_nonneg_of_pos ( Finset.sum_nonneg fun _ _ => norm_nonneg _ ) zero_lt_one, fun i => by linarith [ Finset.single_le_sum ( fun i _ => norm_nonneg ( B.cols i ) ) ( Finset.mem_univ i ) ] ⟩;
    refine' ⟨ r, hr.1, Finset.image ( fun i => B.cols i ) ( Finset.Iic j ), _, _, _ ⟩ <;> aesop;
    · rw [ Finset.card_image_of_injective _ fun i j hij => by simpa [ Fin.ext_iff ] using B.li.injective hij, Finset.card_eq_sum_ones ] ; aesop;
    · exact Submodule.subset_span ( Set.mem_range_self w );
    · exact absurd a ( by exact ne_of_apply_ne ( fun x => ‖x‖ ) ( by simpa using B.li.ne_zero w ) );
    · have := B.li;
      -- Since the basis vectors are linearly independent, any subset of them is also linearly independent.
      have h_subset : LinearIndependent ℝ (fun i : Fin n => B.cols i) := by
        convert this using 1;
      convert h_subset.comp _ _;
      rotate_left;
      use fun x => Classical.choose ( Finset.mem_image.mp x.2 ) |> fun i => i;
      · intro x y; have := Classical.choose_spec ( Finset.mem_image.mp x.2 ) ; have := Classical.choose_spec ( Finset.mem_image.mp y.2 ) ; aesop;
      · ext ⟨ x, hx ⟩ ; have := Classical.choose_spec ( Finset.mem_image.mp hx ) ; aesop;
  · -- Any r in the set for λⱼ is also in the set for λᵢ
    intro r ⟨hr_pos, S, hS_card, hS_props, hS_li⟩
    refine ⟨hr_pos, ?_⟩
    -- Take a subset of S of size i+1
    have hi_le : i.val + 1 ≤ S.card := by
      rw [hS_card]
      linarith [ show ( i : ℕ ) ≤ j from hij ]
    obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hi_le
    use T
    refine ⟨hT_card, ?_, ?_⟩
    · intro v hv
      exact hS_props v (hT_sub hv)
    · -- Since T is a subset of S and S is linearly independent, T must also be linearly independent.
      have hT_li : LinearIndependent ℝ (fun v : S => (v : 𝔼 n)) := by
        -- Since $T$ is a subset of $S$, and $S$ is linearly independent, any subset of $S$ is also linearly independent. Therefore, the function from $T$ to the vector space is linearly independent.
        apply hS_li;
      convert hT_li.comp _ _;
      rotate_left;
      exacts [ fun x => ⟨ x, hT_sub x.2 ⟩, fun x y hxy => by simpa [ Subtype.ext_iff ] using hxy, funext fun x => rfl ]

/-- All successive minima are positive. -/
theorem GeometricLattice.successiveMinima_pos (L : GeometricLattice n n) (i : Fin n) :
    0 < L.successiveMinima i := by
  -- λ₁ ≤ λᵢ and λ₁ > 0
  calc 0 < L.successiveMinima ⟨0, n.pos⟩ := by
           rw [successiveMinima_one]
           exact shortestVectorLength_pos L
       _ ≤ L.successiveMinima i := successiveMinima_mono L (Fin.zero_le i)

/-- All successive minima are finite (bounded above). -/
theorem GeometricLattice.successiveMinima_boundedAbove (L : GeometricLattice n n) (i : Fin n) :
    ∃ M : ℝ, L.successiveMinima i ≤ M := by
  -- Use the basis vectors: they are n linearly independent vectors
  -- M = max { ‖bⱼ‖ : j ∈ Fin n } works for all λᵢ
  let M := Finset.sup' Finset.univ Finset.univ_nonempty (fun j => ‖L.basis.cols j‖)
  use M
  apply csInf_le
  · exact ⟨0, fun r ⟨hr, _⟩ => le_of_lt hr⟩
  · refine ⟨?_, ?_⟩
    · -- M > 0
      have idx : Fin n := ⟨0, n.pos⟩
      apply lt_of_lt_of_le (norm_pos_iff.mpr _) (Finset.le_sup' (fun j => ‖L.basis.cols j‖) (Finset.mem_univ idx))
      intro h
      have hli := L.basis.li
      rw [Fintype.linearIndependent_iff] at hli
      have := hli (fun j => if j = idx then 1 else 0) ?_ idx
      · simp at this
      · aesop
    · -- Construct the finset of i+1 basis vectors
      use Finset.image ( fun j => L.basis.cols j ) ( Finset.Iic i ) ; aesop;
      · rw [ Finset.card_image_of_injective _ fun x y hxy => _ ] <;> aesop;
        have := L.basis.li; have := this.injective; aesop;
      · -- Since the basis vectors are in the lattice, we have L.basis.cols a ∈ L.
        apply L.carrier_eq.symm ▸ Submodule.subset_span (Set.mem_range_self a);
      · -- Since the basis is linearly independent, the only solution to the equation ∑ c_i * b_i = 0 is c_i = 0 for all i.
        have h_lin_ind : LinearIndependent ℝ (fun j : Fin n => L.basis.cols j) := by
          -- Since the basis is a Basis, it is linearly independent by definition.
          apply L.basis.li;
        exact h_lin_ind.ne_zero a a_2;
      · use a;
      · -- Since the basis is linearly independent, any subset of it is also linearly independent.
        have h_basis_lin_ind : LinearIndependent ℝ (fun j : Fin n => L.basis.cols j) := by
          -- Since the basis is linearly independent by definition, we can conclude the proof.
          apply L.basis.li;
        convert h_basis_lin_ind.comp _ _;
        rotate_left;
        use fun x => Classical.choose ( Finset.mem_image.mp x.2 ) |> fun j => j;
        · intro x y; have := Classical.choose_spec ( Finset.mem_image.mp x.2 ) ; have := Classical.choose_spec ( Finset.mem_image.mp y.2 ) ; aesop;
        · -- Since the image is exactly the set of basis vectors, and the chosen element is the one that was mapped to x, this should hold.
          funext x; exact (by
          have := Classical.choose_spec ( Finset.mem_image.mp x.2 ) ; aesop;)

/-- Helper -/
lemma LatticeCrypto.Foundations.Lattice.exists_min_norm_subset_proven {n : ℕ+} (L : GeometricLattice n n) (S : Set ℝ)
    (h_subset : S ⊆ { ‖v‖ | v ∈ L.nonzeroVectors })
    (h_nonempty : S.Nonempty) :
    ∃ m ∈ S, ∀ s ∈ S, m ≤ s := by
      exact exists_min_norm_subset L S h_subset h_nonempty

/-- The successive minima are achieved by lattice vectors. -/
theorem GeometricLattice.successiveMinima_attained (L : GeometricLattice n n) (i : Fin n) :
    ∃ v ∈ L.nonzeroVectors, ‖v‖ = L.successiveMinima i := by
  classical
  -- Abbreviate the defining set of λᵢ
  let A : Set ℝ :=
    { r : ℝ | 0 < r ∧
      ∃ (S : Finset (𝔼 n)),
        S.card = i.val + 1 ∧
        (∀ v ∈ S, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r) ∧
        LinearIndependent ℝ (fun v : S => (v : 𝔼 n)) }

  have hA_def :
      L.successiveMinima i = sInf A := rfl

  -- Define the "snapped" set of candidate radii: max norm inside the finite set S
  let B : Set ℝ :=
    { r : ℝ |
        ∃ (S : Finset (𝔼 n)) (v : 𝔼 n),
          v ∈ S ∧
          S.card = i.val + 1 ∧
          (∀ w ∈ S, w ∈ L ∧ w ≠ 0 ∧ ‖w‖ ≤ r) ∧
          LinearIndependent ℝ (fun w : S => (w : 𝔼 n)) ∧
          r = ‖v‖ ∧
          ∀ w ∈ S, ‖w‖ ≤ ‖v‖ }

  -- 1. B ⊆ A
  have hB_sub_A : B ⊆ A := by
    intro r hr
    rcases hr with ⟨S, v, hvS, hS_card, hS_props, hS_li, rfl, hmax⟩
    -- We know: ∀ w ∈ S, w ∈ L ∧ w ≠ 0 ∧ ‖w‖ ≤ ‖v‖
    -- and λᵢ is defined from sets like this; only need 0 < r.
    have hS_nonempty : S.Nonempty := ⟨v, hvS⟩
    -- v is nonzero, so ‖v‖ > 0
    have hv_ne : v ≠ 0 := (hS_props v hvS).2.1
    have h_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
    refine ⟨h_pos, ?_⟩
    refine ⟨S, hS_card, ?_, hS_li⟩
    intro w hw
    obtain ⟨hw_L, hw_ne, hw_le⟩ := hS_props w hw
    exact ⟨hw_L, hw_ne, hw_le⟩

  -- 2. For every r ∈ A, there is some b ∈ B with b ≤ r
  have hA_to_B : ∀ r ∈ A, ∃ b ∈ B, b ≤ r := by
    intro r hr
    rcases hr with ⟨hr_pos, S, hS_card, hS_props, hS_li⟩
    -- S.nonempty because card = i+1 > 0
    have hS_nonempty : S.Nonempty := by
      have : 0 < S.card := by
        simp [hS_card]
      exact Finset.card_pos.mp this

    -- Use sup' to pick a v achieving max norm in S
    obtain ⟨v, hvS, hv_eq⟩ :=
      Finset.exists_mem_eq_sup' hS_nonempty (fun w => ‖w‖)
    -- Define b := ‖v‖
    let b : ℝ := ‖v‖

    have hb_le_r : b ≤ r := by
      -- Every w in S has ‖w‖ ≤ r, so in particular the maximum does
      have := ((Finset.sup'_le_iff (f := fun w : (𝔼 n) => ‖w‖) (a := r) (s := S)) hS_nonempty).mpr ?h
      · simpa [b, hv_eq] using this
      . intro w hw
        exact (hS_props w hw).2.2  -- ‖w‖ ≤ r

    -- Show b ∈ B
    have hbB : b ∈ B := by
      refine ⟨S, v, hvS, hS_card, ?_, hS_li, rfl, ?_⟩
      · intro w hw
        have := hS_props w hw
        -- Since $b$ is the supremum of the norms of the elements in $S$, for any $w \in S$, we have $\|w\| \leq b$.
        have h_norm_le_b : ∀ w ∈ S, ‖w‖ ≤ b := by
          -- By definition of Finset.sup', since v is in S, for any w in S, ‖w‖ ≤ ‖v‖.
          intros w hw
          apply hv_eq ▸ Finset.le_sup' (fun w => ‖w‖) hw;
        exact ⟨ this.1, this.2.1, h_norm_le_b w hw ⟩
      · intro w hw
        -- show ‖w‖ ≤ ‖v‖ using max property
        have hw_le_sup : ‖w‖ ≤ S.sup' hS_nonempty (fun w => ‖w‖) :=
          Finset.le_sup' (f := fun w => ‖w‖) hw
        simpa [b, hv_eq] using hw_le_sup

    exact ⟨b, hbB, hb_le_r⟩

  -- 3. A and B have the same infimum
  have h_inf_eq : sInf A = sInf B := by
    -- (a) From B ⊆ A we get sInf A ≤ sInf B
    have h1 : sInf A ≤ sInf B := by
      -- Larger set → smaller inf, so subset B ⊆ A gives sInf A ≤ sInf B
      -- Larger set → smaller inf, so subset B ⊆ A gives sInf A ≤ sInf B
      apply_rules [ csInf_le_csInf ];
      · exact ⟨ 0, fun r hr => hr.1.le ⟩;
      · obtain ⟨ r, hr ⟩ := GeometricLattice.exists_successiveMinima L i;
        obtain ⟨ b, hb₁, hb₂ ⟩ := hA_to_B r ⟨ hr.1, hr.2 ⟩ ; exact ⟨ b, hb₁ ⟩

    -- (b) sInf B is a lower bound of A, hence ≤ sInf A
    have h2 : sInf B ≤ sInf A := by
      -- "sInf B is a lower bound of A"
      have h_lb : ∀ r ∈ A, sInf B ≤ r := by
        intro r hrA
        rcases hA_to_B r hrA with ⟨b, hbB, hb_le⟩
        have h_sInf_le_b : sInf B ≤ b := by
          exact csInf_le ⟨ 0, fun x hx => by obtain ⟨ S, v, hvS, hS_card, hS_cond, hS_lin, rfl, hv_norm ⟩ := hx; exact norm_nonneg _ ⟩ hbB
        exact le_trans h_sInf_le_b hb_le
      -- greatest lower bound property
      -- Apply the fact that if every element of A is greater than or equal to the infimum of B, then the infimum of A must be greater than or equal to the infimum of B.
      apply le_csInf;
      · -- By definition of $A$, there exists some $r \in A$.
        apply Classical.byContradiction
        intro hA_empty;
        exact hA_empty <| by obtain ⟨ r, hr ⟩ := exists_successiveMinima L i; exact ⟨ r, ⟨ hr.1, hr.2 ⟩ ⟩ ;
      · exact h_lb
    exact le_antisymm h1 h2

  -- 4. Nonemptiness of B and that B ⊆ {‖v‖ | v ∈ L.nonzeroVectors}
  have hB_nonempty : B.Nonempty := by
    -- from exists_successiveMinima we get some r ∈ A, then snap it down into B
    obtain ⟨r, hr_pos, S, hS_card, hS_props, hS_li⟩ := L.exists_successiveMinima i
    have : r ∈ A := by
      refine ⟨hr_pos, S, hS_card, hS_props, hS_li⟩
    rcases hA_to_B r this with ⟨b, hbB, hb_le⟩
    exact ⟨b, hbB⟩

  have hB_subset_norms : B ⊆ { ‖v‖ | v ∈ L.nonzeroVectors } := by
    intro r hrB
    rcases hrB with ⟨S, v, hvS, hS_card, hS_props, hS_li, rfl, hmax⟩
    -- v is nonzero lattice vector
    have hv_L : v ∈ L := (hS_props v hvS).1
    have hv_ne : v ≠ 0 := (hS_props v hvS).2.1
    refine ⟨v, ⟨hv_L, hv_ne⟩, rfl⟩

  -- 5. Use your "min norm in subset" lemma on B
  obtain ⟨m, hmB, hm_min⟩ :=
    LatticeCrypto.Foundations.Lattice.exists_min_norm_subset_proven
      L B hB_subset_norms hB_nonempty

  -- hm_min: ∀ s ∈ B, m ≤ s, so m is min of B; hence m = sInf B
  have hm_isInf : sInf B = m := by
    -- sInf B ≤ m because m ∈ B
    have h_le : sInf B ≤ m := by
      -- Since m is in B, by definition of infimum, we have sInf B ≤ m.
      apply csInf_le; exact (by
      exact ⟨ m, fun x hx => hm_min x hx ⟩); exact hmB
     -- and m ≤ sInf B because m is a lower bound of B
    have h_ge : m ≤ sInf B := by
      exact le_csInf hB_nonempty hm_min
    exact le_antisymm h_le h_ge

  -- 6. Glue everything together: λᵢ = m
-- λᵢ = sInf A = sInf B = m
  have h_lambda_eq_m : L.successiveMinima i = m := by
    have : sInf A = sInf B := h_inf_eq
    simp [hA_def, this, hm_isInf]

  -- Use the witness for m ∈ B to get v
  rcases hmB with ⟨S, v, hvS, hS_card, hS_props, hS_li, hm_eq, hmax⟩

  have hv_L : v ∈ L := (hS_props v hvS).1
  have hv_ne : v ≠ 0 := (hS_props v hvS).2.1

  refine ⟨v, ⟨hv_L, hv_ne⟩, ?_⟩
  -- r = ‖v‖ and λᵢ = m = ‖v‖
  simp [h_lambda_eq_m, hm_eq]

end

end LatticeCrypto.Foundations.Lattice
