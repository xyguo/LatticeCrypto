import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.LinearAlgebra
import LatticeCrypto.Utils.Vec

open scoped ENNReal NNReal Pointwise
open scoped Module
open scoped RealInnerProductSpace
open scoped Classical
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Utils.LinearAlgebra

namespace LatticeCrypto.Foundations.Lattice

variable {n : ℕ+}

/-!
# Successive Minima definitions

This file defines the successive minima of a geometric lattice and some basic properties they satisfy.

## Main Definitions

* `EuclideanLattice.successiveMinima` - The i-th successive minimum λᵢ(L)
* `EuclideanLattice.shortestVectorLength` - The length of the shortest non-zero vector λ₁(L)

## References

* [Peikert, *Lecture Notes: Lattices in Cryptography*, 2022]
* [Regev, *Lecture Notes: Lattices in Computer Science*, 2004]
* [Olds-Lax-Davidoff, *The Geometry of Numbers*, 2001]
-/

noncomputable section successive_minima_basics

/-!
## Successive Minima
-/

/-- The set of non-zero lattice vectors. -/
def EuclideanLattice.nonzeroVectors (L : EuclideanLattice n n) : Set (𝓔 n) :=
  { v | v ∈ L ∧ v ≠ 0 }

/-- The set of lattice vectors with norm at most r. -/
def EuclideanLattice.ballIntersect (L : EuclideanLattice n n) (r : ℝ) : Set (𝓔 n) :=
  { v | v ∈ L ∧ ‖v‖ ≤ r }

/-- The set of non-zero lattice vectors with norm at most r. -/
def EuclideanLattice.nonzeroBallIntersect (L : EuclideanLattice n n) (r : ℝ) : Set (𝓔 n) :=
  { v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r }

/-
Helper lemma: Any non-empty subset of the norms of non-zero lattice vectors has a minimum element.
-/
lemma exists_min_norm_subset (L : EuclideanLattice n n) (S : Set ℝ)
    (h_subset : S ⊆ { ‖v‖ | v ∈ L.nonzeroVectors })
    (h_nonempty : S.Nonempty) :
    ∃ m ∈ S, ∀ s ∈ S, m ≤ s := by
      -- Let x be an element of S. Consider the intersection of S with [0, x]. This subset consists of norms of lattice vectors of length at most x.
      obtain ⟨x, hx⟩ : ∃ x ∈ S, True := by
        exact ⟨ _, h_nonempty.choose_spec, trivial ⟩
      set T := S ∩ Set.Icc 0 x with hT_def
      have hT_finite : T.Finite := by
        -- Since the lattice intersection with any ball is finite, the set of such norms is finite.
        have hT_finite : Set.Finite {v : 𝓔 n | v ∈ L.nonzeroVectors ∧ ‖v‖ ≤ x} := by
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
theorem EuclideanLattice.exists_shortest_vector (L : EuclideanLattice n n) :
    ∃ v ∈ L.nonzeroVectors, ∀ w ∈ L.nonzeroVectors, ‖v‖ ≤ ‖w‖ := by
  -- Discreteness means there exists ε > 0 such that B(0, ε) ∩ L = {0}
  have hdiscrete := discreteTopology_iff_isOpen_singleton_zero.mp L.discrete
  obtain ⟨t, ht_open, ht_preimage⟩ := hdiscrete
  have h0_mem : (0 : L.carrier) ∈ Subtype.val ⁻¹' t := by rw [ht_preimage]; exact Set.mem_singleton _
  have ht_open' : IsOpen t := ht_open
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp ht_open' (0 : 𝓔 n) h0_mem
  have hε_discrete : ∀ v : L.carrier, ‖(v : 𝓔 n)‖ < ε → v = 0 := fun v hv => by
    have : (v : 𝓔 n) ∈ t := hε_ball (by simp [dist_zero_right, hv])
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
    have hv_in_ball : v ∈ Metric.ball (0 : 𝓔 n) ε := by
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
     apply EuclideanLattice.finite_intersection_closedBall L ‖v₀‖;
   -- Since ball₀ is a subset of the finite set {v ∈ L.carrier | ‖v‖ ≤ ‖v₀‖}, it must also be finite.
   apply Set.Finite.subset h_finite; intro v hv; exact ⟨hv.left, hv.right.right⟩

  -- This set is nonempty
  have hnonempty : { v ∈ L.carrier | v ≠ 0 ∧ ‖v‖ ≤ ‖v₀‖ }.Nonempty := by
    use v₀
    exact ⟨hv₀.1, hv₀.2, le_refl _⟩

  -- A finite nonempty set has a minimum element (by norm)
  obtain ⟨v, ⟨hv_mem, hv_ne, hv_bound⟩, hv_min⟩ :=
    hfinite.exists_minimalFor (fun x : (𝓔 n) => ‖x‖) ball₀ hnonempty

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
noncomputable def EuclideanLattice.shortestVectorLength (L : EuclideanLattice n n) : ℝ :=
  iInf (fun v : L.nonzeroVectors => ‖(v : 𝓔 n)‖)

/-- Alternative definition: λ₁(L) = inf { ‖v‖ : v ∈ L, v ≠ 0 } -/
theorem EuclideanLattice.shortestVectorLength_eq (L : EuclideanLattice n n) :
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
      have h_b_in_set : b ∈ Set.image (fun v : L.nonzeroVectors => ‖(v : 𝓔 n)‖) Set.univ := by
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
      have h_inf_ge : ⨅ (v : L.nonzeroVectors), ‖(v : 𝓔 n)‖ ≥ ‖v‖ := by
        -- Apply the fact that the infimum is the greatest lower bound.
        apply le_csInf;
        · exact ⟨ _, ⟨ ⟨ v, hv ⟩, rfl ⟩ ⟩;
        · aesop;
      exact le_antisymm h_inf_ge <| ciInf_le_of_le ⟨ 0, Set.forall_mem_range.mpr fun _ => norm_nonneg _ ⟩ ⟨ v, hv ⟩ <| by aesop;

/-- The shortest vector length is positive. -/
theorem EuclideanLattice.shortestVectorLength_pos (L : EuclideanLattice n n) :
    0 < L.shortestVectorLength := by
  -- Since the lattice is discrete, there exists a shortest non-zero vector. Let's call this vector v. Then ‖v‖ is positive.
  obtain ⟨v, hv⟩ : ∃ v : L.nonzeroVectors, ∀ w : L.nonzeroVectors, ‖(v : 𝓔 n)‖ ≤ ‖(w : 𝓔 n)‖ := by
    have := L.exists_shortest_vector;
    exact ⟨ ⟨ this.choose, this.choose_spec.1 ⟩, fun w => this.choose_spec.2 _ w.2 ⟩;
  exact lt_of_lt_of_le ( norm_pos_iff.mpr v.2.2 ) ( le_csInf ⟨ _, Set.mem_range_self v ⟩ <| Set.forall_mem_range.mpr hv )

/-- Any lattice point in the open ball of radius λ₀ is the origin. -/
lemma EuclideanLattice.lattice_point_in_lambda_zero_ball_is_zero (L : EuclideanLattice n n)
    (v : 𝓔 n) (hv : v ∈ L) (hr : ‖v‖ < L.shortestVectorLength) :
    v = 0 := by
  by_contra hne
  -- v is a non-zero lattice vector with ‖v‖ < λ₁, contradicting definition of λ₁
  have hv_nonzero : v ∈ L.nonzeroVectors := ⟨hv, hne⟩
  have := ciInf_le (⟨0, fun x ⟨w, hw⟩ => hw ▸ norm_nonneg _⟩ : BddBelow (Set.range fun v : L.nonzeroVectors => ‖(v : 𝓔 n)‖)) ⟨v, hv_nonzero⟩
  convert hr.not_ge _;
  convert this using 1


/--
  The i-th successive minimum λᵢ(L) is the smallest r such that
  the ball of radius r contains i linearly independent lattice vectors.

  Formally: λᵢ(L) = inf { r > 0 : dim(span_ℝ(L ∩ B(0,r))) ≥ i }
  In the literature, the index i is 1-based, but here we use 0-based indexing for Fin type.
-/
noncomputable def EuclideanLattice.successiveMinima (L : EuclideanLattice n n) (i : Fin n) : ℝ :=
  sInf { r : ℝ | 0 < r ∧
    ∃ (S : Finset (𝓔 n)),
      S.card = i.val + 1 ∧
      (∀ v ∈ S, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r) ∧
      LinearIndependent ℝ (fun v : S => (v : 𝓔 n)) }

noncomputable abbrev EuclideanLattice.succMin₁ (L : EuclideanLattice n n) : ℝ :=
  L.successiveMinima ⟨0, n.pos⟩

noncomputable abbrev EuclideanLattice.succMin₂ (L : EuclideanLattice n n) (h : 1 < n := by decide) : ℝ :=
  L.successiveMinima ⟨1, h⟩

noncomputable abbrev EuclideanLattice.succMinₙ (L : EuclideanLattice n n) : ℝ :=
  L.successiveMinima ⟨n - 1, by
    have : 0 < (n : ℕ) := by exact n.pos
    exact Nat.sub_lt (Nat.pos_of_ne_zero (by exact n.pos.ne.symm)) (by decide)
  ⟩


noncomputable def EuclideanLattice.successiveMinima' (L : EuclideanLattice n n) (i : Fin n) : ℝ :=
  sInf { r : ℝ | 0 < r ∧
      (Module.rank ℝ (Submodule.span ℝ {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r})) ≥ i + 1}


theorem EuclideanLattice.successiveMinima_defs_eq (L : EuclideanLattice n n) :
  ∀ (i : Fin n), L.successiveMinima i = L.successiveMinima' i
:= by
  intro i
  unfold EuclideanLattice.successiveMinima EuclideanLattice.successiveMinima'
  congr 1
  ext r
  apply Iff.intro
  .
    -- Since S is a subset of B(0, r) and is linearly independent, the span of S is a subspace of the span of B(0, r).
    intro hr
    obtain ⟨S, hS_card, hS_subset, hS_lin_ind⟩ := hr.right
    have h_span_S : Submodule.span ℝ (S : Set (𝓔 n)) ≤ Submodule.span ℝ {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r} := by
      exact Submodule.span_mono fun x hx => hS_subset x hx;
    have h_dim_S : Module.rank ℝ (↥(Submodule.span ℝ (S : Set (𝓔 n)))) = (i : ℕ) + 1 := by
      rw [ @rank_span_set ];
      · aesop;
      · exact hS_lin_ind;
    exact ⟨ hr.1, h_dim_S ▸ Submodule.rank_mono h_span_S ⟩
  .
    norm_num +zetaDelta at *;
    intro hr h; use hr;
    have h' : ((i.val + 1 : ℕ) : Cardinal) ≤ Module.rank ℝ (Submodule.span ℝ {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r}) := by
      simpa using h
    have := rank_span_ge_iff_subset { v : 𝓔 n | v ∈ L ∧ ¬v = 0 ∧ ‖v‖ ≤ r } ( i + 1 );
    exact this.mp ( mod_cast h' )

/-
  Immediate corollary from successive minima definition: If there exists a set of `i+1`
  linearly independent lattice vectors with norms at most `r`, then the `i`-th successive
  minimum is at most `r`.
-/
corollary EuclideanLattice.le_successiveMinima_of_exists_linearIndependent
    (L : EuclideanLattice n n)
    {i : Fin n} {r : ℝ} (hr : 0 < r)
    (S : Finset (𝓔 n))
    (h_card : S.card = i.val + 1)
    (h_mem : ∀ v ∈ S, v ∈ L.nonzeroVectors)
    (h_norm : ∀ v ∈ S, ‖v‖ ≤ r)
    (h_li : LinearIndependent ℝ (fun v : S => (v : 𝓔 n))) :
    L.successiveMinima i ≤ r := by
      refine' csInf_le _ _;
      · exact ⟨ 0, fun x hx => hx.1.le ⟩;
      · exact ⟨ hr, S, h_card, fun v hv => ⟨ h_mem v hv |>.1, h_mem v hv |>.2, h_norm v hv ⟩, h_li ⟩


theorem EuclideanLattice.exists_successiveMinima (L : EuclideanLattice n n) (i : Fin n) :
  ∃ (r : ℝ), 0 < r ∧ ∃ (S : Finset (𝓔 n)),
      S.card = i.val + 1 ∧
      (∀ v ∈ S, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r) ∧
      LinearIndependent ℝ (fun v : S => (v : 𝓔 n)) := by
  classical
  -- Choose the first i.val+1 basis vectors
  let idx : Finset (Fin n) := Finset.Iic i
  have hcard : idx.card = i.val + 1 := by
    simp [idx]
  let S : Finset (𝓔 n) := idx.image fun j => (L.basis.cols j : 𝓔 n)
  -- Define r as the maximum norm of these chosen basis vectors
  have hnonempty : S.Nonempty := by
    have hidx_nonempty : idx.Nonempty := by
      use i
      simp [idx]
    obtain ⟨j, hj⟩ := hidx_nonempty
    exact ⟨L.basis.cols j, by
      exact Finset.mem_image_of_mem _ hj⟩
  let r : ℝ := S.sup' hnonempty (fun v => ‖v‖)
  have hr_pos : 0 < r := by
    have hi_mem : (L.basis.cols i : 𝓔 n) ∈ S := by
      exact Finset.mem_image_of_mem _ (by simp [idx])
    have hi_ne : (L.basis.cols i : 𝓔 n) ≠ 0 := by
      exact L.basis.li.ne_zero i
    have hi_le : ‖(L.basis.cols i : 𝓔 n)‖ ≤ r := by
      exact Finset.le_sup' (fun v => ‖v‖) (by simpa [S, idx] using hi_mem)
    exact lt_of_lt_of_le (norm_pos_iff.mpr hi_ne) hi_le
  have h_mem : ∀ v ∈ S, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨j, hj_idx, rfl⟩
    have hjL : (L.basis.cols j : 𝓔 n) ∈ L := L.basis_mem j
    have hj_ne : (L.basis.cols j : 𝓔 n) ≠ 0 := by
      -- basis vectors are nonzero
      have := L.basis.li;
      -- Since the basis is linearly independent, having a zero vector would contradict that.
      apply this.ne_zero j;
    have hj_le : ‖(L.basis.cols j : 𝓔 n)‖ ≤ r := by
      -- by definition of r = sup' over S
      exact Finset.le_sup' (fun v => ‖v‖) (by simpa [S, idx] using hv)
    exact ⟨hjL, hj_ne, hj_le⟩
  have h_li : LinearIndependent ℝ (fun v : S => (v : 𝓔 n)) := by
    -- a subset of a linearly independent family is linearly independent
    have h_basis_li : LinearIndependent ℝ (fun j : Fin n => (L.basis.cols j : 𝓔 n)) := L.basis.li
    -- choose the original index for each element of the image
    let f : S → Fin n := fun x => Classical.choose (Finset.mem_image.mp x.2)
    have hf_spec : ∀ x : S, (L.basis.cols (f x) : 𝓔 n) = x := by
      intro x
      exact (Classical.choose_spec (Finset.mem_image.mp x.2)).2
    have hf_inj : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have : (L.basis.cols (f x) : 𝓔 n) = L.basis.cols (f y) := by
        simp [hxy]
      simpa [hf_spec x, hf_spec y] using this
    have h_li' : LinearIndependent ℝ (fun x : S => (L.basis.cols (f x) : 𝓔 n)) :=
      h_basis_li.comp f hf_inj
    simpa [hf_spec] using h_li'
  have hS_card : S.card = i.val + 1 := by
    rw [Finset.card_image_of_injective]
    · exact hcard
    · intro x y hxy
      exact L.basis.li.injective hxy
  refine ⟨r, hr_pos, S, hS_card, h_mem, h_li⟩


/-- The first successive minimum equals the shortest vector length. -/
theorem EuclideanLattice.successiveMinima_one (L : EuclideanLattice n n) :
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
      have h_nonneg : ∀ v : L.nonzeroVectors, 0 ≤ ‖(v : 𝓔 n)‖ := by
        exact fun v => norm_nonneg _;
      exact ⟨ 0, Set.forall_mem_range.mpr h_nonneg ⟩;
      exacts [ ⟨ v, hv_L, hv_ne ⟩, hv_norm ]

/-
 Immediate corollary from the definition: The norm of any non-zero lattice vector is at least the first successive minimum.
-/
corollary EuclideanLattice.norm_ge_successiveMinima_one (L : EuclideanLattice n n) (v : 𝓔 n)
    (hv : v ∈ L.nonzeroVectors) :
    L.successiveMinima ⟨0, n.pos⟩ ≤ ‖v‖ := by
      have := hv;
      rw [ @EuclideanLattice.successiveMinima_one ];
      rw [ @EuclideanLattice.shortestVectorLength_eq ];
      exact csInf_le ⟨ 0, by rintro x ⟨ w, hw, rfl ⟩ ; exact norm_nonneg _ ⟩ ⟨ v, this, rfl ⟩


/-- Successive minima are non-decreasing: λᵢ ≤ λⱼ for i ≤ j. -/
theorem EuclideanLattice.successiveMinima_mono (L : EuclideanLattice n n)
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
      have hT_li : LinearIndependent ℝ (fun v : S => (v : 𝓔 n)) := by
        -- Since $T$ is a subset of $S$, and $S$ is linearly independent, any subset of $S$ is also linearly independent. Therefore, the function from $T$ to the vector space is linearly independent.
        apply hS_li;
      convert hT_li.comp _ _;
      rotate_left;
      exacts [ fun x => ⟨ x, hT_sub x.2 ⟩, fun x y hxy => by simpa [ Subtype.ext_iff ] using hxy, funext fun x => rfl ]

/-- All successive minima are positive. -/
theorem EuclideanLattice.successiveMinima_pos (L : EuclideanLattice n n) (i : Fin n) :
    0 < L.successiveMinima i := by
  -- λ₁ ≤ λᵢ and λ₁ > 0
  calc 0 < L.successiveMinima ⟨0, n.pos⟩ := by
           rw [successiveMinima_one]
           exact shortestVectorLength_pos L
       _ ≤ L.successiveMinima i := successiveMinima_mono L (Fin.zero_le i)

/-- All successive minima are finite (bounded above). -/
theorem EuclideanLattice.successiveMinima_boundedAbove (L : EuclideanLattice n n) (i : Fin n) :
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

/-- Scaling a geometric lattice by a positive scalar scales its successive minima by the same factor. -/
theorem EuclideanLattice.successiveMinima_scale (L : EuclideanLattice n n) (i : Fin n) (s : ℝ) (hs : 0 < s) :
  (L.smul s hs.ne.symm).successiveMinima i = s * L.successiveMinima i := by
  generalize_proofs at *;
  -- Since scaling each vector by s scales the norms by s, the dimension of the span remains the same. Therefore, the successive minima of sL is s times the successive minima of L.
  have h_scale : ∀ r : ℝ, (Module.rank ℝ (Submodule.span ℝ {v | v ∈ (L.smul s ‹_›) ∧ v ≠ 0 ∧ ‖v‖ ≤ r})) = (Module.rank ℝ (Submodule.span ℝ {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r / s})) := by
    intro r;
    -- By definition of scaling, we have that $v \in (L.smul s ‹_›)$ if and only if $v = s \cdot u$ for some $u \in L$.
    have h_scale : {v : 𝓔 n | v ∈ (L.smul s ‹_›) ∧ v ≠ 0 ∧ ‖v‖ ≤ r} = {s • u | u ∈ {v : 𝓔 n | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r / s}} := by
      ext v; simp [EuclideanLattice.smul];
      constructor;
      · intro hv
        obtain ⟨u, hu⟩ : ∃ u ∈ L, v = s • u := by
          have h_scale : v ∈ Submodule.span ℤ (Set.range (fun i => s • L.basis.cols i)) := by
            exact hv.1;
          rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_scale;
          obtain ⟨ c, rfl ⟩ := h_scale;
          use ∑ i, c i • L.basis.cols i;
          simp_all +decide [ Finsupp.sum_fintype, Finset.smul_sum ];
          exact ⟨ by simpa [ smul_smul, mul_comm ] using L.mem_iff_exists_coeffs ( ∑ i, c i • L.basis.cols i ) |>.2 ⟨ c, rfl ⟩, Finset.sum_congr rfl fun _ _ => by rw [ SMulCommClass.smul_comm ] ⟩;
        field_simp;
        exact ⟨ u, ⟨ hu.1, by aesop, by rw [ hu.2, norm_smul, Real.norm_of_nonneg hs.le ] at hv; linarith ⟩, hu.2.symm ⟩;
      · rintro ⟨ u, ⟨ hu₁, hu₂, hu₃ ⟩, rfl ⟩ ; simp_all +decide [ norm_smul, abs_of_pos hs ];
        -- Since $u \in L$, multiplying by $s$ (a scalar) keeps it in the lattice.
        have h_smul : s • u ∈ (L.basis.smul s ‹_›).toLattice := by
          -- Since $u \in L$, we can write $u$ as a linear combination of the basis vectors of $L$.
          obtain ⟨c, hc⟩ : ∃ c : Fin n → ℤ, u = ∑ i, c i • L.basis.cols i := by
            exact (mem_iff_exists_coeffs L u).mp hu₁;
          -- Since $s • u$ is a linear combination of the scaled basis vectors with integer coefficients, it is in the lattice.
          have h_comb : s • u = ∑ i, c i • (s • L.basis.cols i) := by
            simp +decide [ hc, Finset.smul_sum ];
            exact Finset.sum_congr rfl fun _ _ => by rw [ SMulCommClass.smul_comm ] ;
          exact h_comb.symm ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( Submodule.subset_span <| Set.mem_range_self _ );
        exact ⟨ h_smul, by rwa [ le_div_iff₀' hs ] at hu₃ ⟩;
    rw [ h_scale ];
    rw [ show { x : LatticeCrypto.Utils.Vec.𝓔 n | ∃ u ∈ { v : LatticeCrypto.Utils.Vec.𝓔 n | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r / s }, s • u = x } = ( fun u => s • u ) '' { v : LatticeCrypto.Utils.Vec.𝓔 n | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r / s } by aesop, Submodule.span_eq_span ];
    · exact Set.image_subset_iff.mpr fun x hx => Submodule.smul_mem _ _ ( Submodule.subset_span hx );
    · intro v hv; exact (by
      -- Since $v$ is in the set ${v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r / s}$, we have $s • v$ in the image of this set under the function $u ↦ s • u$.
      have h_image : s • v ∈ (fun u => s • u) '' {v : LatticeCrypto.Utils.Vec.𝓔 n | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r / s} := by
        exact ⟨ v, hv, rfl ⟩;
      exact Submodule.smul_mem _ ( s⁻¹ ) ( Submodule.subset_span h_image ) |> fun h => by simpa [ hs.ne' ] using h;);
  -- By definition of successive minima, we know that if the dimension of the span is the same, then the infimum of the radii is the same.
  have h_inf : ∀ r : ℝ, (Module.rank ℝ (Submodule.span ℝ {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r})) ≥ i.val + 1 ↔ (Module.rank ℝ (Submodule.span ℝ {v | v ∈ (L.smul s ‹_›) ∧ v ≠ 0 ∧ ‖v‖ ≤ s * r})) ≥ i.val + 1 := by
    simp_all +decide ;
    exact fun r => by rw [ mul_div_cancel_left₀ _ hs.ne' ] ;
  have h_inf_eq : sInf { r : ℝ | 0 < r ∧ (Module.rank ℝ (Submodule.span ℝ {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r})) ≥ i.val + 1 } = sInf { r : ℝ | 0 < r ∧ (Module.rank ℝ (Submodule.span ℝ {v | v ∈ (L.smul s ‹_›) ∧ v ≠ 0 ∧ ‖v‖ ≤ r})) ≥ i.val + 1 } / s := by
    rw [ eq_div_iff hs.ne', mul_comm ];
    rw [ ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hs.le ];
    congr with x ; simp +decide [ Set.mem_smul_set ];
    constructor <;> intro h;
    · rcases h with ⟨ y, ⟨ hy₁, hy₂ ⟩, rfl ⟩ ; exact ⟨ mul_pos hs hy₁, by simpa [ mul_comm ] using h_inf y |>.1 hy₂ ⟩ ;
    · use x / s;
      specialize h_inf ( x / s ) ; simp_all +decide [ mul_div_cancel₀ _ hs.ne' ] ;
  convert congr_arg ( fun x => s * x ) h_inf_eq.symm using 1;
  · field_simp;
    convert EuclideanLattice.successiveMinima_defs_eq ( L.smul s ‹_› ) i using 1;
  · congr! 2;
    convert EuclideanLattice.successiveMinima_defs_eq L i using 1

/-- Scaling a geometric lattice by a positive scalar will cause its dual's successive minima to shrink by the same factor. -/
theorem EuclideanLattice.successiveMinima_scale_dual (L : EuclideanLattice n n) (i : Fin n) (s : ℝ) (hs : 0 < s) :
  (L.smul s hs.ne.symm).dual.successiveMinima i = L.dual.successiveMinima i / s := by
  -- By definition of dual, scaling L by s scales its dual by 1/s.
  have h_dual_scale : (L.smul s hs.ne.symm).dual = L.dual.smul (1 / s) (by
  positivity) := by
    all_goals generalize_proofs at *;
    -- By definition of the dual basis, we know that the dual of the scaled lattice is the dual of the original lattice scaled by 1/s.
    have h_dual_scale : (L.smul s hs.ne.symm).basis.dual = (L.basis.dual).smul (1 / s) (by
    (expose_names; exact pf_1)) := by
      all_goals generalize_proofs at *;
      unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.dual;
      -- By definition of matrix multiplication and the properties of the inverse, we can show that the dual of the scaled lattice is the dual of the original lattice scaled by the reciprocal of the scalar.
      have h_dual_scale : (Matrix.transpose (s • L.basis.asMatrix))⁻¹ = (1 / s) • (Matrix.transpose L.basis.asMatrix)⁻¹ := by
        rw [ Matrix.inv_eq_left_inv ];
        simp +decide [ Matrix.transpose_smul, hs.ne' ];
        exact Matrix.nonsing_inv_mul _ ( show IsUnit L.basis.asMatrix.transpose.det from isUnit_iff_ne_zero.mpr <| by simpa [ Matrix.det_transpose ] using LatticeBasis.det_ne_zero L.basis );
      -- By definition of matrix multiplication and the properties of the inverse, we can show that the columns of the dual matrix of the scaled lattice are equal to the columns of the dual matrix of the original lattice scaled by 1/s.
      ext i j; simp ;
      convert congr_fun ( congr_fun h_dual_scale j ) i using 1;
      unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.smul; aesop;
    generalize_proofs at *;
    exact congr_arg _ h_dual_scale
  generalize_proofs at *;
  -- By definition of successive minima, we know that scaling the lattice by $1/s$ scales the successive minima by $1/s$.
  have h_scale_succ_min : ∀ (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s), (L.smul s hs.ne.symm).successiveMinima i = s * L.successiveMinima i := by
    exact fun L s hs => successiveMinima_scale L i s hs
  generalize_proofs at *;
  rw [ h_dual_scale, h_scale_succ_min ] <;> ring_nf ; aesop


end successive_minima_basics


noncomputable section successive_minima_achievable
/-!
## In this section we prove that successive minima are achivable by n linearly independent vectors
-/
/-- Helper -/
lemma LatticeCrypto.Foundations.Lattice.exists_min_norm_subset_proven {n : ℕ+} (L : EuclideanLattice n n) (S : Set ℝ)
    (h_subset : S ⊆ { ‖v‖ | v ∈ L.nonzeroVectors })
    (h_nonempty : S.Nonempty) :
    ∃ m ∈ S, ∀ s ∈ S, m ≤ s := by
      exact exists_min_norm_subset L S h_subset h_nonempty

/-- The successive minima are achieved by lattice vectors. -/
theorem EuclideanLattice.successiveMinima_attained (L : EuclideanLattice n n) (i : Fin n) :
    ∃ v ∈ L.nonzeroVectors, ‖v‖ = L.successiveMinima i := by
  classical
  -- Abbreviate the defining set of λᵢ
  let A : Set ℝ :=
    { r : ℝ | 0 < r ∧
      ∃ (S : Finset (𝓔 n)),
        S.card = i.val + 1 ∧
        (∀ v ∈ S, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r) ∧
        LinearIndependent ℝ (fun v : S => (v : 𝓔 n)) }

  have hA_def :
      L.successiveMinima i = sInf A := rfl

  -- Define the "snapped" set of candidate radii: max norm inside the finite set S
  let B : Set ℝ :=
    { r : ℝ |
        ∃ (S : Finset (𝓔 n)) (v : 𝓔 n),
          v ∈ S ∧
          S.card = i.val + 1 ∧
          (∀ w ∈ S, w ∈ L ∧ w ≠ 0 ∧ ‖w‖ ≤ r) ∧
          LinearIndependent ℝ (fun w : S => (w : 𝓔 n)) ∧
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
      have := ((Finset.sup'_le_iff (f := fun w : (𝓔 n) => ‖w‖) (a := r) (s := S)) hS_nonempty).mpr ?h
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
      · obtain ⟨ r, hr ⟩ := EuclideanLattice.exists_successiveMinima L i;
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

noncomputable section Aristotle_lemmas
/-
The i-th successive minimum is attained by a set of i+1 linearly independent lattice vectors.
-/
theorem successiveMinima_attained_set (L : EuclideanLattice n n) (i : Fin n) :
    ∃ S : Finset (𝓔 n),
      S.card = i.val + 1 ∧
      (∀ v ∈ S, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ L.successiveMinima i) ∧
      LinearIndependent ℝ (fun v : S => (v : 𝓔 n)) := by
  classical
  -- Abbreviate the defining set of λᵢ
  let A : Set ℝ :=
    { r : ℝ | 0 < r ∧
      ∃ (S : Finset (𝓔 n)),
        S.card = i.val + 1 ∧
        (∀ v ∈ S, v ∈ L ∧ v ≠ 0 ∧ ‖v‖ ≤ r) ∧
        LinearIndependent ℝ (fun v : S => (v : 𝓔 n)) }

  have hA_def : L.successiveMinima i = sInf A := rfl

  -- Define the “snapped” set of candidate radii: max norm inside the finite set S
  let B : Set ℝ :=
    { r : ℝ |
        ∃ (S : Finset (𝓔 n)) (v : 𝓔 n),
          v ∈ S ∧
          S.card = i.val + 1 ∧
          (∀ w ∈ S, w ∈ L ∧ w ≠ 0 ∧ ‖w‖ ≤ r) ∧
          LinearIndependent ℝ (fun w : S => (w : 𝓔 n)) ∧
          r = ‖v‖ ∧
          ∀ w ∈ S, ‖w‖ ≤ ‖v‖ }

  -- 1. B ⊆ A
  have hB_sub_A : B ⊆ A := by
    intro r hr
    rcases hr with ⟨S, v, hvS, hS_card, hS_props, hS_li, rfl, hmax⟩
    have hS_nonempty : S.Nonempty := ⟨v, hvS⟩
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
    have hS_nonempty : S.Nonempty := by
      have : 0 < S.card := by
        simp [hS_card]
      exact Finset.card_pos.mp this
    obtain ⟨v, hvS, hv_eq⟩ :=
      Finset.exists_mem_eq_sup' hS_nonempty (fun w => ‖w‖)
    let b : ℝ := ‖v‖
    have hb_le_r : b ≤ r := by
      have := ((Finset.sup'_le_iff (f := fun w : (𝓔 n) => ‖w‖) (a := r) (s := S)) hS_nonempty).mpr ?h
      · simpa [b, hv_eq] using this
      . intro w hw
        exact (hS_props w hw).2.2
    have hbB : b ∈ B := by
      refine ⟨S, v, hvS, hS_card, ?_, hS_li, rfl, ?_⟩
      · intro w hw
        have := hS_props w hw
        have h_norm_le_b : ∀ w ∈ S, ‖w‖ ≤ b := by
          intros w hw
          apply hv_eq ▸ Finset.le_sup' (fun w => ‖w‖) hw
        exact ⟨ this.1, this.2.1, h_norm_le_b w hw ⟩
      · intro w hw
        have hw_le_sup : ‖w‖ ≤ S.sup' hS_nonempty (fun w => ‖w‖) :=
          Finset.le_sup' (f := fun w => ‖w‖) hw
        simpa [b, hv_eq] using hw_le_sup
    exact ⟨b, hbB, hb_le_r⟩

  -- 3. A and B have the same infimum
  have h_inf_eq : sInf A = sInf B := by
    have h1 : sInf A ≤ sInf B := by
      apply_rules [csInf_le_csInf]
      · exact ⟨0, fun r hr => hr.1.le⟩
      · obtain ⟨r, hr⟩ := EuclideanLattice.exists_successiveMinima L i
        obtain ⟨b, hb₁, hb₂⟩ := hA_to_B r ⟨hr.1, hr.2⟩
        exact ⟨b, hb₁⟩
    have h2 : sInf B ≤ sInf A := by
      have h_lb : ∀ r ∈ A, sInf B ≤ r := by
        intro r hrA
        rcases hA_to_B r hrA with ⟨b, hbB, hb_le⟩
        have h_sInf_le_b : sInf B ≤ b := by
          exact csInf_le ⟨0, fun x hx => by
            obtain ⟨S, v, hvS, hS_card, hS_cond, hS_lin, rfl, hv_norm⟩ := hx
            exact norm_nonneg _⟩ hbB
        exact le_trans h_sInf_le_b hb_le
      apply le_csInf
      · apply Classical.byContradiction
        intro hA_empty
        exact hA_empty <| by
          obtain ⟨r, hr⟩ := EuclideanLattice.exists_successiveMinima L i
          exact ⟨r, ⟨hr.1, hr.2⟩⟩
      · exact h_lb
    exact le_antisymm h1 h2

  -- 4. Nonemptiness of B and that B ⊆ {‖v‖ | v ∈ L.nonzeroVectors}
  have hB_nonempty : B.Nonempty := by
    obtain ⟨r, hr_pos, S, hS_card, hS_props, hS_li⟩ := EuclideanLattice.exists_successiveMinima L i
    have : r ∈ A := by
      refine ⟨hr_pos, S, hS_card, hS_props, hS_li⟩
    rcases hA_to_B r this with ⟨b, hbB, hb_le⟩
    exact ⟨b, hbB⟩

  have hB_subset_norms : B ⊆ { ‖v‖ | v ∈ L.nonzeroVectors } := by
    intro r hrB
    rcases hrB with ⟨S, v, hvS, hS_card, hS_props, hS_li, rfl, hmax⟩
    have hv_L : v ∈ L := (hS_props v hvS).1
    have hv_ne : v ≠ 0 := (hS_props v hvS).2.1
    refine ⟨v, ⟨hv_L, hv_ne⟩, rfl⟩

  -- 5. Take the minimal element of B
  obtain ⟨m, hmB, hm_min⟩ :=
    LatticeCrypto.Foundations.Lattice.exists_min_norm_subset_proven
      L B hB_subset_norms hB_nonempty

  -- m is the infimum of B
  have hm_isInf : sInf B = m := by
    have h_le : sInf B ≤ m := by
      apply csInf_le
      · exact ⟨m, fun x hx => hm_min x hx⟩
      · exact hmB
    have h_ge : m ≤ sInf B := by
      exact le_csInf hB_nonempty hm_min
    exact le_antisymm h_le h_ge

  -- Therefore λᵢ = m
  have h_lambda_eq_m : L.successiveMinima i = m := by
    have : sInf A = sInf B := h_inf_eq
    simp [hA_def, this, hm_isInf]

  -- Use the witness for m ∈ B to get the required set
  rcases hmB with ⟨S, v, hvS, hS_card, hS_props, hS_li, hm_eq, hmax⟩
  refine ⟨S, hS_card, ?_, hS_li⟩
  intro w hw
  obtain ⟨hw_L, hw_ne, hw_le⟩ := hS_props w hw
  have hw_le' : ‖w‖ ≤ L.successiveMinima i := by
    have : ‖w‖ ≤ ‖v‖ := hmax w hw
    simpa [h_lambda_eq_m, hm_eq] using this
  exact ⟨hw_L, hw_ne, hw_le'⟩

/-
If a set of k+1 linearly independent lattice vectors exists, at least one must have norm >= lambda_k.
-/
theorem norm_ge_successiveMinima (L : EuclideanLattice n n) (k : Fin n) (s : Finset (𝓔 n))
    (h_card : s.card = k.val + 1)
    (h_li : LinearIndependent ℝ (fun v : s => (v : 𝓔 n)))
    (h_mem : ∀ v ∈ s, v ∈ L.nonzeroVectors) :
    ∃ v ∈ s, L.successiveMinima k ≤ ‖v‖ := by
      by_contra h_contra;
      -- Let $r = \max_{v \in s} \|v\|$.
      obtain ⟨r, hr⟩ : ∃ r : ℝ, ∀ v ∈ s, ‖v‖ ≤ r ∧ r < L.successiveMinima k := by
        by_cases hs : s.Nonempty;
        · obtain ⟨r, hr⟩ : ∃ r : ℝ, r ∈ Set.image (fun v : 𝓔 n => ‖v‖) s ∧ ∀ v ∈ Set.image (fun v : 𝓔 n => ‖v‖) s, v ≤ r := by
            exact ⟨ Finset.max' ( s.image fun v => ‖v‖ ) ⟨ _, Finset.mem_image_of_mem _ hs.choose_spec ⟩, by simpa using Finset.max'_mem ( s.image fun v => ‖v‖ ) ⟨ _, Finset.mem_image_of_mem _ hs.choose_spec ⟩, fun v hv => Finset.le_max' _ _ <| by simpa using hv ⟩;
          aesop;
        · aesop;
      refine' hr _ ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ) ) |>.2.not_ge _;
      refine' csInf_le _ _;
      · exact ⟨ 0, fun x hx => hx.1.le ⟩;
      · exact ⟨ lt_of_lt_of_le ( norm_pos_iff.mpr ( h_mem _ ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ) ) |>.2 ) ) ( hr _ ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith ) ) ) |>.1 ), s, h_card, fun v hv => ⟨ h_mem v hv |>.1, h_mem v hv |>.2, hr v hv |>.1 ⟩, h_li ⟩

/-
Helper lemma: A specific configuration of vectors with small norms leads to a contradiction.
-/
lemma contradiction_of_small_norm (L : EuclideanLattice n n) (j : Fin n) (hj : j.val + 1 < n)
    (x : Fin (j.val + 1) → 𝓔 n) (v : 𝓔 n)
    (h_li : LinearIndependent ℝ (Fin.snoc x v))
    (h_mem_x : ∀ i, x i ∈ L.nonzeroVectors)
    (h_mem_v : v ∈ L.nonzeroVectors)
    (h_norm_x : ∀ i, ‖x i‖ ≤ ‖v‖)
    (h_norm_v : ‖v‖ < L.successiveMinima ⟨j.val + 1, hj⟩) : False := by
  classical
  contrapose! h_norm_v
  refine' csInf_le _ _
  · exact ⟨0, fun r hr => hr.1.le⟩
  ·
    let snoc : Fin (j.val + 1 + 1) → 𝓔 n := Fin.snoc x v
    let S : Finset (𝓔 n) := Finset.image snoc Finset.univ
    refine' ⟨norm_pos_iff.mpr h_mem_v.2, S, _, _, _⟩
    · -- cardinality
      simpa [S, snoc] using (by
        rw [Finset.card_image_of_injective _
          (fun i j hij => by simpa [Fin.ext_iff] using h_li.injective hij),
          Finset.card_fin])
    · -- membership, nonzero, and norm bound
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
      by_cases h : (i.val : ℕ) < j.val + 1
      · -- i is in the first block, so use x
        let i' : Fin (j.val + 1) := ⟨i.val, h⟩
        have hL : snoc i ∈ L := by
          simpa [snoc, Fin.snoc, h, i'] using (h_mem_x i').1
        have hne : snoc i ≠ 0 := by
          simpa [snoc, Fin.snoc, h, i'] using (h_mem_x i').2
        have hnorm : ‖snoc i‖ ≤ ‖v‖ := by
          simpa [snoc, Fin.snoc, h, i'] using h_norm_x i'
        exact ⟨hL, hne, hnorm⟩
      · -- i is the last index, so use v
        have hL : snoc i ∈ L := by
          simpa [snoc, Fin.snoc, h] using h_mem_v.1
        have hne : snoc i ≠ 0 := by
          simpa [snoc, Fin.snoc, h] using h_mem_v.2
        have hnorm : ‖snoc i‖ ≤ ‖v‖ := by
          simp [snoc, Fin.snoc, h]
        exact ⟨hL, hne, hnorm⟩
    · -- linear independence
      let f : S → Fin (j.val + 1 + 1) := fun y => Classical.choose (Finset.mem_image.mp y.2)
      have hf_spec : ∀ y : S, (snoc (f y) : 𝓔 n) = (y : 𝓔 n) := by
        intro y
        exact (Classical.choose_spec (Finset.mem_image.mp y.2)).2
      have hf_inj : Function.Injective f := by
        intro y z h
        apply Subtype.ext
        have : (snoc (f y) : 𝓔 n) = snoc (f z) := by
          simp [h]
        simpa [hf_spec y, hf_spec z] using this
      have h_li' : LinearIndependent ℝ (fun y : S => (snoc (f y) : 𝓔 n)) :=
        h_li.comp f hf_inj
      simpa [hf_spec] using h_li'

/-
Given a vector with norm strictly between lambda_0 and lambda_k, there exists an index j < k such that lambda_j <= norm < lambda_{j+1}.
-/
lemma exists_index_between_norms (L : EuclideanLattice n n) (k : ℕ) (hk : k < n)
    (v : 𝓔 n) (hv_mem : v ∈ L.nonzeroVectors) (hv_lt : ‖v‖ < L.successiveMinima ⟨k, hk⟩) :
    ∃ j : Fin k,
      L.successiveMinima (Fin.castLE (le_of_lt hk) j) ≤ ‖v‖ ∧
      ‖v‖ < L.successiveMinima ⟨j.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt j.is_lt) hk⟩ := by
        -- Since $v \in L \setminus \{0\}$, $\|v\| \ge \lambda_0(L)$ (by `shortestVectorLength` properties).
        have hv_ge_lambda0 : L.successiveMinima ⟨0, n.pos⟩ ≤ ‖v‖ := by
          refine' csInf_le _ _;
          · exact ⟨ 0, fun r hr => hr.1.le ⟩;
          · exact ⟨ norm_pos_iff.mpr hv_mem.2, { v }, by aesop ⟩;
        contrapose! hv_lt;
        have h_seq : ∀ i : Fin (k + 1), L.successiveMinima (Fin.castLE (by linarith) i) ≤ ‖v‖ := by
          intro i; induction i using Fin.inductionOn <;> aesop;
        exact h_seq ⟨ k, Nat.lt_succ_self _ ⟩

/-
Helper lemma: If we find a vector with norm strictly less than lambda_k that is linearly independent of the first k vectors, we get a contradiction.
-/
lemma inductive_step_contradiction (L : EuclideanLattice n n) (k : ℕ) (hk : k < n)
  (x : Fin k → 𝓔 n)
  (h_li : LinearIndependent ℝ x)
  (h_x_mem : ∀ i, x i ∈ L.nonzeroVectors)
  (h_norm : ∀ i : Fin k, ‖x i‖ = L.successiveMinima (Fin.castLE (le_of_lt hk) i))
  (v : 𝓔 n)
  (hv_mem : v ∈ L.nonzeroVectors)
  (hv_li : LinearIndependent ℝ (Fin.snoc x v))
  (hv_lt : ‖v‖ < L.successiveMinima ⟨k, hk⟩) : False := by
    -- Pick the index `j` with λ_j ≤ ‖v‖ < λ_{j+1}.
    obtain ⟨j, hj⟩ : ∃ j : Fin k,
        L.successiveMinima (Fin.castLE (by linarith) j) ≤ ‖v‖ ∧
        ‖v‖ < L.successiveMinima (Fin.mk (j + 1) (by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt j.2) hk)) := by
      exact exists_index_between_norms L k hk v hv_mem hv_lt
    generalize_proofs at *

    -- Restrict the first `k` vectors to the first `j+1` entries.
    set x' : Fin (j.val + 1) → 𝓔 n := fun i =>
      x ⟨i.val, by
        exact lt_of_lt_of_le i.2 (Nat.succ_le_of_lt j.2)⟩

    -- Apply `contradiction_of_small_norm` to the truncated family `x'`.
    refine contradiction_of_small_norm L ⟨j.val, by
      linarith [Fin.is_lt j]⟩ (by
        (expose_names; exact pf_1)) x' v ?_ ?_ ?_ ?_ ?_
    · -- Linearly independent: use `linearIndependent_fin_snoc` plus restriction.
      have hv_li' : LinearIndependent ℝ x ∧ v ∉ Submodule.span ℝ (Set.range x) := by
        simpa [linearIndependent_fin_snoc] using hv_li
      have hincl : Function.Injective (fun i : Fin (j.val + 1) =>
          (⟨i.val, lt_of_lt_of_le i.is_lt (Nat.succ_le_of_lt j.is_lt)⟩ : Fin k)) := by
        intro i i' h
        exact Fin.ext (by simpa using congrArg Fin.val h)
      have h_li' : LinearIndependent ℝ x' := by
        simpa [x'] using h_li.comp
          (fun i : Fin (j.val + 1) =>
            (⟨i.val, lt_of_lt_of_le i.is_lt (Nat.succ_le_of_lt j.is_lt)⟩ : Fin k))
          hincl
      have h_span : Submodule.span ℝ (Set.range x') ≤ Submodule.span ℝ (Set.range x) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨_, rfl⟩
      have hv_not_span : v ∉ Submodule.span ℝ (Set.range x') := by
        intro hv_in
        exact hv_li'.2 (h_span hv_in)
      simpa [linearIndependent_fin_snoc] using And.intro h_li' hv_not_span
    · -- Membership in the lattice is preserved under restriction.
      exact fun i => h_x_mem _
    · -- `v` is a nonzero lattice vector.
      exact hv_mem
    · -- Norms of `x'` are bounded by ‖v‖ using monotonicity of minima.
      intro i
      set i' : Fin k := ⟨i.val, lt_of_lt_of_le i.is_lt (Nat.succ_le_of_lt j.is_lt)⟩
      have h_eq : ‖x' i‖ = L.successiveMinima (Fin.castLE (le_of_lt hk) i') := by
        simpa [x', i'] using h_norm i'
      have hij : (Fin.castLE (le_of_lt hk) i') ≤ (Fin.castLE (le_of_lt hk) j) := by
        exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ i.is_lt)
      have h_le : L.successiveMinima (Fin.castLE (le_of_lt hk) i') ≤ ‖v‖ :=
        le_trans (EuclideanLattice.successiveMinima_mono L hij) hj.1
      simpa [h_eq] using h_le
    · -- Final small-norm hypothesis.
      exact hj.2

/-
Inductive step: given k linearly independent vectors with correct norms, we can find a (k+1)-th vector.
-/
lemma inductive_step_successiveMinima (L : EuclideanLattice n n) (k : ℕ) (hk : k < n)
  (x : Fin k → 𝓔 n)
  (h_li : LinearIndependent ℝ x)
  (h_x_mem : ∀ i, x i ∈ L.nonzeroVectors)
  (h_norm : ∀ i : Fin k, ‖x i‖ = L.successiveMinima (Fin.castLE (le_of_lt hk) i)) :
  ∃ v, v ∈ L.nonzeroVectors ∧ ‖v‖ = L.successiveMinima ⟨k, hk⟩ ∧
    LinearIndependent ℝ (Fin.snoc x v) := by
      obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := successiveMinima_attained_set L ⟨ k, hk ⟩;
      -- Since $\dim(\text{span}(x)) = k$, there is $v \in S$ not in $\text{span}(x)$.
      obtain ⟨ v, hvS, hv_not_span ⟩ : ∃ v ∈ S, v ∉ Submodule.span ℝ (Set.range x) := by
        by_contra! h_contra;
        have h_span : Submodule.span ℝ (Set.range (fun v : S => (v : 𝓔 n))) ≤ Submodule.span ℝ (Set.range x) := by
          exact Submodule.span_le.mpr ( Set.range_subset_iff.mpr fun v => h_contra _ v.2 );
        have := Submodule.finrank_mono h_span; simp_all +decide [ finrank_span_eq_card ] ;
      -- Then $\{x_0, \dots, x_{k-1}, v\}$ is linearly independent.
      have h_lin_ind : LinearIndependent ℝ (Fin.snoc x v) := by
        rw [ linearIndependent_fin_snoc ];
        exact ⟨ h_li, hv_not_span ⟩;
      -- We claim $\|v\| \ge R$. Suppose $\|v\| < R$.
      by_cases hv_lt : ‖v‖ < L.successiveMinima ⟨k, hk⟩;
      · exact False.elim <| inductive_step_contradiction L k hk x h_li h_x_mem h_norm v ( ⟨ hS₂ v hvS |>.1, hS₂ v hvS |>.2.1 ⟩ ) h_lin_ind hv_lt;
      · exact ⟨ v, ⟨ hS₂ v hvS |>.1, hS₂ v hvS |>.2.1 ⟩, le_antisymm ( hS₂ v hvS |>.2.2 ) ( not_lt.mp hv_lt ), h_lin_ind ⟩

/-
There exists a partial basis of size k satisfying the successive minima conditions.
-/
lemma exists_partial_basis (L : EuclideanLattice n n) (k : ℕ) (hk : k ≤ n) :
  ∃ x : Fin k → 𝓔 n,
    LinearIndependent ℝ x ∧
    ∀ i : Fin k, x i ∈ L.nonzeroVectors ∧ ‖x i‖ = L.successiveMinima (Fin.castLE hk i) := by
      induction k <;> aesop;
      -- By the inductive hypothesis, we can find such an x for n_1.
      obtain ⟨x, hx⟩ := a (Nat.le_of_succ_le hk);
      -- Apply the lemma `inductive_step_successiveMinima` to find the (n_1+1)-th vector.
      obtain ⟨v, hv_mem, hv_norm, hv_li⟩ := inductive_step_successiveMinima L n_1 (by linarith) x hx.left (fun i => hx.right i |>.1) (fun i => hx.right i |>.2);
      refine' ⟨ Fin.snoc x v, hv_li, fun i => _ ⟩ ; induction i using Fin.lastCases <;> aesop


end Aristotle_lemmas

/-! There are n linearly independent vectors in the lattice attaining the successive minima. -/
theorem EuclideanLattice.linearIndependent_successiveMinima_attained
    (L : EuclideanLattice n n) :
  ∃ (x : Fin n → 𝓔 n),
    (∀ i : Fin n, x i ∈ L.nonzeroVectors ∧ ‖x i‖ = L.successiveMinima i) ∧
    LinearIndependent ℝ x := by
  classical
  have h : ∃ x : Fin n → 𝓔 n, LinearIndependent ℝ x ∧ ∀ i : Fin n, x i ∈ L.nonzeroVectors ∧ ‖x i‖ = L.successiveMinima i := by
    convert exists_partial_basis L n le_rfl;
  tauto

end successive_minima_achievable

/-!
## The shortest vector length is lower bounded by the Gram-Schmidt of any basis.
 -/
noncomputable section gram_schmidt

open InnerProductSpace

variable {n : ℕ+}

/-
If a vector `v` is a linear combination of basis vectors `b_i` with coefficients `c_i`, and `c_i = 0` for all `i > k`, then the inner product of `v` with the `k`-th Gram-Schmidt vector `b*_k` is `c_k * ‖b*_k‖^2`.
-/
lemma projection_on_gramSchmidt_of_max_index
    (B : SquareLatticeBasis n)
    (c : Fin n → ℝ)
    (k : Fin n)
    (h_max : ∀ i, k < i → c i = 0)
    (v : EuclideanSpace ℝ (Fin n))
    (hv : v = ∑ i, c i • B.basis i) :
    inner ℝ v (gramSchmidt ℝ B.basis k) = c k * ‖gramSchmidt ℝ B.basis k‖ ^ 2 := by
      -- By definition of `gramSchmidt`, we know that `⟪gramSchmidt ℝ B.basis k,gramSchmidt ℝ B.basis i⟫ = 0` for all `i < k`.
      have h_ortho : ∀ i : Fin n, i < k → ⟪gramSchmidt ℝ B.basis k, gramSchmidt ℝ B.basis i⟫ = 0 := by
        intro i hi; rw [ inner_eq_zero_symm ] ; aesop;
        exact gramSchmidt_orthogonal ℝ _ ( ne_of_lt hi );
      have h_inner : ⟪gramSchmidt ℝ B.basis k, B.basis k⟫_ℝ = (‖gramSchmidt ℝ B.basis k‖^2) := by
        have := gramSchmidt_def ℝ B.basis k;
        -- The projection of $B.basis k$ onto the span of the previous vectors is orthogonal to $gramSchmidt ℝ B.basis k$, so their inner product is zero.
        have h_proj_ortho : ∀ i ∈ Finset.Iio k, ⟪gramSchmidt ℝ B.basis k, (Submodule.span ℝ {gramSchmidt ℝ B.basis i}).starProjection (B.basis k)⟫_ℝ = 0 := by
          intro i hi; rw [ Submodule.starProjection ] ; simp +decide ;
          simp +decide [ Submodule.starProjection_singleton ];
          simp +decide [ inner_smul_right, h_ortho i ( Finset.mem_Iio.mp hi ) ];
        have h_inner : ⟪gramSchmidt ℝ B.basis k, B.basis k⟫_ℝ = ⟪gramSchmidt ℝ B.basis k, gramSchmidt ℝ B.basis k⟫_ℝ + ⟪gramSchmidt ℝ B.basis k, ∑ i ∈ Finset.Iio k, (Submodule.span ℝ {gramSchmidt ℝ B.basis i}).starProjection (B.basis k)⟫_ℝ := by
          rw [ ← inner_add_right ];
          rw [ this, sub_add_cancel ];
        rw [ h_inner, inner_self_eq_norm_sq_to_K ];
        simp +decide [ inner_sum ];
        exact Finset.sum_eq_zero h_proj_ortho;
      have h_inner_sum : ⟪gramSchmidt ℝ B.basis k, ∑ i ∈ Finset.univ.erase k, c i • B.basis i⟫_ℝ = 0 := by
        rw [ inner_sum ];
        refine Finset.sum_eq_zero fun i hi => ?_ ; by_cases hi' : i < k <;> aesop;
        · have h_inner_sum : ⟪gramSchmidt ℝ B.basis k, B.basis i⟫_ℝ = 0 := by
            exact gramSchmidt_inv_triangular ℝ B.basis hi';
          simp_all +decide [ inner_smul_right ];
        · rw [ h_max i ( lt_of_le_of_ne hi' ( Ne.symm hi ) ), zero_smul, inner_zero_right ];
      simp_all +decide [ sum_inner ];
      simp_all +decide [ inner_smul_left, inner_sub_right ];
      simp_all +decide [ sub_eq_zero, inner_smul_right, inner_sum ];
      simpa only [ real_inner_comm ] using h_inner_sum

/-
For any non-zero function `f` from `Fin n` to integers, there exists an index `k` such that `f k` is non-zero and `f i` is zero for all `i > k`.
-/
lemma exists_max_nonzero_index {n : ℕ} (f : Fin n → ℤ) (hf : f ≠ 0) :
    ∃ k : Fin n, f k ≠ 0 ∧ ∀ i, k < i → f i = 0 := by
      exact ⟨ Finset.max' ( Finset.univ.filter fun i => f i ≠ 0 ) ⟨ Classical.choose ( Function.ne_iff.mp hf ), Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Classical.choose_spec ( Function.ne_iff.mp hf ) ⟩ ⟩, Finset.mem_filter.mp ( Finset.max'_mem ( Finset.univ.filter fun i => f i ≠ 0 ) ⟨ Classical.choose ( Function.ne_iff.mp hf ), Finset.mem_filter.mpr ⟨ Finset.mem_univ _, Classical.choose_spec ( Function.ne_iff.mp hf ) ⟩ ⟩ ) |>.2, fun i hi => Classical.not_not.mp fun hi' => not_lt_of_ge ( Finset.le_max' _ _ <| by aesop ) hi ⟩

/-
The shortest non-zero vector in the lattice cannot be shorter than the shortest Gram–Schmidt vector of any basis.
-/
theorem shortestVectorLength_ge_gramSchmidt_minNorm
  {n : ℕ+}
  (L : EuclideanLattice n n)
  (B : SquareLatticeBasis n)
  (h : isBasisFor B L) :
  minNorm (InnerProductSpace.gramSchmidt ℝ B.basis) ≤ EuclideanLattice.shortestVectorLength L := by
  refine le_csInf ?_ ?_
  · -- nonempty set of norms
    obtain ⟨v, hv, _⟩ := L.exists_shortest_vector
    exact ⟨‖v‖, ⟨⟨v, hv⟩, rfl⟩⟩
  · rintro b ⟨w, rfl⟩
    -- move membership to the lattice generated by `B`
    have h_carrier : B.toLattice.carrier = L.carrier := by
      simpa [isBasisFor, EuclideanLattice.CarrierEquiv] using h
    have hwB : (w : 𝓔 n) ∈ B.toLattice := by
      -- rewrite membership via carrier equality
      rw [EuclideanLattice.mem_def]
      -- goal: w ∈ B.toLattice.carrier
      rw [h_carrier]
      -- goal: w ∈ L.carrier
      exact w.property.1

    -- extract integer coefficients in the basis `B`
    obtain ⟨c, hc⟩ : ∃ c : Fin n → ℤ, (w : 𝓔 n) = ∑ i, c i • B.basis i := by
      rcases (EuclideanLattice.mem_iff_exists_coeffs (B.toLattice) (w : 𝓔 n)).1 hwB with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      simpa [LatticeBasis.cols] using hc

    -- pick the largest nonzero coefficient
    have hc_ne : c ≠ 0 := by
      intro hc0
      have : (w : 𝓔 n) = 0 := by
        simpa [hc0] using hc
      exact w.property.2 this
    obtain ⟨k, hk_ne_zero, hk_max⟩ := exists_max_nonzero_index c hc_ne

    -- switch to real coefficients for Gram–Schmidt
    let cR : Fin n → ℝ := fun i => (c i : ℝ)
    have hcR : (w : 𝓔 n) = ∑ i, cR i • B.basis i := by
      simpa [cR, Int.cast_smul_eq_zsmul] using hc
    have hk_max' : ∀ i, k < i → cR i = 0 := by
      intro i hi
      have : c i = 0 := hk_max i hi
      simp [cR, this]

    -- project onto the k-th Gram–Schmidt vector
    have h_proj : inner ℝ (w : 𝓔 n) (gramSchmidt ℝ B.basis k) =
        (c k : ℝ) * ‖gramSchmidt ℝ B.basis k‖ ^ 2 := by
      simpa [cR] using
        (projection_on_gramSchmidt_of_max_index B cR k hk_max' (w : 𝓔 n) hcR)

    -- Cauchy–Schwarz and integer coefficient bound
    have h_cauchy_schwarz : |inner ℝ (w : 𝓔 n) (gramSchmidt ℝ B.basis k)| ≤
        ‖(w : 𝓔 n)‖ * ‖gramSchmidt ℝ B.basis k‖ := by
      exact abs_real_inner_le_norm _ _
    have h_norm_gramSchmidt : ‖gramSchmidt ℝ B.basis k‖ ≤ ‖(w : 𝓔 n)‖ := by
      rw [h_proj, abs_mul, abs_sq] at h_cauchy_schwarz
      nlinarith [show (|↑(c k)| : ℝ) ≥ 1 by exact mod_cast abs_pos.mpr hk_ne_zero,
        norm_nonneg (w : 𝓔 n), norm_nonneg (gramSchmidt ℝ B.basis k)]
    exact le_trans (minNorm_le _ k) h_norm_gramSchmidt

end gram_schmidt

end LatticeCrypto.Foundations.Lattice
