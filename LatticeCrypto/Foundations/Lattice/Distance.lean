import LatticeCrypto.Foundations.Lattice.FundamentalDomain
import LatticeCrypto.Foundations.Lattice.SuccessiveMinima

namespace LatticeCrypto.Foundations.Lattice
/-!
  # The covering radius
  * Definition of the covering radius of a lattice
  * Relation between the covering radius and the shortest vector length of the dual lattice
  `EuclideanLattice.coveringRadius_ge_half_succMinₙ (L : EuclideanLattice n n) : L.μ ≥ L.succMinₙ / 2`
-/
open LatticeCrypto.Utils.Vec

variable {n k : ℕ+}

/-!
## Distance to a lattice
-/

/--
  The distance from a point x to the lattice L is defined as the distances
  from x to the nearest lattice point(s).
-/
noncomputable def EuclideanLattice.distanceToLattice (x : 𝓔 n) (L : EuclideanLattice n k) : ℝ :=
  sInf { ‖x - (v : 𝓔 n)‖ | v ∈ L.carrier }

/-- Any lattice point gives an upper bound on `distanceToLattice`. -/
lemma distanceToLattice_le_norm_sub_of_mem
    (L : EuclideanLattice n k) (t v : 𝓔 n) (hv : v ∈ L) :
    L.distanceToLattice t ≤ ‖t - v‖ := by
  unfold EuclideanLattice.distanceToLattice
  exact csInf_le
    ⟨0, by
      rintro r ⟨w, hw, rfl⟩
      exact norm_nonneg _⟩
    ⟨v, hv, rfl⟩

/-- Existence of a closest lattice point to `t` (for the lattice model used in this development). -/
theorem exists_closest_lattice_point
    (L : EuclideanLattice n k) (t : 𝓔 n) :
    ∃ y : 𝓔 n, y ∈ L ∧ ‖t - y‖ = L.distanceToLattice t := by
  have hne : (L.carrier : Set (𝓔 n)).Nonempty := ⟨0, L.zero_mem⟩
  have hclosed : IsClosed (L.carrier : Set (𝓔 n)) := by
    simpa using (EuclideanLattice.isClosed (L := L))
  obtain ⟨y, hy, hyDist⟩ := hclosed.exists_infDist_eq_dist hne t
  refine ⟨y, ?_, ?_⟩
  · simpa [EuclideanLattice.mem_def] using hy
  · have hyL : y ∈ L := by
      simpa [EuclideanLattice.mem_def] using hy
    have hy_min : ∀ v : 𝓔 n, v ∈ L.carrier → ‖t - y‖ ≤ ‖t - v‖ := by
      intro v hv
      have h_inf_le : Metric.infDist t (L.carrier : Set (𝓔 n)) ≤ dist t v :=
        Metric.infDist_le_dist_of_mem hv
      calc
        ‖t - y‖ = dist t y := by simp [dist_eq_norm]
        _ = Metric.infDist t (L.carrier : Set (𝓔 n)) := hyDist.symm
        _ ≤ dist t v := h_inf_le
        _ = ‖t - v‖ := by simp [dist_eq_norm]
    have h_lower : ‖t - y‖ ≤ L.distanceToLattice t := by
      unfold EuclideanLattice.distanceToLattice
      refine le_csInf ?_ ?_
      · exact ⟨‖t - y‖, ⟨y, hyL, rfl⟩⟩
      · intro r hr
        rcases hr with ⟨v, hv, rfl⟩
        exact hy_min v hv
    have h_upper : L.distanceToLattice t ≤ ‖t - y‖ := by
      exact distanceToLattice_le_norm_sub_of_mem (L := L) (t := t) (v := y) hyL
    exact le_antisymm h_lower h_upper

/-- The distance to lattice is invariant under translation by a lattice vector -/
theorem distanceToLattice_translation_invariant (L : EuclideanLattice n k) (t v : 𝓔 n) (hv : v ∈ L) :
    L.distanceToLattice (t + v) = L.distanceToLattice t := by
  apply le_antisymm
  · refine le_csInf ?_ ?_
    · exact ⟨‖t - 0‖, ⟨0, L.zero_mem, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨w, hw, rfl⟩
      have hw' : w + v ∈ L := L.add_mem hw hv
      have h_le : L.distanceToLattice (t + v) ≤ ‖(t + v) - (w + v)‖ :=
        distanceToLattice_le_norm_sub_of_mem (L := L) (t := t + v) (v := w + v) hw'
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h_le
  · refine le_csInf ?_ ?_
    · exact ⟨‖t + v - 0‖, ⟨0, L.zero_mem, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨w, hw, rfl⟩
      have hw' : w - v ∈ L := L.sub_mem hw hv
      have h_le : L.distanceToLattice t ≤ ‖t - (w - v)‖ :=
        distanceToLattice_le_norm_sub_of_mem (L := L) (t := t) (v := w - v) hw'
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h_le

section covering_radius

open scoped Real Complex MeasureTheory
open scoped RealInnerProductSpace
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry

variable {n : ℕ+} (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s)

/--
  The covering radius of a lattice L is defined as the smallest radius r such that
  every point in the ambient space is within distance r of some lattice point.
-/
noncomputable def EuclideanLattice.coveringRadius (L : EuclideanLattice n n) : ℝ :=
  sInf { r : ℝ | ∀ x : 𝓔 n, ∃ v ∈ L.carrier, ‖x - (v : 𝓔 n)‖ ≤ r }

/-
The distance from any point to the lattice is bounded by some constant M.
-/
lemma distanceToLattice_bounded (L : EuclideanLattice n n) :
  ∃ M, ∀ x : 𝓔 n, L.distanceToLattice x ≤ M := by
    have := LatticeBasis.fundamentalDomain_isBounded L.basis;
    obtain ⟨ M, hM ⟩ := this.exists_pos_norm_le; use M; intro x; exact (by
    obtain ⟨ u, v, hu, hv, rfl ⟩ := LatticeBasis.eq_lattice_add_mod L.basis x;
    refine' le_trans ( csInf_le _ _ ) ( hM.2 v hv );
    · exact ⟨ 0, by rintro x ⟨ w, hw, rfl ⟩ ; exact norm_nonneg _ ⟩;
    · use u; aesop;);

/--
  Alternative definition of the covering radius as the maximum distance from any point to the lattice
-/
noncomputable def EuclideanLattice.coveringRadius' (L : EuclideanLattice n n) : ℝ :=
  sSup { L.distanceToLattice x | x : 𝓔 n }


/-- The two definitions are equivalent -/
theorem EuclideanLattice.coveringRadius_eq_alt_def (L : EuclideanLattice n n) :
  L.coveringRadius = L.coveringRadius' := by
  have h_sup : ∀ x : 𝓔 n, ∃ v ∈ L.carrier, ‖x - (v : 𝓔 n)‖ ≤ L.distanceToLattice x := by
    intro x;
    have h_inf : ∃ v ∈ L.carrier, ∀ w ∈ L.carrier, ‖x - v‖ ≤ ‖x - w‖ := by
      have h_closed : IsClosed (L.carrier : Set (𝓔 n)) := by
        exact isClosed L;
      have h_compact : IsCompact {v ∈ L.carrier | ‖x - v‖ ≤ ‖x‖ + 1} := by
        have h_compact : IsCompact {v ∈ L.carrier | ‖v‖ ≤ ‖x‖ + 1 + ‖x‖} := by
          exact ( Metric.isCompact_iff_isClosed_bounded.mpr ⟨ h_closed.inter ( isClosed_le continuous_norm continuous_const ), isBounded_iff_forall_norm_le.mpr ⟨ ‖x‖ + 1 + ‖x‖, fun v hv => hv.2 ⟩ ⟩ );
        refine' h_compact.of_isClosed_subset _ _;
        · exact h_closed.inter ( isClosed_le ( continuous_norm.comp ( continuous_const.sub continuous_id' ) ) continuous_const );
        · intro v hv; exact ⟨ hv.1, by have := hv.2; have := norm_sub_le ( x - v ) x; norm_num at *; linarith ⟩ ;
      have h_inf : ∃ v ∈ {v ∈ L.carrier | ‖x - v‖ ≤ ‖x‖ + 1}, ∀ w ∈ {v ∈ L.carrier | ‖x - v‖ ≤ ‖x‖ + 1}, ‖x - v‖ ≤ ‖x - w‖ := by
        have h_exists_min : ContinuousOn (fun v => ‖x - v‖) {v ∈ L.carrier | ‖x - v‖ ≤ ‖x‖ + 1} := by
          exact Continuous.continuousOn ( continuous_norm.comp ( continuous_const.sub continuous_id' ) )
        generalize_proofs at *;
        exact h_compact.exists_isMinOn ⟨ 0, by aesop ⟩ h_exists_min;
      obtain ⟨ v, hv₁, hv₂ ⟩ := h_inf;
      exact ⟨ v, hv₁.1, fun w hw => if hw' : ‖x - w‖ ≤ ‖x‖ + 1 then hv₂ w ⟨ hw, hw' ⟩ else by linarith [ hv₁.2, norm_sub_le x w ] ⟩;
    obtain ⟨ v, hv₁, hv₂ ⟩ := h_inf;
    exact ⟨ v, hv₁, le_csInf ⟨ _, ⟨ v, hv₁, rfl ⟩ ⟩ fun w hw => by aesop ⟩;
  refine' csInf_eq_of_forall_ge_of_forall_gt_exists_lt _ _ _;
  · have := distanceToLattice_bounded L;
    exact ⟨ this.choose, fun x => by obtain ⟨ v, hv₁, hv₂ ⟩ := h_sup x; exact ⟨ v, hv₁, hv₂.trans ( this.choose_spec x ) ⟩ ⟩;
  · intro r hr;
    exact csSup_le ⟨ _, ⟨ 0, rfl ⟩ ⟩ fun x hx => by rcases hx with ⟨ x, rfl ⟩ ; exact le_trans ( csInf_le ⟨ 0, by rintro x ⟨ y, hy, rfl ⟩ ; positivity ⟩ ⟨ _, hr x |> Classical.choose_spec |> And.left, rfl ⟩ ) ( hr x |> Classical.choose_spec |> And.right ) ;
  · intro w hw;
    refine' ⟨ _, fun x => _, hw ⟩;
    exact Exists.elim ( h_sup x ) fun v hv => ⟨ v, hv.1, le_csSup ( show BddAbove { EuclideanLattice.distanceToLattice x L | x : LatticeCrypto.Utils.Vec.𝓔 n } from by
                   obtain ⟨ M, hM ⟩ := distanceToLattice_bounded L; exact ⟨ M, by rintro _ ⟨ y, rfl ⟩ ; exact hM y ⟩ ; ) ( Set.mem_range_self x ) |> le_trans hv.2 ⟩

/-- The covering radius is non-negative -/
theorem EuclideanLattice.coveringRadius_nonneg (L : EuclideanLattice n n) : 0 ≤ L.coveringRadius := by
  -- The covering radius is defined as the infimum of a set of radii, each of which is non-negative.
  apply Real.sInf_nonneg;
  -- If there exists a v in the lattice such that ‖x - v‖ ≤ r, then since the norm is non-negative, r must be non-negative.
  intros r hr
  obtain ⟨v, hvL, hv⟩ := hr 0
  have h_nonneg : 0 ≤ r := by
    exact le_trans ( norm_nonneg _ ) hv
  exact h_nonneg

/-- notation μ(L) as the covering radius of L -/
noncomputable abbrev EuclideanLattice.μ (L : EuclideanLattice n n) : ℝ :=
  L.coveringRadius

theorem EuclideanLattice.coveringRadius_scale (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) :
  (L.smul s hs.ne.symm).μ = s * L.μ := by
  -- By definition of μ, we have μ(L.smul s) = infimum {r | ∀ x, ∃ v ∈ L.smul s, ‖x - v‖ ≤ r}.
  simp [EuclideanLattice.μ];
  unfold EuclideanLattice.coveringRadius;
  rw [ ← smul_eq_mul, ← Real.sInf_smul_of_nonneg hs.le ];
  congr with r ; simp +decide ;
  -- To prove the equivalence, we show that the two conditions are equivalent by substituting $x$ with $s * x$ and $v$ with $s * v$.
  apply Iff.intro;
  · -- By definition of scalar multiplication, if for every x there exists a v in the span of the scaled basis such that ‖x - v‖ ≤ r, then for every x there exists a v in the span of the original basis such that ‖x - v‖ ≤ r / s.
    intro h
    have h_scaled : ∀ x : 𝓔 n, ∃ v ∈ Submodule.span ℤ (Set.range L.basis.basis), ‖x - v‖ ≤ r / s := by
      intro x
      obtain ⟨v, hv⟩ := h (s • x);
      -- Since $v$ is in the span of the scaled basis, we can write $v = s * w$ for some $w$ in the span of the original basis.
      obtain ⟨w, hw⟩ : ∃ w ∈ Submodule.span ℤ (Set.range L.basis.basis), v = s • w := by
        have h_scaled : v ∈ Submodule.span ℤ (Set.range (fun i => s • L.basis.basis i)) := by
          convert hv.1 using 1;
        rw [ Submodule.mem_span_range_iff_exists_fun ] at h_scaled;
        obtain ⟨ c, rfl ⟩ := h_scaled; use ∑ i, c i • L.basis.basis i; simp +decide [ Finset.smul_sum ] ;
        exact ⟨ Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ( Submodule.subset_span ( Set.mem_range_self _ ) ), Finset.sum_congr rfl fun _ _ => by rw [ SMulCommClass.smul_comm ] ⟩;
      simp_all +decide ;
      exact ⟨ w, hw.1, by rw [ le_div_iff₀' hs ] ; simpa [ ← smul_sub, norm_smul, abs_of_pos hs ] using hv.2 ⟩;
    exact ⟨ r / s, h_scaled, by simp +decide [ mul_div_cancel₀ _ hs.ne' ] ⟩;
  · rintro ⟨ r, hr, rfl ⟩ x;
    obtain ⟨ v, hv₁, hv₂ ⟩ := hr ( s⁻¹ • x );
    refine' ⟨ s • v, _, _ ⟩ <;> simp_all +decide ;
    · rw [ Submodule.mem_span ] at *;
      intro p hp; specialize hv₁ ( p.comap ( s • LinearMap.id ) ) ; simp_all +decide [ Set.range_subset_iff ] ;
      exact hv₁ fun y => by simpa [ Algebra.smul_def ] using hp y;
    · convert mul_le_mul_of_nonneg_left hv₂ hs.le using 1 ; rw [ ← norm_smul_of_nonneg hs.le ] ; simp +decide [ smul_sub, smul_smul, hs.ne' ]

theorem EuclideanLattice.coveringRadius_scale_dual (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) :
  (L.smul s hs.ne.symm).dual.μ = L.dual.μ / s := by
  -- The dual of a scaled lattice is the dual lattice scaled by the inverse of the scalar.
  have h_dual_scale : (L.smul s hs.ne.symm).dual = L.dual.smul (1 / s) (by
  grind) := by
    all_goals generalize_proofs at *;
    unfold LatticeCrypto.Foundations.Lattice.EuclideanLattice.dual LatticeCrypto.Foundations.Lattice.EuclideanLattice.smul
    generalize_proofs at *;
    -- By definition of matrix scaling, we have that $(s • A)^T⁻¹ = (1/s) • A^T⁻¹$.
    have h_dual_scale : (s • L.basis.asMatrix).transpose⁻¹ = (1 / s) • L.basis.asMatrix.transpose⁻¹ := by
      simp +decide [  Matrix.inv_def ];
      simp +decide [  Matrix.adjugate_smul, smul_smul, mul_comm ];
      cases n using PNat.recOn <;> simp_all +decide [ pow_succ, mul_assoc, mul_left_comm ]
    generalize_proofs at *;
    congr! 1
    generalize_proofs at *;
    ext i j; simp +decide  ;
    convert congr_fun ( congr_fun h_dual_scale j ) i using 1 ; ring_nf!;
    exact rfl
  generalize_proofs at *;
  -- Apply the definition of covering radius to the scaled lattice.
  rw [h_dual_scale];
  convert EuclideanLattice.coveringRadius_scale ( L.dual ) ( 1 / s ) ( one_div_pos.mpr hs ) using 1 ; ring

/-- The dimension of all lattice vectors shorter than L.succMinₙ is less than n -/
lemma span_lt_succMin_dim_lt_n (L : EuclideanLattice n n) :
  Module.rank ℝ (Submodule.span ℝ { v : 𝓔 n | v ∈ L ∧ ‖v‖ < L.succMinₙ }) < n := by
    -- Consider the set of lattice vectors with length strictly smaller than the n-th successive minimum.
    set S := {v : L.carrier | ‖(v : 𝓔 n)‖ < L.succMinₙ};
    -- We show that if these vectors are linearly independent and their number is $n$, they form a basis for $\mathbb{R}^n$, then there must be one vector longer than L.succMinₙ.
    have h_basis : ∀ (v : Fin n → L.carrier), LinearIndependent ℝ (fun i => (v i : 𝓔 n)) → ∃ i, ‖(v i : 𝓔 n)‖ ≥ L.succMinₙ := by
      intro v hv_linear_indep
      by_contra h_contra
      push_neg at h_contra
      have h_span : Submodule.span ℝ (Set.range (fun i => (v i : 𝓔 n))) = ⊤ := by
        refine' Submodule.eq_top_of_finrank_eq _;
        rw [ finrank_span_eq_card ] <;> aesop;
      -- By definition of $L.succMinₙ$, we know that $L.succMinₙ \leq \sup_{x \in \mathbb{R}^n \setminus \{0\}} \frac{\|x\|}{\min_{v \in L \setminus \{0\}} \|x - v\|}$.
      have h_succ_min : L.succMinₙ ≤ sInf {r : ℝ | ∃ (v : Fin n → L.carrier), LinearIndependent ℝ (fun i => (v i : 𝓔 n)) ∧ ∀ i, ‖(v i : 𝓔 n)‖ ≤ r} := by
        exact le_csInf ⟨ L.succMinₙ, ⟨ v, hv_linear_indep, fun i => le_of_lt ( h_contra i ) ⟩ ⟩ fun r hr => by rcases hr with ⟨ v, hv_linear_indep, hv_bound ⟩ ; exact (by
        apply_rules [ csInf_le ];
        · exact ⟨ 0, fun r hr => hr.1.le ⟩;
        · refine' ⟨ _, Finset.image ( fun i => ( v i : 𝓔 n ) ) Finset.univ, _, _, _ ⟩ <;> simp_all +decide ;
          · exact lt_of_lt_of_le ( norm_pos_iff.mpr <| show ( v 0 : 𝓔 n ) ≠ 0 from by intro h; simpa [ h ] using hv_linear_indep.ne_zero 0 ) ( hv_bound 0 );
          ·
            have h1 : (1 : Nat) ≤ (↑n : Nat) := by
              simpa using (Nat.succ_le_iff.mpr n.pos)
            rw [
              Finset.card_image_of_injective _ fun i j hij => by
                simpa [hv_linear_indep.ne_zero] using
                  hv_linear_indep.injective <| by simpa using hij,
              Finset.card_fin,
              Nat.sub_add_cancel h1
            ];
          · exact fun i => ⟨ v i |>.2, by intro hi; simpa [ hi ] using hv_linear_indep.ne_zero i ⟩;
          · convert hv_linear_indep.comp _ _;
            rotate_left;
            use fun x => Classical.choose ( Finset.mem_image.mp x.2 );
            · intro x y hxy; have := Classical.choose_spec ( Finset.mem_image.mp x.2 ) ; have := Classical.choose_spec ( Finset.mem_image.mp y.2 ) ; aesop;
            · ext ⟨ x, hx ⟩ ; have := Classical.choose_spec ( Finset.mem_image.mp hx ) ; aesop;);
      -- Since $v$ is a basis for $\mathbb{R}^n$, we can choose $r = \max_{i} \|v_i\|$.
      obtain ⟨r, hr⟩ : ∃ r, ∀ i, ‖(v i : 𝓔 n)‖ ≤ r ∧ r < L.succMinₙ := by
        have h_max : ∃ i, ∀ j, ‖(v j : 𝓔 n)‖ ≤ ‖(v i : 𝓔 n)‖ := by
          simpa using Finset.exists_max_image Finset.univ ( fun i => ‖ ( v i : 𝓔 n )‖ ) ⟨ 0, Finset.mem_univ 0 ⟩;
        exact ⟨ ‖ ( v h_max.choose : 𝓔 n )‖, fun i => ⟨ h_max.choose_spec i, h_contra _ ⟩ ⟩;
      exact not_le_of_gt ( hr 0 |>.2 ) ( h_succ_min.trans <| csInf_le ⟨ 0, by rintro x ⟨ v, hv_linear_indep, hv ⟩ ; exact le_trans ( norm_nonneg _ ) ( hv 0 ) ⟩ ⟨ v, hv_linear_indep, fun i => hr i |>.1 ⟩ );
    contrapose! h_basis;
    have := exists_linearIndependent ℝ ( { v : 𝓔 n | ∃ w : L.carrier, w ∈ S ∧ v = w } : Set ( 𝓔 n ) );
    obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := this;
    have h_card : Cardinal.mk b ≥ n := by
      have h_card : Module.rank ℝ (Submodule.span ℝ b) ≥ n := by
        refine' le_trans h_basis _;
        refine' Submodule.rank_mono _;
        rw [ hb₂ ];
        exact Submodule.span_mono fun x hx => ⟨ ⟨ x, hx.1 ⟩, hx.2, rfl ⟩;
      rw [ rank_span_set ] at h_card ; aesop;
      exact hb₃;
    have := Cardinal.le_mk_iff_exists_set.mp h_card;
    obtain ⟨ p, hp ⟩ := this;
    -- Since $p$ is a subset of $b$ with cardinality $n$, we can define a function $v : Fin n → L.carrier$ such that $v i$ is the $i$-th element of $p$.
    obtain ⟨v, hv⟩ : ∃ v : Fin n → b, Function.Injective v := by
      have := Cardinal.eq.1 hp;
      obtain ⟨ v ⟩ := this; exact ⟨ fun i => v.symm ( ULift.up i ) |>.1, fun i j hij => by simpa [ Fin.ext_iff ] using v.symm.injective <| Subtype.ext hij ⟩ ;
    choose w hw₁ hw₂ using fun i => hb₁ ( v i |>.2 );
    use w;
    exact ⟨ by simpa [ ← hw₂ ] using hb₃.comp _ ( by simpa [ Function.Injective ] using hv ), fun i => hw₁ i ⟩

/-
If a subspace has dimension less than n, there exists a vector of any given norm orthogonal to it.
-/
lemma exists_norm_eq_orth_of_dim_lt (W : Submodule ℝ (𝓔 n)) (hW : Module.rank ℝ W < n) (r : ℝ) (hr : 0 ≤ r) :
  ∃ x : 𝓔 n, ‖x‖ = r ∧ ∀ w ∈ W, ⟪x, w⟫ = 0 := by
    -- Since W is a proper subspace, there exists a non-zero vector u orthogonal to W.
    obtain ⟨u, hu⟩ : ∃ u : 𝓔 n, u ≠ 0 ∧ ∀ w ∈ W, ⟪u, w⟫ = 0 := by
      -- Since W is a proper subspace, its orthogonal complement is non-trivial.
      have h_orthogonal_complement_nontrivial : ∃ u : 𝓔 n, u ≠ 0 ∧ ∀ w ∈ W, ⟪u, w⟫ = 0 := by
        have hW_lt_n : Module.finrank ℝ W < n := by
          exact Module.finrank_lt_of_rank_lt hW
        have h_orthogonal_complement_nontrivial : W ≠ ⊤ := by
          aesop;
        have h_orthogonal_complement_nontrivial : ∃ u : 𝓔 n, u ≠ 0 ∧ u ∈ Wᗮ := by
          exact ( Submodule.ne_bot_iff _ ).mp ( show Wᗮ ≠ ⊥ from fun h => h_orthogonal_complement_nontrivial <| by rw [ Submodule.orthogonal_eq_bot_iff ] at *; aesop ) |> fun ⟨ u, hu ⟩ => ⟨ u, by aesop ⟩;
        exact ⟨ h_orthogonal_complement_nontrivial.choose, h_orthogonal_complement_nontrivial.choose_spec.1, fun w hw => by simpa [ real_inner_comm ] using h_orthogonal_complement_nontrivial.choose_spec.2 w hw ⟩;
      exact h_orthogonal_complement_nontrivial;
    -- Let $x = \frac{r}{\|u\|} u$. Then $\|x\| = r$ and $x$ is orthogonal to $W$.
    use (r / ‖u‖) • u;
    simp_all +decide [ norm_smul, inner_smul_left ]

/-
The covering radius of a lattice is at least half the length of its n-th successive minima.
-/
theorem EuclideanLattice.coveringRadius_ge_half_succMinₙ (L : EuclideanLattice n n) :
  L.μ ≥ L.succMinₙ / 2 := by
    -- Let $S = \{ v \in L \mid \|v\| < L.succMinₙ \}$. By `span_lt_succMin_dim_lt_n`, $W = \text{span}(S)$ has rank $< n$.
    set S := {v : 𝓔 n | v ∈ L.carrier ∧ ‖v‖ < L.succMinₙ} with hS_def
    set W := Submodule.span ℝ S with hW_def
    have hW_rank : Module.rank ℝ W < n := by
      have := span_lt_succMin_dim_lt_n L; aesop;
    -- By `exists_norm_eq_orth_of_dim_lt` with $r = L.succMinₙ / 2$, there exists $x$ with $\|x\| = r$ and $x \perp W$.
    obtain ⟨x, hx_norm, hx_orth⟩ : ∃ x : 𝓔 n, ‖x‖ = L.succMinₙ / 2 ∧ ∀ w ∈ W, ⟪x, w⟫ = 0 := by
      have := exists_norm_eq_orth_of_dim_lt W hW_rank ( L.succMinₙ / 2 ) ( by linarith [ show 0 ≤ L.succMinₙ by exact le_of_lt ( show 0 < L.succMinₙ from by exact
        (successiveMinima_pos L ⟨↑n - 1, succMinₙ._proof_1⟩) ) ] );
      exact this;
    -- We claim $dist(x, L) \ge r$.
    have h_dist_ge_r : ∀ v ∈ L.carrier, ‖x - (v : 𝓔 n)‖ ≥ L.succMinₙ / 2 := by
      intro v hv_mem; by_cases hv : v ∈ S <;> simp_all +decide ;
      · -- Since $x \perp v$, we have $\|x - v\|^2 = \|x\|^2 + \|v\|^2$.
        have h_norm_sq : ‖x - v‖^2 = ‖x‖^2 + ‖v‖^2 := by
          rw [ @norm_sub_sq ℝ ] ; aesop;
        nlinarith [ norm_nonneg x, norm_nonneg v, norm_nonneg ( x - v ) ];
      · have := norm_sub_le ( x - v ) x ; norm_num at * ; linarith;
    have h_dist_ge_r_all : L.distanceToLattice x ≥ L.succMinₙ / 2 := by
      exact le_csInf ⟨ _, ⟨ 0, L.zero_mem, rfl ⟩ ⟩ fun y hy => by rcases hy with ⟨ v, hv, rfl ⟩ ; exact h_dist_ge_r v hv;
    -- Since the covering radius is the supremum of the distances from any point to the lattice, and we have a point x where the distance is at least L.succMinₙ / 2, the supremum must be at least that value.
    have h_sup_ge : sSup {L.distanceToLattice x | x : 𝓔 n} ≥ L.succMinₙ / 2 := by
      refine' le_trans h_dist_ge_r_all ( le_csSup _ ⟨ x, rfl ⟩ );
      have := distanceToLattice_bounded L;
      exact ⟨ this.choose, fun x hx => hx.choose_spec ▸ this.choose_spec _ ⟩;
    convert h_sup_ge using 1;
    convert L.coveringRadius_eq_alt_def

end covering_radius

end LatticeCrypto.Foundations.Lattice
