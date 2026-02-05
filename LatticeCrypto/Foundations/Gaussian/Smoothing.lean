import LatticeCrypto.Foundations.Gaussian.Defs
import LatticeCrypto.Foundations.Gaussian.Fourier
import LatticeCrypto.Foundations.Gaussian.PoissonSummation
import LatticeCrypto.Foundations.Gaussian.Banaszczyk
import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Foundations.Lattice.FundamentalDomain
import LatticeCrypto.Foundations.Lattice.SuccessiveMinima
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec


namespace LatticeCrypto.Foundations.Gaussian

/-!
  # Smoothing Parameter
-/
noncomputable section defs

open scoped Real Complex MeasureTheory
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Foundations.Lattice

variable {n : ℕ+}

/-!
  For an ε > 0, the smoothing parameter η(ε, L) of a lattice L is the smallest s > 0 such that ρ_(1/s)(L.dual \setminus {0}) ≤ ε.
-/
def _root_.LatticeCrypto.Foundations.Lattice.EuclideanLattice.smoothingParameter {n : ℕ+} (L : EuclideanLattice n n) (ε : ℝ) : ℝ :=
  sInf { s : ℝ | 0 < s ∧ rhoSMass (1 / s) (0 : 𝓔 n) (L.dual) ≤ 1 + ε }

def _root_.LatticeCrypto.Foundations.Lattice.EuclideanLattice.smoothingParameter' {n : ℕ+} (L : EuclideanLattice n n) (ε : ℝ) : ℝ :=
  sInf { s : ℝ | 0 < s ∧ rhoSMassOn (1 / s) (0 : 𝓔 n) L.dual {0}ᶜ ≤ ε }

theorem smoothingParameter_eq_smoothingParameter' (L : EuclideanLattice n n) (ε : ℝ) :
    L.smoothingParameter ε = L.smoothingParameter' ε :=
  by
  -- By definition of smoothing parameter, we know that the sets are equal.
  have h_sets_eq : {s : ℝ | 0 < s ∧ rhoSMass (1 / s) 0 L.dual ≤ 1 + ε} = {s : ℝ | 0 < s ∧ rhoSMassOn (1 / s) 0 L.dual {0}ᶜ ≤ ε} := by
    ext s;
    constructor <;> intro h <;> have := rhoSMass_eq_one_add_rhoSMassOn_nonzero L.dual ( 1 / s ) ( one_div_pos.mpr h.1 ) <;> aesop;
  exact congr_arg _ h_sets_eq

def SmoothingSet {n : ℕ+} (L : EuclideanLattice n n) (ε : ℝ) : Set ℝ :=
  { s : ℝ | 0 < s ∧ rhoSMass (1 / s) (0 : 𝓔 n) (L.dual) ≤ 1 + ε }

def SmoothingSet' {n : ℕ+} (L : EuclideanLattice n n) (ε : ℝ) : Set ℝ :=
  { s : ℝ | 0 < s ∧ rhoSMassOn (1 / s) (0 : 𝓔 n) (L.dual) {0}ᶜ ≤ ε }

theorem smoothingSet_eq_smoothingSet' (L : EuclideanLattice n n) (ε : ℝ) :
    SmoothingSet L ε = SmoothingSet' L ε :=
  by
  -- By definition of smoothing parameter, we know that the sets are equal.
  unfold SmoothingSet SmoothingSet';
  ext s;
  constructor <;> intro h <;> have := rhoSMass_eq_one_add_rhoSMassOn_nonzero L.dual ( 1 / s ) ( one_div_pos.mpr h.1 ) <;> aesop;

theorem smoothingParameter_eq_sInf_smoothingSet (L : EuclideanLattice n n) (ε : ℝ) :
    L.smoothingParameter ε = sInf (SmoothingSet L ε) := by
  -- By definition of smoothing parameter, we know that the set defining η(ε, L) is exactly SmoothingSet L ε.
  unfold SmoothingSet;
  rfl

/-- notation μ(L) as the covering radius of L -/
noncomputable abbrev _root_.LatticeCrypto.Foundations.Lattice.EuclideanLattice.η (L : EuclideanLattice n n) (ε : ℝ) : ℝ :=
  L.smoothingParameter ε


noncomputable section AristotleLemmas

/-
As s goes to 0, rho_{1/s}(v) goes to 1.
-/
lemma rhoS_inv_tendsto_one (v : 𝓔 n) :
  Filter.Tendsto (fun s => rhoS (1/s) v) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    -- We'll use the fact that as $s \to 0$, $- \pi * \|v\|^2 * s^2 \to 0$.
    have h_arg : Filter.Tendsto (fun (s : ℝ) => -Real.pi * ‖v‖^2 * s^2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
    convert Real.continuous_exp.continuousAt.tendsto.comp h_arg using 2 ; norm_num [ LatticeCrypto.Foundations.Gaussian.rhoS ];
    · simp +decide [ mul_pow, norm_smul ] ; ring;
    · norm_num

/-
The sum of rho_{1/s}(v) over a finite set S tends to |S| as s -> 0.
-/
lemma sum_rhoS_inv_tendsto_card (L : EuclideanLattice n n) (S : Finset L.dual.carrier) :
    Filter.Tendsto (fun s => ∑ v ∈ S, rhoS (1/s) (v : 𝓔 n)) (nhdsWithin 0 (Set.Ioi 0)) (nhds S.card) := by
  have h_sum : ∀ v ∈ S, Filter.Tendsto (fun s : ℝ => rhoS (1 / s) (v : 𝓔 n)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    intro v hv
    exact rhoS_inv_tendsto_one (v : 𝓔 n)
  simpa using tendsto_finset_sum _ h_sum

/-
The dual lattice is infinite (since n >= 1).
-/
lemma infinite_dual (L : EuclideanLattice n n) : Set.Infinite (L.dual.carrier : Set (𝓔 n)) := by
  -- Since the dual lattice is full rank, there exists a non-zero vector in the dual lattice.
  obtain ⟨v, hv⟩ : ∃ v : 𝓔 n, v ∈ L.dual.carrier ∧ v ≠ 0 := by
    have h_dual_basis : ∃ b : Fin n → 𝓔 n, LinearIndependent ℝ b ∧ (∀ i, b i ∈ L.dual.carrier) ∧ (∀ i, b i ≠ 0) := by
      have := exists_dual_basis_bounded L;
      exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1, fun i => by intro hi; simpa [ hi ] using this.choose_spec.1.ne_zero i ⟩;
    exact ⟨ h_dual_basis.choose ⟨ 0, PNat.pos n ⟩, h_dual_basis.choose_spec.2.1 _, h_dual_basis.choose_spec.2.2 _ ⟩;
  have h_dual_infinite : Set.Infinite (Set.range (fun k : ℤ => (k : ℝ) • v)) := by
    exact Set.infinite_range_of_injective fun a b h => by simpa [ hv.2 ] using smul_left_injective ℝ hv.2 h;
  refine h_dual_infinite.mono ?_;
  rintro _ ⟨ k, rfl ⟩;
  convert L.dual.carrier.smul_mem k hv.1 using 1;
  exact Int.cast_smul_eq_zsmul ℝ k v

/-
The Gaussian mass rho_{1/s}(L*) tends to infinity as s tends to 0 from the right.
-/
theorem rhoSMass_inv_tendsto_atTop (L : EuclideanLattice n n) :
    Filter.Tendsto (fun s => rhoSMass (1/s) 0 L.dual) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
      -- By Lemma `sum_rhoS_inv_tendsto_card`, for any finite subset S of L.dual, the sum of rho_{1/s}(v) over v in S tends to the cardinality of S as s -> 0+.
      have h_finite_subset : ∀ M > 0, ∃ S : Finset L.dual.carrier, S.card > M := by
        intro M hMpos;
        have h_infinite : Infinite (L.dual.carrier : Set (𝓔 n)) := by
          exact Set.infinite_coe_iff.mpr ( infinite_dual L );
        have := h_infinite.natEmbedding;
        exact ⟨ Finset.image ( fun i => this i ) ( Finset.range ( M + 1 ) ), by rw [ Finset.card_image_of_injective _ this.injective ] ; simp +arith +decide ⟩;
      -- By Lemma `summable_rhoSMassOn`, for any finite subset S of L.dual, the sum over S is less than or equal to the total mass.
      have h_le_total : ∀ s : ℝ, 0 < s → ∀ S : Finset L.dual.carrier, ∑ v ∈ S, rhoS (1/s) (v : 𝓔 n) ≤ rhoSMass (1 / s) 0 L.dual := by
        intros s hs S
        have h_sum_le_total : ∑ v ∈ S, rhoS (1/s) (v : 𝓔 n) ≤ ∑' v : L.dual.carrier, rhoS (1/s) (v : 𝓔 n) := by
          refine' Summable.sum_le_tsum _ _ _;
          · exact fun _ _ => Real.exp_nonneg _;
          · have := summable_rhoSMassOn ( 1 / s ) ( one_div_pos.mpr hs ) 0 L.dual ( Set.univ : Set ( 𝓔 n ) ) ; aesop;
        convert h_sum_le_total using 1;
        unfold LatticeCrypto.Foundations.Gaussian.rhoSMass; aesop;
      -- By Lemma `sum_rhoS_inv_tendsto_card`, for any finite subset S of L.dual, the sum over S tends to the cardinality of S as s -> 0+.
      have h_tendsto_card : ∀ S : Finset L.dual.carrier, Filter.Tendsto (fun s : ℝ => ∑ v ∈ S, rhoS (1/s) (v : 𝓔 n)) (nhdsWithin 0 (Set.Ioi 0)) (nhds S.card) := by
        exact fun S => sum_rhoS_inv_tendsto_card L S;
      refine' Filter.tendsto_atTop.2 fun M => _;
      rcases h_finite_subset ( ⌈M⌉₊ + 1 ) ( by positivity ) with ⟨ S, hS ⟩ ; filter_upwards [ h_tendsto_card S |> fun h => h.eventually ( le_mem_nhds <| show ( S.card : ℝ ) > M by exact lt_of_lt_of_le ( Nat.lt_of_ceil_lt <| by linarith ) <| mod_cast le_rfl ), self_mem_nhdsWithin ] with s hs₁ hs₂ using le_trans hs₁ <| h_le_total s hs₂ S

/-
For any non-zero vector v, the function s ↦ ρ_{1/s}(v) tends to 0 as s tends to infinity.
-/
lemma tendsto_rhoS_inv_atTop_zero {n : ℕ+} (v : 𝓔 n) (hv : v ≠ 0) :
  Filter.Tendsto (fun s : ℝ => rhoS (1/s) v) Filter.atTop (nhds 0) := by
    norm_num [ rhoS, hv ];
    -- Since $v \neq 0$, we have $‖s • v‖^2 = s^2 * ‖v‖^2$.
    have h_norm_sq : ∀ s : ℝ, ‖s • v‖^2 = s^2 * ‖v‖^2 := by
      norm_num [ norm_smul, mul_pow ];
    norm_num [ h_norm_sq ];
    exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( Filter.Tendsto.atTop_mul_const ( by positivity ) ( by norm_num ) )

/-
For s >= 1, the Gaussian with parameter 1/s is bounded by the standard Gaussian.
-/
lemma rhoS_inv_le_rho_of_ge_one {n : ℕ+} (v : 𝓔 n) (s : ℝ) (hs : 1 ≤ s) :
  rhoS (1/s) v ≤ rho v := by
    unfold LatticeCrypto.Foundations.Gaussian.rhoS LatticeCrypto.Foundations.Gaussian.rho;
    field_simp;
    exact Real.exp_le_exp.mpr ( neg_le_neg <| mul_le_mul_of_nonneg_left ( by simpa [ norm_smul, abs_of_nonneg ( zero_le_one.trans hs ) ] using pow_le_pow_left₀ ( norm_nonneg _ ) ( show ‖v‖ ≤ s * ‖v‖ by exact le_mul_of_one_le_left ( norm_nonneg _ ) hs ) 2 ) <| by positivity )


/-
For s >= 1 and a non-zero lattice vector v, rho_{1/s}(v) is bounded by exp(-pi * (s^2 - 1) * lambda_1^2) * rho(v).
-/
lemma rhoS_inv_le_exp_mul_rho {n : ℕ+} (L : EuclideanLattice n n) (v : 𝓔 n) (hv : v ∈ L.nonzeroVectors) (s : ℝ) (hs : 1 ≤ s) :
  rhoS (1/s) v ≤ Real.exp (-Real.pi * (s^2 - 1) * L.succMin₁^2) * rho v := by
    -- Since ‖v‖ ≥ L.succMin₁, we have ‖v‖^2 ≥ L.succMin₁^2. Therefore, -(π/s^2) * ‖v‖^2 ≤ -(π/s^2) * L.succMin₁^2.
    have h_norm_sq : ‖v‖^2 ≥ L.succMin₁^2 := by
      have h_norm_sq_bound : ‖v‖ ≥ L.succMin₁ := by
        have := L.successiveMinima_one
        exact EuclideanLattice.norm_ge_successiveMinima_one L v hv;
      exact pow_le_pow_left₀ ( by exact le_of_lt ( by exact
        (EuclideanLattice.successiveMinima_pos L ⟨0, PNat.pos n⟩) ) ) h_norm_sq_bound 2;
    simp_all +decide [ LatticeCrypto.Foundations.Gaussian.rhoS, LatticeCrypto.Foundations.Gaussian.rho ];
    rw [ ← Real.exp_add ] ; norm_num [ norm_smul, mul_pow ];
    nlinarith [ show 0 ≤ Real.pi * ( s ^ 2 - 1 ) by exact mul_nonneg Real.pi_pos.le ( by nlinarith ) ]

/-
Dominated convergence theorem for series: if terms are dominated by a summable function and tend to 0, the sum tends to 0.
-/
lemma tendsto_tsum_zero_of_dominated_real {α : Type*} (f : α → ℝ) (hf : Summable f) (g : ℝ → α → ℝ)
  (hg_le : ∀ s, 1 ≤ s → ∀ a, |g s a| ≤ f a)
  (hg_lim : ∀ a, Filter.Tendsto (g · a) Filter.atTop (nhds 0)) :
  Filter.Tendsto (fun s => ∑' a, g s a) Filter.atTop (nhds 0) := by
    -- Let's choose any $\epsilon > 0$.
    have h_eps : ∀ ε > 0, ∃ T : ℝ, ∀ s ≥ T, |∑' a, g s a| < ε := by
      intro ε hε;
      -- Since `f` is summable, there exists a finite set `S` such that `∑_{a \notin S} f a < ε / 2` (using `summable_sum_compl_lt`).
      obtain ⟨S, hS⟩ : ∃ S : Finset α, ∑' a, f a - ∑ a ∈ S, f a < ε / 2 := by
        have h_summable : Filter.Tendsto (fun S : Finset α => ∑ a ∈ S, f a) Filter.atTop (nhds (∑' a, f a)) := by
          exact hf.hasSum;
        exact Filter.Eventually.exists ( h_summable.eventually ( Metric.ball_mem_nhds _ ( half_pos hε ) ) ) |> fun ⟨ S, hS ⟩ => ⟨ S, by linarith [ abs_lt.mp hS ] ⟩;
      -- For each `a \in S`, `g s a \to 0`, so there exists `T_a` such that for `s \ge T_a`, `|g s a| < ε / (2 * |S| + 1)`.
      obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ s ≥ T, ∀ a ∈ S, |g s a| < ε / (2 * S.card + 1) := by
        have hT : ∀ a ∈ S, ∃ T_a : ℝ, ∀ s ≥ T_a, |g s a| < ε / (2 * S.card + 1) := by
          exact fun a ha => by rcases Metric.tendsto_atTop.mp ( hg_lim a ) ( ε / ( 2 * ( S.card : ℝ ) + 1 ) ) ( by positivity ) with ⟨ T, hT ⟩ ; exact ⟨ T, fun s hs => by simpa using hT s hs ⟩ ;
        choose! T hT using hT;
        exact ⟨ ∑ a ∈ S, |T a| + 1, fun s hs a ha => by nlinarith [ hT a ha s ( by linarith [ abs_le.mp ( Finset.single_le_sum ( fun a _ => abs_nonneg ( T a ) ) ha ) ] ), abs_le.mp ( Finset.single_le_sum ( fun a _ => abs_nonneg ( T a ) ) ha ), mul_div_cancel₀ ε ( by positivity : ( 2 * ( S.card : ℝ ) + 1 ) ≠ 0 ) ] ⟩;
      -- For `s ≥ T`, we can bound the sum as follows:
      have h_bound : ∀ s ≥ max T 1, |∑' a, g s a| ≤ ∑ a ∈ S, |g s a| + ∑' a, f a - ∑ a ∈ S, f a := by
        intro s hs
        have h_split : |∑' a, g s a| ≤ ∑ a ∈ S, |g s a| + ∑' a, |g s a| - ∑ a ∈ S, |g s a| := by
          convert norm_tsum_le_tsum_norm _ <;> norm_num;
          any_goals tauto;
          exact Summable.of_nonneg_of_le ( fun a => norm_nonneg _ ) ( fun a => hg_le s ( le_trans ( le_max_right _ _ ) hs ) a ) hf;
        simp +zetaDelta at *;
        refine' le_trans h_split _;
        rw [ add_sub_assoc ];
        rw [ ← Summable.sum_add_tsum_compl ( show Summable fun a => f a from hf ) ];
        rw [ ← Summable.sum_add_tsum_compl ];
        any_goals exact S;
        · simp +zetaDelta at *;
          refine' Summable.tsum_le_tsum _ _ _;
          · exact fun a => hg_le s hs.2 _;
          · exact Summable.of_nonneg_of_le ( fun _ => abs_nonneg _ ) ( fun _ => hg_le s hs.2 _ ) ( hf.comp_injective Subtype.coe_injective );
          · exact hf.comp_injective Subtype.coe_injective;
        · exact Summable.of_nonneg_of_le ( fun a => abs_nonneg _ ) ( fun a => hg_le s hs.2 a ) hf;
      -- Using the bound from h_bound and the fact that |g s a| < ε / (2 * |S| + 1) for a ∈ S, we can further bound the sum.
      have h_final_bound : ∀ s ≥ max T 1, |∑' a, g s a| ≤ S.card * (ε / (2 * S.card + 1)) + ε / 2 := by
        exact fun s hs => le_trans ( h_bound s hs ) ( by nlinarith [ show ( ∑ a ∈ S, |g s a| ) ≤ S.card * ( ε / ( 2 * S.card + 1 ) ) by exact le_trans ( Finset.sum_le_sum fun a ha => le_of_lt ( hT s ( le_trans ( le_max_left _ _ ) hs ) a ha ) ) ( by simp +decide ) ] );
      exact ⟨ Max.max T 1, fun s hs => lt_of_le_of_lt ( h_final_bound s hs ) ( by nlinarith [ mul_div_cancel₀ ε ( by positivity : ( 2 * S.card + 1 : ℝ ) ≠ 0 ) ] ) ⟩;
    exact Metric.tendsto_atTop.mpr fun ε hε => by obtain ⟨ T, hT ⟩ := h_eps ε hε; exact ⟨ T, fun s hs => by simpa using hT s hs ⟩ ;

/-
As s goes to infinity, the Gaussian mass of the dual lattice excluding the origin (with parameter 1/s) tends to 0.
-/
lemma tendsto_rhoSMassOn_atTop_zero  (L : EuclideanLattice n n) :
  Filter.Tendsto (fun s => rhoSMassOn (1/s) (0 : 𝓔 n) L {0}ᶜ) Filter.atTop (nhds 0) := by
    apply_rules [ tendsto_tsum_zero_of_dominated_real ];
    case f => exact fun v => if v = 0 then 0 else LatticeCrypto.Foundations.Gaussian.rho ( v : LatticeCrypto.Utils.Vec.𝓔 n );
    · have := @LatticeCrypto.Foundations.Gaussian.summable_rhoS n L 1 zero_lt_one 0;
      convert this.sub ( show Summable fun v : L.carrier => if v = 0 then LatticeCrypto.Foundations.Gaussian.rho ( v : LatticeCrypto.Utils.Vec.𝓔 n ) else 0 from ?_ ) using 2 ; aesop;
      exact ⟨ _, hasSum_single 0 <| by aesop ⟩;
    · simp +zetaDelta at *;
      intro s hs a ha; split_ifs <;> simp_all +decide ;
      rw [ abs_of_nonneg ( by exact Real.exp_nonneg _ ) ];
      field_simp;
      exact LatticeCrypto.Foundations.Gaussian.rhoS_inv_le_rho_of_ge_one _ _ hs;
    · simp +zetaDelta at *;
      intro v hv; by_cases hv' : v = 0 <;> simp_all +decide ;
      convert tendsto_rhoS_inv_atTop_zero v hv' using 1;
      norm_num [ LatticeCrypto.Foundations.Gaussian.rhoS ]

end AristotleLemmas

/-- By definition of smoothing parameter, we know that the set is non-empty. -/
theorem smoothingParameter_exists (L : EuclideanLattice n n) (ε : ℝ) (hε : ε > 0) :
    Set.Nonempty (SmoothingSet L ε) := by
  -- By definition of smoothing parameter, we know that the set is non-empty.
  -- By the definition of limit at infinity, for any $\epsilon > 0$, there exists $s_0$ such that for all $s \ge s_0$, $|f(s) - 0| \le \epsilon$. Since $f(s) \ge 0$, this means $f(s) \le \epsilon$.
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℝ, ∀ s ≥ s₀, rhoSMassOn (1/s) 0 L.dual {0}ᶜ ≤ ε := by
    have := tendsto_rhoSMassOn_atTop_zero L.dual;
    simpa using this.eventually ( ge_mem_nhds hε );
  use Max.max s₀ 1;
  exact ⟨ by positivity, by rw [ rhoSMass_eq_one_add_rhoSMassOn_nonzero ( L.dual ) ( 1 / Max.max s₀ 1 ) ( by positivity ) ] ; linarith [ hs₀ ( Max.max s₀ 1 ) ( le_max_left s₀ 1 ) ] ⟩

/-- The smoothing parameter is non-negative. -/
theorem smoothingParameter_nonneg (L : EuclideanLattice n n) (ε : ℝ) :
    L.η ε ≥ 0 := by
  have hs : ∀ s ∈ SmoothingSet L ε, 0 ≤ s := by
    intros s hs;
    exact hs.1.le;
  exact Real.sInf_nonneg hs

/-- The SmoothingSet is upward closed -/
theorem smoothingParameter_mono_s (L : EuclideanLattice n n) (ε : ℝ) (s : ℝ) (hs : s ∈ SmoothingSet L ε) :
    ∀ s' ≥ s, s' ∈ SmoothingSet L ε := by
  -- By definition of smoothing parameter, the set defining η(ε', L) is a superset of the set defining η(ε, L).
  intros s' hs'
  have h_s_pos : 0 < s := by
    unfold SmoothingSet at hs;
    exact hs.1
  have h_s'_pos : 0 < s' := by
    exact Std.lt_of_lt_of_le h_s_pos hs'
  have h_s_inv_pos : 0 < 1 / s := by
    exact one_div_pos.mpr h_s_pos
  have h_s'_inv_pos : 0 < 1 / s' := by
    exact one_div_pos.mpr h_s'_pos
  have hs'_inv_le : 1 / s' ≤ 1 / s := by
    exact one_div_le_one_div_of_le hs.1 hs'
  have h_le : rhoSMass (1 / s') (0 : 𝓔 n) L.dual ≤ rhoSMass (1 / s) (0 : 𝓔 n) L.dual := by
    exact rhoSMass_mono h_s'_inv_pos hs'_inv_le L.dual
  have h_final : rhoSMass (1 / s') (0 : 𝓔 n) L.dual ≤ 1 + ε := by
    linarith [hs.2]
  exact ⟨ h_s'_pos, h_final ⟩

/-- The smoothing parameter is monotonically decreasing with ε -/
theorem smoothingParameter_mono_ε (L : EuclideanLattice n n) (ε : ℝ) (hε : ε > 0) :
    ∀ ε' ≥ ε, L.η ε' ≤ L.η ε := by
  -- By definition of smoothing parameter, the set defining η(ε', L) is a superset of the set defining η(ε, L).
  intros ε' hε'
  have h_subset : {s : ℝ | 0 < s ∧ rhoSMass (1 / s) (0 : 𝓔 n) L.dual ≤ 1 + ε'} ⊇ {s : ℝ | 0 < s ∧ rhoSMass (1 / s) (0 : 𝓔 n) L.dual ≤ 1 + ε} := by
    exact fun x hx => ⟨ hx.1, le_trans hx.2 ( by linarith ) ⟩;
  apply_rules [ csInf_le_csInf ];
  · exact ⟨ 0, fun s hs => hs.1.le ⟩;
  · -- By definition of $L.η$, we know that $L.η ε$ is the infimum of the set.
    have h_eta_inf : ∃ s : ℝ, 0 < s ∧ rhoSMass (1 / s) (0 : 𝓔 n) L.dual ≤ 1 + ε := by
      exact smoothingParameter_exists L ε hε;
    exact h_eta_inf

/-- Direct implication of the smoothing parameter -/
theorem smoothingParameter_imply (L : EuclideanLattice n n) (ε : ℝ) :
    ∀ s ∈ SmoothingSet L ε, s ≥ L.η ε := by
  intro s hs
  exact csInf_le ⟨ 0, fun x hx => hx.1.le ⟩ hs


/-- The smoothing parameter is a threshold -/
theorem smoothingParameter_thresh (L : EuclideanLattice n n) (ε : ℝ) (hε : ε > 0) :
    ∀ s > L.η ε, s ∈ SmoothingSet L ε := by
  intro s hs;
  -- By definition of infimum, if $s > L.η ε$, then there exists some $t \in \text{SmoothingSet } L ε$ such that $t < s$.
  obtain ⟨t, ht⟩ : ∃ t ∈ SmoothingSet L ε, t < s := by
    exact exists_lt_of_csInf_lt ( by exact smoothingParameter_exists L ε hε ) hs;
  have h_t_le_s : ∀ t ∈ SmoothingSet L ε, t < s → s ∈ SmoothingSet L ε := by
    intros t ht ht_lt_s
    apply smoothingParameter_mono_s L ε t ht s ht_lt_s.le;
  exact h_t_le_s t ht.1 ht.2

/-!
  The smoothing parameter is positive for any constant ε > 0.
  Note this is actually nontrivial since the definition itself allows the infimum to be 0.
-/
theorem smoothingParameter_pos (L : EuclideanLattice n n) (ε : ℝ) (hε : ε > 0) :
    L.η ε > 0 := by
  -- By definition of smoothing parameter, we know that the set is non-empty.
  have h_nonempty : Set.Nonempty (SmoothingSet L ε) := by
    exact smoothingParameter_exists L ε hε;
  have h_inf_pos : 0 < sInf (SmoothingSet L ε) := by
    have h_inf_pos : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), s ∉ SmoothingSet L ε := by
      have h_inf_pos : Filter.Tendsto (fun s => rhoSMass (1/s) 0 L.dual) (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
        exact rhoSMass_inv_tendsto_atTop L;
      filter_upwards [ h_inf_pos.eventually_gt_atTop ( 1 + ε ) ] with s hs using by rintro ⟨ hs', hs'' ⟩ ; linarith!;
    rw [ eventually_nhdsWithin_iff ] at h_inf_pos;
    rw [ Metric.eventually_nhds_iff ] at h_inf_pos;
    obtain ⟨ δ, hδ_pos, hδ ⟩ := h_inf_pos; exact lt_of_lt_of_le hδ_pos <| le_csInf h_nonempty fun x hx => le_of_not_gt fun hx' => hδ ( abs_lt.mpr ⟨ by linarith [ hx.1 ], by linarith [ hx.1 ] ⟩ ) hx.1 hx;
  exact h_inf_pos

end defs

/-!
  ## Some handy corollaries immediately from the definition

  * `smoothing_parameter_ub_via_dual_succMin₁_for_ε_ge_4_pow_neg_n`: For any ε ≥ 4^{−n} , η_ε(L) ≤ √n / λ_1(L.dual)
  * `smoothing_parameter_ub_via_succMinₙ_for_ε_ge_4_pow_neg_n`: For any ε ≥ 4^{−n} , η_ε(L) ≤ √n * λ_n(L)
  * `smoothing_paramter_lb_via_dual_succMin₁`: For any lattice L and ε > 0, we have that η_ε(L) ≥ Real.sqrt ((ln 1 / ε) / Real.pi) / λ_1(L.dual)
  * `smoothing_paramter_lb_via_succMinₙ`: For any lattice L and ε > 0, we have that η_ε(L) ≥ Real.sqrt ((ln 1 / ε) / Real.pi) * (λ_n(L) / n)
-/
namespace LatticeCrypto.Foundations.Gaussian

noncomputable section smoothing_properties

open scoped Real Complex MeasureTheory
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Foundations.Gaussian
open LatticeCrypto.Foundations.Lattice

variable {n : ℕ+} (L : EuclideanLattice n n) (s : ℝ) (ε : ℝ)

/-- If ρ_{1/s}(L.dual \setminus {0}) ≤ (ε / 1+ε) * ρ_{1/s}(L.dual) iff s ≥ η_ε(L).-/
theorem rhoSMassOn_nonzero_in_smoothing_regime (L : EuclideanLattice n n) (s : ℝ) (hs : s > 0) (ε : ℝ) (hε : ε > 0) :
    rhoSMassOn (1 / s) (0 : 𝓔 n) L.dual {0}ᶜ ≤ (ε / (1 + ε)) * rhoSMass (1 / s) (0 : 𝓔 n) L.dual → s ≥ L.η ε := by
  intro h_rhoSMassOn_nonzero_le
  have h_rhoSMass_decomp := rhoSMass_eq_one_add_rhoSMassOn_nonzero L.dual ( 1 / s ) ( one_div_pos.mpr hs ) ;
  rw [ h_rhoSMass_decomp ] at h_rhoSMassOn_nonzero_le ;

  let M := rhoSMassOn (1 / s) (0 : 𝓔 n) L.dual {0}ᶜ
  have h1 : M  ≤ ε / (1 + ε) * (1 + M) := by
    exact h_rhoSMassOn_nonzero_le
  have h2 : M * (1 + ε) ≤ ε + ε * M := by
    rw [ div_mul_eq_mul_div, le_div_iff₀ ] at h1 <;> linarith
  have h3 : M ≤ ε := by
    nlinarith
  -- Since $M \leq \epsilon$, we have $s \geq \eta_\epsilon(L)$ by definition of $\eta_\epsilon(L)$.
  have h4 : s ∈ {s : ℝ | 0 < s ∧ rhoSMass (1 / s) (0 : 𝓔 n) L.dual ≤ 1 + ε} := by
    exact ⟨ hs, by linarith ⟩;
  exact csInf_le ⟨ 0, fun x hx => hx.1.le ⟩ h4

open Pointwise
/-- Scaling property of rhoSMassOn on the non-zero lattice points -/
lemma rhoSMassOn_nonzero_scale {n : ℕ+} (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) :
    rhoSMassOn (1 / s) (0 : 𝓔 n) L {0}ᶜ = rhoMassOn (0 : 𝓔 n) (L.smul s hs.ne.symm) {0}ᶜ := by
  have : s • ({0}ᶜ : Set (𝓔 n)) = {0}ᶜ := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      have hs0 : s ≠ 0 := hs.ne'
      have hy0 : y ≠ 0 := by simpa [Set.mem_singleton_iff] using hy
      have : s • y ≠ 0 := smul_ne_zero hs0 hy0
      simpa [Set.mem_singleton_iff] using this
    · intro hx
      have hs0 : s ≠ 0 := hs.ne'
      have hx0 : x ≠ 0 := by simpa [Set.mem_singleton_iff] using hx
      refine ⟨s⁻¹ • x, ?_, ?_⟩
      ·
        have hrepr : s • (s⁻¹ • x) = x := by simp [smul_smul, hs0]
        have hne : s⁻¹ • x ≠ 0 := by
          intro hzero
          have : s • (s⁻¹ • x) = 0 := by simp [hzero]
          have : x = 0 := by simpa [hrepr] using this
          exact hx0 this
        simpa [Set.mem_singleton_iff] using hne
      · simp [smul_smul, hs0]
  have h_scale := rhoSMassOn_scale L s hs.ne' {0}ᶜ
  rw [ this ] at h_scale ;
  exact h_scale

/-- Handy bound 4^{-n} on rhoMass on nonzero lattice points -/
lemma rhoMass_nonzero_le_4_pow_neg_n_for_succMin₁_ge_sqrt_n {n : ℕ+} (L : EuclideanLattice n n) (h : L.succMin₁ ≥ Real.sqrt n) :
  rhoMassOn (0 : 𝓔 n) L {0}ᶜ ≤ (4 : ℝ) ^ (-(n : ℝ)) := by
  -- Let $M = \rho(L \setminus \{0\})$.
  have : L.succMin₁ = L.shortestVectorLength := by exact L.successiveMinima_one
  rw [ this ] at h
  -- By the previous steps, we have $M \leq (0.2)^n / (1 - (0.2)^n)$.
  have h_M_le : rhoMassOn (0 : 𝓔 n) L {0}ᶜ < (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) := by
    exact rhoMass_with_long_sv_stronger L h;
  have : (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) ≤ (4 : ℝ) ^ (-(n : ℝ)) := by
    -- By simplifying, we can see that the inequality holds for all positive integers n.
    have h_simplify : ∀ n : ℕ+, (0.2 : ℝ) ^ (n : ℝ) / (1 - (0.2 : ℝ) ^ (n : ℝ)) ≤ (4 : ℝ) ^ (-(n : ℝ)) := by
      intro n; rw [ div_le_iff₀ ] <;> norm_num [ Real.rpow_neg ];
      · induction n using PNat.recOn <;> norm_num [ pow_succ' ] at *;
        nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 5 ) ( ↑‹ℕ+› : ℕ ), pow_le_pow_of_le_one ( by norm_num : ( 0 : ℝ ) ≤ 1 / 5 ) ( by norm_num ) ( show ( ↑‹ℕ+› : ℕ ) ≥ 1 from Nat.one_le_iff_ne_zero.mpr <| PNat.ne_zero _ ) ];
      · exact pow_lt_one₀ ( by norm_num ) ( by norm_num ) ( by positivity );
    exact h_simplify n
  linarith


/-- For any ε ≥ 4^{−n} , η_ε(L) ≤ √n / λ_1(L.dual)-/
theorem smoothing_parameter_ub_via_dual_succMin₁_for_ε_ge_4_pow_neg_n {n : ℕ+} (L : EuclideanLattice n n) (ε : ℝ) :
    ε ≥ 4 ^ (-n : ℝ) → L.η ε ≤ (Real.sqrt n) / L.dual.succMin₁ := by
  intro hε;
  -- Let $s = \sqrt{n}/\lambda_1(L^*)$, so $s\lambda_1(L^*)\geq \sqrt{n}$.
  set s := Real.sqrt n / L.dual.succMin₁ with hs_def
  have hs_lambda_ge_sqrt_n : s * L.dual.succMin₁ ≥ Real.sqrt n := by
    rw [ div_mul_cancel₀ ];
    -- Since $L$ is a full-rank lattice, its dual $L^*$ is also a full-rank lattice, and thus $\lambda_1(L^*) > 0$.
    have h_dual_pos : 0 < L.dual.succMin₁ := by
      exact EuclideanLattice.successiveMinima_pos L.dual ⟨0, PNat.pos n⟩
    exact ne_of_gt h_dual_pos;
  -- By the properties of the Gaussian function, we have $\rho(sL^* \setminus \{0\}) \le 4^{-n}$.
  have h_gauss_tail : rhoSMassOn (1 / s) (0 : 𝓔 n) L.dual {0}ᶜ ≤ (4 : ℝ) ^ (-(n : ℝ)) := by
    convert rhoMass_nonzero_le_4_pow_neg_n_for_succMin₁_ge_sqrt_n _ _ using 1;
    convert rhoSMassOn_nonzero_scale _ _ _ using 1;
    refine' div_pos ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr n.pos ) <| _;
    exact EuclideanLattice.successiveMinima_pos L.dual ⟨0, PNat.pos n⟩;
    convert hs_lambda_ge_sqrt_n using 1;
    convert EuclideanLattice.successiveMinima_scale _ _ _ _ using 1;
    refine' div_pos ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr n.pos ) _;
    exact EuclideanLattice.successiveMinima_pos L.dual ⟨0, PNat.pos n⟩;
  refine' csInf_le _ _;
  · exact ⟨ 0, fun x hx => hx.1.le ⟩;
  · refine' ⟨ div_pos ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr n.pos ) ) ( _ ), _ ⟩;
    · exact EuclideanLattice.successiveMinima_pos L.dual ⟨0, PNat.pos n⟩;
    · -- By definition of rhoSMass, we have rhoSMass (1 / s) 0 L.dual = 1 + rhoSMassOn (1 / s) 0 L.dual {0}ᶜ.
      have h_rhoSMass_def : rhoSMass (1 / s) 0 L.dual = 1 + rhoSMassOn (1 / s) 0 L.dual {0}ᶜ := by
        convert Gaussian.rhoSMass_eq_one_add_rhoSMassOn_nonzero L.dual ( 1 / s ) ( one_div_pos.mpr <| div_pos ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr n.pos ) <| ?_ ) using 1;
        exact EuclideanLattice.successiveMinima_pos L.dual ⟨0, PNat.pos n⟩;
      linarith

/-- For any ε ≥ 4^{−n} , η_ε(L) ≤ √n * λ_n(L)-/
theorem smoothing_parameter_ub_via_succMinₙ_for_ε_ge_4_pow_neg_n {n : ℕ+} (L : EuclideanLattice n n) (ε : ℝ) :
    ε ≥ 4 ^ (-n : ℝ) → L.η ε ≤ (Real.sqrt n) * L.succMinₙ := by
  intro hε
  have h_transference_lb : 1 ≤ L.dual.succMinₙ * L.succMin₁ := by
    exact transference_lb L
  have h_transference_lb' : 1 / L.dual.succMin₁ ≤ L.succMinₙ := by
    rw [ div_le_iff₀ ];
    · have := LatticeCrypto.Foundations.Gaussian.transference_lb L.dual;
      rw [ show L.dual.dual = L from ?_ ] at this ; aesop;
      have h_dual_dual : ∀ (L : EuclideanLattice n n), L.dual.dual = L := by
        intro L; exact (by
        have h_dual_dual : ∀ (B : SquareLatticeBasis n), B.dual.dual = B := by
          exact fun B => LatticeBasis.dual_dual B;
        convert congr_arg ( fun B : SquareLatticeBasis n => B.toLattice ) ( h_dual_dual L.basis ) using 1;
        exact EuclideanLattice.eq_basis_toLattice L);
      exact h_dual_dual L;
    · exact EuclideanLattice.successiveMinima_pos L.dual ⟨0, PNat.pos n⟩
  have h_smoothing_ub : L.η ε ≤ Real.sqrt n / L.dual.succMin₁ := by
    exact smoothing_parameter_ub_via_dual_succMin₁_for_ε_ge_4_pow_neg_n L ε hε
  have h_final : L.η ε ≤ Real.sqrt n * L.succMinₙ := by
    exact h_smoothing_ub.trans ( by simpa only [ mul_one_div ] using mul_le_mul_of_nonneg_left h_transference_lb' <| Real.sqrt_nonneg _ )
  exact h_final


noncomputable section AristotleLemmas

/-
If s < 1/lambda_1(L*), then the Gaussian mass of L* \ {0} with parameter 1/s is strictly greater than 2 * exp(-pi).
-/
lemma rhoSMassOn_dual_nonzero_gt_of_s_lt_inv_succMin₁ (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s)
    (h_s_lt : s < 1 / L.dual.succMin₁) :
    rhoSMassOn (1 / s) 0 L.dual {0}ᶜ > 2 * Real.exp (-Real.pi) := by
      have h_shortest_dual : ∃ v ∈ L.dual.nonzeroVectors, ∀ w ∈ L.dual.nonzeroVectors, ‖v‖ ≤ ‖w‖ := by
        exact EuclideanLattice.exists_shortest_vector L.dual;
      obtain ⟨ v, hv₁, hv₂ ⟩ := h_shortest_dual;
      have h_rho_v_minus_v : rhoSMassOn (1 / s) 0 L.dual {0}ᶜ ≥ rhoS (1 / s) v + rhoS (1 / s) (-v) := by
        refine' le_trans _ ( Summable.sum_le_tsum _ _ _ );
        case refine'_2 => exact { ⟨ v, by simpa using hv₁.1 ⟩, ⟨ -v, by simpa using neg_mem_iff.mpr hv₁.1 ⟩ };
        · by_cases h : v = 0 <;> simp_all +decide [ Set.indicator ];
          · exact absurd h hv₁.2;
          · rw [ Finset.sum_pair ] <;> norm_num [ h ];
            exact fun h' => h <| by ext i; have := congr_fun h' i; norm_num at *; linarith;
        · norm_num +zetaDelta at *;
          intro w hw₁ hw₂ hw₃; by_cases hw₄ : w = 0 <;> simp_all +decide ;
          exact Real.exp_nonneg _;
        · exact summable_rhoSMassOn ( 1 / s ) ( one_div_pos.mpr hs ) 0 L.dual { 0 } ᶜ;
      -- Since $s < 1/\lambda_1(L^*)$, we have $s \|v\| < 1$.
      have h_s_norm_v_lt_1 : s * ‖v‖ < 1 := by
        rw [ lt_div_iff₀ ( _ ) ] at h_s_lt;
        · refine' lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( show ‖v‖ ≤ L.dual.succMin₁ from _ ) hs.le ) h_s_lt;
          have h_norm_v_le_succMin₁ : ∃ w ∈ L.dual.nonzeroVectors, ‖w‖ = L.dual.succMin₁ := by
            exact EuclideanLattice.successiveMinima_attained L.dual ⟨0, PNat.pos n⟩;
          exact h_norm_v_le_succMin₁.choose_spec.2 ▸ hv₂ _ h_norm_v_le_succMin₁.choose_spec.1;
        · exact EuclideanLattice.successiveMinima_pos L.dual ⟨0, PNat.pos n⟩;
      -- Since $s \|v\| < 1$, we have $\exp(-\pi (s \|v\|)^2) > \exp(-\pi)$.
      have h_exp_gt_exp_pi : Real.exp (-Real.pi * (s * ‖v‖) ^ 2) > Real.exp (-Real.pi) := by
        exact Real.exp_lt_exp.mpr ( by nlinarith [ Real.pi_pos, show ( s * ‖v‖ ) ^ 2 < 1 by exact pow_lt_one₀ ( mul_nonneg hs.le ( norm_nonneg v ) ) h_s_norm_v_lt_1 ( by norm_num ) ] );
      -- Since $\rhoS(1/s, v) = \exp(-\pi (s \|v\|)^2)$ and $\rhoS(1/s, -v) = \exp(-\pi (s \|v\|)^2)$, we have:
      have h_rho_v_minus_v_eq : LatticeCrypto.Foundations.Gaussian.rhoS (1 / s) v + LatticeCrypto.Foundations.Gaussian.rhoS (1 / s) (-v) = 2 * Real.exp (-Real.pi * (s * ‖v‖) ^ 2) := by
        unfold LatticeCrypto.Foundations.Gaussian.rhoS; norm_num ; ring_nf;
        norm_num ; ring_nf;
        rw [ norm_smul, Real.norm_of_nonneg hs.le ] ; ring_nf;
      linarith

/-
For s >= 1, the Gaussian mass of the dual lattice excluding the origin with parameter 1/s is bounded by a factor times the mass with parameter 1.
-/
lemma rhoSMassOn_le_pow_rhoMassOn (L : EuclideanLattice n n) (s : ℝ) (hs : s ≥ 1) :
    rhoSMassOn (1 / s) 0 L.dual {0}ᶜ ≤ (Real.exp (-Real.pi * L.dual.succMin₁^2))^(s^2 - 1) * rhoMassOn 0 L.dual {0}ᶜ := by
      -- Applying the inequality $\rho_{1/s}(v) \leq \rho(v) \cdot (\exp(-\pi \lambda_1^2))^{(s^2 - 1)}$ to each term in the sum.
      have h_term_bound : ∀ w ∈ L.dual.nonzeroVectors, rhoS (1 / s) w ≤ rho w * (Real.exp (-Real.pi * L.dual.succMin₁ ^ 2)) ^ (s ^ 2 - 1) := by
        intro w hw
        have h_exp_bound : Real.exp (-Real.pi * ‖w‖^2 * (s^2 - 1)) ≤ (Real.exp (-Real.pi * L.dual.succMin₁^2)) ^ (s^2 - 1) := by
          rw [ ← Real.exp_mul ] ; ring_nf;
          have h_exp_bound : ‖w‖^2 ≥ L.dual.succMin₁^2 := by
            gcongr;
            · apply_rules [ Real.sInf_nonneg ];
              exact fun x hx => hx.1.le;
            · exact L.dual.norm_ge_successiveMinima_one w ( by aesop );
          exact Real.exp_le_exp.mpr ( by nlinarith [ Real.pi_pos, mul_le_mul_of_nonneg_left hs Real.pi_pos.le, mul_le_mul_of_nonneg_left ( sq_nonneg ( s - 1 ) ) Real.pi_pos.le ] );
        convert mul_le_mul_of_nonneg_left h_exp_bound ( Real.exp_nonneg ( -Real.pi * ‖w‖ ^ 2 ) ) using 1 ; ring_nf;
        unfold LatticeCrypto.Foundations.Gaussian.rhoS ; rw [ ← Real.exp_add ] ; ring_nf;
        norm_num [ norm_smul, mul_pow ] ; ring;
      convert Summable.tsum_le_tsum ( fun x => ?_ ) ?_ ?_;
      any_goals rw [ tsum_mul_right ];
      any_goals rw [ mul_comm ];
      congr! 1;
      all_goals try infer_instance;
      · by_cases hx : x = 0 <;> simp_all +decide [ mul_comm ];
        convert h_term_bound x _ using 1;
        · exact ⟨ x.2, by simpa using hx ⟩;
      · convert LatticeCrypto.Foundations.Gaussian.summable_rhoSMassOn ( 1 / s ) ( by positivity ) 0 L.dual { 0 } ᶜ using 1;
      · refine' Summable.mul_right _ _;
        convert summable_rhoMassOn 0 L.dual { 0 } ᶜ using 1

/-
For any epsilon > 0, there exists a positive s such that the Gaussian mass of the dual lattice excluding the origin with parameter 1/s is at most epsilon.
-/
lemma exists_s_rhoSMassOn_le (L : EuclideanLattice n n) (ε : ℝ) (hε : 0 < ε) :
    ∃ s > 0, rhoSMassOn (1 / s) 0 L.dual {0}ᶜ ≤ ε := by
      have h_lim : Filter.Tendsto (fun s : ℝ => (Real.exp (-Real.pi * L.dual.succMin₁^2))^(s^2 - 1) * rhoMassOn 0 L.dual {0}ᶜ) Filter.atTop (nhds 0) := by
        have h_lim : Filter.Tendsto (fun s : ℝ => Real.exp (-Real.pi * L.dual.succMin₁^2 * (s^2 - 1))) Filter.atTop (nhds 0) := by
          norm_num +zetaDelta at *;
          exact Filter.Tendsto.const_mul_atTop ( mul_pos Real.pi_pos ( sq_pos_of_pos ( show 0 < L.dual.succMin₁ from by exact
            (EuclideanLattice.successiveMinima_pos L.dual ⟨0, PNat.pos n⟩) ) ) ) ( Filter.tendsto_atTop_add_const_right _ _ ( by norm_num ) );
        simpa [ ← Real.exp_mul ] using h_lim.mul_const _;
      have := h_lim.eventually ( gt_mem_nhds hε );
      obtain ⟨ s, hs ⟩ := this.and ( Filter.eventually_gt_atTop 1 ) |> fun h => h.exists;
      exact ⟨ s, by linarith, le_trans ( rhoSMassOn_le_pow_rhoMassOn L s ( by linarith ) ) ( le_of_lt hs.1 ) ⟩

end AristotleLemmas

/-- For any lattice L and ε≤2 * exp(−π), we have that η_ε(L) ≥ 1 / λ_1(L.dual)-/
theorem smoothing_paramter_lb_via_dual_succMin₁_for_small_ε (hε : 0 < ε ∧ ε ≤ 2 * Real.exp (-Real.pi)) :
    (1 / L.dual.succMin₁) ≤ L.η ε :=
  by
  have h_lower_bound : ∀ s > 0, s ∈ {s : ℝ | 0 < s ∧ rhoSMassOn (1 / s) (0 : (EuclideanSpace ℝ (Fin n))) L.dual {0}ᶜ ≤ ε} → 1 / L.dual.succMin₁ ≤ s := by
    intro s hs hS
    by_contra h_contra
    have h_contra' : s < 1 / L.dual.succMin₁ := by
      exact not_le.mp h_contra;
    exact hε.2.not_gt <| hS.2.trans_lt' <| by linarith [ Real.exp_pos ( -Real.pi ), show LatticeCrypto.Foundations.Gaussian.rhoSMassOn ( 1 / s ) 0 L.dual { 0 } ᶜ > 2 * Real.exp ( -Real.pi ) from rhoSMassOn_dual_nonzero_gt_of_s_lt_inv_succMin₁ L s hs h_contra' ] ;
  rw [ show L.η ε = sInf { s : ℝ | 0 < s ∧ rhoSMassOn ( 1 / s ) 0 L.dual { 0 } ᶜ ≤ ε } from ?_ ];
  · exact le_csInf ( by obtain ⟨ s, hs ⟩ := exists_s_rhoSMassOn_le L ε hε.1; exact ⟨ s, hs ⟩ ) fun s hs => h_lower_bound s hs.1 hs |> le_trans <| le_rfl;
  · convert smoothingParameter_eq_smoothingParameter' L ε


noncomputable section AristotleLemmas

/-
  The Gaussian mass of the non-zero vectors is at least 2 * exp(-pi * lambda_1^2).
  Essentially a special case of `rhoSMassOn_dual_nonzero_gt_of_s_lt_inv_succMin₁`
-/
theorem rhoMass_nonzero_ge_2_exp_neg_pi_mul_succMin₁_sq {n : ℕ+} (L : EuclideanLattice n n) :
    rhoMassOn (0 : 𝓔 n) L {0}ᶜ ≥ 2 * Real.exp (-Real.pi * L.succMin₁ ^ 2) := by
      have h_two_factors : ∃ v : 𝓔 n, v ∈ L.carrier ∧ v ≠ 0 ∧ ‖v‖ = L.succMin₁ := by
        -- Since the shortest vector is non-zero, we can obtain such a vector from the set of non-zero vectors.
        obtain ⟨v, hv⟩ : ∃ v ∈ {v : 𝓔 n | v ∈ L.carrier ∧ v ≠ 0}, ‖v‖ = L.succMin₁ := by
          exact EuclideanLattice.successiveMinima_attained L ⟨0, PNat.pos n⟩;
        aesop;
      obtain ⟨ v, hv₁, hv₂, hv₃ ⟩ := h_two_factors;
      have h_two_factors : rhoMassOn 0 L {0}ᶜ ≥ rho v + rho (-v) := by
        refine' le_trans _ ( Summable.sum_le_tsum _ _ _ );
        rotate_left;
        exact { ⟨ v, hv₁ ⟩, ⟨ -v, by simpa using L.carrier.neg_mem hv₁ ⟩ };
        · simp +decide [ Set.indicator ];
          intro a ha ha' ha''; split_ifs <;> norm_num [ rhoST ] ;
          exact Real.exp_nonneg _;
        · convert summable_rhoMassOn 0 L { 0 } ᶜ using 1;
        · field_simp;
          rw [ Finset.sum_pair ] <;> norm_num [ hv₂ ];
          exact fun h' => hv₂ <| by ext i; have := congr_fun h' i; norm_num at *; linarith;
      simp_all +decide [ two_mul, rho ]

/-
rhoSMassOn (1/s) of dual lattice tail is at least exp(-pi * (s * lambda_1(dual))^2).
-/
theorem rhoSMassOn_nonzero_ge_exp_neg_pi_mul_s_sq_mul_succMin₁_sq {n : ℕ+} (L : EuclideanLattice n n) (s : ℝ) (hs : 0 < s) :
    rhoSMassOn (1 / s) (0 : 𝓔 n) L {0}ᶜ ≥ Real.exp (-Real.pi * ( s * L.succMin₁)^2) := by
    -- Apply `rhoSMassOn_nonzero_scale` to convert `rhoSMassOn (1/s)` to `rhoMassOn` of the scaled lattice `s * L`.
    have h_convert : rhoSMassOn (1 / s) (0 : 𝓔 n) L {0}ᶜ = rhoMassOn (0 : 𝓔 n) (L.smul s hs.ne.symm) {0}ᶜ := by
      exact rhoSMassOn_nonzero_scale L s hs
    -- Apply `rhoMass_nonzero_ge_2_exp_neg_pi_mul_succMin₁_sq` to the scaled lattice `s * L`.
    have h_lower_bound : rhoMassOn (0 : 𝓔 n) (L.smul s hs.ne.symm) {0}ᶜ ≥ 2 * Real.exp (-Real.pi * (s * L.succMin₁) ^ 2) := by
      convert rhoMass_nonzero_ge_2_exp_neg_pi_mul_succMin₁_sq _ using 2;
      -- The first successive minimum of the lattice of the smul of L is s times the first successive minimum of the lattice of L.
      have h_succMin₁_smul : (L.smul s hs.ne.symm).succMin₁ = s * L.succMin₁ := by
        have := EuclideanLattice.successiveMinima_scale L 0 s hs
        exact this;
      rw [ h_succMin₁_smul ];
    linarith [ Real.exp_pos ( -Real.pi * ( s * L.succMin₁ ) ^ 2 ) ]

/-
Algebraic lemma for smoothing parameter lower bound.
-/
lemma smoothing_parameter_lb_algebraic_lemma {s lambda epsilon : ℝ}
  (hs : 0 < s) (hlambda : 0 < lambda) (hepsilon : 0 < epsilon) :
  Real.exp (-Real.pi * (s * lambda)^2) ≤ epsilon →
  Real.sqrt (Real.log (1 / epsilon) / Real.pi) / lambda ≤ s := by
    -- Taking the natural logarithm of both sides of the inequality $\exp(-\pi (s \lambda)^2) \le \epsilon$ gives $-\pi (s \lambda)^2 \le \ln \epsilon$.
    intro h_exp
    have h_ln : -Real.pi * (s * lambda) ^ 2 ≤ Real.log epsilon := by
      rwa [ Real.le_log_iff_exp_le hepsilon ];
    rw [ div_le_iff₀ hlambda, Real.sqrt_le_iff ];
    exact ⟨ by positivity, by rw [ div_le_iff₀ ( by positivity ) ] ; simpa [ Real.log_div, hepsilon.ne' ] using by nlinarith ⟩


/-
Auxiliary lemma for smoothing parameter lower bound.
-/
lemma smoothing_parameter_lb_aux {n : ℕ+} (L : EuclideanLattice n n) (ε : ℝ) (hε : ε > 0) (s : ℝ) (hs : 0 < s) :
  rhoSMass (1 / s) 0 L.dual ≤ 1 + ε → (Real.sqrt (Real.log (1 / ε) / Real.pi)) * (1 / L.dual.succMin₁) ≤ s := by
    intro h;
    -- Using the inequality from the provided solution, we have:
    have h_ineq : Real.exp (-Real.pi * (s * L.dual.succMin₁)^2) ≤ ε := by
      have h_ineq : rhoSMassOn (1 / s) (0 : 𝓔 n) L.dual {0}ᶜ ≥ Real.exp (-Real.pi * (s * L.dual.succMin₁)^2) := by
        exact rhoSMassOn_nonzero_ge_exp_neg_pi_mul_s_sq_mul_succMin₁_sq L.dual s hs;
      rw [ rhoSMass_eq_one_add_rhoSMassOn_nonzero ] at h ; linarith;
      positivity;
    have := @smoothing_parameter_lb_algebraic_lemma s L.dual.succMin₁ ε hs;
    by_cases hε1 : ε ≤ 1;
    · -- Apply the lemma with the given hypotheses.
      have := this (by
      exact EuclideanLattice.successiveMinima_pos L.dual ⟨0, PNat.pos n⟩) hε h_ineq;
      aesop;
    · rw [ Real.sqrt_eq_zero_of_nonpos ( div_nonpos_of_nonpos_of_nonneg ( Real.log_nonpos ( by positivity ) ( by rw [ div_le_iff₀ ( by positivity ) ] ; linarith ) ) Real.pi_pos.le ) ] ; norm_num ; linarith

/-
If rhoSMassOn (1/s) <= epsilon, then s >= LB.
-/
lemma smoothing_parameter_lb_imp_ge {n : ℕ+} (L : EuclideanLattice n n) (ε : ℝ) (hε : ε > 0) (s : ℝ) (hs : 0 < s) :
  rhoSMassOn (1 / s) (0 : 𝓔 n) L.dual {0}ᶜ ≤ ε →
  (Real.sqrt (Real.log (1 / ε) / Real.pi)) * (1 / L.dual.succMin₁) ≤ s := by
    intro h;
    have := @smoothing_parameter_lb_aux;
    contrapose! this;
    refine' ⟨ n, L, ε, hε, s, hs, _, this ⟩;
    rw [ rhoSMass_eq_one_add_rhoSMassOn_nonzero ];
    · linarith;
    · positivity



end AristotleLemmas


/-- For any lattice L and ε > 0, we have that η_ε(L) ≥ Real.sqrt ((ln 1 / ε) / Real.pi) / λ_1(L.dual)-/
theorem smoothing_paramter_lb_via_dual_succMin₁ (L : EuclideanLattice n n) (ε : ℝ) (hε : ε > 0) :
    (Real.sqrt (Real.log (1 / ε) / Real.pi)) * (1 / L.dual.succMin₁) ≤ L.η ε :=
  by
  -- Apply the `smoothing_parameter_lb_imp_ge` lemma to show the inequality holds for every `s` in `S`.
  have h_all_s_in_S_ge : ∀ s, s ∈ {s | 0 < s ∧ rhoSMassOn (1 / s) (0 : 𝓔 n) L.dual {0}ᶜ ≤ ε} → (Real.sqrt (Real.log (1 / ε) / Real.pi)) * (1 / L.dual.succMin₁) ≤ s := by
    exact fun s hs => smoothing_parameter_lb_imp_ge L ε hε s hs.1 hs.2;
  -- By definition of `smoothingParameter'`, we know that it is the infimum of the set `S`.
  have h_smoothingParameter' : L.η ε = sInf {s | 0 < s ∧ rhoSMassOn (1 / s) (0 : 𝓔 n) L.dual {0}ᶜ ≤ ε} := by
    convert smoothingParameter_eq_smoothingParameter' L ε;
  refine' le_trans _ ( h_smoothingParameter'.le.trans _ );
  · convert le_csInf _ h_all_s_in_S_ge;
    -- By definition of `rhoSMassOn`, we know that it tends to 0 as `s` tends to infinity.
    have h_tendsto_zero : Filter.Tendsto (fun s => rhoSMassOn (1 / s) (0 : 𝓔 n) L.dual {0}ᶜ) Filter.atTop (nhds 0) := by
      exact tendsto_rhoSMassOn_atTop_zero L.dual;
    exact Filter.Eventually.and ( Filter.eventually_gt_atTop 0 ) ( h_tendsto_zero.eventually ( ge_mem_nhds hε ) ) |> fun h => h.exists;
  · exact h_smoothingParameter'.ge

/-- For any lattice L and ε > 0, we have that η_ε(L) ≥ Real.sqrt ((ln 1 / ε) / Real.pi) * (λ_n(L) / n)-/
theorem smoothing_paramter_lb_via_succMinₙ (L : EuclideanLattice n n) (ε : ℝ) (hε : ε > 0) (hn : n ≥ Banaszczyk_transference_threshold_constant):
     (Real.sqrt (Real.log (1 / ε) / Real.pi)) * (L.succMinₙ / (2 * n)) ≤ L.η ε :=
   by
  have h_lb : L.succMinₙ / (2 * n) ≤ 1 / L.dual.succMin₁ := by
    have h_transference_lb : L.dual.succMinₙ * L.succMin₁ ≤ 2 * n:= by
      exact transference_ub L hn
    rw [ div_le_div_iff₀ ] <;> norm_num;
    · -- Since the dual of the dual of L is L itself, we can replace L.dual.dual.succMinₙ with L.succMinₙ.
      have h_dual_dual : L.dual.dual.succMinₙ = L.succMinₙ := by
        unfold LatticeCrypto.Foundations.Lattice.EuclideanLattice.dual;
        unfold LatticeCrypto.Foundations.Lattice.LatticeBasis.toLattice;
        -- The dual of the dual basis is the original basis.
        have h_dual_dual_basis : L.basis.dual.dual = L.basis := by
          exact LatticeBasis.dual_dual L.basis;
        cases L ; aesop;
      have := transference_ub L.dual hn; aesop;
    · exact EuclideanLattice.successiveMinima_pos L.dual ⟨0, PNat.pos n⟩
  have : (Real.sqrt (Real.log (1 / ε) / Real.pi)) * (1 / L.dual.succMin₁) ≤ L.η ε := by
    exact smoothing_paramter_lb_via_dual_succMin₁ L ε hε
  exact le_trans ( mul_le_mul_of_nonneg_left h_lb <| Real.sqrt_nonneg _ ) this


open Filter

/-- Asymptotically tight bound on the smoothing parameter for ε = 2^{−n}: L.η = Θ(√n) / L.dual.succMin₁ -/
theorem smoothing_parameter_asymptotic_for_ε_eq_2_pow_neg_n
  (L : ∀ n, EuclideanLattice n n) :
    (fun n => (L n).η (2 ^ (-n : ℝ))) =Θ[atTop] (fun n => Real.sqrt (n : ℝ) / (L n).dual.succMin₁) := by
  -- For the upper bound, we use the fact that the smoothing parameter is bounded above by $\sqrt{n} / \lambda_1(L^*)$.
  have upper_bound : ∀ n : ℕ+, (L n).η (2 ^ (-(n : ℝ))) ≤ (Real.sqrt n) / (L n).dual.succMin₁ := by
    -- By definition of the smoothing parameter, we know that $\eta_{2^{-n}}(L) \leq \frac{\sqrt{n}}{\lambda_1(L^*)}$ for any $n \geq 1$.
    intros n
    apply LatticeCrypto.Foundations.Gaussian.smoothing_parameter_ub_via_dual_succMin₁_for_ε_ge_4_pow_neg_n;
    rw [ Real.rpow_neg, Real.rpow_neg ] <;> norm_num;
    gcongr ; norm_num;
  -- For the lower bound, we use the fact that the smoothing parameter is bounded below by $\sqrt{n} / \lambda_1(L^*)$.
  have lower_bound : ∀ n : ℕ+, (Real.sqrt (Real.log (1 / (2 ^ (-(n : ℝ)))) / Real.pi)) * (1 / (L n).dual.succMin₁) ≤ (L n).η (2 ^ (-(n : ℝ))) := by
    intro n;
    convert smoothing_paramter_lb_via_dual_succMin₁ ( L n ) ( 2 ^ ( - ( n : ℝ ) ) ) using 1 ; norm_num [ Real.rpow_neg ];
  -- By combining the upper and lower bounds, we can conclude that the smoothing parameter is asymptotically tight.
  have asymptotic_tightness : ∀ n : ℕ+, (Real.sqrt (Real.log 2 / Real.pi)) * (Real.sqrt n / (L n).dual.succMin₁) ≤ (L n).η (2 ^ (-(n : ℝ))) ∧ (L n).η (2 ^ (-(n : ℝ))) ≤ (Real.sqrt n / (L n).dual.succMin₁) := by
    simp_all +decide [ mul_div_assoc ];
    exact fun n => by convert lower_bound n using 1; ring;
  refine' ⟨ _, _ ⟩;
  · rw [ Asymptotics.isBigO_iff ];
    use 1;
    filter_upwards [ Filter.eventually_ge_atTop 1 ] with n hn using
      by
        rw [
            Real.norm_of_nonneg
              ( by exact le_trans
                    ( mul_nonneg ( Real.sqrt_nonneg _ ) ( div_nonneg ( Real.sqrt_nonneg _ ) ( by exact le_of_lt ( show 0 < ( L n |> EuclideanLattice.dual |> EuclideanLattice.succMin₁ ) from by exact (EuclideanLattice.successiveMinima_pos (L n).dual ⟨0, PNat.pos n⟩) ) ) ) )
                    ( asymptotic_tightness n |>.1 )
              ),
            Real.norm_of_nonneg
              ( by exact div_nonneg
                    ( Real.sqrt_nonneg _ )
                    ( by exact le_of_lt ( show 0 < ( L n |> EuclideanLattice.dual |> EuclideanLattice.succMin₁ ) from by exact (EuclideanLattice.successiveMinima_pos (L n).dual ⟨0, PNat.pos n⟩) ) )
              )
           ] ;
        simpa using asymptotic_tightness n |>.2;
  · rw [ Asymptotics.isBigO_iff ];
    use 1 / Real.sqrt ( Real.log 2 / Real.pi );
    filter_upwards [ Filter.eventually_ge_atTop 1 ] with n hn using
      by
        rw [
            Real.norm_of_nonneg
              ( div_nonneg ( Real.sqrt_nonneg _ )
                  ( le_of_lt ( show 0 < ( L n |> EuclideanLattice.dual |> EuclideanLattice.succMin₁ ) from by exact
                    (EuclideanLattice.successiveMinima_pos (L n).dual ⟨0, PNat.pos n⟩) ) ) ),
            Real.norm_of_nonneg ( show 0 ≤ ( L n |> EuclideanLattice.η ) ( 2 ^ ( - ( n : ℝ ) ) ) from by (expose_names; exact smoothingParameter_nonneg (L n) (2 ^ (-n : ℝ))) )
          ] ;
        rw [ div_mul_eq_mul_div, le_div_iff₀ ( Real.sqrt_pos.mpr <| by positivity ) ] ;
        nlinarith [ asymptotic_tightness n, Real.sqrt_nonneg ( Real.log 2 / Real.pi ), Real.mul_self_sqrt ( show 0 ≤ Real.log 2 / Real.pi by positivity ) ] ;


end smoothing_properties

/-!
  ## Tight upper bound on the smoothing parameter due to [Micciancio and Regev 2004]
  * `smoothing_parameter_ub_micciancio_regev_by_succMinₙ`: For any ε>0 and (full-rank) n-dimensional lattice L, we have η_ε(L) ≤ λ_n(L) * Real.sqrt (\ln (2n(1 + 1/ε)) / π)
-/
noncomputable section tight_upperbound

open scoped Real Complex MeasureTheory
open scoped RealInnerProductSpace
open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open LatticeCrypto.Foundations.Gaussian
open LatticeCrypto.Foundations.Lattice


variable {n : ℕ+} (L : EuclideanLattice n n) (s : ℝ)

set_option linter.unusedVariables false in
/-- Affine (open) half-space -/
def AffineHalfSpace (u : 𝓔 n) (hu : ‖u‖ = 1) (t : ℝ) : Set (𝓔 n) :=
  { x : 𝓔 n | inner ℝ u x < t }

abbrev 𝓗 (u : 𝓔 n) (hu : ‖u‖ = 1) (t : ℝ) := AffineHalfSpace u hu t

/-
Algebraic identity for completing the square in the exponent.
-/
private lemma square_completion {n : ℕ+} (v u : 𝓔 n) (t : ℝ) (hu : ‖u‖ = 1) :
    -π * ‖v‖^2 + 2 * π * inner ℝ v (t • u) = -π * ‖v - t • u‖^2 + π * t^2 := by
      norm_num [ @norm_sub_sq ℝ ];
      rw [ norm_smul, hu ] ; ring_nf;
      norm_num [ Real.norm_eq_abs ];
      ring

/-
Pointwise inequality for the Gaussian terms in the half-space tail bound.
-/
private lemma gaussian_ineq {n : ℕ+} (v u : 𝓔 n) (t : ℝ) (hu : ‖u‖ = 1) (h : inner ℝ u v ≥ t) (ht : t ≥ 0) :
    Real.exp (-Real.pi * ‖v‖^2) ≤ Real.exp (-Real.pi * t^2) * Real.exp (-Real.pi * ‖v - t • u‖^2) := by
  rw [ ← Real.exp_add ];
  -- Substitute the expression for ‖v - t • u‖^2 into the inequality.
  have h_sub : ‖v‖^2 ≥ t^2 + ‖v - t • u‖^2 := by
    rw [ @norm_sub_sq ℝ ];
    simp_all +decide [ norm_smul, inner_smul_right ];
    rw [ real_inner_comm ] ; nlinarith;
  exact Real.exp_le_exp.mpr ( by nlinarith [ Real.pi_pos ] )

/-
Intermediate bound: mass outside half-space is bounded by shifted mass times exponential factor.
-/
protected lemma rhoMassOn_le_shifted_rhoMass {n : ℕ+} (L : EuclideanLattice n n) (u : 𝓔 n) (hu : ‖u‖ = 1) (t : ℝ) (ht : t ≥ 0) (x : 𝓔 n) :
    rhoMassOn x L (𝓗 u hu t)ᶜ ≤ Real.exp (-Real.pi * t ^ 2) * rhoMass (x - t • u) L := by
  convert Summable.tsum_le_tsum _ _ _ using 1;
  rw [ tsum_mul_left ];
  congr! 1;
  all_goals try infer_instance;
  · intro v;
    by_cases hv : inner ℝ u ( v + x ) ≥ t <;> simp_all +decide [ Set.indicator ];
    · rw [ if_pos ];
      · convert gaussian_ineq _ _ _ hu _ ht using 1;
        · norm_num [ rhoST ];
          rw [ show ( v : 𝓔 n ) + ( x - t • u ) = ( v : 𝓔 n ) + x - t • u by abel1 ] ; unfold rho; norm_num [ Real.exp_neg, mul_comm ] ;
        · aesop;
      · exact fun h => hv.not_gt <| by simpa using h.out;
    · rw [ if_neg ];
      · exact mul_nonneg ( Real.exp_nonneg _ ) ( Real.exp_nonneg _ );
      · exact fun h => hv.not_ge <| by simpa [ hu ] using h ( by simpa [ hu ] ) ;
  · convert summable_rhoMassOn x L ( 𝓗 u hu t ) ᶜ using 1;
  · refine' Summable.mul_left _ _;
    convert summable_rhoMassOn ( x - t • u ) L ( Set.univ : Set ( 𝓔 n ) ) using 1;
       ext; simp

/-
For any lattice L, unit vector u ∈ R n, real t ≥ 0, and x ∈ R^n, we have that
ρ((x + L) \setminus 𝓗 u t) ≤ exp(−πt^2) * ρ(L).
-/
theorem rhoMass_affine_half_space_tail_bound {n : ℕ+} (L : EuclideanLattice n n) (u : 𝓔 n) (hu : ‖u‖ = 1) (t : ℝ) (ht : t ≥ 0) (x : 𝓔 n) :
    rhoMassOn (x : 𝓔 n) L (𝓗 u hu t)ᶜ ≤ Real.exp (-Real.pi * t ^ 2) * rhoMass 0 L := by
  have := @rhoSMass_shift_mono n L 1 zero_lt_one ( x - t • u );
  rw [rhoSMass_one_eq_rhoMass] at this ;
  convert le_trans ( Gaussian.rhoMassOn_le_shifted_rhoMass L u hu t ht x ) ( mul_le_mul_of_nonneg_left this <| by positivity ) using 1
  rw [rhoSMass_one_eq_rhoMass]

/-
For any non-zero vector w in the dual lattice and any basis v of the primal lattice, there is a basis vector v_i such that |<w, v_i>| >= 1.
-/
private lemma exists_dual_inner_ge_one {n : ℕ+} (L : EuclideanLattice n n) (w : 𝓔 n)
    (hw : w ∈ L.dual.carrier) (hw_ne : w ≠ 0)
    (v : Fin n → 𝓔 n) (hv_li : LinearIndependent ℝ v) (hv_mem : ∀ i, v i ∈ L.carrier) :
    ∃ i, 1 ≤ |inner ℝ w (v i)| := by
      -- Since $w$ is in the dual lattice and $v_i$ are in the primal lattice, the inner product $\langle w, v_i \rangle$ is an integer for all $i$.
      have h_int : ∀ i, ∃ k : ℤ, inner ℝ w (v i) = k := by
        norm_num +zetaDelta at *;
        -- Since the inner product of two lattice vectors is an integer, we can apply the lemma `inner_lattice_dual_int`.
        have h_inner_int : ∀ v ∈ L.carrier, ∀ w ∈ L.dual.carrier, ∃ k : ℤ, inner ℝ v w = k := by
          exact fun v a w a_1 => inner_lattice_dual_int L v w a a_1;
        intro i;
        convert h_inner_int ( v i ) ( by simpa using hv_mem i ) w ( by simpa using hw ) using 1;
        norm_num [ real_inner_comm ];
      -- Since $w$ is non-zero, there must exist some $i$ such that $\langle w, v_i \rangle \neq 0$.
      obtain ⟨i, hi⟩ : ∃ i, inner ℝ w (v i) ≠ 0 := by
        by_contra h_contra; push_neg at h_contra; (
        -- Since $v$ is a basis, we can write $w$ as a linear combination of the $v_i$.
        obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, w = ∑ i, c i • v i := by
          have h_basis : Submodule.span ℝ (Set.range v) = ⊤ := by
            refine' Submodule.eq_top_of_finrank_eq _;
            rw [ finrank_span_eq_card ] <;> aesop;
          have := h_basis.ge ( Submodule.mem_top : w ∈ ⊤ ) ; rw [ Submodule.mem_span_range_iff_exists_fun ] at this; tauto;
        have h_zero : ⟪w, w⟫ = 0 := by
          simp_all +decide [ inner_sum, inner_smul_right ];
        exact hw_ne ( by simpa [ inner_self_eq_norm_sq_to_K ] using h_zero ));
      exact ⟨ i, by obtain ⟨ k, hk ⟩ := h_int i; norm_num [ hk ] ; exact mod_cast abs_pos.mpr ( show ( k : ℝ ) ≠ 0 from mod_cast by aesop ) ⟩

/-
Any non-zero lattice vector is in the complement of at least one of the halfspaces defined by u_i or -u_i.
-/
private lemma covering_of_nonzero {n : ℕ+} (L : EuclideanLattice n n)
    (u : Fin n → 𝓔 n) (hu : ∀ i, ‖u i‖ = 1) (t : ℝ)
    (h_cover : ∀ w ∈ L.carrier, w ≠ 0 → ∃ i, |inner ℝ w (u i)| ≥ t) :
    ∀ w ∈ L.carrier, w ≠ 0 → ∃ i, w ∈ (AffineHalfSpace (u i) (hu i) t)ᶜ ∨ w ∈ (AffineHalfSpace (-(u i)) (by simp [hu]) t)ᶜ := by
      intro w hw hw'; rcases h_cover w hw hw' with ⟨ i, hi ⟩ ; use i; cases abs_cases ( ⟪w, u i⟫ ) <;> simp_all +decide [ AffineHalfSpace ] ;
      · exact Or.inl ( by rwa [ real_inner_comm ] );
      · exact Or.inr ( by rw [ real_inner_comm ] ; linarith )

/-
The Gaussian mass of a union of sets is at most the sum of the Gaussian masses of the individual sets.
-/
lemma rhoMassOn_le_sum {n : ℕ+} (L : EuclideanLattice n n) {ι : Type*} [Fintype ι] (S : ι → Set (𝓔 n)) :
    rhoMassOn 0 L (⋃ i, S i) ≤ ∑ i, rhoMassOn 0 L (S i) := by
  -- By definition of rhoMassOn, we can expand the left-hand side as a sum over lattice vectors.
  simp [rhoMassOn];
  have h_union_expansion : ∀ v : L.carrier, (⋃ i, S i).indicator rho (v : 𝓔 n) ≤ ∑ i, (S i).indicator rho (v : 𝓔 n) := by
    intro v
    simp [Set.indicator];
    split_ifs <;> simp_all +decide [ Finset.sum_ite ];
    exact le_mul_of_one_le_left ( by exact le_of_lt ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by unfold rho; positivity ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ( mod_cast Finset.card_pos.mpr ⟨ Classical.choose ‹∃ i, ( v : 𝓔 n ) ∈ S i›, by simpa using Classical.choose_spec ‹∃ i, ( v : 𝓔 n ) ∈ S i› ⟩ );
  -- By definition of summability, we can interchange the order of summation.
  have h_summable : Summable (fun v : L.carrier => (⋃ i, S i).indicator rho (v : 𝓔 n)) ∧ ∀ i, Summable (fun v : L.carrier => (S i).indicator rho (v : 𝓔 n)) := by
    have h_summable : Summable (fun v : L.carrier => rho (v : 𝓔 n)) := by
      convert summable_rhoMassOn 0 L _ using 1;
      swap;
      exact Set.univ;
      aesop;
    refine' ⟨ _, fun i => _ ⟩;
    · refine' .of_nonneg_of_le ( fun v => _ ) ( fun v => _ ) h_summable;
      · exact Set.indicator_nonneg ( fun _ _ => Real.exp_nonneg _ ) _;
      · by_cases hv : ( v : 𝓔 n ) ∈ ⋃ i, S i <;> simp +decide [ hv ];
        exact Real.exp_nonneg _;
    · refine' Summable.of_nonneg_of_le ( fun v => _ ) ( fun v => _ ) h_summable;
      · by_cases hi : v.val ∈ S i <;> simp +decide [ hi ];
        exact Real.exp_nonneg _;
      · by_cases hi : v.val ∈ S i <;> simp +decide [ hi ];
        exact Real.exp_nonneg _;
  have h_summable : ∑' v : L.carrier, (⋃ i, S i).indicator rho (v : 𝓔 n) ≤ ∑' v : L.carrier, ∑ i, (S i).indicator rho (v : 𝓔 n) := by
    apply_rules [ Summable.tsum_le_tsum ];
    · exact h_summable.1;
    · exact summable_sum fun i _ => h_summable.2 i;
  have h_fubini : ∑' v : L.carrier, ∑ i, (S i).indicator rho (v : 𝓔 n) = ∑ i, ∑' v : L.carrier, (S i).indicator rho (v : 𝓔 n) := by
    have h_fubini : ∀ {f : ι → L.carrier → ℝ}, (∀ i, Summable (fun v : L.carrier => f i v)) → (∑' v : L.carrier, ∑ i, f i v) = ∑ i, ∑' v : L.carrier, f i v := by
      exact fun {f} a => Summable.tsum_finsetSum fun i a_1 => a i;
    exact h_fubini fun i => by tauto;
  convert h_summable.trans_eq h_fubini using 1

/-
If every non-zero lattice vector is outside at least one of the slabs defined by u_i and t, then the total Gaussian mass of non-zero vectors is bounded by the sum of the masses outside each halfspace.
-/
private lemma rhoMass_le_sum_halfspaces {n : ℕ+} (L : EuclideanLattice n n)
  (u : Fin n → 𝓔 n) (hu : ∀ i, ‖u i‖ = 1) (t : ℝ)
  (h_cover : ∀ w ∈ L.carrier, w ≠ 0 → ∃ i, |inner ℝ w (u i)| ≥ t) :
  rhoMassOn 0 L {0}ᶜ ≤ ∑ i : Fin n, (rhoMassOn 0 L (AffineHalfSpace (u i) (hu i) t)ᶜ + rhoMassOn 0 L (AffineHalfSpace (-(u i)) (by simp [hu]) t)ᶜ) := by

  have h_union : {0}ᶜ ∩ (L.carrier : Set (𝓔 n)) ⊆ ⋃ i, ((AffineHalfSpace (u i) (hu i) t)ᶜ ∪ (AffineHalfSpace (-(u i)) (by
  rw [ norm_neg, hu ]) t)ᶜ) := by
    intros w hw;
    rcases h_cover _ hw.2 hw.1 with ⟨ i, hi ⟩ ; simp_all +decide [ AffineHalfSpace ];
    exact ⟨ i, by rw [ real_inner_comm ] ; cases abs_cases ( ⟪w, u i⟫ ) <;> first | left; linarith | right; linarith ⟩
  generalize_proofs at *;
  refine' le_trans ( _ : _ ≤ _ ) ( _ : _ ≤ _ );
  exact rhoMassOn 0 L ( ⋃ i, ( AffineHalfSpace ( u i ) ( hu i ) t ) ᶜ ∪ ( AffineHalfSpace ( -u i ) ( by simpa using ‹∀ i, ‖-u i‖ = 1› i ) t ) ᶜ );
  · apply_rules [ Summable.tsum_le_tsum ];
    · intro i; by_cases hi : ( i : 𝓔 n ) = 0 <;> simp_all +decide [ Set.indicator ] ;
      · split_ifs <;> norm_num [ rhoST ];
        exact Real.exp_nonneg _;
      · rw [ if_pos ];
        convert h_union ⟨ _, _ ⟩ <;> aesop;
    · convert summable_rhoMassOn 0 L { 0 } ᶜ using 1;
    · convert summable_rhoMassOn 0 L _;
  · refine' le_trans ( _ : _ ≤ _ ) ( Finset.sum_le_sum fun i _ => _ );
    convert rhoMassOn_le_sum L _;
    convert rhoMassOn_le_sum L _;
    any_goals exact Fin 2;
    rotate_right;
    use fun j => if j = 0 then ( AffineHalfSpace ( u i ) ( hu i ) t ) ᶜ else ( AffineHalfSpace ( -u i ) ( by simpa using ‹∀ i, ‖-u i‖ = 1› i ) t ) ᶜ;
    all_goals try infer_instance;
    · ext; simp ;
    · rw [ Fin.sum_univ_two ] ; aesop

/-
If the non-zero lattice vectors are covered by the complements of halfspaces defined by `u_i` and `t`, then the Gaussian mass of the non-zero vectors is bounded by `2n * exp(-pi * t^2) * rho(L)`.
-/
private lemma rhoMass_nonzero_bound_of_covering {n : ℕ+} (L : EuclideanLattice n n)
  (u : Fin n → 𝓔 n) (hu : ∀ i, ‖u i‖ = 1) (t : ℝ) (ht : t ≥ 0)
  (h_cover : ∀ w ∈ L.carrier, w ≠ 0 → ∃ i, |inner ℝ w (u i)| ≥ t) :
  rhoMassOn 0 L {0}ᶜ ≤ 2 * n * Real.exp (-Real.pi * t^2) * rhoMass 0 L := by

  -- Applying the lemma `rhoMass_affine_half_space_tail_bound` to each halfspace.
  have h_bound : ∀ i, rhoMassOn 0 L (AffineHalfSpace (u i) (hu i) t)ᶜ ≤ Real.exp (-Real.pi * t^2) * rhoMass 0 L := by
    exact fun i => rhoMass_affine_half_space_tail_bound L (u i) (hu i) t ht 0;
  convert le_trans ( rhoMass_le_sum_halfspaces L u hu t h_cover ) ?_;
  refine' le_trans ( Finset.sum_le_sum fun i _ => add_le_add ( h_bound i ) _ ) _;
  use fun i => Real.exp ( -Real.pi * t ^ 2 ) * rhoMass 0 L;
  · convert rhoMass_affine_half_space_tail_bound L ( -u i ) ( by simpa using hu i ) t ht 0 using 1;
  · norm_num ; ring_nf ; norm_num

/-
If the n-th successive minimum of L is at most 1/t, then the Gaussian mass of the non-zero dual vectors is bounded by 2n * exp(-pi * t^2) * rho(L*).
-/
lemma rhoMass_dual_bound {n : ℕ+} (L : EuclideanLattice n n) (t : ℝ) (ht : t > 0)
  (h_lambda : L.succMinₙ ≤ 1 / t) :
  rhoMassOn 0 L.dual {0}ᶜ ≤ 2 * n * Real.exp (-Real.pi * t^2) * rhoMass 0 L.dual := by
  -- By definition of successive minima, there exist vectors $v_i \in L$ such that $\|v_i\| = \lambda_i(L)$ and these vectors are linearly independent.
  obtain ⟨v, hv⟩ : ∃ v : Fin n → 𝓔 n, LinearIndependent ℝ v ∧ (∀ i, v i ∈ L.carrier) ∧ (∀ i, ‖v i‖ ≤ 1 / t) := by
    have := L.linearIndependent_successiveMinima_attained;
    obtain ⟨ v, hv₁, hv₂ ⟩ := this;
    refine' ⟨ v, hv₂, fun i => _, fun i => _ ⟩;
    · exact hv₁ i |>.1.1;
    · have := h_lambda;
      refine' le_trans _ this;
      have h_succMin_le : ∀ i j : Fin n, i ≤ j → L.successiveMinima i ≤ L.successiveMinima j := by
        exact fun i j a => EuclideanLattice.successiveMinima_mono L a;
      exact hv₁ i |>.2.symm ▸ h_succMin_le _ _ ( Nat.le_pred_of_lt i.2 );
  -- Let $u_i = v_i / \|v_i\|$.
  obtain ⟨u, hu⟩ : ∃ u : Fin n → 𝓔 n, (∀ i, ‖u i‖ = 1) ∧ (∀ i, u i = (1 / ‖v i‖) • v i) := by
    use fun i => (1 / ‖v i‖) • v i;
    norm_num +zetaDelta at *;
    intro i; rw [ norm_smul, norm_inv, norm_norm ] ; by_cases hi : v i = 0 <;> simp_all +decide [ hv.1.ne_zero ] ;
  -- For any $w \in L^* \setminus \{0\}$, by `exists_dual_inner_ge_one`, there exists $i$ such that $|\langle w, v_i \rangle| \ge 1$.
  have h_cover : ∀ w ∈ L.dual.carrier, w ≠ 0 → ∃ i, |inner ℝ w (u i)| ≥ t := by
    intros w hw hw_ne_zero
    obtain ⟨i, hi⟩ : ∃ i, 1 ≤ |inner ℝ w (v i)| := by
      apply exists_dual_inner_ge_one L w hw hw_ne_zero v hv.1 hv.2.1;
    use i; simp_all +decide [ inner_smul_right ];
    rw [ inv_mul_eq_div, le_div_iff₀ ] <;> nlinarith [ norm_pos_iff.mpr ( show v i ≠ 0 from by intro h; norm_num [ h ] at hi ), hv.2.2 i, mul_inv_cancel₀ ( ne_of_gt ht ) ];
  convert rhoMass_nonzero_bound_of_covering L.dual u hu.1 t ht.le h_cover using 1

/-
The dual of a lattice scaled by c is equivalent to the dual of the original lattice scaled by 1/c.
-/
lemma dual_smul_eq_smul_inv {n : ℕ+} (L : EuclideanLattice n n) (c : ℝ) (hc : c ≠ 0) :
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

/-
If the scaled n-th successive minimum is small enough, the Gaussian mass of the dual tail is bounded.
-/
lemma rhoSMass_dual_bound_scaled {n : ℕ+} (L : EuclideanLattice n n) (s t : ℝ) (hs : s > 0) (ht : t > 0)
    (h_lambda : L.succMinₙ / s ≤ 1 / t) :
    rhoSMassOn (1 / s) 0 L.dual {0}ᶜ ≤ 2 * n * Real.exp (-Real.pi * t^2) * rhoSMass (1 / s) 0 L.dual := by
      convert rhoMass_dual_bound ( L.smul ( 1/s ) ( by positivity ) ) t ht _ using 1;
      · rw [ rhoSMassOn_scale ];
        -- Since the dual of a lattice scaled by $c$ is the dual of the original lattice scaled by $1/c$, we have:
        have h_dual_smul : (L.smul (1 / s) (by positivity)).dual ≡ᵤ L.dual.smul s (by positivity) := by
          convert dual_smul_eq_smul_inv L ( 1 / s ) ( by positivity ) using 1;
          norm_num;
        have h_dual_smul : ∀ (L L' : EuclideanLattice n n) (S : Set (𝓔 n)), L ≡ᵤ L' → rhoMassOn 0 L S = rhoMassOn 0 L' S := by
          intros L L' S hL_L'
          simp [rhoMassOn];
          unfold EuclideanLattice.latticeSum;
          have h_dual_smul : L.carrier = L'.carrier := by
            exact hL_L';
          rw [ h_dual_smul ];
        convert h_dual_smul _ _ _ ‹_› |> Eq.symm using 1;
        congr! 1;
        ext; simp [Set.mem_smul_set];
        exact ⟨ fun hx => ⟨ ( 1 / s ) • ‹_›, by simpa [ hs.ne' ] using hx, by simp +decide [ hs.ne' ] ⟩, by rintro ⟨ y, hy, rfl ⟩ ; simpa [ hs.ne' ] using hy ⟩;
      · congr! 1;
        have h_dual_smul : (L.smul (1 / s) (by positivity)).dual ≡ᵤ L.dual.smul s (by positivity) := by
          convert dual_smul_eq_smul_inv L ( 1 / s ) ( by positivity ) using 1;
          norm_num;
        have h_dual_smul : ∀ (L L' : EuclideanLattice n n), L ≡ᵤ L' → rhoMass 0 L = rhoMass 0 L' := by
          intros L L' h_equiv;
          unfold rhoMass;
          unfold EuclideanLattice.latticeSum;
          have h_dual_smul : L.carrier = L'.carrier := by
            exact h_equiv;
          rw [ h_dual_smul ];
        convert h_dual_smul _ _ ‹_› |> Eq.symm using 1;
        exact rhoSMass_scale s hs L.dual;
      · refine' le_trans _ h_lambda;
        -- Apply the lemma that states the n-th successive minimum of a scaled lattice is the original n-th successive minimum multiplied by the scaling factor.
        have h_succMinₙ_smul : ∀ (L : EuclideanLattice n n) (s : ℝ) (hs : s > 0), (L.smul s hs.ne').succMinₙ = s * L.succMinₙ := by
          exact fun L s hs =>
            EuclideanLattice.successiveMinima_scale L ⟨↑n - 1, EuclideanLattice.succMinₙ._proof_1⟩ s
              hs;
        rw [ h_succMinₙ_smul L ( 1 / s ) ( one_div_pos.mpr hs ), one_div, inv_mul_eq_div ]

/-
Helper lemma to simplify the exponential term in the Micciancio-Regev bound.
-/
lemma exp_neg_pi_t_sq (n : ℕ+) (ε : ℝ) (hε : ε > 0) (hn : 1 ≤ (n : ℝ)) :
    let t := Real.sqrt (Real.log (2 * n * (1 + 1 / ε)) / Real.pi)
    Real.exp (-Real.pi * t^2) = ε / (2 * n * (1 + ε)) := by
      field_simp;
      -- Simplify the exponent using properties of logarithms and exponents.
      have h_exp : Real.exp (-(Real.pi * (Real.sqrt (Real.log (2 * n * (ε + 1) / ε) / Real.pi)) ^ 2)) = 1 / (2 * n * (ε + 1) / ε) := by
        rw [ Real.sq_sqrt ( div_nonneg ( Real.log_nonneg <| by rw [ le_div_iff₀ hε ] ; nlinarith [ show ( n : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr n.pos ] ) Real.pi_pos.le ), mul_div_cancel₀ _ Real.pi_ne_zero, Real.exp_neg, Real.exp_log ( by positivity ) ] ; norm_num;
      -- Substitute h_exp into the goal.
      rw [h_exp];
      -- Simplify the resulting expression.
      field_simp;
      ring

-- /-- For any ε>0 and (full-rank) n-dimensional lattice L, we have
--   η_ε(L) ≤ λ_n(L) * Real.sqrt (\ln (2n(1 + 1/ε)) / π)
-- -/
theorem smoothing_parameter_ub_micciancio_regev_by_succMinₙ (L : EuclideanLattice n n) (hn : n ≥ Banaszczyk_transference_threshold_constant) (ε : ℝ) (hε : ε > 0) :
    L.η ε ≤ L.succMinₙ * Real.sqrt (Real.log (2 * n * (1 + 1 / ε)) / Real.pi) := by
  let t := Real.sqrt (Real.log (2 * n * (1 + 1 / ε)) / Real.pi)
  let s := L.succMinₙ * t
  have h_n_ge_1 : 1 ≤ (n : ℝ) := by
    exact Nat.one_le_cast.mpr n.2
  have ht : 0 < t := by
    exact Real.sqrt_pos_of_pos <| div_pos ( Real.log_pos <| by nlinarith [ show ( n : ℝ ) ≥ 2 by exact_mod_cast hn, one_div_mul_cancel hε.ne' ] ) Real.pi_pos
  have hs : 0 < s := by
    exact mul_pos ( L.successiveMinima_pos ⟨ n - 1, Nat.sub_lt n.pos one_pos ⟩ ) ht
  have h_lambda : L.succMinₙ / s ≤ 1 / t := by
    -- Substitute s with L.succMinₙ * t in the inequality.
    field_simp [s];
    exact le_rfl
  have h_bound : rhoSMassOn (1 / s) 0 L.dual {0}ᶜ ≤ 2 * n * Real.exp (-Real.pi * t^2) * rhoSMass (1 / s) 0 L.dual := by
    apply rhoSMass_dual_bound_scaled L s t hs ht h_lambda
  have h_exp : Real.exp (-Real.pi * t^2) = ε / (2 * n * (1 + ε)) := by
    apply exp_neg_pi_t_sq n ε hε h_n_ge_1
  rw [h_exp] at h_bound
  have h_ineq : rhoSMassOn (1 / s) 0 L.dual {0}ᶜ ≤ (ε / (1 + ε)) * rhoSMass (1 / s) 0 L.dual := by
    convert h_bound using 1 ; ring_nf;
    -- Simplify the right-hand side of the inequality.
    field_simp
    ring
  have h_smoothing : s ≥ L.η ε := by
    exact (rhoSMassOn_nonzero_in_smoothing_regime L s hs ε hε) h_ineq
  exact h_smoothing

end tight_upperbound

end LatticeCrypto.Foundations.Gaussian
