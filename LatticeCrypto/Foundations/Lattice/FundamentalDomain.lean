import LatticeCrypto.Foundations.Lattice.Defs
import LatticeCrypto.Foundations.Lattice.Basic
import LatticeCrypto.Utils.Geometry
import LatticeCrypto.Utils.Vec

open LatticeCrypto.Utils.Vec
open LatticeCrypto.Utils.Geometry
open scoped ENNReal NNReal Pointwise
open scoped RealInnerProductSpace


/-!
  This file defines fundamental domains for `EuclideanLattice` and `LatticeBasis`.

  - `LatticeBasis.fundamentalDomain`
  - `LatticeBasis.centeredFundamentalDomain`

-/

namespace LatticeCrypto.Foundations.Lattice

variable {n k : ℕ+}

/-!
## Fundamental Domain and Determinant
-/

noncomputable section fundamental_domain

/-- The fundamental parallelepiped of a lattice basis. -/
def LatticeBasis.fundamentalDomain (B : SquareLatticeBasis n) : Set (𝓔 n) :=
  ZSpan.fundamentalDomain B.asTopBasis

/-- We define the closure of the fundamental parallelepiped as generated with coefficents from [0, 1] -/
def LatticeBasis.fundamentalDomain_closure (B : SquareLatticeBasis n) : Set (𝓔 n) :=
  {m | ∀ i, B.asTopBasis.repr m i ∈ Set.Icc (0 : ℝ) 1}

/-- The closure defined as above is indeed a topological closure -/
theorem LatticeBasis.fundamentalDomain.closure_apply (B : SquareLatticeBasis n) :
  B.fundamentalDomain_closure = closure B.fundamentalDomain := by
  -- The closure of the fundamental domain is the set of points where each coordinate is in [0, 1], which is exactly the fundamental domain closure.
  ext; simp [LatticeBasis.fundamentalDomain_closure, LatticeBasis.fundamentalDomain];
  rw [ mem_closure_iff_seq_limit ] ; aesop (config := { warnOnNonterminal := false });
  · refine' ⟨ fun n => ( 1 - 1 / ( n + 1 ) : ℝ ) • x, _, _ ⟩ <;> aesop (config := { warnOnNonterminal := false });
    · exact mul_nonneg ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| by linarith ) <| a i |>.1;
    · nlinarith [ a i, inv_mul_cancel₀ ( by linarith : ( n_1 : ℝ ) + 1 ≠ 0 ) ];
    · exact le_trans ( Filter.Tendsto.smul ( tendsto_const_nhds.sub <| tendsto_inv_atTop_zero.comp <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) tendsto_const_nhds ) ( by norm_num );
  · -- Since the coordinate function is continuous, the limit of the coordinates of $w_n$ is the coordinate of $x$.
    have h_coord_cont : Filter.Tendsto (fun n => (B.asTopBasis.repr (w n)) i) Filter.atTop (nhds ((B.asTopBasis.repr x) i)) := by
      have h_coord_cont : Continuous (fun x => (B.asTopBasis.repr x) i) := by
        exact Continuous.comp ( continuous_apply i ) ( by exact
          (Module.Basis.continuous_coe_repr (asTopBasis B)) );
      exact h_coord_cont.continuousAt.tendsto.comp right;
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_coord_cont fun n => left n i |>.1;
  · have h_closure : Filter.Tendsto (fun n => (B.asTopBasis.repr (w n)) i) Filter.atTop (nhds ((B.asTopBasis.repr x) i)) := by
      have h_coord_cont : Continuous (fun x => (B.asTopBasis.repr x) i) := by
        exact Continuous.comp ( continuous_apply i ) ( by exact
          (Module.Basis.continuous_coe_repr (asTopBasis B)) );
      exact h_coord_cont.continuousAt.tendsto.comp right;
    exact le_of_tendsto_of_tendsto' h_closure tendsto_const_nhds fun n => left n i |>.2.le

/-- The fundamental parallelepiped of a lattice basis is convex. -/
theorem LatticeBasis.fundamentalDomain_measurableSet (B : SquareLatticeBasis n) : MeasurableSet B.fundamentalDomain := by
  exact ZSpan.fundamentalDomain_measurableSet B.asTopBasis

/-- Theorem proving that `LatticeBasis.fundamentalDomain` is indeed a fundamental domain w.r.t.
  the Lebesgue measure over its ZSpan
 -/
theorem LatticeBasis.fundamentalDomain_isAddFundamentalDomain (B : SquareLatticeBasis n) :
MeasureTheory.IsAddFundamentalDomain (↥(Submodule.span ℤ (Set.range B.asTopBasis)))
    (B.fundamentalDomain) lebesgueMeasure := by
  exact ZSpan.isAddFundamentalDomain B.asTopBasis lebesgueMeasure

/-- The fundamental parallelepiped of a lattice basis is convex. -/
theorem LatticeBasis.fundamentalDomain_isBounded (B : SquareLatticeBasis n) : Bornology.IsBounded B.fundamentalDomain := by
  exact ZSpan.fundamentalDomain_isBounded B.asTopBasis

/-- The fundamental parallelepiped of a lattice basis is convex. -/
theorem LatticeBasis.fundamentalDomain_isConvex (B : SquareLatticeBasis n) : Convex ℝ B.fundamentalDomain := by
  refine' convex_iff_forall_pos.mpr _;
  unfold LatticeBasis.fundamentalDomain; aesop (config := { warnOnNonterminal := false });
  · nlinarith [ a i, a_1 i ];
  · nlinarith [ a i, a_1 i ]

/-- The determinant of a square lattice basis. -/
noncomputable def LatticeBasis.det (B : SquareLatticeBasis n) : ℝ :=
  B.asMatrix.det

/-- The volume of a square lattice basis. -/
noncomputable def LatticeBasis.volume (B : SquareLatticeBasis n) : ℝ :=
  |B.asMatrix.det|

theorem LatticeBasis.volume_pos (B : SquareLatticeBasis n) : 0 < B.volume := by
  rw [volume, abs_pos]
  exact B.det_ne_zero

/- The volume (as ENNReal) of a square lattice basis equals the Lebesgue measure of its fundamental domain. -/
@[simp]
theorem LatticeBasis.volume_fundamentalDomain (B : SquareLatticeBasis n) : lebesgueMeasure B.fundamentalDomain = ENNReal.ofReal B.volume := by
  unfold LatticeBasis.fundamentalDomain LatticeBasis.volume --lebesgueMeasure
  let mb := B.asTopBasis
  rw [ZSpan.measure_fundamentalDomain mb lebesgueMeasure (b₀ := stdBasis)]
  rw [volume_fundamentalDomain_stdBasis, mul_one, Module.Basis.det_apply]
  congr
  rw [toMatrix_on_stdBasis_eq_self mb, LatticeBasis.coe_topBasis, LatticeBasis.asMatrix]

/- The volume of a square lattice basis equals the Lebesgue measure (as Real) of its fundamental domain. -/
@[simp]
theorem LatticeBasis.volume_real_fundamentalDomain (B : SquareLatticeBasis n) : (lebesgueMeasure B.fundamentalDomain).toReal = B.volume := by
  convert congr_arg ENNReal.toReal ( LatticeBasis.volume_fundamentalDomain B ) using 1;
  unfold LatticeBasis.volume; aesop


/-- Determinant is invariant under unimodular equivalence. -/
theorem LatticeBasis.volume_of_unimodularEquiv {B1 B2 : SquareLatticeBasis n}
    (h : B1 =ᵤ B2) : B1.volume = B2.volume := by
  obtain ⟨U, rfl⟩ := h
  rw [ show B1.volume = |Matrix.det ( B1.asMatrix )| by rfl, show ( B1 ◾ U ).volume = |Matrix.det ( ( B1.asMatrix * ( U.val.map ( Int.castRingHom ℝ ) ) ) )| by rfl ] ; simp +decide [ Matrix.det_mul ];
  -- Since U is a unit in the matrix ring over ℤ, its determinant is ±1.
  have h_det_U : IsUnit (Matrix.det U.val) := by
    exact Matrix.isUnits_det_units U;
  -- Since U is a unit in the matrix ring over ℤ, its determinant is ±1. Therefore, the absolute value of the determinant of U is 1.
  have h_det_U_abs : |(U.val.det : ℝ)| = 1 := by
    rcases Int.isUnit_iff.mp h_det_U with ( h | h ) <;> norm_num [ h ];
  simp_all +decide [ Matrix.det_apply' ]

/-- The determinant (covolume) of a lattice. -/
noncomputable def EuclideanLattice.det (L : EuclideanLattice n n) : ℝ :=
  L.basis.volume

/-- Well-definedness of lattice determinant. -/
theorem EuclideanLattice.det_def (L : EuclideanLattice n n) :
    L.det = L.basis.volume := by rfl

theorem EuclideanLattice.det_pos (L : EuclideanLattice n n) :
    L.det > 0 := by exact L.basis.volume_pos

theorem EuclideanLattice.det_eq_of_equiv {L1 L2 : EuclideanLattice n n}
    (h : L1 ≡ᵤ L2) : L1.det = L2.det := by
  rw [eq_iff_basis_equiv] at h
  exact LatticeBasis.volume_of_unimodularEquiv h

/-- The det of the dual lattice is simply the inverse -/
theorem LatticeBasis.dual_volume_eq_inv (B : SquareLatticeBasis n) :
    B.dual.volume = 1 / B.volume := by
  simp [LatticeBasis.volume];
  rw [ LatticeBasis.dual_asMatrix ];
  simp +decide [ Matrix.det_transpose ]

theorem EuclideanLattice.dual_det_eq_inv (L : EuclideanLattice n n) :
    L.dual.det = 1 / L.det := by
  -- Apply the theorem that states the volume of the dual basis is the inverse of the volume of the original basis.
  have h_det_inv : L.basis.dual.volume = 1 / L.basis.volume := by
    exact LatticeBasis.dual_volume_eq_inv L.basis;
  -- Apply the theorem that states the volume of the dual basis is the inverse of the volume of the original basis to conclude the proof.
  convert h_det_inv using 1

/-- Theorem proving that `LatticeBasis.fundamentalDomain` is indeed a fundamental domain.
  over its ZSpan
 -/
theorem EuclideanLattice.fundamentalDomain_isAddFundamentalDomain (L : EuclideanLattice n n) (μ : MeasureTheory.Measure (𝓔 n)) :
MeasureTheory.IsAddFundamentalDomain (↥L.carrier)
    (L.basis.fundamentalDomain) μ := by
  rw [L.full_rank_eq_module_span]
  exact ZSpan.isAddFundamentalDomain L.basis.asTopBasis μ


/-- The det of a lattice equals the Lebesgue measure (converted to real) of its fundamental domain. -/
theorem EuclideanLattice.det_eq_real_measure_fundamentalDomain (L : EuclideanLattice n n) :
    L.det = (lebesgueMeasure L.basis.fundamentalDomain).toReal := by
  rw [LatticeBasis.volume_real_fundamentalDomain L.basis]
  bound

/-- The det (on ENNReal) of a lattice equals the Lebesgue measure of its fundamental domain. -/
theorem EuclideanLattice.det_eq_measure_fundamentalDomain (L : EuclideanLattice n n) :
    ENNReal.ofReal L.det = lebesgueMeasure L.basis.fundamentalDomain := by
  rw [LatticeBasis.volume_fundamentalDomain L.basis]
  bound

/-- Reduce a vector modulo the fundamental domain. -/
noncomputable def LatticeBasis.mod (B : SquareLatticeBasis n) (v : 𝓔 n) : 𝓔 n :=
  ZSpan.fract B.asTopBasis v

/-- The reduction of a vector modulo the fundamental domain lies within the fundamental domain. -/
theorem LatticeBasis.mod_mem_fundamentalDomain (B : SquareLatticeBasis n) (v : 𝓔 n) :
    B.mod v ∈ B.fundamentalDomain := by
  exact ZSpan.fract_mem_fundamentalDomain B.asTopBasis v

/-- Any vector minus its module will lie in the lattice. -/
theorem LatticeBasis.sub_mod_mem_lattice (B : SquareLatticeBasis n) (v : 𝓔 n) :
    v - B.mod v ∈ B.toLattice.carrier := by
  rw [toLattice, mod]
  -- v - B.mod v = B * c - B * {c} = B * (c - {c}) = B * floor(c)
  refine' Submodule.mem_span.mpr _;
  aesop (config := { warnOnNonterminal := false });
  have := a ( Set.mem_range_self ( ⟨ 0, PNat.pos n ⟩ : Fin n ) ) ; simp_all +decide [ ZSpan.fract ] ;
  -- Since the floor of v is a linear combination of the basis vectors with integer coefficients, and each basis vector is in p, the floor of v is in p.
  have h_floor : ∀ (c : Fin n → ℤ), (∑ i, c i • B.cols i) ∈ p := by
    -- Since p is a submodule, it is closed under addition and scalar multiplication. Each basis vector is in p by hypothesis a, so multiplying each by an integer c_i keeps them in p. Then, adding them up should also keep the result in p.
    intros c
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply a
    simp [LatticeBasis.cols];
  unfold ZSpan.floor; aesop;

/-- The floor function is measurable because it is a step function. -/
lemma measurable_int_floor : Measurable (Int.floor : ℝ → ℤ) := by
  apply Monotone.measurable; exact Int.floor_mono

/-- Moding a basis' parallelpiped is a measurable function. -/
lemma LatticeBasis.measurable_mod {n : ℕ+} (B : SquareLatticeBasis n) : Measurable B.mod := by
  -- The fractional part function is measurable.
  have h_fract_measurable : Measurable (fun x : 𝓔 n => x - ∑ i, ⌊(B.asTopBasis.repr x) i⌋ • B.cols i) := by
    -- The floor function is measurable, and the sum of measurable functions is measurable.
    have h_floor_measurable : ∀ i, Measurable (fun x : 𝓔 n => ⌊(B.asTopBasis.repr x) i⌋) := by
      intro i;
      have h_floor : Measurable (fun x : ℝ => Int.floor x) := by
        exact measurable_int_floor;
      have h_floor : Measurable (fun x : Fin n → ℝ => Int.floor (x i)) := by
        exact h_floor.comp ( measurable_pi_apply i );
      convert h_floor.comp ( show Measurable ( fun x : LatticeCrypto.Utils.Vec.𝓔 n => ( B.asTopBasis.repr x : Fin n → ℝ ) ) from ?_ ) using 1;
      convert ( Continuous.measurable ( show Continuous ( fun x : LatticeCrypto.Utils.Vec.𝓔 n => ( B.asTopBasis.repr x : Fin n → ℝ ) ) from ?_ ) ) using 1;
      exact Module.Basis.continuous_coe_repr (asTopBasis B);
    fun_prop;
  unfold LatticeBasis.mod; simp +decide [ ZSpan.fract ] ;
  unfold ZSpan.floor ; aesop


/-- Corollary: Any vector v can be decomposed into a lattice point and a point in the fundamental domain. -/
theorem EuclideanLattice.sub_mod_mem_lattice (L : EuclideanLattice n n) (v : 𝓔 n) :
    v - L.basis.mod v ∈ L.carrier := by
  rw [L.carrier_eq]
  exact L.basis.sub_mod_mem_lattice v

/-- Any vector v can be decomposed into a lattice point and a point in the fundamental domain. -/
theorem LatticeBasis.eq_lattice_add_mod (B : SquareLatticeBasis n) (v : 𝓔 n) :
    ∃ (u : 𝓔 n) (w : 𝓔 n), u ∈ B.toLattice.carrier ∧ w ∈ B.fundamentalDomain ∧ v = u + w := by
  use v - B.mod v, B.mod v
  refine ⟨B.sub_mod_mem_lattice v, B.mod_mem_fundamentalDomain v, by abel⟩

/-- The fundamental domain partitions the space into disjoint translates by lattice points. -/
theorem EuclideanLattice.partition_by_fundamentalDomain (L : EuclideanLattice n n) :
    ∀ v : 𝓔 n, ∃! x : L.carrier, v ∈ ((x : 𝓔 n) +ᵥ L.basis.fundamentalDomain) := by
  intro v

  -- Step 1: Existence - every vector can be written as lattice point + fundamental domain point
  have h_exists : ∃ x : L.carrier, v ∈ ((x : 𝓔 n) +ᵥ L.basis.fundamentalDomain) := by
    -- By the decomposition theorem, v = u + w where u ∈ L and w ∈ fundamentalDomain
    obtain ⟨u, w, hu_L, hw_fd, h_eq⟩ := L.basis.eq_lattice_add_mod v
    -- u is a lattice point, so it corresponds to some x ∈ L.carrier
    have hu_carrier : ∃ x : L.carrier, (x : 𝓔 n) = u := by
      -- u ∈ L.carrier by hu_L
      rw [← L.eq_basis_toLattice] at hu_L
      use ⟨u, hu_L⟩
    obtain ⟨x, hx_eq⟩ := hu_carrier
    -- v = u + w = x + w, so v ∈ x + fundamentalDomain
    use x
    rw [hx_eq, h_eq]
    exact mem_leftAddCoset u hw_fd

  -- Step 2: Uniqueness - the lattice point is unique
  have h_unique : ∀ x y : L.carrier,
      v ∈ ((x : 𝓔 n) +ᵥ L.basis.fundamentalDomain) →
      v ∈ ((y : 𝓔 n) +ᵥ L.basis.fundamentalDomain) →
      x = y := by
    intro x y hx_fd hy_fd
    -- If v ∈ x + P and v ∈ y + P, then v - x ∈ P and v - y ∈ P
    have hx_in_fd : v - (x : 𝓔 n) ∈ L.basis.fundamentalDomain := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hx_fd
      convert hx_fd using 1
      simp +decide [ sub_eq_add_neg, add_comm ]

    have hy_in_fd : v - (y : 𝓔 n) ∈ L.basis.fundamentalDomain := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hy_fd
      convert hy_fd using 1
      simp [add_comm, sub_eq_add_neg]

    -- Then x - y = (v - y) - (v - x) ∈ L ∩ (P - P)
    have h_diff : (x : 𝓔 n) - (y : 𝓔 n) = (v - (y : 𝓔 n)) - (v - (x : 𝓔 n)) := by
      bound

    -- But the only lattice point in P - P is 0 (fundamental domain has bounded measure)
    have h_diff_mem_L : (x : 𝓔 n) - (y : 𝓔 n) ∈ L.carrier := by
      apply L.carrier.sub_mem; exact x.2; exact y.2

    have h_diff_in_fd_sub : (x : 𝓔 n) - (y : 𝓔 n) ∈ L.basis.fundamentalDomain - L.basis.fundamentalDomain := by
      rw [h_diff]
      apply Set.sub_mem_sub
      · exact hy_in_fd
      · exact hx_in_fd

    -- The only lattice point in the fundamental domain difference is 0
    have h_zero : (x : 𝓔 n) - (y : 𝓔 n) = 0 := by
      -- This follows from the fact that the fundamental domain is a fundamental domain
      -- i.e., each lattice point appears exactly once in the translates
      -- The intersection of a translate and the fundamental domain with another translate
      -- is empty unless they're the same translate
      -- If there's a non-zero element in the fundamental domain, then the fundamental domain isn't unique, which contradicts the definition of a fundamental domain.
      have h_unique : ∀ x y : 𝓔 n, x ∈ L.basis.fundamentalDomain → y ∈ L.basis.fundamentalDomain → x - y ∈ L.carrier → x = y := by
        intros x y hx hy hxy;
        -- Since $x$ and $y$ are in the fundamental domain, their coordinates are between 0 and 1. The difference $x - y$ must have integer coordinates because it's in the lattice. The only way for the difference to have integer coordinates is if each coordinate is 0.
        have h_coords : ∀ i, (L.basis.asTopBasis.repr (x - y) i) = 0 := by
          intro i
          have h_int : ∃ m : ℤ, (L.basis.asTopBasis.repr (x - y) i) = m := by
            have h_int : x - y ∈ Submodule.span ℤ (Set.range L.basis.asTopBasis) := by
              convert hxy using 1;
              exact Eq.symm (full_rank_eq_module_span L);
            rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at h_int;
            obtain ⟨ c, hc ⟩ := h_int; use c i; simp +decide [ ← hc, Finsupp.sum_fintype ] ;
            have h_coeff : ∀ j : Fin n, (L.basis.asTopBasis.repr (L.basis.basis j)) i = if j = i then 1 else 0 := by
              intro j; rw [ show L.basis.basis j = L.basis.asTopBasis j from by aesop ] ;
              rw [ L.basis.asTopBasis.repr_self ] ; aesop;
            simp +decide [ h_coeff ]
          obtain ⟨ m, hm ⟩ := h_int;
          have h_bound : -1 < (L.basis.asTopBasis.repr (x - y) i) ∧ (L.basis.asTopBasis.repr (x - y) i) < 1 := by
            have := hx i; have := hy i; norm_num at *; constructor <;> linarith;
          rcases m with ⟨ _ | _ | m ⟩ <;> norm_num at hm h_bound ⊢ <;> linarith;
        exact sub_eq_zero.mp ( L.basis.asTopBasis.ext_elem fun i => by simpa using h_coords i );
      grind +ring -- Use fundamental domain uniqueness property


    -- Therefore x = y
    have : (x : 𝓔 n) = (y : 𝓔 n) := by
      apply eq_of_sub_eq_zero h_zero
    exact Subtype.ext this

  -- Combine existence and uniqueness
  obtain ⟨x, hx⟩ := h_exists
  use x
  exact ⟨hx, fun y hy => (h_unique x y hx hy).symm⟩


/-- The fundamental parallelepiped of a lattice basis whose center is shifted to the origin. -/
def LatticeBasis.centeredFundamentalDomain (B : SquareLatticeBasis n) : Set (𝓔 n) :=
  {m | ∀ i, B.asTopBasis.repr m i ∈ Set.Ico (-0.5 : ℝ) 0.5}

/-- We define the closure of the centered fundamental parallelepiped as generated with coefficents
    from [-0.5, 0.5] -/
def LatticeBasis.centeredFundamentalDomain_closure (B : SquareLatticeBasis n) : Set (𝓔 n) :=
  {m | ∀ i, B.asTopBasis.repr m i ∈ Set.Icc (-0.5 : ℝ) 0.5}

/-- The closure defined as above is indeed a topological closure -/
theorem LatticeBasis.centeredFundamentalDomain.closure_apply (B : SquareLatticeBasis n) :
  B.centeredFundamentalDomain_closure = closure B.centeredFundamentalDomain := by
  apply le_antisymm;
  · -- The closure of the centered fundamental domain is a subset of the closure of the fundamental domain because the coordinates of the centered fundamental domain are within the coordinates of the fundamental domain.
    intros x hx
    simp [LatticeBasis.centeredFundamentalDomain_closure] at hx;
    refine' mem_closure_iff_seq_limit.mpr _;
    use fun m => x - (1 / (m + 1) : ℝ) • ∑ i : Fin n, (B.asTopBasis.repr x i) • B.asTopBasis i;
    aesop (config := { warnOnNonterminal := false });
    · intro i; specialize hx i; norm_num at *;
      -- Since the sum is over the basis vectors, each term in the sum is (B.basis x_1) i. But the basis vectors are orthogonal, so the sum should simplify to x i. Therefore, the sum is equal to x i.
      have h_sum : ∑ x_1 : Fin n, (((LatticeBasis.asTopBasis B).repr : 𝓔 n → Fin (↑n : ℕ) →₀ ℝ) x : Fin (↑n : ℕ) → ℝ) x_1 * (((LatticeBasis.asTopBasis B).repr : 𝓔 n → Fin (↑n : ℕ) →₀ ℝ) (B.basis x_1) : Fin (↑n : ℕ) → ℝ) i = (((LatticeBasis.asTopBasis B).repr : 𝓔 n → Fin (↑n : ℕ) →₀ ℝ) x : Fin (↑n : ℕ) → ℝ) i := by
        -- Since the basis vectors are orthogonal, the sum simplifies to x i.
        have h_sum : ∀ j : Fin n, (((LatticeBasis.asTopBasis B).repr : 𝓔 n → Fin (↑n : ℕ) →₀ ℝ) (B.basis j) : Fin (↑n : ℕ) → ℝ) i = if j = i then 1 else 0 := by
          have := B.asTopBasis.repr_self; aesop;
        aesop;
      constructor <;> nlinarith [ inv_mul_cancel₀ ( by linarith : ( n_1 : ℝ ) + 1 ≠ 0 ) ]
    · exact le_trans ( tendsto_const_nhds.sub ( Filter.Tendsto.smul ( tendsto_inv_atTop_zero.comp ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) tendsto_const_nhds ) ) ( by norm_num );
  · intro m hm; replace hm := mem_closure_iff_seq_limit.mp hm; aesop (config := { warnOnNonterminal := false });
    -- Since the coordinates of $m$ are the limits of the coordinates of $w$, and each coordinate of $w$ is in $[-0.5, 0.5]$, it follows that each coordinate of $m$ is also in $[-0.5, 0.5]$.
    have h_coords : ∀ i, Filter.Tendsto (fun n => (B.asTopBasis.repr (w n) i)) Filter.atTop (nhds (B.asTopBasis.repr m i)) := by
      -- The basis representation is a continuous linear map, so if w converges to m, then the basis representation of w converges to the basis representation of m.
      have h_cont : Continuous (fun v : 𝓔 n => (B.asTopBasis.repr v : Fin n → ℝ)) := by
        exact Module.Basis.continuous_coe_repr (asTopBasis B);
      exact fun i => Filter.Tendsto.comp ( continuous_apply i |> Continuous.tendsto <| _ ) ( h_cont.tendsto m |> Filter.Tendsto.comp <| right );
    exact fun i => ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds ( h_coords i ) fun n => left n i |>.1, le_of_tendsto_of_tendsto' ( h_coords i ) tendsto_const_nhds fun n => left n i |>.2.le ⟩

/-- The shift vector: sum of half of each basis vector -/
noncomputable def LatticeBasis.halfBasisSum (B : SquareLatticeBasis n) : 𝓔 n :=
  ∑ i, (0.5 : ℝ) • B.cols i

/-- The centered fundamental domain equals the fundamental domain shifted by -½ ∑ bᵢ -/
theorem LatticeBasis.centeredFundamentalDomain_eq_shifted (B : SquareLatticeBasis n) :
    B.centeredFundamentalDomain = (fun v => v - B.halfBasisSum) '' B.fundamentalDomain := by
    unfold LatticeBasis.centeredFundamentalDomain; unfold LatticeBasis.fundamentalDomain; ext; aesop (config := { warnOnNonterminal := false });
    · refine' ⟨ x + LatticeBasis.halfBasisSum B, _, _ ⟩ <;> aesop (config := { warnOnNonterminal := false });
      · -- By definition of `halfBasisSum`, we know that its i-th component is 0.5.
        have h_halfBasisSum_i : ((B.asTopBasis.repr (LatticeBasis.halfBasisSum B)) i) = 0.5 := by
          -- The i-th component of the sum is the sum of the i-th components of each term.
          have h_halfBasisSum_i : ((B.asTopBasis.repr (LatticeBasis.halfBasisSum B)) i) = ∑ j : Fin n, (0.5 : ℝ) * (B.asTopBasis.repr (B.cols j)) i := by
            unfold LatticeBasis.halfBasisSum; aesop;
          -- Since the basis is a basis, the representation of each basis vector in the basis is the standard basis vector.
          have h_basis_rep : ∀ x : Fin n, (B.asTopBasis.repr (B.cols x)) = Finsupp.single x 1 := by
            aesop (config := { warnOnNonterminal := false });
            convert ( B.asTopBasis.repr_self x_1 ) using 1;
            unfold LatticeBasis.asTopBasis; aesop;
          simp_all +decide [ Finsupp.single_apply ];
        linarith [ a i ];
      · -- The i-th component of the halfBasisSum is 0.5 times the i-th component of the i-th basis vector, which is 1.
        have h_halfBasisSum_i : (((LatticeBasis.asTopBasis B).repr (LatticeBasis.halfBasisSum B)) i) = 0.5 := by
          -- The i-th component of the sum is the sum of the i-th components of each term.
          have h_halfBasisSum_i : ((B.asTopBasis.repr (LatticeBasis.halfBasisSum B)) i) = ∑ j : Fin n, (0.5 : ℝ) * (B.asTopBasis.repr (B.cols j)) i := by
            unfold LatticeBasis.halfBasisSum; aesop;
          -- Since the basis is a basis, the representation of each basis vector in the basis is the standard basis vector.
          have h_basis_rep : ∀ x : Fin n, (B.asTopBasis.repr (B.cols x)) = Finsupp.single x 1 := by
            aesop (config := { warnOnNonterminal := false });
            convert ( B.asTopBasis.repr_self x_1 ) using 1;
            unfold LatticeBasis.asTopBasis; aesop;
          simp_all +decide [ Finsupp.single_apply ];
        linarith [ a i ];
    · -- By definition of `halfBasisSum`, we have `halfBasisSum B = ∑ i, (0.5 : ℝ) • B.cols i`.
      have h_halfBasisSum : LatticeBasis.halfBasisSum B = ∑ i, (0.5 : ℝ) • B.asTopBasis i := by
        unfold LatticeBasis.asTopBasis; aesop;
      rw [ h_halfBasisSum ] ; norm_num [ left ] ;
      -- Since $B$ is a basis, the $i$-th coefficient of $B.basis j$ is $1$ if $j = i$ and $0$ otherwise.
      have h_coeff : ∀ j : Fin n, (B.asTopBasis.repr (B.basis j) i) = if j = i then 1 else 0 := by
        -- Since $B$ is a basis, the basis vectors are linearly independent. The representation of a vector in terms of a basis should give the coefficients that, when multiplied by the basis vectors and summed, give the original vector.
        have h_basis_rep : ∀ j : Fin n, (B.asTopBasis.repr (B.basis j)) = Finsupp.single j 1 := by
          intro j; exact (by
          convert B.asTopBasis.repr_self j;
          exact Eq.symm coe_topBasis);
        aesop;
      rw [ Finset.sum_congr rfl fun j _ => by rw [ h_coeff j ] ] ; aesop
    · unfold LatticeBasis.halfBasisSum; norm_num;
      have h_sum : ∑ x : Fin n, (1 / 2 : ℝ) * (((LatticeBasis.asTopBasis B).repr : 𝓔 n → Fin (↑n : ℕ) →₀ ℝ) (LatticeBasis.cols B x) : Fin (↑n : ℕ) → ℝ) i = (1 / 2 : ℝ) := by
        -- Since the basis vectors are linearly independent, their representations in the basis are the standard basis vectors.
        have h_basis_rep : ∀ i : Fin n, (B.asTopBasis.repr (B.cols i)) = Finsupp.single i 1 := by
          aesop (config := { warnOnNonterminal := false });
          convert B.asTopBasis.repr_self i_1 using 1;
          unfold LatticeBasis.asTopBasis; aesop;
        rw [ Finset.sum_eq_single i ] <;> aesop;
      linarith [ left i ]

/-- The fundamental parallelepiped of a lattice basis whose center is shifted to the origin is symmetric. -/
theorem LatticeBasis.centeredFundamentalDomain_closureIsSymmetric {x : 𝓔 n} (B: SquareLatticeBasis n) : x ∈ B.centeredFundamentalDomain_closure ↔ -x ∈ B.centeredFundamentalDomain_closure := by
  unfold LatticeBasis.centeredFundamentalDomain_closure; aesop (config := { warnOnNonterminal := false });
  · linarith [ a i ];
  · linarith [ a i ]

/-- The fundamental parallelepiped of a lattice basis is convex. -/
theorem LatticeBasis.centeredFundamentalDomain_isBounded (B : SquareLatticeBasis n) : Bornology.IsBounded B.centeredFundamentalDomain := by
  -- The centered fundamental domain is contained within a ball of radius 0.5 times the sum of the norms of the basis vectors.
  have h_bounded : ∃ C : ℝ, ∀ m ∈ B.centeredFundamentalDomain, ‖m‖ ≤ C := by
    -- The norm of a sum is less than or equal to the sum of the norms.
    have h_norm_sum : ∀ m : 𝓔 n, ‖m‖ ≤ ∑ i, |B.asTopBasis.repr m i| * ‖B.cols i‖ := by
      intros m
      have h_norm_sum : ‖m‖ ≤ ‖∑ i, (B.asTopBasis.repr m i) • B.cols i‖ := by
        rw [ ← B.asTopBasis.sum_repr m ];
        convert le_rfl;
        · exact B.asTopBasis.sum_repr m;
        · ext; simp [LatticeBasis.asTopBasis];
          rfl;
      -- Apply the triangle inequality to the sum.
      have h_triangle : ‖∑ i, (B.asTopBasis.repr m i) • B.cols i‖ ≤ ∑ i, ‖(B.asTopBasis.repr m i) • B.cols i‖ := by
        exact norm_sum_le _ _;
      exact h_norm_sum.trans ( h_triangle.trans_eq ( Finset.sum_congr rfl fun _ _ => by rw [ norm_smul, Real.norm_eq_abs ] ) );
    -- Since each coordinate of m is between -0.5 and 0.5, the absolute value of each coordinate is at most 0.5.
    have h_abs_coord : ∀ m ∈ B.centeredFundamentalDomain, ∀ i, |B.asTopBasis.repr m i| ≤ 0.5 := by
      exact fun m hm i => abs_le.mpr ⟨ by linarith [ Set.mem_Ico.mp ( hm i ) ], by linarith [ Set.mem_Ico.mp ( hm i ) ] ⟩;
    exact ⟨ ∑ i : Fin n, 0.5 * ‖B.cols i‖, fun m hm => le_trans ( h_norm_sum m ) ( Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ( h_abs_coord m hm i ) ( norm_nonneg _ ) ) ⟩;
  -- Since the norm of every element in the set is bounded by C, the set is bounded.
  obtain ⟨C, hC⟩ := h_bounded;
  exact isBounded_iff_forall_norm_le.mpr ⟨C, fun m hm => hC m hm⟩

/-- The fundamental parallelepiped of a lattice basis is convex. -/
theorem LatticeBasis.centeredFundamentalDomain_isConvex (B : SquareLatticeBasis n) : Convex ℝ B.centeredFundamentalDomain := by
  -- To prove convexity, take any two points $x$ and $y$ in the centered fundamental domain and show that any convex combination of $x$ and $y$ is also in the domain.
  intro x hx y hy t ht
  simp [LatticeBasis.centeredFundamentalDomain] at hx hy ⊢;
  -- By definition of convex combination, we can write the combination as a weighted average of the coordinates of x and y.
  intros ht_nonneg ht_nonneg' ht_sum
  intro i
  have h_coord : -0.5 ≤ t * (B.asTopBasis.repr x) i + (1 - t) * (B.asTopBasis.repr y) i ∧ t * (B.asTopBasis.repr x) i + (1 - t) * (B.asTopBasis.repr y) i < 0.5 := by
    -- By combining the inequalities for x and y, we can show that the convex combination is within the interval [-0.5, 0.5).
    apply And.intro;
    · nlinarith [ hx i, hy i ];
    · cases lt_or_eq_of_le ht_nonneg <;> cases lt_or_eq_of_le ht_nonneg' <;> nlinarith [ hx i, hy i ];
  convert h_coord using 1 <;> rw [ ← ht_sum ] ; ring_nf;
  rw [ add_sub_cancel_left ]


end fundamental_domain

end LatticeCrypto.Foundations.Lattice
