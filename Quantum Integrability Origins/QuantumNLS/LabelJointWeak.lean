import QuantumNLS.LabelTightness

/-!
# PROP-002 `lem:B3-weak-joint-limit`, part (2a)–(2b): tightness and properties of joint limits

Source: `source/chapters/propagation/label_periods.tex:43-63`. "The uniform bound
`QG:eq:B3-uniform-label-distance` implies tightness of the integer marginal from tightness of the
rapidity marginal. ... Pass to a weak limit `γ` of the joint measures. The pairwise monotonicity
relation `(q−q′)(n−n′) ≥ 0` passes to the product limit. If `μ_n(E) = γ(E × {n})`, the support of
`μ_n` lies to the left of the support of `μ_m` when `n < m`."

Imports (read-only, frozen, the auxiliary construction): `LabelTightness` (`3c7ed0d1…`, uniform label distance and
`|n_j|` bounds) → `LabelJointLimit` (`4120590e…`, `OnShellBethe`, Bethe pairing identity).

Here, for a sequence of on-shell configurations `B k` (`N_k ≥ 1` roots, coupling `κ/N_k`) whose root
empirical measures `L_k = N_k⁻¹ Σ_j δ_{q_j}` converge weakly to `μ`:
* `emp`, `jointP`, `rootP`: the empirical measures `N⁻¹ Σ_j δ_{(q_j,n_j)}` on `ℝ × ℤ` and `L_N`
  (probability measures); `jointP_map_fst` (first marginal);
* **`tight_joint`** (2a): the joint empirical measures form a tight family on `ℝ × ℤ`;
* **`exists_subseq_tendsto`** (2b): every subsequence has a further subsequence converging weakly
  (Prokhorov, mathlib `isCompact_closure_of_isTightMeasureSet`);
* for every such subsequential limit `γ`: `limit_map_fst` (first marginal `μ`),
  **`limit_prod_monotone`** (the monotonicity relation passes to `γ ⊗ γ`:
  `(γ ⊗ γ){(q−q′)(n−n′) < 0} = 0`), **`limit_ordering`** (for `n < m` and every `a`, `γ` gives no
  mass to `(a, ∞) × {n}` or none to `(−∞, a) × {m}`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.LabelJointWeak

open QuantumNLS.LabelJointLimit QuantumNLS.LabelTightness

/-! ## 1. Empirical measures of finite families -/

section Emp

variable {X : Type*} [MeasurableSpace X] {N : ℕ}

/-- `N⁻¹ Σ_j δ_{p_j}`. -/
def emp (p : Fin N → X) : Measure X := ((N : ℝ≥0∞)⁻¹) • ∑ j, Measure.dirac (p j)

open Classical in
lemma emp_apply (p : Fin N → X) {S : Set X} (hS : MeasurableSet S) :
    emp p S = (N : ℝ≥0∞)⁻¹ * ((Finset.univ.filter fun j => p j ∈ S).card : ℝ≥0∞) := by
  simp only [emp, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ hS, smul_eq_mul]
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : p j ∈ S <;> simp [h]

instance (p : Fin N → X) : IsFiniteMeasure (emp p) := by
  classical
  refine ⟨?_⟩
  rw [emp_apply p MeasurableSet.univ]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · exact ENNReal.mul_lt_top (by simpa using h) (by simp)

lemma emp_univ (p : Fin N → X) (hN : 0 < N) : emp p univ = 1 := by
  simp only [emp, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, measure_univ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

lemma emp_eq_zero {p : Fin N → X} {S : Set X} (hS : MeasurableSet S) (h : ∀ j, p j ∉ S) :
    emp p S = 0 := by
  simp only [emp, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.dirac_apply' _ hS, Set.indicator_of_notMem (h _), Finset.sum_const_zero, smul_eq_mul,
    mul_zero]

lemma emp_le_of_imp {Y : Type*} [MeasurableSpace Y] {p : Fin N → X} {p' : Fin N → Y}
    {S : Set X} {S' : Set Y} (hS : MeasurableSet S) (hS' : MeasurableSet S')
    (h : ∀ j, p j ∈ S → p' j ∈ S') : emp p S ≤ emp p' S' := by
  classical
  rw [emp_apply p hS, emp_apply p' hS']
  refine mul_le_mul_right ?_ _
  exact_mod_cast Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, h j hj.2⟩

lemma emp_map {Y : Type*} [MeasurableSpace Y] (p : Fin N → X) {f : X → Y} (hf : Measurable f) :
    (emp p).map f = emp (f ∘ p) := by
  classical
  ext S hS
  rw [Measure.map_apply hf hS, emp_apply p (hf hS), emp_apply (f ∘ p) hS]
  rfl

lemma emp_prod_eq_zero [MeasurableSingletonClass X] (p : Fin N → X) {U : Set (X × X)}
    (h : ∀ j l, (p j, p l) ∉ U) : ((emp p).prod (emp p)) U = 0 := by
  set P := Set.range p
  have hP : MeasurableSet P := (Set.finite_range p).measurableSet
  have hPc : emp p Pᶜ = 0 := emp_eq_zero hP.compl fun j hj => hj ⟨j, rfl⟩
  have hsub : U ⊆ Pᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ Pᶜ := by
    rintro ⟨a, b⟩ hab
    by_contra hc
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true,
      true_and, not_or, not_not] at hc
    obtain ⟨⟨j, rfl⟩, ⟨l, rfl⟩⟩ := hc
    exact h j l hab
  refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) bot_le
  rw [Measure.prod_prod, Measure.prod_prod, hPc, zero_mul, mul_zero, add_zero]

lemma integral_emp [MeasurableSingletonClass X] (p : Fin N → X) (f : X → ℝ) :
    ∫ x, f x ∂(emp p) = (N : ℝ)⁻¹ * ∑ j, f (p j) := by
  rw [emp, integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, ENNReal.toReal_inv]
  · intro j _
    exact (integrable_dirac (by simp))

end Emp

/-! ## 2. The empirical measures of an on-shell configuration -/

section Config

variable {L κ : ℝ} {N : ℕ}

/-- The joint rapidity–label points `(q_j, n_j)`. -/
def pts (B : OnShellBethe L κ N) : Fin N → ℝ × ℤ := fun j => (B.q j, B.n j)

/-- `N⁻¹ Σ_j δ_{(q_j, n_j)}` as a probability measure on `ℝ × ℤ`. -/
def jointP (B : OnShellBethe L κ N) (hN : 0 < N) : ProbabilityMeasure (ℝ × ℤ) :=
  ⟨emp (pts B), ⟨emp_univ _ hN⟩⟩

/-- `L_N = N⁻¹ Σ_j δ_{q_j}` as a probability measure on `ℝ`. -/
def rootP (B : OnShellBethe L κ N) (hN : 0 < N) : ProbabilityMeasure ℝ :=
  ⟨emp B.q, ⟨emp_univ _ hN⟩⟩

lemma jointP_map_fst (B : OnShellBethe L κ N) (hN : 0 < N) :
    (jointP B hN).map Prod.fst = rootP B hN := by
  apply Subtype.ext
  show Measure.map Prod.fst (emp (pts B)) = emp B.q
  rw [emp_map _ measurable_fst]
  rfl

/-- The finite monotonicity relation `(q_j − q_l)(n_j − n_l) ≥ 0`. -/
lemma pair_monotone (B : OnShellBethe L κ N) (j l : Fin N) :
    0 ≤ (B.q j - B.q l) * ((B.n j : ℝ) - B.n l) := by
  rcases lt_trichotomy j l with h | h | h
  · have h1 : B.q j < B.q l := B.q_strict h
    have h2 : (B.n j : ℝ) ≤ B.n l := by exact_mod_cast B.n_mono h.le
    nlinarith
  · subst h; simp
  · have h1 : B.q l < B.q j := B.q_strict h
    have h2 : (B.n l : ℝ) ≤ B.n j := by exact_mod_cast B.n_mono h.le
    nlinarith

/-- The open set `{(q−q′)(n−n′) < 0}` in `(ℝ × ℤ)²`. -/
def antiSet : Set ((ℝ × ℤ) × (ℝ × ℤ)) :=
  {x | (x.1.1 - x.2.1) * ((x.1.2 : ℝ) - x.2.2) < 0}

lemma isOpen_antiSet : IsOpen antiSet := by
  have hc : Continuous fun x : (ℝ × ℤ) × (ℝ × ℤ) => (x.1.1 - x.2.1) * ((x.1.2 : ℝ) - x.2.2) := by
    have h1 : Continuous fun z : ℤ => (z : ℝ) := continuous_of_discreteTopology
    fun_prop
  exact isOpen_lt hc continuous_const

lemma jointP_prod_antiSet (B : OnShellBethe L κ N) (hN : 0 < N) :
    (((jointP B hN).prod (jointP B hN) : ProbabilityMeasure _) : Measure _) antiSet = 0 := by
  show ((emp (pts B)).prod (emp (pts B))) antiSet = 0
  refine emp_prod_eq_zero _ fun j l h => ?_
  have := pair_monotone B j l
  simp only [antiSet, Set.mem_ofPred_eq, pts] at h
  linarith

end Config

/-! ## 3. Sequences: tightness and subsequential limits -/

section Seq

variable {L κ : ℝ} (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (B : ∀ k, OnShellBethe L κ (N k))
  (μ : ProbabilityMeasure ℝ)

/-- **(2a) Tightness of the joint empirical measures** on `ℝ × ℤ`, from weak convergence of the
root empirical measures and the uniform label distance. -/
theorem tight_joint (hL : 0 < L) (hκ : 0 < κ)
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) :
    IsTightMeasureSet {((γ : ProbabilityMeasure (ℝ × ℤ)) : Measure (ℝ × ℤ)) |
      γ ∈ Set.range fun k => jointP (B k) (hN k)} := by
  -- tightness of the roots
  have hcpt : IsCompact (closure (Set.range fun k => rootP (B k) (hN k))) := by
    have h1 := hconv.isCompact_insert_range
    exact h1.of_isClosed_subset isClosed_closure
      (closure_minimal (Set.subset_insert _ _) h1.isClosed)
  have hroot := isTightMeasureSet_of_isCompact_closure hcpt
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hroot ⊢
  intro ε hε
  obtain ⟨K, hK, hKε⟩ := hroot ε hε
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall 0
  set M' := max M 0
  set Kn : ℤ := ⌈(L / (2 * Real.pi)) * (M' + 3 * Real.sqrt (κ / L))⌉
  refine ⟨Metric.closedBall (0 : ℝ) M' ×ˢ (Set.Icc (-Kn) Kn : Set ℤ),
    (isCompact_closedBall _ _).prod (Set.finite_Icc _ _).isCompact, ?_⟩
  rintro _ ⟨γ, ⟨k, rfl⟩, rfl⟩
  have hle : (jointP (B k) (hN k) : Measure (ℝ × ℤ))
      (Metric.closedBall (0 : ℝ) M' ×ˢ (Set.Icc (-Kn) Kn : Set ℤ))ᶜ ≤
      (rootP (B k) (hN k) : Measure ℝ) Kᶜ := by
    show emp (pts (B k)) _ ≤ emp (B k).q _
    refine emp_le_of_imp (((Metric.isClosed_closedBall).prod (Set.finite_Icc _ _).isClosed).measurableSet.compl)
      hK.isClosed.measurableSet.compl fun j hj hqK => hj ?_
    have hq : |(B k).q j| ≤ M' := by
      have := hM hqK
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    refine ⟨by rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact hq, ?_⟩
    have hb := label_abs_le_bound hL hκ (hN k) (B k) j
    have h2 : (L / (2 * Real.pi)) * (|(B k).q j| + 3 * Real.sqrt (κ / L)) ≤
        (L / (2 * Real.pi)) * (M' + 3 * Real.sqrt (κ / L)) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hL.le (by positivity))
    have h3 : ((|(B k).n j| : ℤ) : ℝ) ≤ (Kn : ℝ) := by
      rw [Int.cast_abs]; exact (hb.trans h2).trans (Int.le_ceil _)
    have h4 : |(B k).n j| ≤ Kn := by exact_mod_cast h3
    exact ⟨by have := neg_abs_le ((B k).n j); simp only [pts]; omega,
      by have := le_abs_self ((B k).n j); simp only [pts]; omega⟩
  exact hle.trans (hKε _ ⟨_, ⟨k, rfl⟩, rfl⟩)

/-- **(2b) Subsequential weak limits exist** (Prokhorov). -/
theorem exists_subseq_tendsto (hL : 0 < L) (hκ : 0 < κ)
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (φ : ℕ → ℕ) :
    ∃ γ : ProbabilityMeasure (ℝ × ℤ), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun k => jointP (B (φ (ψ k))) (hN (φ (ψ k)))) atTop (𝓝 γ) := by
  have hcpt := isCompact_closure_of_isTightMeasureSet (tight_joint N hN B μ hL hκ hconv)
  obtain ⟨γ, -, ψ, hψ, hlim⟩ := hcpt.tendsto_subseq
    (x := fun k => jointP (B (φ k)) (hN (φ k))) fun k => subset_closure ⟨φ k, rfl⟩
  exact ⟨γ, ψ, hψ, hlim⟩

variable {N hN B μ}

/-- The first marginal of a subsequential limit is `μ`. -/
theorem limit_map_fst (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ))
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {γ : ProbabilityMeasure (ℝ × ℤ)}
    (hγ : Tendsto (fun k => jointP (B (φ k)) (hN (φ k))) atTop (𝓝 γ)) :
    γ.map Prod.fst = μ := by
  have h1 := ((ProbabilityMeasure.continuous_map continuous_fst).tendsto γ).comp hγ
  have h2 := hconv.comp hφ
  refine tendsto_nhds_unique (h1.congr fun k => ?_) h2
  simp only [Function.comp_apply]
  exact jointP_map_fst _ _

/-- **The monotonicity relation passes to the product limit**: `(γ ⊗ γ){(q−q′)(n−n′) < 0} = 0`. -/
theorem limit_prod_monotone {φ : ℕ → ℕ} {γ : ProbabilityMeasure (ℝ × ℤ)}
    (hγ : Tendsto (fun k => jointP (B (φ k)) (hN (φ k))) atTop (𝓝 γ)) :
    ((γ.prod γ : ProbabilityMeasure _) : Measure _) antiSet = 0 := by
  have hpair : Tendsto (fun k => (jointP (B (φ k)) (hN (φ k)), jointP (B (φ k)) (hN (φ k))))
      atTop (𝓝 (γ, γ)) := hγ.prodMk_nhds hγ
  have hprod := (ProbabilityMeasure.continuous_prod.tendsto (γ, γ)).comp hpair
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hprod isOpen_antiSet
  have h0 : ∀ k, (((jointP (B (φ k)) (hN (φ k))).prod (jointP (B (φ k)) (hN (φ k))) :
      ProbabilityMeasure _) : Measure _) antiSet = 0 := fun k => jointP_prod_antiSet _ _
  simp only [Function.comp_apply, h0, liminf_const] at hle
  exact le_antisymm hle bot_le

/-- **Support ordering**: for `n < m` and every `a`, the limit gives no mass to `(a, ∞) × {n}` or
none to `(−∞, a) × {m}`. -/
theorem limit_ordering {φ : ℕ → ℕ} {γ : ProbabilityMeasure (ℝ × ℤ)}
    (hγ : Tendsto (fun k => jointP (B (φ k)) (hN (φ k))) atTop (𝓝 γ)) {n m : ℤ} (hnm : n < m)
    (a : ℝ) :
    (γ : Measure (ℝ × ℤ)) (Set.Ioi a ×ˢ {n}) = 0 ∨ (γ : Measure (ℝ × ℤ)) (Set.Iio a ×ˢ {m}) = 0 := by
  have h0 := limit_prod_monotone hγ
  have hsub : (Set.Ioi a ×ˢ ({n} : Set ℤ)) ×ˢ (Set.Iio a ×ˢ ({m} : Set ℤ)) ⊆ antiSet := by
    rintro ⟨⟨t, n'⟩, ⟨t', m'⟩⟩ ⟨⟨ht, hn'⟩, ⟨ht', hm'⟩⟩
    simp only [Set.mem_singleton_iff, Set.mem_Ioi, Set.mem_Iio] at hn' hm' ht ht'
    subst hn' hm'
    show (t - t') * ((n' : ℝ) - m') < 0
    have : (n' : ℝ) < m' := by exact_mod_cast hnm
    nlinarith
  have := measure_mono_null hsub h0
  rw [ProbabilityMeasure.toMeasure_prod, Measure.prod_prod] at this
  exact mul_eq_zero.1 this

end Seq

#print axioms tight_joint
#print axioms exists_subseq_tendsto
#print axioms limit_map_fst
#print axioms limit_prod_monotone
#print axioms limit_ordering

end QuantumNLS.LabelJointWeak
