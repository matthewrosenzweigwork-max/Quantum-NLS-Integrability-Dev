import QuantumNLS.Reg003CellLocalization
import QuantumNLS.LocalHeight
import QuantumNLS.AdjacentResponse

/-! R-F4C3E5BE CC:F04:selection (root_response/F04.tex:202), stage S2: the physical band data of the
printed proof.  For a unit `u in L2`, `mu = M_u = PhysicalQuantumMeasure.measure hκ u`, indexed masses
`I_n = RootIndexedMasses.masses`, integers `b <= k < a` with `I_b, I_a > 0`:
* `j` = last index `<= k` with `I_j > 0`, `l` = first index `> k` with `I_l > 0` (`exists_jl`);
* `r` = rightmost point of the support of the `j`th indexed component, `lft` = leftmost point of the
  `l`th one (finite by `Reg003CellLocalization`, REG-003), with `theta(r) = j pi`, `theta(lft) = l pi`,
  `r < lft` and `mu = 0` on `(r, lft)` (`band_data`);
* the cumulative-mass brackets `mu(-inf, x] < alpha` for `x < r` and `alpha < mu(-inf, y)` for
  `y > lft`, with `alpha = sum_{n <= k} I_n` (`cum_mass`, `band_data`);
* `Ccum_tendsto`: the rank fraction `C_{k,N}/N -> alpha` from `eta/N -> I` in l1;
* `exists_xlam`: for `lambda in (k, k+1)` the point `x(lambda)` of the printed
  `CC:F04:phase-inverse` exists in `(r, lft)`, every solution of `theta = pi lambda` lies there, and
  `theta = LocalHeight.theta L kappa mu` there (`th_eq_theta`).
Inputs read-only: `Reg003CellLocalization`, `RootIndexedMasses`, `RootIndexedPhase`, `Prop026Bound`. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace QuantumNLS.F04SelBand
open QuantumNLS.Reg003 QuantumNLS.IndexedScalarMeasure
open PhysicalTensor (L2T)

variable {L κ : ℝ} [Fact (0 < L)]

abbrev sep (hκ : 0 < κ) (u : L2T L) : ℤ → ℝ := RootIndexedPhase.separator hκ u
abbrev th (hκ : 0 < κ) (u : L2T L) : ℝ → ℝ := RootIndexedPhase.theta hκ u
abbrev Mu (hκ : 0 < κ) (u : L2T L) : Measure ℝ := PhysicalQuantumMeasure.measure hκ u
abbrev II (hκ : 0 < κ) (u : L2T L) (n : ℤ) : ℝ := (RootIndexedMasses.masses hκ u).1 n

instance (hκ : 0 < κ) (u : L2T L) : IsFiniteMeasure (Mu hκ u) :=
  (PhysicalSourceFinal.sourceFacts hκ u).finite

theorem Mu_prob (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) : IsProbabilityMeasure (Mu hκ u) :=
  ⟨by rw [PhysicalQuantumMeasure.measure_univ, hu]; norm_num⟩

theorem Mu_singleton (hκ : 0 < κ) (u : L2T L) (x : ℝ) : Mu hκ u {x} = 0 := by
  have := PhysicalUnconditionalTrace.atomless hκ u
  exact NullSingletonClass.measure_singleton x

theorem II_nonneg (hκ : 0 < κ) (u : L2T L) (n : ℤ) : 0 ≤ II hκ u n :=
  (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1 n

theorem II_eq (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    II hκ u n = (Mu hκ u (cell hκ u n)).toReal :=
  (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).1 n

theorem Mu_cell_pos (hκ : 0 < κ) (u : L2T L) {n : ℤ} (h : 0 < II hκ u n) :
    0 < Mu hκ u (cell hκ u n) := by
  rw [II_eq] at h
  by_contra hc
  rw [not_lt, nonpos_iff_eq_zero] at hc
  rw [hc] at h
  simp at h

theorem Mu_cell_zero (hκ : 0 < κ) (u : L2T L) {n : ℤ} (h : II hκ u n = 0) :
    Mu hκ u (cell hκ u n) = 0 := by
  rw [II_eq] at h
  rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

theorem ne_zero_of_II_pos (hκ : 0 < κ) {u : L2T L} {n : ℤ} (h : 0 < II hκ u n) : u ≠ 0 :=
  masses_pos_ne_zero hκ h

/-! ### 1. The phase -/

theorem th_cont (hκ : 0 < κ) (u : L2T L) : Continuous (th hκ u) :=
  Complex.continuous_re.comp (PhysicalContinuousBoundary.continuous_boundary hκ u)

theorem th_mono (hκ : 0 < κ) (u : L2T L) : Monotone (th hκ u) :=
  PhysicalContinuousBoundary.monotone_all hκ u

theorem th_sep (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    th hκ u (sep hκ u n) = ((n : ℝ) + 1 / 2) * Real.pi :=
  (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_spec n

theorem theta_cell_ae (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (j : ℤ) :
    ∀ᵐ t ∂(Mu hκ u), t ∈ cell hκ u j → th hκ u t = (j : ℝ) * Real.pi := by
  filter_upwards [Prop026Bound.integer_ae hκ hu] with t ⟨m, hm⟩ hmem
  have hm' : ((fun _ : ℝ => m) t : ℝ) = indexLabel L κ (Prop026Bound.reG hκ u) t := hm.symm
  have h1 := (label_iff_cell hκ u (n := fun _ => m) hm' j).2 hmem
  have h2 := Prop026Bound.label_eq hκ u t
  rw [hm] at h2
  have hpi := Real.pi_pos
  have : th hκ u t = m * Real.pi := by
    have := (eq_div_iff hpi.ne').1 h2
    linarith
  rw [this]
  rw [h1]

theorem comp_support_sub (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (j : ℤ) :
    ((Mu hκ u).restrict (cell hκ u j)).support ⊆
      {t | th hκ u t = (j : ℝ) * Real.pi} ∩ Icc (sep hκ u (j - 1)) (sep hκ u j) := by
  have hF : IsClosed ({t | th hκ u t = (j : ℝ) * Real.pi} ∩ Icc (sep hκ u (j - 1)) (sep hκ u j)) :=
    (isClosed_eq (th_cont hκ u) continuous_const).inter isClosed_Icc
  apply support_sub_of_null hF
  rw [Measure.restrict_apply hF.measurableSet.compl]
  have h := theta_cell_ae hκ hu j
  rw [ae_iff] at h
  refine measure_mono_null ?_ h
  intro t ht
  refine fun hh => ht.1 ⟨hh ht.2, ?_⟩
  exact ⟨ht.2.1.le, ht.2.2.le⟩

/-! ### 2. Null stretches between cells and cumulative masses -/

theorem cover_null (hκ : 0 < κ) (u : L2T L) :
    Mu hκ u {t | ¬ ∃ m, t ∈ cell hκ u m} = 0 := by
  have := cover_ae hκ u
  rw [ae_iff] at this
  exact this

theorem null_between (hκ : 0 < κ) (u : L2T L) (p q : ℤ)
    (h : ∀ m, p < m → m ≤ q → II hκ u m = 0) :
    Mu hκ u (Ioo (sep hκ u p) (sep hκ u q)) = 0 := by
  have hm := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_strictMono
  have hsub : Ioo (sep hκ u p) (sep hκ u q) ⊆ {t | ¬ ∃ m, t ∈ cell hκ u m} ∪
      ⋃ m, (cell hκ u m ∩ Ioo (sep hκ u p) (sep hκ u q)) := by
    intro t ht
    by_cases hc : ∃ m, t ∈ cell hκ u m
    · obtain ⟨m, hm'⟩ := hc
      exact Or.inr (mem_iUnion.2 ⟨m, hm', ht⟩)
    · exact Or.inl hc
  refine measure_mono_null hsub (measure_union_null (cover_null hκ u) (measure_iUnion_null fun m => ?_))
  by_cases h1 : m ≤ p
  · have : cell hκ u m ∩ Ioo (sep hκ u p) (sep hκ u q) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun t ht => ?_
      obtain ⟨ht1, ht2⟩ := ht
      simp only [cell, mem_Ioo] at ht1 ht2
      have := hm.monotone h1
      linarith [ht1.2, ht2.1]
    rw [this, measure_empty]
  by_cases h2 : q < m
  · have : cell hκ u m ∩ Ioo (sep hκ u p) (sep hκ u q) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun t ht => ?_
      obtain ⟨ht1, ht2⟩ := ht
      simp only [cell, mem_Ioo] at ht1 ht2
      have := hm.monotone (show q ≤ m - 1 by omega)
      linarith [ht1.1, ht2.2]
    rw [this, measure_empty]
  · exact measure_mono_null inter_subset_left (Mu_cell_zero hκ u (h m (by omega) (by omega)))

theorem Mu_Iio_eq (hκ : 0 < κ) (u : L2T L) {p q : ℤ} (hpq : p ≤ q)
    (h : ∀ m, p < m → m ≤ q → II hκ u m = 0) :
    Mu hκ u (Iio (sep hκ u q)) = Mu hκ u (Iio (sep hκ u p)) := by
  have hm := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_strictMono
  apply le_antisymm
  · have hsub : Iio (sep hκ u q) ⊆ Iio (sep hκ u p) ∪ ({sep hκ u p} ∪ Ioo (sep hκ u p) (sep hκ u q)) := by
      intro t ht
      simp only [mem_Iio] at ht
      rcases lt_trichotomy t (sep hκ u p) with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨h1, ht⟩)
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    have h0 : Mu hκ u ({sep hκ u p} ∪ Ioo (sep hκ u p) (sep hκ u q)) = 0 :=
      measure_union_null (Mu_singleton hκ u _) (null_between hκ u p q h)
    rw [h0, add_zero]
  · exact measure_mono (Iio_subset_Iio (hm.monotone hpq))

/-! ### 3. The cumulative mass and the rank fraction -/

theorem cum_mass (hκ : 0 < κ) (u : L2T L) (k : ℤ) :
    (Mu hκ u (Iio (sep hκ u k))).toReal = ∑' m : ℤ, (if m ≤ k then II hκ u m else 0) := by
  have hm := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_strictMono
  set A : ℤ → Set ℝ := fun m => cell hκ u m ∩ Iio (sep hκ u k) with hA
  have hdisj : Pairwise (Function.onFun Disjoint A) := fun i j hij =>
    (cell_disjoint hκ u hij).mono inter_subset_left inter_subset_left
  have hmeas : ∀ m, MeasurableSet (A m) := fun m =>
    (cell_measurable hκ u m).inter measurableSet_Iio
  have hunion : Mu hκ u (Iio (sep hκ u k)) = Mu hκ u (⋃ m, A m) := by
    apply le_antisymm
    · have hsub : Iio (sep hκ u k) ⊆ {t | ¬ ∃ m, t ∈ cell hκ u m} ∪ ⋃ m, A m := by
        intro t ht
        by_cases hc : ∃ m, t ∈ cell hκ u m
        · obtain ⟨m, hm'⟩ := hc
          exact Or.inr (mem_iUnion.2 ⟨m, hm', ht⟩)
        · exact Or.inl hc
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
      rw [cover_null hκ u, zero_add]
    · exact measure_mono (iUnion_subset fun m => inter_subset_right)
  rw [hunion, measure_iUnion hdisj hmeas]
  have hterm : ∀ m, Mu hκ u (A m) = if m ≤ k then Mu hκ u (cell hκ u m) else 0 := by
    intro m
    by_cases hmk : m ≤ k
    · rw [if_pos hmk]
      congr 1
      ext t
      simp only [hA, cell, mem_inter_iff, mem_Ioo, mem_Iio]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        have := hm.monotone hmk
        linarith [h.2]
    · rw [if_neg hmk]
      have : A m = ∅ := by
        ext t
        simp only [hA, cell, mem_inter_iff, mem_Ioo, mem_Iio, mem_empty_iff_false, iff_false, not_and]
        intro ht1 ht2
        have := hm.monotone (show k ≤ m - 1 by omega)
        linarith [ht1.1]
      rw [this, measure_empty]
  simp_rw [hterm]
  rw [ENNReal.tsum_toReal_eq (fun m => by split_ifs <;> simp [measure_ne_top])]
  refine tsum_congr fun m => ?_
  by_cases hmk : m ≤ k
  · simp [hmk, II_eq]
  · simp [hmk]

theorem Ccum_tendsto (hκ : 0 < κ) (u : L2T L) {b : ℤ} (η : (n : ℕ) → BetheLabels.MArr (n + 1))
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0)) (k : ℤ) :
    Tendsto (fun n : ℕ => ((AdjacentResponse.Ccum (η n) k : ℕ) : ℝ) / ((n : ℝ) + 1)) atTop
      (𝓝 (∑' m : ℤ, (if m ≤ k then II hκ u m else 0))) := by
  have hI : Summable (fun m => II hκ u m) := (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.2.1
  have hIk : Summable (fun m : ℤ => (if m ≤ k then II hκ u m else 0)) :=
    Summable.of_nonneg_of_le (fun m => by split_ifs <;> simp [II_nonneg]) (fun m => by
      split_ifs <;> simp [II_nonneg]) hI
  have hfin : ∀ n : ℕ, ((AdjacentResponse.Ccum (η n) k : ℕ) : ℝ) / ((n : ℝ) + 1) =
      ∑' m : ℤ, (if m ≤ k then (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) else 0) := by
    intro n
    have hs : ∀ m ∉ (η n).1.support, (if m ≤ k then (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) else 0) = 0 := by
      intro m hm
      rw [Finsupp.notMem_support_iff.1 hm]
      simp
    rw [tsum_eq_sum hs]
    unfold AdjacentResponse.Ccum
    rw [← Finset.sum_filter]
    push_cast
    rw [Finset.sum_div]
  have hsum : ∀ n : ℕ, Summable (fun m : ℤ => (if m ≤ k then (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) else 0)) := by
    intro n
    apply summable_of_ne_finset_zero (s := (η n).1.support)
    intro m hm
    rw [Finsupp.notMem_support_iff.1 hm]
    simp
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hη
  rw [hfin n, ← (hsum n).tsum_sub hIk, Real.norm_eq_abs]
  have hab : Summable (fun m : ℤ => |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|) := by
    have hs1 : Summable (fun m : ℤ => (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1)) := by
      apply summable_of_ne_finset_zero (s := (η n).1.support)
      intro m hm
      rw [Finsupp.notMem_support_iff.1 hm]
      simp
    exact (hs1.sub hI).abs
  have hterm : ∀ m : ℤ, |(if m ≤ k then (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) else 0) -
      (if m ≤ k then II hκ u m else 0)| ≤ |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m| := by
    intro m
    split_ifs <;> simp
  have hsabs : Summable (fun m : ℤ => |(if m ≤ k then (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) else 0) -
      (if m ≤ k then II hκ u m else 0)|) := ((hsum n).sub hIk).abs
  calc |∑' m : ℤ, ((if m ≤ k then (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) else 0) -
        (if m ≤ k then II hκ u m else 0))|
      ≤ ∑' m : ℤ, |(if m ≤ k then (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) else 0) -
        (if m ≤ k then II hκ u m else 0)| := by
        have := norm_tsum_le_tsum_norm (f := fun m : ℤ =>
          (if m ≤ k then (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) else 0) -
            (if m ≤ k then II hκ u m else 0)) (by simpa [Real.norm_eq_abs] using hsabs)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m| :=
        Summable.tsum_le_tsum hterm hsabs hab

/-! ### 4. The band data -/

theorem exists_jl (hκ : 0 < κ) (u : L2T L) {b a k : ℤ} (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (hbk : b ≤ k) (hka : k < a) :
    ∃ j ℓ : ℤ, b ≤ j ∧ j ≤ k ∧ k < ℓ ∧ ℓ ≤ a ∧ 0 < II hκ u j ∧ 0 < II hκ u ℓ ∧
      (∀ m, j < m → m ≤ k → II hκ u m = 0) ∧ (∀ m, k < m → m < ℓ → II hκ u m = 0) := by
  obtain ⟨j, ⟨hj1, hj2⟩, hj3⟩ := Int.exists_greatest_of_bdd
    (P := fun z => z ≤ k ∧ 0 < II hκ u z) ⟨k, fun z hz => hz.1⟩ ⟨b, hbk, hb⟩
  obtain ⟨ℓ, ⟨hl1, hl2⟩, hl3⟩ := Int.exists_least_of_bdd
    (P := fun z => k < z ∧ 0 < II hκ u z) ⟨k + 1, fun z hz => by have := hz.1; omega⟩ ⟨a, hka, ha⟩
  refine ⟨j, ℓ, hj3 b ⟨hbk, hb⟩, hj1, hl1, hl3 a ⟨hka, ha⟩, hj2, hl2, fun m hjm hmk => ?_,
    fun m hkm hml => ?_⟩
  · by_contra hne
    have : 0 < II hκ u m := lt_of_le_of_ne (II_nonneg hκ u m) (Ne.symm hne)
    have := hj3 m ⟨hmk, this⟩
    omega
  · by_contra hne
    have : 0 < II hκ u m := lt_of_le_of_ne (II_nonneg hκ u m) (Ne.symm hne)
    have := hl3 m ⟨hkm, this⟩
    omega

theorem band_data (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {b a k : ℤ} (hb : 0 < II hκ u b)
    (ha : 0 < II hκ u a) (hbk : b ≤ k) (hka : k < a) :
    ∃ (j ℓ : ℤ) (r l : ℝ), b ≤ j ∧ j ≤ k ∧ k < ℓ ∧ ℓ ≤ a ∧ r < l ∧
      Mu hκ u (Ioo r l) = 0 ∧ th hκ u r = (j : ℝ) * Real.pi ∧ th hκ u l = (ℓ : ℝ) * Real.pi ∧
      (∀ x < r, (Mu hκ u).real (Iic x) < ∑' m : ℤ, (if m ≤ k then II hκ u m else 0)) ∧
      (∀ y > l, ∑' m : ℤ, (if m ≤ k then II hκ u m else 0) < (Mu hκ u).real (Iio y)) := by
  haveI := Mu_prob hκ u hu
  have hu0 : u ≠ 0 := ne_zero_of_II_pos hκ hb
  have hm := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_strictMono
  obtain ⟨j, ℓ, hbj, hjk, hkl, hla, hj, hl, hjz, hlz⟩ := exists_jl hκ u hb ha hbk hka
  set Sj := ((Mu hκ u).restrict (cell hκ u j)).support with hSj
  set Sl := ((Mu hκ u).restrict (cell hκ u ℓ)).support with hSl
  have hSjne : Sj.Nonempty := by
    apply Measure.nonempty_support
    intro h0
    have := Mu_cell_pos hκ u hj
    rw [← Measure.restrict_apply_self, h0] at this
    simp at this
  have hSlne : Sl.Nonempty := by
    apply Measure.nonempty_support
    intro h0
    have := Mu_cell_pos hκ u hl
    rw [← Measure.restrict_apply_self, h0] at this
    simp at this
  have hSjc : IsClosed Sj := Measure.isClosed_support
  have hSlc : IsClosed Sl := Measure.isClosed_support
  have hSjb : BddAbove Sj := ⟨sep hκ u j, fun t ht => (comp_support_sub hκ hu0 j ht).2.2⟩
  have hSlb : BddBelow Sl := ⟨sep hκ u (ℓ - 1), fun t ht => (comp_support_sub hκ hu0 ℓ ht).2.1⟩
  set r := sSup Sj with hr
  set l := sInf Sl with hl'
  have hrS : r ∈ Sj := hSjc.csSup_mem hSjne hSjb
  have hlS : l ∈ Sl := hSlc.csInf_mem hSlne hSlb
  have hrth : th hκ u r = (j : ℝ) * Real.pi := (comp_support_sub hκ hu0 j hrS).1
  have hlth : th hκ u l = (ℓ : ℝ) * Real.pi := (comp_support_sub hκ hu0 ℓ hlS).1
  have hrj : sep hκ u (j - 1) ≤ r ∧ r ≤ sep hκ u j := (comp_support_sub hκ hu0 j hrS).2
  have hll : sep hκ u (ℓ - 1) ≤ l ∧ l ≤ sep hκ u ℓ := (comp_support_sub hκ hu0 ℓ hlS).2
  have hrl : r < l := by
    by_contra hcon
    push Not at hcon
    have := th_mono hκ u hcon
    rw [hrth, hlth] at this
    have hpi := Real.pi_pos
    have : (ℓ : ℝ) ≤ j := by nlinarith
    have : ℓ ≤ j := by exact_mod_cast this
    omega
  -- the part of each component beyond its extreme point is null
  have hnullr : Mu hκ u (cell hκ u j ∩ Ioi r) = 0 := by
    have hc : Ioi r ⊆ Sjᶜ := fun t ht hts => absurd (le_csSup hSjb hts) (not_le.2 ht)
    have h0 : ((Mu hκ u).restrict (cell hκ u j)) (Ioi r) = 0 :=
      measure_mono_null hc Measure.measure_compl_support
    rw [Measure.restrict_apply measurableSet_Ioi, inter_comm] at h0
    exact h0
  have hnulll : Mu hκ u (cell hκ u ℓ ∩ Iio l) = 0 := by
    have hc : Iio l ⊆ Slᶜ := fun t ht hts => absurd (csInf_le hSlb hts) (not_le.2 ht)
    have h0 : ((Mu hκ u).restrict (cell hκ u ℓ)) (Iio l) = 0 :=
      measure_mono_null hc Measure.measure_compl_support
    rw [Measure.restrict_apply measurableSet_Iio, inter_comm] at h0
    exact h0
  have hposr : ∀ x < r, 0 < Mu hκ u (Ioc x r ∩ cell hκ u j) := by
    intro x hx
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    apply (Measure.notMem_support_iff_exists.2 ⟨Ioo x (r + 1), Ioo_mem_nhds hx (by linarith), ?_⟩) hrS
    rw [Measure.restrict_apply measurableSet_Ioo]
    have hnr' : Mu hκ u (Ioi r ∩ cell hκ u j) = 0 := by rwa [inter_comm] at hnullr
    refine measure_mono_null (t := (Ioc x r ∩ cell hκ u j) ∪ (Ioi r ∩ cell hκ u j))
      (fun t ht => ?_) (measure_union_null h0 hnr')
    by_cases htr : t ≤ r
    · exact Or.inl ⟨⟨ht.1.1, htr⟩, ht.2⟩
    · exact Or.inr ⟨not_le.1 htr, ht.2⟩
  have hposl : ∀ y > l, 0 < Mu hκ u (cell hκ u ℓ ∩ Iio y) := by
    intro y hy
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    apply (Measure.notMem_support_iff_exists.2 ⟨Ioo (l - 1) y, Ioo_mem_nhds (by linarith) hy, ?_⟩) hlS
    rw [Measure.restrict_apply measurableSet_Ioo]
    refine measure_mono_null (t := (cell hκ u ℓ ∩ Iio y) ∪ (cell hκ u ℓ ∩ Iio l))
      (fun t ht => ?_) (measure_union_null h0 hnulll)
    by_cases htl : t < l
    · exact Or.inr ⟨ht.2, htl⟩
    · exact Or.inl ⟨ht.2, ht.1.2⟩
  -- the stretch between is null
  have hnull : Mu hκ u (Ioo r l) = 0 := by
    have hsub : Ioo r l ⊆ {t | ¬ ∃ m, t ∈ cell hκ u m} ∪
        ⋃ m, (cell hκ u m ∩ Ioo r l) := by
      intro t ht
      by_cases hc : ∃ m, t ∈ cell hκ u m
      · obtain ⟨m, hm'⟩ := hc
        exact Or.inr (mem_iUnion.2 ⟨m, hm', ht⟩)
      · exact Or.inl hc
    refine measure_mono_null hsub (measure_union_null (cover_null hκ u)
      (measure_iUnion_null fun m => ?_))
    rcases lt_trichotomy m j with h1 | h1 | h1
    · have : cell hκ u m ∩ Ioo r l = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun t ht => ?_
        obtain ⟨ht1, ht2⟩ := ht
        simp only [cell, mem_Ioo] at ht1 ht2
        have := hm.monotone (show m ≤ j - 1 by omega)
        linarith [ht1.2, ht2.1, hrj.1]
      rw [this, measure_empty]
    · subst h1
      refine measure_mono_null (t := cell hκ u m ∩ Ioi r) ?_ hnullr
      exact fun t ht => ⟨ht.1, ht.2.1⟩
    · rcases lt_trichotomy m ℓ with h2 | h2 | h2
      · refine measure_mono_null inter_subset_left (Mu_cell_zero hκ u ?_)
        by_cases hmk : m ≤ k
        · exact hjz m h1 hmk
        · exact hlz m (by omega) h2
      · subst h2
        refine measure_mono_null (t := cell hκ u m ∩ Iio l) ?_ hnulll
        exact fun t ht => ⟨ht.1, ht.2.2⟩
      · have : cell hκ u m ∩ Ioo r l = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.2 fun t ht => ?_
          obtain ⟨ht1, ht2⟩ := ht
          simp only [cell, mem_Ioo] at ht1 ht2
          have := hm.monotone (show ℓ ≤ m - 1 by omega)
          linarith [ht1.1, ht2.2, hll.2]
        rw [this, measure_empty]
  have hcum := cum_mass hκ u k
  refine ⟨j, ℓ, r, l, hbj, hjk, hkl, hla, hrl, hnull, hrth, hlth, ?_, ?_⟩
  · intro x hx
    rw [← hcum]
    have hlt : Mu hκ u (Iic x) < Mu hκ u (Iio (sep hκ u k)) := by
      rw [Mu_Iio_eq hκ u hjk hjz]
      have hunion : Mu hκ u (Iic x ∪ (Ioc x r ∩ cell hκ u j)) =
          Mu hκ u (Iic x) + Mu hκ u (Ioc x r ∩ cell hκ u j) :=
        measure_union (by
          rw [Set.disjoint_left]
          intro t ht1 ht2
          exact absurd ht1 (not_le.2 ht2.1.1)) (measurableSet_Ioc.inter (cell_measurable hκ u j))
      have hsub : Iic x ∪ (Ioc x r ∩ cell hκ u j) ⊆ Iio (sep hκ u j) := by
        rintro t (ht | ht)
        · exact lt_of_le_of_lt ht (lt_of_lt_of_le hx hrj.2)
        · exact ht.2.2
      have h1 := measure_mono (μ := Mu hκ u) hsub
      rw [hunion] at h1
      have h2 := hposr x hx
      exact lt_of_lt_of_le (ENNReal.lt_add_right (measure_ne_top _ _) h2.ne') h1
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 hlt
  · intro y hy
    rw [← hcum]
    have hlt : Mu hκ u (Iio (sep hκ u k)) < Mu hκ u (Iio y) := by
      rw [← Mu_Iio_eq hκ u (show k ≤ ℓ - 1 by omega) (fun m hkm hml => hlz m hkm (by omega))]
      have hunion : Mu hκ u (Iio (sep hκ u (ℓ - 1)) ∪ (cell hκ u ℓ ∩ Iio y)) =
          Mu hκ u (Iio (sep hκ u (ℓ - 1))) + Mu hκ u (cell hκ u ℓ ∩ Iio y) :=
        measure_union (by
          rw [Set.disjoint_left]
          intro t ht1 ht2
          exact absurd ht1 (not_lt.2 ht2.1.1.le)) ((cell_measurable hκ u ℓ).inter measurableSet_Iio)
      have hsub : Iio (sep hκ u (ℓ - 1)) ∪ (cell hκ u ℓ ∩ Iio y) ⊆ Iio y := by
        rintro t (ht | ht)
        · exact lt_of_lt_of_le ht (hll.1.trans hy.le)
        · exact ht.2
      have h1 := measure_mono (μ := Mu hκ u) hsub
      rw [hunion] at h1
      have h2 := hposl y hy
      exact lt_of_lt_of_le (ENNReal.lt_add_right (measure_ne_top _ _) h2.ne') h1
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).2 hlt


/-! ### 5. The point `x(lambda)` and the phase formula -/

theorem abs_disc_lt_two (hκ : 0 < κ) (u : L2T L) (x : ℝ)
    (h : ∀ m : ℤ, th hκ u x ≠ (m : ℝ) * Real.pi) :
    |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re| < 2 := by
  by_contra hge
  push Not at hge
  have hcos : 2 * Complex.cos (PhysicalContinuousBoundary.boundary hκ u x) =
      (((L2SpatialTransfer.discriminant κ u (x : ℂ)).re : ℝ) : ℂ) := by
    rw [PhysicalContinuousBoundary.boundary_cosine]
    exact Complex.ext (by simp) (by simp [L2DiscriminantRegularity.discriminant_real κ u x])
  set d := (L2SpatialTransfer.discriminant κ u (x : ℂ)).re with hd
  set β := PhysicalContinuousBoundary.boundary hκ u x with hβ
  rcases hge.lt_or_eq with hlt | heq
  · obtain ⟨m, hm⟩ := PhysicalTraceSymbolDependency.gap_value_integer_pi hcos hlt
    exact h m hm
  · rcases abs_cases d with ⟨h1, _⟩ | ⟨h1, _⟩
    · have hd2 : d = 2 := by linarith
      have hc : Complex.cos β = 1 := by
        rw [hd2] at hcos
        have : (2 : ℂ) * Complex.cos β = 2 * 1 := by rw [hcos]; push_cast; ring
        exact mul_left_cancel₀ two_ne_zero this
      obtain ⟨k, hk⟩ := Complex.cos_eq_one_iff.1 hc
      have := congrArg Complex.re hk
      simp at this
      exact h (2 * k) (by push_cast; linarith)
    · have hd2 : d = -2 := by linarith
      have hc : Complex.cos β = -1 := by
        rw [hd2] at hcos
        have : (2 : ℂ) * Complex.cos β = 2 * (-1) := by rw [hcos]; push_cast; ring
        exact mul_left_cancel₀ two_ne_zero this
      obtain ⟨k, hk⟩ := Complex.cos_eq_neg_one_iff.1 hc
      have := congrArg Complex.re hk
      simp at this
      exact h (2 * k + 1) (by push_cast; linarith)

theorem th_eq_theta (hκ : 0 < κ) {u : L2T L} (hu : u ≠ 0) (x : ℝ)
    (h : ∀ m : ℤ, th hκ u x ≠ (m : ℝ) * Real.pi) :
    th hκ u x = LocalHeight.theta L κ (Mu hκ u) x := by
  have hx : x ∈ Prop026Bound.cuts κ u := abs_disc_lt_two hκ u x h
  have h1 := Prop026Bound.force_eq hκ hu hx
  rw [exteriorForce_eq] at h1
  unfold LocalHeight.theta
  simp only [one_div]
  change L * x - 2 * κ * ∫ t : ℝ, (x - t)⁻¹ ∂(Mu hκ u) = 2 * th hκ u x at h1
  linarith

theorem nonint_of_between {k : ℤ} {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) (m : ℤ) :
    lam * Real.pi ≠ (m : ℝ) * Real.pi := by
  intro h
  have hpi := Real.pi_pos
  have : lam = m := by
    have := mul_right_cancel₀ hpi.ne' h
    exact this
  rcases le_or_gt m k with hmk | hmk
  · have : (m : ℝ) ≤ k := by exact_mod_cast hmk
    linarith
  · have : (k : ℝ) + 1 ≤ m := by exact_mod_cast hmk
    linarith

/-- The printed `CC:F04:phase-inverse` for `lambda in (k, k+1)`: solutions of `theta = pi lambda` exist,
all lie in the null band `(r, l)`, and there `theta` is `LocalHeight.theta`. -/
theorem xlam_data (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {j ℓ k : ℤ} {r l : ℝ} (hjk : j ≤ k)
    (hkl : k < ℓ) (hrth : th hκ u r = (j : ℝ) * Real.pi) (hlth : th hκ u l = (ℓ : ℝ) * Real.pi)
    (hrl : r < l) (hu0 : u ≠ 0) {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) :
    (∃ x ∈ Ioo r l, th hκ u x = lam * Real.pi) ∧
    ∀ x, th hκ u x = lam * Real.pi → x ∈ Ioo r l ∧
      LocalHeight.theta L κ (Mu hκ u) x = lam * Real.pi := by
  have hpi := Real.pi_pos
  have hj : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hl : (k : ℝ) + 1 ≤ ℓ := by exact_mod_cast hkl
  have hlo : th hκ u r < lam * Real.pi := by rw [hrth]; nlinarith
  have hhi : lam * Real.pi < th hκ u l := by rw [hlth]; nlinarith
  refine ⟨?_, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨x, hx, hxe⟩ := intermediate_value_Ioo hrl.le (th_cont hκ u).continuousOn ⟨hlo, hhi⟩
    exact ⟨x, hx, hxe⟩
  · constructor
    · by_contra hxr
      have := th_mono hκ u (not_lt.1 hxr)
      linarith
    · by_contra hxl
      have := th_mono hκ u (not_lt.1 hxl)
      linarith
  · rw [← th_eq_theta hκ hu0 x (fun m => by rw [hx]; exact nonint_of_between h1 h2 m)]
    exact hx

end QuantumNLS.F04SelBand
#print axioms QuantumNLS.F04SelBand.cum_mass
#print axioms QuantumNLS.F04SelBand.Ccum_tendsto
#print axioms QuantumNLS.F04SelBand.band_data
#print axioms QuantumNLS.F04SelBand.abs_disc_lt_two
#print axioms QuantumNLS.F04SelBand.th_eq_theta
#print axioms QuantumNLS.F04SelBand.xlam_data
