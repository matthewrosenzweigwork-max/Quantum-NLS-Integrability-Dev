import Mathlib

/-!
# Ramer Step 1: locality implies the global change-of-variables identity

If `(*)` holds locally (for all bounded uniformly continuous `F ≥ 0` with `tsupport F ⊆ T '' V`)
around every point, then `μ.map T.symm = μ.withDensity J`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Ramer

open MeasureTheory Set Metric
open scoped ENNReal

section
variable {X : Type*} [MetricSpace X]

/-- Approximating Lipschitz functions of an open set. -/
theorem exists_open_approx (W : Set X) (hW : IsOpen W) :
    ∃ F : ℕ → X → ℝ, (∀ k, UniformContinuous (F k)) ∧ (∀ k y, 0 ≤ F k y ∧ F k y ≤ 1) ∧
      (∀ k y, F k y ≠ 0 → y ∈ W) ∧ (∀ k l, k ≤ l → ∀ y, F k y ≤ F l y) ∧
      (∀ y, y ∈ W → ∃ k, F k y = 1) ∧ (∀ k y, y ∉ W → F k y = 0) := by
  by_cases hU : W = univ
  · refine ⟨fun _ _ => 1, fun _ => uniformContinuous_const, fun _ _ => ⟨zero_le_one, le_rfl⟩,
      ?_, fun _ _ _ _ => le_rfl, fun _ _ => ⟨0, rfl⟩, ?_⟩
    · intro k y _; rw [hU]; trivial
    · intro k y hy; exact absurd (hU ▸ mem_univ y) hy
  · have hne : Wᶜ.Nonempty := by
      rw [nonempty_compl]; exact hU
    refine ⟨fun k y => min 1 ((k : ℝ) * infDist y Wᶜ), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      have h2 : LipschitzWith (Real.toNNReal k) (fun y : X => (k : ℝ) * infDist y Wᶜ) := by
        refine LipschitzWith.of_dist_le_mul fun x y => ?_
        have h1 := (lipschitz_infDist_pt (s := Wᶜ)).dist_le_mul x y
        rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        simp only [Real.coe_toNNReal _ (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.dist_eq] using h1) (Nat.cast_nonneg _)
      exact (h2.const_min 1).uniformContinuous
    · intro k y
      refine ⟨le_min zero_le_one (mul_nonneg (Nat.cast_nonneg _) infDist_nonneg), min_le_left _ _⟩
    · intro k y hy
      by_contra hyW
      have : infDist y Wᶜ = 0 := by
        rw [infDist_zero_of_mem]; exact hyW
      simp [this] at hy
    · intro k l hkl y
      refine min_le_min le_rfl ?_
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) infDist_nonneg
    · intro y hy
      have hpos : 0 < infDist y Wᶜ := by
        rw [← hW.isClosed_compl.notMem_iff_infDist_pos hne]; simpa using hy
      obtain ⟨k, hk⟩ := exists_nat_ge (1 / infDist y Wᶜ)
      refine ⟨k, min_eq_left ?_⟩
      rw [div_le_iff₀ hpos] at hk; linarith
    · intro k y hy
      have : infDist y Wᶜ = 0 := infDist_zero_of_mem hy
      simp [this]
end


section
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- From the `F`-identity on `V` to the identity on open sets whose closure lies in `V`. -/
theorem measure_image_eq_of_local (μ : Measure X) (T : X ≃ₜ X) (J : X → ℝ≥0∞)
    (hJ : Measurable J) (V O : Set X) (hO : IsOpen O) (hcl : closure O ⊆ V)
    (hV : ∀ F : X → ℝ, UniformContinuous F → (∃ C, ∀ y, |F y| ≤ C) →
        (∀ y, 0 ≤ F y) → tsupport F ⊆ T '' V →
        ∫⁻ y in T '' V, ENNReal.ofReal (F y) ∂μ = ∫⁻ x in V, ENNReal.ofReal (F (T x)) * J x ∂μ) :
    μ (T '' O) = ∫⁻ x in O, J x ∂μ := by
  have hW : IsOpen (T '' O) := T.isOpenMap O hO
  obtain ⟨F, hUC, hb, hsupp, hmono, hone, hzero⟩ := exists_open_approx (T '' O) hW
  have hFm : ∀ k, Measurable (F k) := fun k => (hUC k).continuous.measurable
  have hsub : ∀ k, tsupport (F k) ⊆ T '' V := by
    intro k
    have h1 : tsupport (F k) ⊆ closure (T '' O) :=
      closure_mono (fun y hy => hsupp k y hy)
    rw [← T.image_closure] at h1
    exact h1.trans (image_mono hcl)
  have hid := fun k => hV (F k) (hUC k) ⟨1, fun y => by
    rw [abs_of_nonneg (hb k y).1]; exact (hb k y).2⟩ (fun y => (hb k y).1) (hsub k)
  have hsup : ∀ y, ⨆ k, ENNReal.ofReal (F k y) = (T '' O).indicator 1 y := by
    intro y
    by_cases hy : y ∈ T '' O
    · obtain ⟨k, hk⟩ := hone y hy
      rw [indicator_of_mem hy]
      refine le_antisymm (iSup_le fun l => ?_) (le_iSup_of_le k (by rw [hk]; simp))
      simpa using ENNReal.ofReal_le_ofReal (hb l y).2
    · simp [indicator_of_notMem hy, hzero _ y hy]
  have hmono' : Monotone fun k => fun y => ENNReal.ofReal (F k y) :=
    fun k l hkl y => ENNReal.ofReal_le_ofReal (hmono k l hkl y)
  have hL : μ (T '' O) = ⨆ k, ∫⁻ y in T '' V, ENNReal.ofReal (F k y) ∂μ := by
    refine Eq.trans ?_ (lintegral_iSup (μ := μ.restrict (T '' V))
      (f := fun k y => ENNReal.ofReal (F k y))
      (fun k => ENNReal.measurable_ofReal.comp (hFm k)) hmono')
    simp_rw [hsup]
    rw [lintegral_indicator_one hW.measurableSet, Measure.restrict_apply hW.measurableSet]
    congr 1
    exact (inter_eq_left.2 (image_mono (subset_closure.trans hcl))).symm
  have hsupO : ∀ x, ⨆ k, ENNReal.ofReal (F k (T x)) * J x = O.indicator J x := by
    intro x
    rw [← ENNReal.iSup_mul]
    by_cases hx : x ∈ O
    · rw [indicator_of_mem hx, hsup, indicator_of_mem (mem_image_of_mem T hx)]; simp
    · have : T x ∉ T '' O := fun h => hx (T.injective.mem_set_image.1 h)
      rw [indicator_of_notMem hx, hsup, indicator_of_notMem this]; simp
  have hmonoO : Monotone fun k => fun x => ENNReal.ofReal (F k (T x)) * J x :=
    fun k l hkl x => mul_le_mul_left (ENNReal.ofReal_le_ofReal (hmono k l hkl _)) _
  have hR : ⨆ k, ∫⁻ x in V, ENNReal.ofReal (F k (T x)) * J x ∂μ = ∫⁻ x in O, J x ∂μ := by
    refine Eq.trans (lintegral_iSup (μ := μ.restrict V)
      (f := fun k x => ENNReal.ofReal (F k (T x)) * J x)
      (fun k => (ENNReal.measurable_ofReal.comp
      ((hFm k).comp T.continuous.measurable)).mul hJ) hmonoO).symm ?_
    simp_rw [hsupO]
    rw [lintegral_indicator hO.measurableSet, Measure.restrict_restrict hO.measurableSet,
      inter_eq_left.2 (subset_closure.trans hcl)]
  rw [hL, ← hR]
  exact iSup_congr hid

variable [SecondCountableTopology X]

theorem map_symm_eq_withDensity_of_local (μ : Measure X) [IsFiniteMeasure μ] (T : X ≃ₜ X)
    (J : X → ℝ≥0∞) (hJ : Measurable J)
    (hloc : ∀ x₀, ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ ∀ F : X → ℝ, UniformContinuous F →
        (∃ C, ∀ y, |F y| ≤ C) → (∀ y, 0 ≤ F y) → tsupport F ⊆ T '' V →
        ∫⁻ y in T '' V, ENNReal.ofReal (F y) ∂μ =
          ∫⁻ x in V, ENNReal.ofReal (F (T x)) * J x ∂μ) :
    μ.map T.symm = μ.withDensity J := by
  -- good open sets
  let Good : Set X → Prop := fun O => IsOpen O ∧ ∃ V : Set X, IsOpen V ∧
    (∀ F : X → ℝ, UniformContinuous F → (∃ C, ∀ y, |F y| ≤ C) → (∀ y, 0 ≤ F y) →
      tsupport F ⊆ T '' V →
      ∫⁻ y in T '' V, ENNReal.ofReal (F y) ∂μ =
        ∫⁻ x in V, ENNReal.ofReal (F (T x)) * J x ∂μ) ∧ closure O ⊆ V
  let C : Set (Set X) := {O | O = ∅ ∨ Good O}
  -- every open set is a countable union of good sets inside it
  have hcover : ∀ U : Set X, IsOpen U → ∃ S : Set (Set X), S.Countable ∧ (∀ O ∈ S, Good O) ∧
      ⋃₀ S = U := by
    intro U hU
    let S0 : Set (Set X) := {O | Good O ∧ O ⊆ U}
    obtain ⟨S, hSc, hSS, hSU⟩ := TopologicalSpace.isOpen_sUnion_countable S0 (fun O hO => hO.1.1)
    refine ⟨S, hSc, fun O hO => (hSS hO).1, ?_⟩
    rw [hSU]
    refine subset_antisymm (sUnion_subset fun O hO => hO.2) fun x hx => ?_
    obtain ⟨V, hV, hxV, hVp⟩ := hloc x
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hU.inter hV) x ⟨hx, hxV⟩
    refine ⟨Metric.ball x (r / 2), ⟨⟨Metric.isOpen_ball, V, hV, hVp, ?_⟩, ?_⟩,
      Metric.mem_ball_self (half_pos hr)⟩
    · refine (closure_ball_subset_closedBall).trans ?_
      intro y hy
      exact (hball (Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 hy)
        (half_lt_self hr)))).2
    · intro y hy
      exact (hball (Metric.ball_subset_ball (half_le_self hr.le) hy)).1
  have hgood : ∀ O, Good O → μ.map T.symm O = μ.withDensity J O := by
    rintro O ⟨hO, V, hV, hVp, hcl⟩
    rw [Measure.map_apply T.symm.continuous.measurable hO.measurableSet,
      withDensity_apply _ hO.measurableSet]
    have : T.symm ⁻¹' O = T '' O := (T.toEquiv.image_eq_preimage_symm O).symm
    rw [this]
    exact (measure_image_eq_of_local μ T J hJ V O hO hcl hVp)
  have hpi : IsPiSystem C := by
    rintro O1 (rfl | ⟨h1, V, hV, hVp, hcl⟩) O2 (rfl | ⟨h2, V2, hV2, hVp2, hcl2⟩) _
    · left; simp
    · left; simp
    · left; simp
    · right
      exact ⟨h1.inter h2, V, hV, hVp, (closure_inter_subset_inter_closure _ _).trans
        (inter_subset_left.trans hcl)⟩
  have hgen : (inferInstance : MeasurableSpace X) = MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · rw [BorelSpace.measurable_eq (α := X)]
      refine MeasurableSpace.generateFrom_le fun U hU => ?_
      obtain ⟨S, hSc, hS, hSU⟩ := hcover U hU
      rw [← hSU]
      exact MeasurableSet.sUnion hSc fun O hO => MeasurableSpace.measurableSet_generateFrom
        (Or.inr (hS O hO))
    · refine MeasurableSpace.generateFrom_le ?_
      rintro O (rfl | ⟨hO, _⟩)
      · exact MeasurableSet.empty
      · exact hO.measurableSet
  obtain ⟨S, hSc, hS, hSU⟩ := hcover univ isOpen_univ
  obtain ⟨f, hf⟩ := (hSc.insert (∅ : Set X)).exists_eq_range (insert_nonempty _ _)
  refine Measure.ext_of_generateFrom_of_iUnion C f hgen hpi ?_ ?_ (fun i => measure_ne_top _ _) ?_
  · apply eq_univ_of_univ_subset
    rw [← hSU]
    refine sUnion_subset fun O hO => ?_
    have : O ∈ range f := hf ▸ mem_insert_of_mem _ hO
    obtain ⟨i, rfl⟩ := this
    exact subset_iUnion f i
  · intro i
    have : f i ∈ insert (∅ : Set X) S := hf ▸ mem_range_self i
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr (hS _ h)
  · rintro O (rfl | hO)
    · simp
    · exact hgood O hO

end

end NlsGge.Ramer
