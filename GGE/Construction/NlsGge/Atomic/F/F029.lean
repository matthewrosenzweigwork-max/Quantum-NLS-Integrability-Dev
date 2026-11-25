                                                                                                                                                                                                                                                            
                                                                     
import Mathlib

                                                                                  
                                                                                  
                                                                                                
                                                                                                    

set_option autoImplicit false

open MeasureTheory

namespace NlsGge.Atomic.F029

/-- Core clause-1 bound for a strongly measurable integrable nonnegative `F'`. -/
theorem core_clause1 {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝒜 : ℕ → MeasurableSpace Ω) (h𝒜 : ∀ N : ℕ, 𝒜 N ≤ mΩ)
    (F' : Ω → ℝ) (hF' : Integrable F' μ) (hmeas : StronglyMeasurable F')
    (hpos : ∀ᵐ ω ∂μ, 0 ≤ F' ω) (K : ℝ) (hK : 0 < K) (N : ℕ) :
    (∫ ω in {ω | K < μ[F' | 𝒜 N] ω}, μ[F' | 𝒜 N] ω ∂μ) ≤
      2 * ∫ ω in {ω | K / 2 < F' ω}, F' ω ∂μ := by
  have hG_int : Integrable (μ[F' | 𝒜 N]) μ := integrable_condExp
  have hGmeas : Measurable[𝒜 N] (μ[F' | 𝒜 N]) := stronglyMeasurable_condExp.measurable
  have hs_m : MeasurableSet[𝒜 N] {ω | K < μ[F' | 𝒜 N] ω} :=
    measurableSet_lt measurable_const hGmeas
  have hs : MeasurableSet {ω | K < μ[F' | 𝒜 N] ω} := h𝒜 N _ hs_m
  have ht : MeasurableSet {ω | K / 2 < F' ω} := measurableSet_lt measurable_const hmeas.measurable
  have hX : ∫ ω in {ω | K < μ[F' | 𝒜 N] ω}, μ[F' | 𝒜 N] ω ∂μ =
      ∫ ω in {ω | K < μ[F' | 𝒜 N] ω}, F' ω ∂μ :=
    setIntegral_condExp (h𝒜 N) hF' hs_m
  have hM : K * (μ {ω | K < μ[F' | 𝒜 N] ω}).toReal ≤
      ∫ ω in {ω | K < μ[F' | 𝒜 N] ω}, μ[F' | 𝒜 N] ω ∂μ :=
    setIntegral_ge_of_const_le_real hs (measure_ne_top μ _)
      (fun ω hω => le_of_lt hω) hG_int.integrableOn
  set s := {ω | K < μ[F' | 𝒜 N] ω} with hsdef
  set t := {ω | K / 2 < F' ω} with htdef
  have hsplit : ∫ ω in s, F' ω ∂μ = ∫ ω in s ∩ t, F' ω ∂μ + ∫ ω in s \ t, F' ω ∂μ :=
    (integral_inter_add_diff ht hF'.integrableOn).symm
  have hA : ∫ ω in s ∩ t, F' ω ∂μ ≤ ∫ ω in t, F' ω ∂μ :=
    setIntegral_mono_set hF'.integrableOn (ae_restrict_of_ae hpos)
      (Filter.Eventually.of_forall (fun ω hω => hω.2))
  have hB : ∫ ω in s \ t, F' ω ∂μ ≤ (K / 2) * (μ (s \ t)).toReal := by
    calc ∫ ω in s \ t, F' ω ∂μ ≤ ∫ ω in s \ t, (K / 2) ∂μ := by
          refine setIntegral_mono_on hF'.integrableOn
            ((integrable_const (K / 2)).integrableOn) (hs.diff ht) ?_
          intro ω hω
          have hωt : ω ∉ t := hω.2
          have : ¬ (K / 2 < F' ω) := hωt
          exact not_lt.mp this
      _ = (K / 2) * (μ (s \ t)).toReal := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
  have hmeasdiff : (μ (s \ t)).toReal ≤ (μ s).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ s) (measure_mono Set.diff_subset)
  have h1 : (K / 2) * (μ s).toReal ≤ (∫ ω in s, F' ω ∂μ) / 2 := by
    rw [← hX] at *
    linarith
  have h2 : (K / 2) * (μ (s \ t)).toReal ≤ (K / 2) * (μ s).toReal :=
    mul_le_mul_of_nonneg_left hmeasdiff (by positivity)
  rw [hX]
  linarith

theorem f029_clause12 {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝒜 : ℕ → MeasurableSpace Ω) (h𝒜 : ∀ N : ℕ, 𝒜 N ≤ mΩ)
    (F : Ω → ℝ) (hF : Integrable F μ) (hpos : ∀ᵐ ω ∂μ, 0 ≤ F ω) :
    (∀ (K : ℝ), 0 < K → ∀ N : ℕ,
      (∫ ω in {ω | K < μ[F | 𝒜 N] ω}, μ[F | 𝒜 N] ω ∂μ) ≤
        2 * ∫ ω in {ω | K / 2 < F ω}, F ω ∂μ) ∧
    UniformIntegrable (fun N => μ[F | 𝒜 N]) 1 μ := by
  refine ⟨?_, ?_⟩
  · intro K hK N
    set F' : Ω → ℝ := hF.1.mk F with hF'def
    have hFF' : F =ᵐ[μ] F' := hF.1.ae_eq_mk
    have hF'meas : StronglyMeasurable F' := hF.1.stronglyMeasurable_mk
    have hF' : Integrable F' μ := hF.congr hFF'
    have hpos' : ∀ᵐ ω ∂μ, 0 ≤ F' ω := by
      filter_upwards [hpos, hFF'] with ω h1 h2
      rw [← h2]; exact h1
    have hG : μ[F | 𝒜 N] =ᵐ[μ] μ[F' | 𝒜 N] := condExp_congr_ae hFF'
    have hsetG : {ω | K < μ[F | 𝒜 N] ω} =ᵐ[μ] {ω | K < μ[F' | 𝒜 N] ω} := by
      filter_upwards [hG] with ω hω
      simp only [Set.mem_setOf_eq, hω]
    have hsetF : {ω | K / 2 < F ω} =ᵐ[μ] {ω | K / 2 < F' ω} := by
      filter_upwards [hFF'] with ω hω
      simp only [Set.mem_setOf_eq, hω]
    rw [setIntegral_congr_set hsetG, setIntegral_congr_set hsetF,
      integral_congr_ae (ae_restrict_of_ae hG), integral_congr_ae (ae_restrict_of_ae hFF')]
    exact core_clause1 μ 𝒜 h𝒜 F' hF' hF'meas hpos' K hK N
  · exact Integrable.uniformIntegrable_condExp hF (fun N => h𝒜 N)


/-- Truncated indicator of an a.e.-strongly-measurable real function is a.e.-strongly-measurable. -/
lemma aemeas_trunc {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
    (hg : AEStronglyMeasurable g μ) (L : NNReal) :
    AEStronglyMeasurable ({x | L ≤ ‖g x‖₊}.indicator g) μ := by
  refine hg.indicator₀ ?_
  have hset : {x | L ≤ ‖g x‖₊} = {x | ((L : NNReal) : ℝ) ≤ ‖g x‖} := by
    ext x
    simp only [Set.mem_setOf_eq, ← NNReal.coe_le_coe, coe_nnnorm]
  rw [hset]
  exact nullMeasurableSet_le (aemeasurable_const) hg.norm.aemeasurable

/-- Pointwise truncation monotonicity for the indicator norm. -/
lemma ind_trunc_mono {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) {L L' : NNReal} (h : L ≤ L') :
    eLpNorm ({x | L' ≤ ‖f x‖₊}.indicator f) 1 μ ≤ eLpNorm ({x | L ≤ ‖f x‖₊}.indicator f) 1 μ := by
  refine eLpNorm_mono (aemeas_trunc μ f hf L') (fun x => ?_)
  by_cases hx : L' ≤ ‖f x‖₊
  · have hx' : L ≤ ‖f x‖₊ := h.trans hx
    simp [Set.indicator_apply, hx, hx']
  · simp [Set.indicator_apply, hx]

/-- Clause 3: domination by a uniformly integrable conditional-expectation family. -/
theorem f029_clause3 {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝒜 : ℕ → MeasurableSpace Ω) (h𝒜 : ∀ N : ℕ, 𝒜 N ≤ mΩ)
    (F : Ω → ℝ) (hF : Integrable F μ) (hpos : ∀ᵐ ω ∂μ, 0 ≤ F ω) :
    ∀ (W : ℕ → Ω → ℝ) (C : ℝ) (N₀ : ℕ),
      0 ≤ C → (∀ N : ℕ, Integrable (W N) μ) →
      (∀ N : ℕ, N₀ ≤ N → ∀ᵐ ω ∂μ,
        ‖W N ω‖ ≤ C * μ[F | 𝒜 N] ω) →
      UniformIntegrable W 1 μ := by
  intro W C N₀ hC hW hdom
  have hG : UniformIntegrable (fun N => μ[F | 𝒜 N]) 1 μ :=
    Integrable.uniformIntegrable_condExp hF (fun N => h𝒜 N)
  have hGnn : ∀ N : ℕ, ∀ᵐ ω ∂μ, 0 ≤ μ[F | 𝒜 N] ω := fun N => condExp_nonneg hpos
  rw [uniformIntegrable_iff le_rfl ENNReal.one_ne_top]
  refine ⟨fun i => (hW i).aestronglyMeasurable, fun ε hε => ?_⟩
  rw [uniformIntegrable_iff le_rfl ENNReal.one_ne_top] at hG
  obtain ⟨-, hGε⟩ := hG
  set c : ℝ := C + 1 with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hcofe : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  obtain ⟨D, hD⟩ := hGε (ε / ENNReal.ofReal c)
    (ENNReal.div_pos_iff.2 ⟨hε.ne', ENNReal.ofReal_ne_top⟩)
  have hfin := uniformIntegrable_finite (p := 1) (ι := Fin N₀) (f := fun i : Fin N₀ => W i)
    le_rfl ENNReal.one_ne_top (fun i => memLp_one_iff_integrable.mpr (hW i))
  rw [uniformIntegrable_iff le_rfl ENNReal.one_ne_top] at hfin
  obtain ⟨-, hLfin⟩ := hfin
  obtain ⟨L₀, hL₀⟩ := hLfin ε hε
  refine ⟨L₀ + Real.toNNReal c * D, fun N => ?_⟩
  by_cases hN : N < N₀
  · have h1 := hL₀ ⟨N, hN⟩
    have hle : L₀ ≤ L₀ + Real.toNNReal c * D := le_add_of_nonneg_right (by positivity)
    exact (ind_trunc_mono μ (W N) (hW N).aestronglyMeasurable hle).trans h1
  · push Not at hN
    have hbd : ∀ᵐ ω ∂μ, ‖({x | Real.toNNReal c * D ≤ ‖W N x‖₊}.indicator (W N)) ω‖ ≤
        c * ({x | D ≤ ‖μ[F | 𝒜 N] x‖₊}.indicator (μ[F | 𝒜 N])) ω := by
      filter_upwards [hdom N hN, hGnn N] with ω h1 h2
      by_cases hx : Real.toNNReal c * D ≤ ‖W N ω‖₊
      · have hxr : c * (D : ℝ) ≤ ‖W N ω‖ := by
          have := NNReal.coe_le_coe.mpr hx
          simpa [Real.coe_toNNReal _ hc.le, NNReal.coe_mul] using this
        have hGD : (D : ℝ) ≤ μ[F | 𝒜 N] ω := by
          have hle : c * (D : ℝ) ≤ c * μ[F | 𝒜 N] ω := by
            refine hxr.trans ?_
            refine h1.trans ?_
            exact mul_le_mul_of_nonneg_right (by linarith) h2
          exact le_of_mul_le_mul_left hle hc
        have hxD : D ≤ ‖μ[F | 𝒜 N] ω‖₊ := by
          rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_of_nonneg h2]
          exact hGD
        simp only [Set.indicator_apply, Set.mem_setOf_eq, hx, hxD, if_true]
        exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) h2)
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, hx, if_false, norm_zero]
        split_ifs
        · exact mul_nonneg hc.le h2
        · simp
    have hchain : eLpNorm ({x | Real.toNNReal c * D ≤ ‖W N x‖₊}.indicator (W N)) 1 μ ≤ ε := by
      calc eLpNorm ({x | Real.toNNReal c * D ≤ ‖W N x‖₊}.indicator (W N)) 1 μ
          ≤ eLpNorm (fun ω => c * ({x | D ≤ ‖μ[F | 𝒜 N] x‖₊}.indicator (μ[F | 𝒜 N])) ω) 1 μ :=
            eLpNorm_mono_ae_real (aemeas_trunc μ (W N) (hW N).aestronglyMeasurable (Real.toNNReal c * D)) hbd
        _ = ENNReal.ofReal c * eLpNorm ({x | D ≤ ‖μ[F | 𝒜 N] x‖₊}.indicator (μ[F | 𝒜 N])) 1 μ := by
            rw [show (fun ω => c * ({x | D ≤ ‖μ[F | 𝒜 N] x‖₊}.indicator (μ[F | 𝒜 N])) ω) =
              c • ({x | D ≤ ‖μ[F | 𝒜 N] x‖₊}.indicator (μ[F | 𝒜 N])) from rfl,
              eLpNorm_const_smul]
            simp [Real.enorm_eq_ofReal hc.le]
        _ ≤ ENNReal.ofReal c * (ε / ENNReal.ofReal c) := mul_le_mul_of_nonneg_left (hD N) (by positivity)
        _ = ε := ENNReal.mul_div_cancel' (fun h => absurd h hcofe) (fun h => absurd h ENNReal.ofReal_ne_top)
    have hle2 : Real.toNNReal c * D ≤ L₀ + Real.toNNReal c * D := le_add_of_nonneg_left (by positivity)
    exact (ind_trunc_mono μ (W N) (hW N).aestronglyMeasurable hle2).trans hchain


/-- F-029, Pro's full signature (STATEMENTS/F.md, F-029). -/
theorem f029 {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝒜 : ℕ → MeasurableSpace Ω) (h𝒜 : ∀ N : ℕ, 𝒜 N ≤ mΩ)
    (F : Ω → ℝ) (hF : Integrable F μ) (hpos : ∀ᵐ ω ∂μ, 0 ≤ F ω) :
    (∀ (K : ℝ), 0 < K → ∀ N : ℕ,
      (∫ ω in {ω | K < μ[F | 𝒜 N] ω}, μ[F | 𝒜 N] ω ∂μ) ≤
        2 * ∫ ω in {ω | K / 2 < F ω}, F ω ∂μ) ∧
    UniformIntegrable (fun N => μ[F | 𝒜 N]) 1 μ ∧
    (∀ (W : ℕ → Ω → ℝ) (C : ℝ) (N₀ : ℕ),
      0 ≤ C → (∀ N : ℕ, Integrable (W N) μ) →
      (∀ N : ℕ, N₀ ≤ N → ∀ᵐ ω ∂μ,
        ‖W N ω‖ ≤ C * μ[F | 𝒜 N] ω) →
      UniformIntegrable W 1 μ) :=
  ⟨(f029_clause12 μ 𝒜 h𝒜 F hF hpos).1, (f029_clause12 μ 𝒜 h𝒜 F hF hpos).2,
    f029_clause3 μ 𝒜 h𝒜 F hF hpos⟩


end NlsGge.Atomic.F029
