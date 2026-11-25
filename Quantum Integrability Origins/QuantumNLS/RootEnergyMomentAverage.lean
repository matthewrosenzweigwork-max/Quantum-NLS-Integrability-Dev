import QuantumNLS.RootEnergyMomentExpectation
import QuantumNLS.RootEnergyMomentBounded

/-! Actual barycenter integrals, with all nonnegative interchange and
integrability hypotheses proved at each application. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.BulkResponseActual QuantumNLS.EmpiricalRapidity
open QuantumNLS.RootEnergyMomentLaws QuantumNLS.RootEnergyMomentExpectation
open QuantumNLS.RootEnergyMomentBounded QuantumNLS.ProductEnergyPreparation QuantumNLS.ChargeEnergy
namespace QuantumNLS.RootEnergyMomentAverage

lemma bind_nonnegative {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
    (P : Measure A) (K : A → Measure ℝ) (f : ℝ → ℝ)
    (hm : Measurable f) (hn : ∀ t, 0 ≤ f t)
    (hi : ∀ a, Integrable f (K a))
    (ho : Integrable (fun a => ∫ t,f t ∂K a) P) :
    Integrable f (P.bind K) ∧ (∫ t,f t ∂P.bind K) = ∫ a,∫ t,f t ∂K a ∂P := by
  have he : (∫⁻ t,ENNReal.ofReal (f t) ∂P.bind K) =
      ENNReal.ofReal (∫ a,∫ t,f t ∂K a ∂P) := by
    rw [Measure.lintegral_bind (measurable_of_countable K).aemeasurable
      hm.ennreal_ofReal.aemeasurable]
    simp_rw [← ofReal_integral_eq_lintegral_ofReal (hi _) (ae_of_all _ hn)]
    exact (ofReal_integral_eq_lintegral_ofReal ho
      (ae_of_all _ (fun a => integral_nonneg hn))).symm
  have hf : Integrable f (P.bind K) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable (ae_of_all _ hn)).mp
      (by rw [he]; exact ENNReal.ofReal_ne_top)
  refine ⟨hf,?_⟩
  have hh := congrArg ENNReal.toReal
    ((ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ hn)).trans he)
  simpa only [ENNReal.toReal_ofReal (integral_nonneg hn),
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => integral_nonneg hn))] using hh

variable {L κ : ℝ} [Fact (0 < L)]

def barycenter (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (n : ℕ) : Measure ℝ :=
  meanEmpirical (physBasis L hκ (n+1)) u hu (κ/((n+1 : ℕ) : ℝ))

instance (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (n : ℕ) :
    IsProbabilityMeasure (barycenter hκ u hu n) :=
  ⟨meanEmpirical_univ _ u hu _ (Nat.succ_pos n)⟩

omit [Fact (0 < L)] in
lemma empiricalProb_succ (n : ℕ) (m : QuantumNLS.BetheLabels.MArr (n+1)) :
    (empiricalProb L κ (n+1) m : Measure ℝ) =
      empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m := by
  unfold empiricalProb
  split_ifs with hn
  · rfl
  · exact (hn (Nat.succ_pos n)).elim

/-- The actual barycenter has its finite exact contact second moment. -/
theorem barycenter_second (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) (n : ℕ) :
    Integrable (fun t : ℝ => t^2) (barycenter hκ u hu n) ∧
    (∫ t : ℝ,t^2 ∂barycenter hκ u hu n) =
      energyH1 κ (u : AddCircle L → ℂ) - κ * quartic (u : AddCircle L → ℂ) / ((n+1 : ℕ) : ℝ) := by
  have he (m : QuantumNLS.BetheLabels.MArr (n+1)) :
      (∫ t : ℝ,t^2 ∂empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m) = sampleEnergy L κ (n+1) m :=
    (sample_second_moment (Nat.succ_pos n) m).2
  have hi : Integrable (fun m : QuantumNLS.BetheLabels.MArr (n+1) =>
      ∫ t : ℝ,t^2 ∂empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m) (law hκ u hu (n+1)) := by
    simpa only [he] using (actual_energy_expectation (Nat.succ_pos n) hκ u hu hH).1
  have h := bind_nonnegative (law hκ u hu (n+1))
    (fun m => empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m) (fun t : ℝ => t^2)
    ((continuous_id.pow 2).measurable) sq_nonneg (fun m => (sample_second_moment (Nat.succ_pos n) m).1) hi
  refine ⟨h.1,?_⟩
  exact h.2.trans (by
    simp only [he]
    exact (actual_energy_expectation (Nat.succ_pos n) hκ u hu hH).2)

lemma barycenter_moment_limit (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) :
    Tendsto (fun n => ∫ t : ℝ,t^2 ∂barycenter hκ u hu n) atTop
      (nhds (energyH1 κ (u : AddCircle L → ℂ))) := by
  simp_rw [(barycenter_second hκ u hu hH _).2]
  have h := (tendsto_const_div_atTop_nhds_zero_nat
    (κ * quartic (u : AddCircle L → ℂ))).const_sub (energyH1 κ (u : AddCircle L → ℂ))
  simpa only [Function.comp_def,sub_zero] using h.comp (tendsto_add_atTop_nat 1)

lemma barycenter_clip (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (n : ℕ)
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ t,clip R t ∂barycenter hκ u hu n) =
      ∫ m,∫ t,clip R t ∂(empiricalProb L κ (n+1) m : Measure ℝ) ∂law hκ u hu (n+1) := by
  have he (m : QuantumNLS.BetheLabels.MArr (n+1)) :
      (empiricalProb L κ (n+1) m : Measure ℝ) = empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m := by
    exact empiricalProb_succ n m
  have ho : Integrable (fun m : QuantumNLS.BetheLabels.MArr (n+1) =>
      ∫ t,clip R t ∂(empiricalProb L κ (n+1) m : Measure ℝ)) (law hκ u hu (n+1)) := by
    apply (integrable_const R).mono' (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all
    intro m
    rw [Real.norm_eq_abs,abs_of_nonneg (clip_integral_bounds _ hR).1]
    exact (clip_integral_bounds _ hR).2
  simp_rw [he] at ho ⊢
  exact (bind_nonnegative (law hκ u hu (n+1))
    (fun m => empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m) (clip R)
    ((continuous_id.pow 2).min continuous_const).measurable (clip_nonneg hR)
    (fun m => by
      have := isProbabilityMeasure_empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) (Nat.succ_pos n) m
      exact clip_integrable _ hR) ho).2

lemma barycenter_clip_limit (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n => ∫ t,clip R t ∂barycenter hκ u hu n) atTop
      (nhds (∫ t,clip R t ∂(QuantumNLS.FreeLimit.muKappa u hu κ : Measure ℝ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp (actual_clip_L1 hκ u hu hR)) ε hε] with n hn
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at hn
  rw [Real.dist_eq,barycenter_clip hκ u hu n hR]
  have hi : Integrable (fun m : QuantumNLS.BetheLabels.MArr (n+1) =>
      ∫ t,clip R t ∂(empiricalProb L κ (n+1) m : Measure ℝ)) (law hκ u hu (n+1)) := by
    apply (integrable_const R).mono' (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all
    intro m
    rw [Real.norm_eq_abs,abs_of_nonneg (clip_integral_bounds _ hR).1]
    exact (clip_integral_bounds _ hR).2
  have hh := norm_integral_le_integral_norm
    (fun m : QuantumNLS.BetheLabels.MArr (n+1) =>
      (∫ t,clip R t ∂(empiricalProb L κ (n+1) m : Measure ℝ)) -
        (∫ t,clip R t ∂(QuantumNLS.FreeLimit.muKappa u hu κ : Measure ℝ)))
    (μ := law hκ u hu (n+1))
  rw [integral_sub hi (integrable_const _)] at hh
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,Real.norm_eq_abs] at hh
  exact hh.trans_lt hn

#print axioms barycenter_second
#print axioms barycenter_clip_limit
end QuantumNLS.RootEnergyMomentAverage

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentAverage." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentAverage." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
