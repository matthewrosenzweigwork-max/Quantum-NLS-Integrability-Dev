import QuantumNLS.RootEnergyMomentLaws

/-! Elementary L¹ estimates for varying Born probability spaces. These
support lemmas expose all convergence inputs; the physical consumer must
prove them for the actual laws. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootEnergyMomentProbability
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]

/-- Bounded convergence in probability gives L¹ convergence on varying
probability spaces, without constructing a coupling. -/
theorem bounded_probability_L1 (X : ∀ n, Ω n → ℝ) (c B : ℝ)
    (hm : ∀ n, Measurable (X n))
    (hb : ∀ n ω, |X n ω-c| ≤ B)
    (hp : QuantumNLS.BornConvergence.TendstoInProbability P X c) :
    Tendsto (fun n => ∫ ω, |X n ω-c| ∂P n) atTop (nhds 0) := by
  have hi (n : ℕ) : Integrable (fun ω => |X n ω-c|) (P n) := by
    refine (integrable_const B).mono' ((hm n).sub_const c).abs.aestronglyMeasurable ?_
    exact ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs,abs_abs] using hb n ω)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let A := fun n => {ω : Ω n | δ < dist (X n ω) c}
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_lt measurable_const
    ((hm n).dist measurable_const)
  have hlim : Tendsto (fun n => δ + B * (P n (A n)).toReal) atTop (nhds δ) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hp δ hδ)
    simpa using (ht.const_mul B).const_add δ
  have hbound (n : ℕ) : (∫ ω, |X n ω-c| ∂P n) ≤ δ + B * (P n (A n)).toReal := by
    have hmaj : Integrable (fun ω => δ + (A n).indicator (fun _ => B) ω) (P n) :=
      (integrable_const δ).add ((integrable_const B).indicator (hA n))
    calc
      _ ≤ ∫ ω, δ + (A n).indicator (fun _ => B) ω ∂P n := by
        apply integral_mono_ae (hi n) hmaj
        apply ae_of_all
        intro ω
        change |X n ω-c| ≤ δ + (A n).indicator (fun _ => B) ω
        by_cases h : ω ∈ A n
        · rw [Set.indicator_of_mem h]
          exact (hb n ω).trans (by linarith)
        · rw [Set.indicator_of_notMem h,add_zero]
          have hh : ¬δ < |X n ω-c| := by simpa only [A,Set.mem_ofPred_eq,Real.dist_eq] using h
          exact le_of_not_gt hh
      _ = _ := by
        rw [integral_add (integrable_const δ) ((integrable_const B).indicator (hA n)),
          integral_const,integral_indicator_const B (hA n)]
        simp [measureReal_def,mul_comm]
  filter_upwards [hlim.eventually (gt_mem_nhds (show δ < ε by dsimp [δ]; linarith))] with n hn
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
  exact (hbound n).trans_lt hn

/-- A nonnegative variable can be estimated in L¹ by any integrable
nonnegative lower truncation. This avoids an assumed unbounded-moment limit. -/
lemma lower_truncation_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (X Y : α → ℝ) (c d : ℝ)
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (hlo : ∀ ω, Y ω ≤ X ω) :
    (∫ ω, |X ω-c| ∂μ) ≤ (∫ ω, X ω ∂μ) - d +
      2 * (∫ ω, |Y ω-d| ∂μ) + |d-c| := by
  have hxy : Integrable (fun ω => X ω-Y ω) μ := hX.sub hY
  have habs : Integrable (fun ω => |X ω-c|) μ := (hX.sub (integrable_const c)).abs
  have hya : Integrable (fun ω => |Y ω-d|) μ := (hY.sub (integrable_const d)).abs
  have hmaj : Integrable (fun ω => (X ω-Y ω) + |Y ω-d| + |d-c|) μ :=
    (hxy.add hya).add (integrable_const _)
  have hle : (∫ ω, |X ω-c| ∂μ) ≤
      (∫ ω, X ω ∂μ) - (∫ ω, Y ω ∂μ) + (∫ ω, |Y ω-d| ∂μ) + |d-c| := by
    calc
      _ ≤ ∫ ω, (X ω-Y ω) + |Y ω-d| + |d-c| ∂μ := by
        apply integral_mono_ae habs hmaj
        apply ae_of_all
        intro ω
        change |X ω-c| ≤ X ω-Y ω + |Y ω-d| + |d-c|
        have h : ‖(X ω-Y ω) + (Y ω-d) + (d-c)‖ ≤
            ‖X ω-Y ω‖ + ‖Y ω-d‖ + ‖d-c‖ := norm_add₃_le
        simp only [Real.norm_eq_abs] at h
        rw [abs_of_nonneg (sub_nonneg.mpr (hlo ω)),
          show (X ω-Y ω) + (Y ω-d) + (d-c) = X ω-c by ring] at h
        exact h
      _ = (∫ ω,(X ω-Y ω) + |Y ω-d| ∂μ) + (∫ _ : α,|d-c| ∂μ) :=
        integral_add (hxy.add hya) (integrable_const _)
      _ = _ := by
        rw [show (∫ ω,(X ω-Y ω) + |Y ω-d| ∂μ) =
          (∫ ω,X ω-Y ω ∂μ) + (∫ ω,|Y ω-d| ∂μ) from integral_add hxy hya,
          integral_sub hX hY]
        simp
  have hlow : d - (∫ ω, Y ω ∂μ) ≤ ∫ ω, |Y ω-d| ∂μ := by
    have hh := norm_integral_le_integral_norm (fun ω => Y ω-d) (μ := μ)
    rw [integral_sub hY (integrable_const d)] at hh
    simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans (by rw [abs_sub_comm]; exact hh)
  linarith

#print axioms bounded_probability_L1
#print axioms lower_truncation_bound
end QuantumNLS.RootEnergyMomentProbability

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentProbability." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentProbability." then
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
