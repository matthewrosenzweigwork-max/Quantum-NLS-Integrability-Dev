import QuantumNLS.RootEnergyMomentProbability
import QuantumNLS.RootEnergyMomentScalar
import QuantumNLS.FullMassLimit

/-! Actual bounded-square observables under the physical Born laws. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.BulkResponseActual
open QuantumNLS.RootEnergyMomentLaws
namespace QuantumNLS.RootEnergyMomentBounded
variable {L κ : ℝ} [Fact (0 < L)]

def clip (R : ℝ) (t : ℝ) : ℝ := min (t^2) R

lemma clip_nonneg {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : 0 ≤ clip R t :=
  le_min (sq_nonneg t) hR

lemma clip_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] {R : ℝ} (hR : 0 ≤ R) :
    Integrable (clip R) μ := by
  apply (integrable_const R).mono' ((continuous_id.pow 2).min continuous_const).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    change ‖clip R t‖ ≤ R
    rw [Real.norm_eq_abs,abs_of_nonneg (clip_nonneg hR t)]
    exact min_le_right _ _)

def clipBCF (R : ℝ) (hR : 0 ≤ R) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨clip R,(continuous_id.pow 2).min continuous_const⟩ R
    (fun x y => by
      change dist (clip R x) (clip R y) ≤ R
      have hx : clip R x ≤ R := min_le_right _ _
      have hy : clip R y ≤ R := min_le_right _ _
      rw [Real.dist_eq,abs_sub_le_iff]
      constructor <;> linarith [clip_nonneg hR x,clip_nonneg hR y])

lemma clip_integral_bounds (μ : ProbabilityMeasure ℝ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ (∫ t,clip R t ∂μ) ∧ (∫ t,clip R t ∂μ) ≤ R := by
  constructor
  · exact integral_nonneg (clip_nonneg hR)
  · calc
      _ ≤ ∫ _ : ℝ,R ∂μ := integral_mono_ae (clip_integrable _ hR) (integrable_const _)
        (ae_of_all _ (fun _ => min_le_right _ _))
      _ = R := by simp

lemma fullMass_unit (u : L2T L) (hu : ‖u‖ = 1) :
    QuantumNLS.FullMass.Mmeas κ u =
      (QuantumNLS.FreeLimit.muKappa u hu κ : Measure ℝ) := by
  have hn : u ≠ 0 := by
    intro h
    rw [h,norm_zero] at hu
    exact zero_ne_one hu
  rw [QuantumNLS.FullMass.Mmeas_of_ne κ hn]
  have hdir : QuantumNLS.FullMass.unitDir u = u := by simp [QuantumNLS.FullMass.unitDir,hu]
  simp only [hu,one_pow,mul_one,ENNReal.ofReal_one,one_smul]
  congr 1
  exact QuantumNLS.FullMassLimit.muKappa_congr hdir _ _ κ

/-- Actual clipped empirical second moments converge in L¹, using the
already proved weak-in-probability limit and boundedness. -/
theorem actual_clip_L1 (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n => ∫ m, |(∫ t,clip R t ∂(empiricalProb L κ (n+1) m : Measure ℝ)) -
      (∫ t,clip R t ∂(QuantumNLS.FreeLimit.muKappa u hu κ : Measure ℝ))|
        ∂law hκ u hu (n+1)) atTop (nhds 0) := by
  let μ := QuantumNLS.FreeLimit.muKappa u hu κ
  let X := fun N (m : QuantumNLS.BetheLabels.MArr N) =>
    ∫ t,clip R t ∂(empiricalProb L κ N m : Measure ℝ)
  let c := ∫ t,clip R t ∂(μ : Measure ℝ)
  have hc : ContinuousAt (fun ρ : LevyProkhorov (ProbabilityMeasure ℝ) =>
      ∫ t,clip R t ∂((LevyProkhorov.toMeasure ρ : ProbabilityMeasure ℝ) : Measure ℝ))
      (LevyProkhorov.ofMeasure μ) :=
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction (clipBCF R hR)).comp
      LevyProkhorov.continuous_toMeasure_probabilityMeasure).continuousAt
  have hp := QuantumNLS.BornConvergence.TendstoInProbability.comp_continuousAt
    (QuantumNLS.FreeLimit.muKappa_spec u hu hκ) hc
  have hp' : QuantumNLS.BornConvergence.TendstoInProbability
      (fun n => law hκ u hu (n+1)) (fun n => X (n+1)) c := by
    intro ε hε
    exact (hp ε hε).comp (tendsto_add_atTop_nat 1)
  exact QuantumNLS.RootEnergyMomentProbability.bounded_probability_L1
    (fun n => law hκ u hu (n+1)) (fun n => X (n+1)) c R
    (fun _ => measurable_of_countable _) (fun n m => by
      have hx := clip_integral_bounds (empiricalProb L κ (n+1) m) hR
      have hc' := clip_integral_bounds μ hR
      rw [abs_sub_le_iff]
      constructor <;> linarith [hx.1,hx.2,hc'.1,hc'.2]) hp'

#print axioms actual_clip_L1
end QuantumNLS.RootEnergyMomentBounded

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentBounded." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentBounded." then
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
