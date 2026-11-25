import QuantumNLS.RootEnergyMomentAverage
import QuantumNLS.RootEnergyMomentTails

/-! R-484B3F6D, thm:root-energy-moment. One assembled statement on the
quantum-derived full-mass measure and the actual Born product spectral laws.
Only the printed positivity, H¹ membership, and unit-input qualifier occur. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.ProductEnergyPreparation QuantumNLS.ChargeEnergy
open QuantumNLS.RootEnergyMomentLaws QuantumNLS.RootEnergyMomentExpectation
open QuantumNLS.RootEnergyMomentBounded QuantumNLS.RootEnergyMomentAverage
open QuantumNLS.RootEnergyMomentTails QuantumNLS.BulkResponseActual
namespace QuantumNLS.RootEnergyMoment
variable {L κ : ℝ} [Fact (0 < L)]

lemma unit_scalar (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) :
    Integrable (fun t : ℝ => t^2) (QuantumNLS.FreeLimit.muKappa u hu κ : Measure ℝ) ∧
      (∫ t : ℝ,t^2 ∂(QuantumNLS.FreeLimit.muKappa u hu κ : Measure ℝ)) =
        energyH1 κ (u : AddCircle L → ℂ) := by
  have h := QuantumNLS.RootEnergyMomentScalar.scalar_energy_moment hκ u hH
  rwa [fullMass_unit u hu] at h

/-- The actual empirical second moment converges in L¹, by proved bounded
truncation convergence and the exact unbounded finite expectation. -/
lemma actual_random_L1 (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (hH : OneH1 u) :
    Tendsto (fun n => ∫ m,|sampleEnergy L κ (n+1) m -
      energyH1 κ (u : AddCircle L → ℂ)| ∂law hκ u hu (n+1)) atTop (nhds 0) := by
  let ν := QuantumNLS.FreeLimit.muKappa u hu κ
  let E := energyH1 κ (u : AddCircle L → ℂ)
  have hν := unit_scalar hκ u hu hH
  have hEX : Tendsto (fun n => ∫ m,sampleEnergy L κ (n+1) m ∂law hκ u hu (n+1))
      atTop (nhds E) := by
    have h := barycenter_moment_limit hκ u hu hH
    convert h using 1
    funext n
    rw [(actual_energy_expectation (Nat.succ_pos n) hκ u hu hH).2,
      (barycenter_second hκ u hu hH n).2]
  have hc : Tendsto (fun r : ℕ => ∫ t,clip r t ∂(ν : Measure ℝ)) atTop (nhds E) := by
    have h := clip_tendsto hν.1
    rwa [hν.2] at h
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r,hr⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp hc) (ε/4) (by positivity))
  have hr' : |(∫ t,clip r t ∂(ν : Measure ℝ)) - E| < ε/4 := by
    simpa only [Real.dist_eq] using hr r le_rfl
  let d := ∫ t,clip r t ∂(ν : Measure ℝ)
  let Y := fun n (m : QuantumNLS.BetheLabels.MArr (n+1)) =>
    ∫ t,clip r t ∂(empiricalProb L κ (n+1) m : Measure ℝ)
  have hiY (n : ℕ) : Integrable (Y n) (law hκ u hu (n+1)) := by
    apply (integrable_const (r : ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
    apply ae_of_all
    intro m
    rw [Real.norm_eq_abs,abs_of_nonneg (clip_integral_bounds _ (Nat.cast_nonneg r)).1]
    exact (clip_integral_bounds _ (Nat.cast_nonneg r)).2
  have hlo (n : ℕ) (m : QuantumNLS.BetheLabels.MArr (n+1)) :
      Y n m ≤ sampleEnergy L κ (n+1) m := by
    have he : (empiricalProb L κ (n+1) m : Measure ℝ) =
        EmpiricalRapidity.empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m := by
      exact empiricalProb_succ n m
    change (∫ t,clip r t ∂(empiricalProb L κ (n+1) m : Measure ℝ)) ≤ _
    rw [he]
    have := EmpiricalRapidity.isProbabilityMeasure_empiricalMeasure L
      (κ/((n+1 : ℕ) : ℝ)) (Nat.succ_pos n) m
    calc
      _ ≤ ∫ t : ℝ,t^2 ∂EmpiricalRapidity.empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m :=
        integral_mono_ae (clip_integrable _ (Nat.cast_nonneg r))
          (sample_second_moment (Nat.succ_pos n) m).1 (ae_of_all _ (fun _ => min_le_left _ _))
      _ = _ := (sample_second_moment (Nat.succ_pos n) m).2
  have hbound (n : ℕ) :
      (∫ m,|sampleEnergy L κ (n+1) m-E| ∂law hκ u hu (n+1)) ≤
      (∫ m,sampleEnergy L κ (n+1) m ∂law hκ u hu (n+1)) - d +
        2*(∫ m,|Y n m-d| ∂law hκ u hu (n+1)) + |d-E| :=
    QuantumNLS.RootEnergyMomentProbability.lower_truncation_bound
      (law hκ u hu (n+1)) (sampleEnergy L κ (n+1)) (Y n) E d
      (actual_energy_expectation (Nat.succ_pos n) hκ u hu hH).1 (hiY n) (hlo n)
  have hlim : Tendsto (fun n =>
      (∫ m,sampleEnergy L κ (n+1) m ∂law hκ u hu (n+1)) - d +
        2*(∫ m,|Y n m-d| ∂law hκ u hu (n+1)) + |d-E|) atTop
      (nhds (E-d+|d-E|)) := by
    have h := ((hEX.sub_const d).add
      ((actual_clip_L1 hκ u hu (Nat.cast_nonneg r)).const_mul 2)).add_const |d-E|
    simpa only [mul_zero,add_zero] using h
  have hlt : E-d+|d-E| < ε := by
    have hh : E-d ≤ |d-E| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  filter_upwards [hlim.eventually (gt_mem_nhds hlt)] with n hn
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
  exact (hbound n).trans_lt hn

/-- R-484B3F6D in full. n+1 enumerates every positive particle number.
The second clause is uniform integrability of the actual barycenters; the
third is the actual random second moment converging in L¹. -/
theorem root_energy_moment (hκ : 0 < κ) (u : L2T L) (hH : OneH1 u) :
    Integrable (fun t : ℝ => t^2) (QuantumNLS.FullMass.Mmeas κ u) ∧
    (∫ t : ℝ,t^2 ∂QuantumNLS.FullMass.Mmeas κ u) = energyH1 κ (u : AddCircle L → ℂ) ∧
    ∀ hu : ‖u‖ = 1,
      (∀ n, Integrable (fun t : ℝ => t^2) (barycenter hκ u hu n) ∧
        (∫ t : ℝ,t^2 ∂barycenter hκ u hu n) =
          energyH1 κ (u : AddCircle L → ℂ) - κ*quartic (u : AddCircle L → ℂ)/((n+1 : ℕ) : ℝ)) ∧
      (∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 < R ∧ ∀ n,squareTail (barycenter hκ u hu n) R < ε) ∧
      (∀ n,Integrable (fun m : QuantumNLS.BetheLabels.MArr (n+1) =>
        ∫ t : ℝ,t^2 ∂EmpiricalRapidity.empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m)
          (law hκ u hu (n+1))) ∧
      Tendsto (fun n => ∫ m,|(∫ t : ℝ,t^2 ∂EmpiricalRapidity.empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m) -
        energyH1 κ (u : AddCircle L → ℂ)| ∂law hκ u hu (n+1)) atTop (nhds 0) := by
  have hs := QuantumNLS.RootEnergyMomentScalar.scalar_energy_moment hκ u hH
  refine ⟨hs.1,hs.2,fun hu => ?_⟩
  have hν := unit_scalar hκ u hu hH
  have hm : Tendsto (fun n => ∫ t : ℝ,t^2 ∂barycenter hκ u hu n) atTop
      (nhds (∫ t : ℝ,t^2 ∂(QuantumNLS.FreeLimit.muKappa u hu κ : Measure ℝ))) := by
    rw [hν.2]
    exact barycenter_moment_limit hκ u hu hH
  have hui := square_uniform_integrability (barycenter hκ u hu)
    (QuantumNLS.FreeLimit.muKappa u hu κ : Measure ℝ)
    (fun n => (barycenter_second hκ u hu hH n).1) hν.1 hm
    (fun R hR => barycenter_clip_limit hκ u hu hR)
  have he (n : ℕ) (m : QuantumNLS.BetheLabels.MArr (n+1)) :
      (∫ t : ℝ,t^2 ∂EmpiricalRapidity.empiricalMeasure L (κ/((n+1 : ℕ) : ℝ)) m) =
        sampleEnergy L κ (n+1) m := (sample_second_moment (Nat.succ_pos n) m).2
  refine ⟨barycenter_second hκ u hu hH,hui,?_,?_⟩
  · intro n
    simpa only [he] using (actual_energy_expectation (Nat.succ_pos n) hκ u hu hH).1
  · simpa only [he] using actual_random_L1 hκ u hu hH

#print axioms root_energy_moment
end QuantumNLS.RootEnergyMoment

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMoment." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMoment." then
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
