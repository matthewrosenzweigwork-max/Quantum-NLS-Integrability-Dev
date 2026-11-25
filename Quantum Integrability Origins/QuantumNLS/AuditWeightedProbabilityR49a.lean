import QuantumNLS.AuditWeightedDetR49a
import QuantumNLS.AuditWeightedActionsR49a
import QuantumNLS.RootOccupationLimit

/-! R-115CAA16: the probability bridge. This is INTERMEDIATE: tightness
of the stronger actual root moment is an explicit analytical hypothesis.
It must be discharged from the moving-cutoff tail argument before the
named final theorem can be supplied. All probabilities are probabilities
of deviation under the specified N-dependent full Born laws. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.AuditWeightedProbabilityR49a
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.EmpiricalRapidity QuantumNLS.BulkResponseActual
open QuantumNLS.AuditWeightedSeriesR49a QuantumNLS.AuditWeightedDetR49a
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
variable {L κ : ℝ} [Fact (0 < L)]

def rootMoment (p : ℝ) (N : ℕ) (m : MArr N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j, rootWeight p (arrRoots L (κ/N) m j)

def error (hκ : 0 < κ) (u : L2T L) (p : ℝ) (N : ℕ) (m : MArr N) : ℝ :=
  ∑' n : ℤ, weight p n * |(m.1 n : ℝ)/N-(QuantumNLS.RootIndexedMasses.masses hκ u).1 n|

/-- Boundedness in probability of a specified actual empirical moment.
This is an intermediate hypothesis, not a theorem about the Born laws. -/
def RootMomentTight (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖=1) (p : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, ∀ᶠ N in atTop,
    (bornMeasure (physBasis L hκ N) u hu).real {m | M < rootMoment (L := L) (κ := κ) p N m} ≤ δ

/-- The exact printed real series is summable for every sample, including
N=0, so `error` never uses the default real value of a divergent series. -/
theorem summable_error {f : ℝ → ℂ} (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (p : ℝ) (hp : 0 ≤ p) (N : ℕ) (m : MArr N) :
    Summable (fun n : ℤ => weight p n *
      |(m.1 n : ℝ)/N-(QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hf)).1 n|) := by
  have hs : Summable (fun n : ℤ => weight p n*((m.1 n : ℝ)/N)) := by
    apply summable_of_ne_finset_zero (s := m.1.support)
    intro n hn
    simp [Finsupp.notMem_support_iff.mp hn]
  have ht := QuantumNLS.AuditWeightedActionsR49a.smooth_actions_summable hκ hf p hp
  apply (hs.sub ht).abs.congr
  intro n
  rw [← mul_sub, abs_mul, abs_of_pos (weight_pos p n)]

/-- The zero weight case of the printed probability conclusion is already
unconditional and holds for every unit L² datum. -/
theorem weighted_zero_prob (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖=1)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => bornMeasure (physBasis L hκ N) u hu
      {m | ε < error hκ u 0 N m}) atTop (𝓝 0) := by
  simpa only [error, weight, zero_div, Real.rpow_zero, one_mul,
    QuantumNLS.RootOccupationLimit.occDist, QuantumNLS.RootOccupationLimit.occVec] using
    QuantumNLS.RootOccupationLimit.occDist_prob hκ u hu hε

theorem weighted_probability_of_root_moment_tight (hκ : 0 < κ)
    (u : L2T L) (hu : ‖u‖=1) (p : ℝ) (hp : 0 ≤ p)
    (htight : RootMomentTight hκ u hu (p+2)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N => bornMeasure (physBasis L hκ N) u hu
      {m | ε < error hκ u p N m}) atTop (𝓝 0) := by
  obtain ⟨μ,hμ⟩ := QuantumNLS.RootMeasureExistence.exists_limiting_measure hκ u hu
  have hμe : (μ : Measure ℝ)=QuantumNLS.PhysicalQuantumMeasure.measure hκ u :=
    (QuantumNLS.Prop026Bound.physical_eq_limit hκ u hu hμ).symm
  apply (ENNReal.tendsto_toReal_zero_iff (fun N => measure_ne_top _ _)).mp
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨M,hM⟩ := htight (δ/2) (by positivity)
  obtain ⟨U,hU,N0,huniform⟩ := deterministic_weighted_uniform hκ u hu hμe p hp M hε
  obtain ⟨r,hr,hrU⟩ := QuantumNLS.RootOccupationLimit.exists_lp_ball μ U hU
  have hweak := (QuantumNLS.BornConvergence.tendstoInProbabilityWeak_iff _ _ _).1 hμ
    (r/2) (half_pos hr)
  have hweakReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hweak
  simp only [ENNReal.toReal_zero] at hweakReal
  filter_upwards [hM, hweakReal.eventually (gt_mem_nhds (half_pos hδ)),
    eventually_ge_atTop (max N0 1)] with N hMN hweakN hNN
  have hN : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hNN)
  let P := bornMeasure (physBasis L hκ N) u hu
  have hsub : {m | ε < error hκ u p N m} ⊆
      {m | M < rootMoment (L := L) (κ := κ) (p+2) N m} ∪
      {m | r/2 < levyProkhorovDist (empiricalProb L κ N m).toMeasure μ.toMeasure} := by
    intro m hm
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hn
    obtain ⟨B,hq,hcount⟩ := QuantumNLS.RootOccupationDet.onShell_arr
      (Fact.out : 0 < L) hκ hN m
    have hB : QuantumNLS.LabelJointWeak.rootP B hN=empiricalProb L κ N m := by
      have h := QuantumNLS.LabelWeakJointLimit.rootP_eq_empirical B hN m hq
      have he : empiricalProb L κ N m=QuantumNLS.LabelWeakJointLimit.empiricalP L κ hN m := by
        unfold empiricalProb QuantumNLS.LabelWeakJointLimit.empiricalP
        exact dite_eq_left hN
      rw [he]
      exact Subtype.ext h
    have hBU : QuantumNLS.LabelJointWeak.rootP B hN ∈ U := by
      rw [hB]
      exact hrU _ (hn.2.trans_lt (half_lt_self hr))
    have hroot : ((N : ℝ)⁻¹ * ∑ j, rootWeight (p+2) (B.q j)) ≤ M := by
      simpa only [rootMoment, hq] using hn.1
    have he := huniform N hN ((le_max_left _ _).trans hNN) B hBU hroot
    have heq : (∑' n, weight p n * |QuantumNLS.RootOccupationDet.occ B n-
        (QuantumNLS.RootIndexedMasses.masses hκ u).1 n|)=error hκ u p N m := by
      unfold error QuantumNLS.RootOccupationDet.occ
      apply tsum_congr
      intro n
      rw [← hcount n]
      congr 3
      ring
    rw [heq] at he
    exact (not_lt_of_ge he.le) hm
  have hle : P.real {m | ε < error hκ u p N m} < δ := by
    have : IsProbabilityMeasure P := by dsimp [P]; infer_instance
    have h1 := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le _ _)
    change P.real {m | M < rootMoment (L := L) (κ := κ) (p+2) N m} ≤ δ/2 at hMN
    have h2 : P.real {m | r/2 < levyProkhorovDist
        (empiricalProb L κ N m).toMeasure μ.toMeasure} < δ/2 := hweakN
    linarith
  simpa only [P, measureReal_def, Real.dist_eq, sub_zero,
    abs_of_nonneg ENNReal.toReal_nonneg] using hle

end QuantumNLS.AuditWeightedProbabilityR49a

#print axioms QuantumNLS.AuditWeightedProbabilityR49a.rootMoment

#print axioms QuantumNLS.AuditWeightedProbabilityR49a.error

#print axioms QuantumNLS.AuditWeightedProbabilityR49a.RootMomentTight

#print axioms QuantumNLS.AuditWeightedProbabilityR49a.summable_error

#print axioms QuantumNLS.AuditWeightedProbabilityR49a.weighted_zero_prob

#print axioms QuantumNLS.AuditWeightedProbabilityR49a.weighted_probability_of_root_moment_tight

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedProbabilityR49a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedProbabilityR49a." then
      pending := pending.push n
      roots := roots + 1
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round49 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
