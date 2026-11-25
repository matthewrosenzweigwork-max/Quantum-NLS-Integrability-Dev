import QuantumNLS.AuditWeightedTightR50a
import QuantumNLS.Reg013OAnalysis
import QuantumNLS.BetheSpectralCharges

/-! Conserved values from weak probability convergence and root moment
tightness; bounded continuous truncations are the only quantum tests. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators
namespace QuantumNLS.AuditWeightedValuesR50a
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.EmpiricalRapidity QuantumNLS.BulkResponseActual
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.AuditWeightedProbabilityR49a QuantumNLS.AuditWeightedDetR49a
open QuantumNLS.Reg013OAnalysis
variable {L κ : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

def average (g : ℝ → ℝ) (N : ℕ) (m : MArr N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j, g (arrRoots L (κ/N) m j)

omit [Fact (0 < L)] in
theorem average_integral {N : ℕ} (hN : 0 < N) (m : MArr N) (g : ℝ → ℝ) :
    average (L := L) (κ := κ) g N m = ∫ t, g t ∂(empiricalProb L κ N m : Measure ℝ) := by
  have he : empiricalProb L κ N m =
      (⟨empiricalMeasure L (κ/N) m,isProbabilityMeasure_empiricalMeasure L (κ/N) hN m⟩ : ProbabilityMeasure ℝ) := by
    unfold empiricalProb
    exact dite_eq_left hN
  rw [he]
  change _ = ∫ t, g t ∂empiricalMeasure L (κ/N) m
  unfold empiricalMeasure
  rw [integral_smul_measure,integral_finsetSum_measure]
  · simp only [integral_dirac,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,average]
  · intro j _
    exact integrable_dirac (by simp)

/-- Bounded continuous test convergence under the original full Born laws. -/
theorem bounded_test_probability (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖=1)
    {μ : ProbabilityMeasure ℝ} (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ)
    (g : BoundedContinuousFunction ℝ ℝ) : QuantumNLS.BornConvergence.TendstoInProbability
      (fun N => bornMeasure (physBasis L hκ N) u hu)
      (fun N m => average (L := L) (κ := κ) g N m) (∫ t, g t ∂(μ : Measure ℝ)) := by
  have hc : Continuous (fun ν : LevyProkhorov (ProbabilityMeasure ℝ) =>
      ∫ t, g t ∂((LevyProkhorov.toMeasure ν : ProbabilityMeasure ℝ) : Measure ℝ)) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).comp
      LevyProkhorov.continuous_toMeasure_probabilityMeasure
  have ht := QuantumNLS.BornConvergence.TendstoInProbability.comp_continuousAt hμ hc.continuousAt
  intro ε hε
  apply (ht ε hε).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq]
  rw [average_integral (by omega)]

omit [Fact (0 < L)] in
/-- A higher weighted moment controls the truncation error by M/R. -/
theorem power_truncation_bound (r : ℕ) {R M : ℝ} (hR : 1 ≤ R)
    (N : ℕ) (m : MArr N)
    (hm : rootMoment (L := L) (κ := κ) (2*((r+1 : ℕ) : ℝ)) N m ≤ M) :
    |average (L := L) (κ := κ) (fun t => t^r) N m -
      average (L := L) (κ := κ) (truncBCF (fun t => t^r) (continuous_pow r) R) N m| ≤ M/R := by
  have hR0 : 0 < R := by linarith
  have hpt (t : ℝ) : |t^r-t^r*cut R t| ≤ (1+t^2)^(r+1)/R := by
    by_cases ht : |t| ≤ R
    · rw [cut_eq_one ht]; simp; positivity
    · have hRt : R < |t| := lt_of_not_ge ht
      have hab : 1 ≤ |t| := hR.trans hRt.le
      have h1 : |t| ≤ 1+t^2 := by nlinarith [sq_abs t,sq_nonneg (|t|-1)]
      have h2 : |t|^r*R ≤ (1+t^2)^r*(1+t^2) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 r) (hRt.le.trans h1)
          hR0.le (by positivity)
      rw [show t^r-t^r*cut R t=t^r*(1-cut R t) by ring,abs_mul,abs_pow,abs_of_nonneg (show 0 ≤ 1-cut R t by linarith [cut_le_one R t])]
      apply (mul_le_of_le_one_right (pow_nonneg (abs_nonneg _) r)
        (by linarith [cut_nonneg R t])).trans
      rw [le_div_iff₀ hR0,pow_succ]
      exact h2
  have hle : |average (L := L) (κ := κ) (fun t => t^r) N m -
      average (L := L) (κ := κ) (truncBCF (fun t => t^r) (continuous_pow r) R) N m| ≤
      rootMoment (L := L) (κ := κ) (2*((r+1 : ℕ) : ℝ)) N m/R := by
    unfold average rootMoment rootWeight
    simp only [truncBCF_apply,show 2*((r+1 : ℕ) : ℝ)/2=((r+1 : ℕ) : ℝ) by ring,Real.rpow_natCast]
    rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹),← Finset.sum_sub_distrib]
    calc
      _ ≤ (N : ℝ)⁻¹ * ∑ j, |(arrRoots L (κ/N) m j)^r-
          (arrRoots L (κ/N) m j)^r*cut R (arrRoots L (κ/N) m j)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (N : ℝ)⁻¹ * ∑ j, (1+(arrRoots L (κ/N) m j)^2)^(r+1)/R :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hpt _) (by positivity)
      _ = _ := by rw [← Finset.sum_div]; ring
  exact hle.trans (div_le_div_of_nonneg_right hm hR0.le)

/-- Every fixed polynomial root moment converges to its identified scalar
moment, in probability under the specified N-dependent Born laws. -/
theorem power_probability (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) (r : ℕ) :
    QuantumNLS.BornConvergence.TendstoInProbability
      (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu)
      (fun N m => average (L := L) (κ := κ) (fun t => t^r) N m)
      (charge L κ f (r+1)).re := by
  obtain ⟨μ,hμ⟩ := QuantumNLS.RootMeasureExistence.exists_limiting_measure hκ (smoothL2 hf) hu
  have habs := QuantumNLS.ValuesTailIdentify.integrable_moment_of_limit hκ hf hu hμ r
  have hi : Integrable (fun t : ℝ => t^r) (μ : Measure ℝ) := by
    apply habs.mono' (by fun_prop)
    exact ae_of_all _ (fun t => by simp [Real.norm_eq_abs])
  have hid : (∫ t : ℝ, t^r ∂(μ : Measure ℝ)) = (charge L κ f (r+1)).re := by
    have h := congrArg Complex.re ((QuantumNLS.R275Unconditional.R_275B7656 κ hκ hf).2 r).2
    rw [QuantumNLS.ValuesTailIdentify.limit_eq_Mmeas hκ hf hu hμ]
    exact h
  rw [← hid]
  intro ε hε
  apply (ENNReal.tendsto_toReal_zero_iff (fun N => measure_ne_top _ _)).mp
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨M,hM⟩ := QuantumNLS.AuditWeightedTightR50a.root_moment_tight hκ hf hu
    (2*((r+1 : ℕ) : ℝ)) (δ/2) (half_pos hδ)
  have hfar := (far_tendsto (μ : Measure ℝ) (fun t => t^r) (continuous_pow r) hi).abs
  simp only [abs_zero] at hfar
  have hsmall := hfar.eventually (gt_mem_nhds (show (0 : ℝ)<ε/3 by positivity))
  obtain ⟨R,hRs,hRbig⟩ := (hsmall.and (eventually_ge_atTop ⌈max 1 (3*|M|/ε+1)⌉₊)).exists
  have hR : 1 ≤ (R : ℝ) := (le_max_left _ _).trans
    ((Nat.le_ceil _).trans (by exact_mod_cast hRbig))
  have hMR : M/(R : ℝ) < ε/3 := by
    have hh : 3*|M|/ε+1 ≤ (R : ℝ) := (le_max_right _ _).trans
      ((Nat.le_ceil _).trans (by exact_mod_cast hRbig))
    rw [div_lt_iff₀ (by linarith : 0 < (R : ℝ))]
    have hhh := (div_le_iff₀ hε).mp (show 3*|M|/ε ≤ (R : ℝ)-1 by linarith)
    nlinarith [le_abs_self M]
  let g := truncBCF (fun t : ℝ => t^r) (continuous_pow r) R
  have hgi : Integrable (fun t : ℝ => t^r*cut R t) (μ : Measure ℝ) :=
    integrable_mul_cut (continuous_pow r) hi R
  have hscalar : |(∫ t, g t ∂(μ : Measure ℝ))-(∫ t : ℝ, t^r ∂(μ : Measure ℝ))| < ε/3 := by
    have he : (∫ t : ℝ, t^r*(1-cut R t) ∂(μ : Measure ℝ)) =
        (∫ t : ℝ, t^r ∂(μ : Measure ℝ))-(∫ t, g t ∂(μ : Measure ℝ)) := by
      change _ = _-(∫ t : ℝ, t^r*cut R t ∂(μ : Measure ℝ))
      rw [← integral_sub hi hgi]
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by ring)
    rw [he,abs_sub_comm] at hRs
    exact hRs
  have htest := bounded_test_probability hκ (smoothL2 hf) hu hμ g (ε/3) (by positivity)
  have htestReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htest
  simp only [ENNReal.toReal_zero] at htestReal
  filter_upwards [hM,htestReal.eventually (gt_mem_nhds (half_pos hδ))] with N hMN htN
  let P := bornMeasure (physBasis L hκ N) (smoothL2 hf) hu
  have hsub : {m | ε < dist (average (L := L) (κ := κ) (fun t => t^r) N m)
        (∫ t : ℝ, t^r ∂(μ : Measure ℝ))} ⊆
      {m | M < rootMoment (L := L) (κ := κ) (2*((r+1 : ℕ) : ℝ)) N m} ∪
      {m | ε/3 < dist (average (L := L) (κ := κ) g N m) (∫ t, g t ∂(μ : Measure ℝ))} := by
    intro m hm
    by_contra hn
    simp only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt] at hn
    have hp := power_truncation_bound r hR N m hn.1
    have htri := dist_triangle (average (L := L) (κ := κ) (fun t => t^r) N m)
      (average (L := L) (κ := κ) g N m) (∫ t : ℝ, t^r ∂(μ : Measure ℝ))
    have htri2 := dist_triangle (average (L := L) (κ := κ) g N m)
      (∫ t, g t ∂(μ : Measure ℝ)) (∫ t : ℝ, t^r ∂(μ : Measure ℝ))
    simp only [Set.mem_ofPred_eq,Real.dist_eq] at hn htri htri2 hm
    change |average (L := L) (κ := κ) (fun t => t^r) N m-average (L := L) (κ := κ) g N m| ≤ M/(R : ℝ) at hp
    linarith
  have hbound := (measureReal_mono (μ := P) hsub).trans (measureReal_union_le _ _)
  have hh : P.real {m | ε < dist (average (L := L) (κ := κ) (fun t => t^r) N m)
      (∫ t : ℝ, t^r ∂(μ : Measure ℝ))} < δ := by
    change P.real {m | M < rootMoment (L := L) (κ := κ) (2*((r+1 : ℕ) : ℝ)) N m} ≤ δ/2 at hMN
    change P.real {m | ε/3 < dist (average (L := L) (κ := κ) g N m) (∫ t, g t ∂(μ : Measure ℝ))} < δ/2 at htN
    linarith
  simpa only [P,measureReal_def,Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg] using hh

/-- The charge roots and empirical roots differ only by enumeration. -/
theorem rapidity_eq_arrRoots_rev (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (m : MArr N) (j : Fin N) :
    QuantumNLS.BetheSpectralCharges.rapidity L N (κ/N) m j =
      arrRoots L (κ/N) m (Fin.rev j) := by
  have hc : 0 < κ/(N : ℝ) := div_pos hκ (by exact_mod_cast hN)
  have he : correctedInt (labelsEquivArr.symm m) = (correctedEquivArr.symm m).val :=
    congrArg Subtype.val (labelsEquivCorrected.apply_symm_apply (correctedEquivArr.symm m))
  change QuantumNLS.BetheSmooth.sourceRoots L (srcOf (correctedEquivArr.symm m).val) (κ/N) j = _
  rw [← he,sourceRoots_eq_roots_rev (Fact.out : 0 < L) hc]
  rfl

theorem spectral_average_eq (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (r : ℕ) (m : MArr N) :
    QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ) =
      average (L := L) (κ := κ) (fun t => t^r) N m := by
  unfold QuantumNLS.BetheSpectralCharges.eigenvalue average
  simp_rw [rapidity_eq_arrRoots_rev hκ hN]
  have hs := Equiv.sum_comp Fin.revPerm (fun j => arrRoots L (κ/N) m j^r)
  change (∑ j, arrRoots L (κ/N) m (Fin.rev j)^r) = ∑ j, arrRoots L (κ/N) m j^r at hs
  rw [hs]
  ring

/-- The actual fixed intensive spectral charge has the scalar Riccati value. -/
theorem charge_probability (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) (r : ℕ) :
    QuantumNLS.BornConvergence.TendstoInProbability
      (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu)
      (fun N m => QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ))
      (charge L κ f (r+1)).re := by
  intro ε hε
  apply (power_probability hκ hf hu r ε hε).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq]
  rw [spectral_average_eq hκ (by omega)]

end QuantumNLS.AuditWeightedValuesR50a

#print axioms QuantumNLS.AuditWeightedValuesR50a.power_probability
#print axioms QuantumNLS.AuditWeightedValuesR50a.spectral_average_eq
#print axioms QuantumNLS.AuditWeightedValuesR50a.charge_probability

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedValuesR50a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedValuesR50a." then
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
  Lean.logInfo m!"Round50 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
