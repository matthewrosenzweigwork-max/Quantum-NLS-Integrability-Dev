import QuantumNLS.EnergyFormPassFinal
import QuantumNLS.EnergyTraceConvergence

/-! R-568BCDF8: bounded Fourier tests at time zero, scalar energy recovery,
and the passage from conserved energy and contact convergence to all fixed
kinetic trace limits. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
open Filter Topology
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.AllOrderEnergyLimitsR55a
open EnergyPreparationDef Energy PhysicalEnergyTrace TraceClass
variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- Each finite sum of the nonnegative Fourier-mode kinetic tests is continuous
in operator norm. Their increasing supremum is the literal physical trace. -/
theorem energyTrace_lowerSemicontinuous :
    LowerSemicontinuous (fun ρ : Xk L k →L[ℂ] Xk L k => energyTrace ρ) := by
  simp only [energyTrace, physTrace_eq_modes]
  intro ρ
  apply lowerSemicontinuousAt_tsum
  intro w
  let b := (eK L k).symm (EnergyRealization.ev w)
  have hc : Continuous (fun ρ : Xk L k →L[ℂ] Xk L k => ρ b) :=
    (ContinuousLinearMap.apply ℂ (Xk L k) b).continuous
  exact (ENNReal.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.inner hc) |>.const_mul (kinWeight L k w))).continuousAt.lowerSemicontinuousAt

/-- Trace-norm convergence implies operator-norm convergence even if individual
trace differences are represented in the extended nonnegative norm. -/
theorem tendsto_of_traceNorm {ι : Type*} {l : Filter ι}
    (ρ : ι → Xk L k →L[ℂ] Xk L k) (σ : Xk L k →L[ℂ] Xk L k)
    (h : Tendsto (fun n => traceNorm (ρ n - σ)) l (𝓝 0)) : Tendsto ρ l (𝓝 σ) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [(tendsto_order.1 h).2 (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)] with n hn
  rw [dist_eq_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp ((norm_le_traceNorm _).trans_lt hn)

/-- The lower bound of the initial kinetic term, in the eventual form of the
liminf inequality. For trace-one states at rank one, subtracting one gives
exactly the expectation of D². -/
theorem initial_kinetic_lower {ρ : ℕ → Xk L k →L[ℂ] Xk L k} {σ : Xk L k →L[ℂ] Xk L k}
    (h : Tendsto (fun n => traceNorm (ρ n - σ)) atTop (𝓝 0))
    (hρ : ∀ n, energyTrace (ρ n) ≠ ⊤) {a : ℝ} (ha : 0 ≤ a)
    (hσ : energyTrace σ = ENNReal.ofReal (1 + a)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, a - ε < (energyTrace (ρ n)).toReal - 1 := by
  have hl := energyTrace_lowerSemicontinuous (L := L) (k := k) σ
    (ENNReal.ofReal (1 + a - ε)) (by
      change ENNReal.ofReal (1 + a - ε) < energyTrace σ
      rw [hσ]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith))
  filter_upwards [(tendsto_of_traceNorm ρ σ h).eventually hl] with n hn
  have ht := ENNReal.toReal_strict_mono (hρ n) hn
  rw [ENNReal.toReal_ofReal'] at ht
  have hx : 1 + a - ε ≤ max (1 + a - ε) 0 := le_max_left _ _
  linarith

/-- The initial contact convergence and the kinetic liminf force equality in
energy preparation. The upper premise is DEF-031's limsup convention. -/
theorem energy_limit (E kinetic contact weight : ℕ → ℝ) (a b : ℝ)
    (hIdentity : ∀ᶠ n in atTop, E n = kinetic n + weight n * contact n)
    (hKinetic : ∀ ε > 0, ∀ᶠ n in atTop, a - ε < kinetic n)
    (hContact : Tendsto contact atTop (𝓝 b)) (hWeight : Tendsto weight atTop (𝓝 1))
    (hUpper : ∀ ε > 0, ∀ᶠ n in atTop, E n ≤ a + b + ε) :
    Tendsto E atTop (𝓝 (a + b)) := by
  have hwc : Tendsto (fun n => weight n * contact n) atTop (𝓝 b) := by
    simpa only [one_mul] using hWeight.mul hContact
  apply tendsto_order.2
  constructor
  · intro c hc
    let ε := (a + b - c) / 3
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [hIdentity, hKinetic ε hε,
      (tendsto_order.1 hwc).1 (b - ε) (by linarith)] with n hn hk hb
    dsimp [ε] at hk hb
    linarith
  · intro c hc
    let ε := (c - (a + b)) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [hUpper ε hε] with n hn
    dsimp [ε] at hn
    linarith

/-- The finite-N coefficient may be absorbed before uniform subtraction. The
uniform estimate uses only a bound on the limiting contact expectation. -/
theorem weighted_contact_limit {T : Type*} (contact : ℕ → T → ℝ) (target : T → ℝ)
    (weight : ℕ → ℝ) (hw : Tendsto weight atTop (𝓝 1))
    (hc : TendstoUniformly contact target atTop)
    (B : ℝ) (hB : ∀ t, |target t| ≤ B) (hB₀ : 0 ≤ B) :
    TendstoUniformly (fun n t => weight n * contact n t) target atTop := by
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  obtain hweight := Metric.tendsto_nhds.1 hw (min 1 (ε / (2 * (B + 1))))
    (lt_min zero_lt_one (div_pos hε (by positivity)))
  filter_upwards [hweight, Metric.tendstoUniformly_iff.1 hc (ε / 4) (by positivity)] with n hn hcn
  intro t
  rw [dist_eq_norm, Real.norm_eq_abs] at hn ⊢
  have hnear : |weight n - 1| < 1 := hn.trans_le (min_le_left _ _)
  have hweight' : |weight n| ≤ 2 := by
    have h := abs_add_le (weight n - 1) 1
    rw [sub_add_cancel, abs_one] at h
    linarith
  have hsmall : |weight n - 1| * |target t| ≤ ε / 2 := by
    apply le_trans (mul_le_mul_of_nonneg_left ((hB t).trans (by linarith : B ≤ B + 1)) (abs_nonneg _))
    have hh := hn.trans_le (min_le_right _ _)
    exact le_of_lt (by
      calc
        |weight n - 1| * (B + 1) < (ε / (2 * (B + 1))) * (B + 1) :=
          mul_lt_mul_of_pos_right hh (by linarith)
        _ = ε / 2 := by field_simp)
  have ht := hcn t
  rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm (target t)] at ht
  rw [abs_sub_comm (target t)]
  calc
    |weight n * contact n t - target t| =
        |weight n * (contact n t - target t) + (weight n - 1) * target t| := by ring_nf
    _ ≤ |weight n| * |contact n t - target t| + |weight n - 1| * |target t| := by
        simpa only [abs_mul] using abs_add_le (weight n * (contact n t - target t)) ((weight n - 1) * target t)
    _ < ε := by
      have hp := mul_le_mul_of_nonneg_right hweight' (abs_nonneg (contact n t - target t))
      linarith

/-- Subtraction of the convergent contact term from the conserved energy gives
uniform convergence of the rank-one kinetic expectations. -/
theorem kinetic_limit {T : Type*} (E : ℕ → ℝ) (kinetic contact : ℕ → T → ℝ)
    (a b : T → ℝ) (c : ℝ)
    (hE : Tendsto E atTop (𝓝 c))
    (hIdentity : ∀ᶠ n in atTop, ∀ t, E n = kinetic n t + contact n t)
    (hConservation : ∀ t, c = a t + b t)
    (hContact : TendstoUniformly contact b atTop) : TendstoUniformly kinetic a atTop := by
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  filter_upwards [hIdentity, Metric.tendsto_nhds.1 hE (ε / 2) (by positivity),
    Metric.tendstoUniformly_iff.1 hContact (ε / 2) (by positivity)] with n hn he hb
  intro t
  have hc := hb t
  rw [dist_eq_norm, Real.norm_eq_abs] at he hc ⊢
  rw [abs_sub_comm (a t)]
  rw [abs_sub_comm (b t)] at hc
  rw [show kinetic n t - a t = (E n - c) + -(contact n t - b t) by
    rw [hn t, hConservation t]; ring]
  exact (abs_add_le _ _).trans_lt (by rw [abs_neg]; linarith)

end QuantumNLS.AllOrderEnergyLimitsR55a

set_option maxHeartbeats 15000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := env.constants.toList.filterMap fun (n, _) =>
    if n.toString.startsWith "QuantumNLS.AllOrderEnergyLimitsR55a." then some n else none
  let roots := pending.length
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := ci.type.getUsedConstants.toList ++ pending
        if let some v := ci.value? (allowOpaque := true) then
          pending := v.getUsedConstants.toList ++ pending
      else throwError "Missing dependency: {n}"
  Lean.logInfo m!"R55a audit PASS: {roots} namespace constants; {seen.size} transitive constants."
