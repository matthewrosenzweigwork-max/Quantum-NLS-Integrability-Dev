import QuantumNLS.Prop017Quantum
import QuantumNLS.ValuesTailIdentify

/-! R-115CAA16: discharge the old scalar-law premises in the actual
quantum tail estimate. The limiting measure is produced, its all-order
moments are proved, and the actual full Born law is used throughout. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace QuantumNLS.AuditWeightedTailR49a
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.PhysicalTensor QuantumNLS.BetheLabels
open QuantumNLS.EmpiricalRapidity QuantumNLS.BulkResponseActual
open QuantumNLS.RootEvent QuantumNLS.Prop017Quantum
variable {L κ : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

/-- The rational-filter tail bound for the actual product spectral law,
with every scalar moment hypothesis discharged for a smooth unit profile. -/
theorem smooth_born_tail (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) (a : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (N : ℕ) (_hN : 0 < N) (R : ℝ),
      eta0 L κ ≤ R →
      (∫ m, tailFraction (qAct L κ N) R m
        ∂bornMeasure (physBasis L hκ N) (smoothL2 hf) hu) ≤
        C / R^(2*a) + D/((N : ℝ)*R) := by
  obtain ⟨μ, hμ⟩ := QuantumNLS.RootMeasureExistence.exists_limiting_measure hκ (smoothL2 hf) hu
  have hmom (p : ℕ) : Integrable (fun t : ℝ => t^(2*p)) (μ : Measure ℝ) := by
    apply (QuantumNLS.ValuesTailIdentify.integrable_moment_of_limit hκ hf hu hμ (2*p)).mono'
      (by fun_prop)
    exact ae_of_all _ (fun t => by simp [Real.norm_eq_abs])
  refine ⟨|Ctail (μ : Measure ℝ) a|, |Dtail κ a|, abs_nonneg _, abs_nonneg _, ?_⟩
  intro N hN R hR
  have ht := tail_actual hκ (smoothL2 hf) hu hμ hmom hN a R hR
  have hRpos : 0 < R := (eta0_pos hκ).trans_le hR
  apply ht.trans
  rw [mul_one_div]
  exact add_le_add
    (div_le_div_of_nonneg_right (le_abs_self _) (pow_nonneg hRpos.le _))
    (div_le_div_of_nonneg_right (le_abs_self _) (by positivity))

/-- The corresponding maximum-root estimate. In particular this has the
`N R^(-2a) + R^(-1)` scaling used at the moving cutoff in the printed proof. -/
theorem smooth_maximum_bound (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) (a : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ (N : ℕ) (_hN : 0 < N) (R : ℝ),
      eta0 L κ ≤ R →
      (bornMeasure (physBasis L hκ N) (smoothL2 hf) hu).real
        (outside (qAct L κ N) R) ≤
        (N : ℝ)*(C/R^(2*a)) + D/R := by
  obtain ⟨C, D, hC, hD, ht⟩ := smooth_born_tail hκ hf hu a
  refine ⟨C,D,hC,hD,?_⟩
  intro N hN R hR
  have hRpos : 0 < R := (eta0_pos hκ).trans_le hR
  have h := root_event_bound hN
    (bornMeasure (physBasis L hκ N) (smoothL2 hf) hu)
    (qAct L κ N) Measurable.of_discrete a C D (eta0 L κ) R hR hRpos
    (fun R' hR' _ => by simpa only [div_eq_mul_inv, one_div, one_mul] using ht N hN R' hR')
  simpa only [div_eq_mul_inv, one_div, one_mul] using h

/-- The maximum-root event vanishes at any admissible power cutoff.
Taking `a=b+1` and `α=1/(2b)`, b≥1, gives precisely the printed cutoff.
This does not assert convergence of untruncated moments in expectation. -/
theorem maximum_power_cutoff (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hu : ‖smoothL2 hf‖=1) (a : ℕ) (α : ℝ) (hα : 0 < α)
    (haα : 1 < 2*(a : ℝ)*α) :
    Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) (smoothL2 hf) hu).real
      (outside (qAct L κ N) ((N : ℝ)^α))) atTop (𝓝 0) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := smooth_maximum_bound hκ hf hu a
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  have h1 : Tendsto (fun N : ℕ => C*(N : ℝ)*((N : ℝ)^α)^(-(2*(a : ℝ))))
      atTop (𝓝 0) := by
    have hy : 0 < 2*(a : ℝ)*α-1 := by linarith
    have ht := ((tendsto_rpow_neg_atTop hy).comp hnat).const_mul C
    rw [mul_zero] at ht
    refine ht.congr' ?_
    filter_upwards [hpos] with N hN
    have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hN0.le]
    rw [show -(2*(a : ℝ)*α-1)=1+α*(-(2*(a : ℝ))) by ring,
      Real.rpow_add hN0, Real.rpow_one]
    ring
  have h2 : Tendsto (fun N : ℕ => D*((N : ℝ)^α)⁻¹) atTop (𝓝 0) := by
    have ht := ((tendsto_rpow_neg_atTop hα).comp hnat).const_mul D
    rw [mul_zero] at ht
    exact ht.congr (fun N => by simp only [Function.comp_apply, Real.rpow_neg (Nat.cast_nonneg N)])
  have ht := h1.add h2
  simp only [add_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => measureReal_nonneg)
  have hR := ((tendsto_rpow_atTop hα).comp hnat).eventually (eventually_ge_atTop (eta0 L κ))
  filter_upwards [hpos,hR] with N hN hRN
  have h := hbound N (by omega) ((N : ℝ)^α) hRN
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hR0 : 0 < (N : ℝ)^α := Real.rpow_pos_of_pos hN0 _
  convert h using 1
  rw [Real.rpow_neg hR0.le, show 2*(a : ℝ)=((2*a : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  ring

end QuantumNLS.AuditWeightedTailR49a

#print axioms QuantumNLS.AuditWeightedTailR49a.smooth_born_tail

#print axioms QuantumNLS.AuditWeightedTailR49a.smooth_maximum_bound

#print axioms QuantumNLS.AuditWeightedTailR49a.maximum_power_cutoff

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedTailR49a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedTailR49a." then
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
