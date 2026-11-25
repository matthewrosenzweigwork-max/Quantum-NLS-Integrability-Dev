import QuantumNLS.AuditWeightedSeriesR49a
import QuantumNLS.Reg015HFinal
import QuantumNLS.R275Unconditional

/-! R-115CAA16: all weighted target tails, from the authorized conditional
REG-015 final (7a2945b4), whose review status is NOT promoted here.
The scalar moments are imported directly from accepted R-275B7656.
This does not use, assume, or duplicate the pending hierarchy flow proof. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.AuditWeightedActionsR49a
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.PhysicalTensor QuantumNLS.RootWeightedCellsR26
open QuantumNLS.AuditWeightedSeriesR49a
variable {L κ : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

theorem smooth_shifted_moment (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (p : ℝ) (hp : 0 ≤ p) : Integrable (fun t : ℝ => (1+|t|)^p)
      (QuantumNLS.PhysicalQuantumMeasure.measure hκ (smoothL2 hf)) := by
  rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas]
  obtain ⟨b, hb⟩ := exists_nat_ge p
  have hm := ((QuantumNLS.R275Unconditional.R_275B7656 κ hκ hf).2 b).1
  have hI : Integrable (fun t : ℝ => (2 : ℝ)^b * (1+|t|^b))
      (QuantumNLS.FullMass.Mmeas κ (smoothL2 hf)) :=
    ((integrable_const 1).add hm).const_mul _
  refine hI.mono' (by fun_prop) (ae_of_all _ fun t => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc
    (1+|t|)^p ≤ (1+|t|)^b := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) hb
    _ ≤ (2 : ℝ)^(b-1) * (1^b+|t|^b) := add_pow_le (by positivity) (abs_nonneg t) b
    _ ≤ (2 : ℝ)^b * (1+|t|^b) := by
      simp only [one_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le b 1)) (by positivity)

/-- Every fixed real shifted momentum weight is summable for smooth data.
The only pending scientific dependency is REG-015 and its review chain. -/
theorem smooth_actions_momentum (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (p : ℝ) (hp : 0 ≤ p) : Summable (fun n : ℤ =>
      (1+|momentum L n|)^p * (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hf)).1 n) := by
  have h := ((QuantumNLS.Reg015HFinal.REG015_final (L := L) hκ (p/2)
    (by positivity)).1 (smoothL2 hf)).2
  rw [show 2*(p/2)=p by ring] at h
  exact h.mp (smooth_shifted_moment hκ hf p hp)

/-- Exact printed weights are bounded by the physical momentum weights,
with a constant depending only on fixed `L,p`. -/
theorem weight_le_momentum (p : ℝ) (hp : 0 ≤ p) (n : ℤ) :
    weight p n ≤ (max 1 (L/(2*Real.pi)))^p * (1+|momentum L n|)^p := by
  have hL : 0 < L := Fact.out
  let c := max 1 (L/(2*Real.pi))
  have hc : 1 ≤ c := le_max_left _ _
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hm : (L/(2*Real.pi)) * |momentum L n| = |(n : ℝ)| := by
    unfold momentum
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos Real.pi_pos, abs_of_pos hL]
    field_simp
  have hn : 1+|(n : ℝ)| ≤ c*(1+|momentum L n|) := by
    have := mul_le_mul_of_nonneg_right (le_max_right 1 (L/(2*Real.pi)))
      (abs_nonneg (momentum L n))
    rw [hm] at this
    nlinarith
  calc
    weight p n ≤ ((1+|(n : ℝ)|)^2)^(p/2) := by
      unfold weight
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      nlinarith [abs_nonneg (n : ℝ), sq_abs (n : ℝ)]
    _ = (1+|(n : ℝ)|)^p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    _ ≤ (c*(1+|momentum L n|))^p := Real.rpow_le_rpow (by positivity) hn hp
    _ = _ := Real.mul_rpow hc0 (by positivity)

theorem smooth_actions_summable (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (p : ℝ) (hp : 0 ≤ p) : Summable (fun n : ℤ =>
      weight p n * (QuantumNLS.RootIndexedMasses.masses hκ (smoothL2 hf)).1 n) := by
  have hA := (QuantumNLS.RootIndexedMasses.root_indexed_masses_proved_clauses hκ (smoothL2 hf)).2.1
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (weight_pos p n).le (hA n))
    (fun n => ?_) ((smooth_actions_momentum hκ hf p hp).mul_left
      ((max 1 (L/(2*Real.pi)))^p))
  have := mul_le_mul_of_nonneg_right (weight_le_momentum (L := L) p hp n) (hA n)
  simpa only [mul_assoc] using this

end QuantumNLS.AuditWeightedActionsR49a

#print axioms QuantumNLS.AuditWeightedActionsR49a.smooth_shifted_moment

#print axioms QuantumNLS.AuditWeightedActionsR49a.smooth_actions_momentum

#print axioms QuantumNLS.AuditWeightedActionsR49a.weight_le_momentum

#print axioms QuantumNLS.AuditWeightedActionsR49a.smooth_actions_summable

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.AuditWeightedActionsR49a." ||
        n.toString.startsWith "_private.QuantumNLS.AuditWeightedActionsR49a." then
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
