import QuantumNLS.Def021ChartR41b
import QuantumNLS.AnalyticIdentity
import QuantumNLS.HierarchyScaling

/-! DEF-021: global coupling conversion for the actual accepted charts.
LOCAL-023's small-ball identity extends by the accepted real analytic
identity theorem. This theorem changes coupling at FIXED period. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.Def021CouplingR41b
open PhysicalTensor (L2T)
open Def021ChartR41b Metric Set
variable {L κ : ℝ} [Fact (0 < L)]

theorem global_coupling_scaling (hκ : 0 < κ) (s : ℝ) (hs : 0 < s) (u : L2T L) :
    Phi L κ (s • u) = s • Phi L (κ * s ^ 2) u := by
  have hκs : 0 < κ * s ^ 2 := mul_pos hκ (sq_pos_of_pos hs)
  let d := (localChart L).d
  have hd : 0 < d := (localChart L).positive
  have hroot : Real.sqrt (κ * s ^ 2) = Real.sqrt κ * s := by
    rw [Real.sqrt_mul hκ.le, Real.sqrt_sq hs.le]
  have hsqrt : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  let A : L2T L → D01LocalPrimitive.K :=
    fun x => Phi L κ (s • x) - s • Phi L (κ * s ^ 2) x
  have hA : ∀ x, AnalyticAt ℝ A x := fun x =>
    ((analytic L κ hκ (s • x)).comp (Local023.analyticAt_smul_gen s x)).sub
      ((analytic L (κ * s ^ 2) hκs x).const_smul (c := s))
  have hz : ∀ x ∈ ball (0 : L2T L) (d / Real.sqrt (κ * s ^ 2)), A x = 0 := by
    intro x hx
    rw [mem_ball_zero_iff] at hx
    have hx' : ‖x‖ * (Real.sqrt κ * s) < d := by
      apply (lt_div_iff₀ (mul_pos hsqrt hs)).mp
      simpa only [hroot] using hx
    have hv : s • x ∈ ball (0 : L2T L) (d / Real.sqrt κ) := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      apply (lt_div_iff₀ hsqrt).2
      nlinarith
    have hl := (localChart L).spec.2.1 κ hκ s hs x hx
    change Phi L κ (s • x) - s • Phi L (κ * s ^ 2) x = 0
    rw [local_agreement L κ hκ (s • x) hv,
      local_agreement L (κ * s ^ 2) hκs x (mem_ball_zero_iff.2 hx), hl, sub_self]
  exact sub_eq_zero.mp (AnalyticIdentity.identity_of_vanishing_ball A hA
    (div_pos hd (Real.sqrt_pos.2 hκs)) hz u)

theorem unit_coupling (hκ : 0 < κ) (u : L2T L) :
    Phi L κ u = (Real.sqrt κ)⁻¹ • Phi L 1 (Real.sqrt κ • u) := by
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have h := global_coupling_scaling (L := L) (κ := 1) one_pos (Real.sqrt κ) hs u
  rw [one_mul, Real.sq_sqrt hκ.le] at h
  rw [h, inv_smul_smul₀ hs.ne']

/-- The literal negative-half-power coefficient, at any fixed period. -/
theorem unit_coupling_rpow (hκ : 0 < κ) (u : L2T L) :
    Phi L κ u = ((κ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • Phi L 1 (Real.sqrt κ • u) := by
  rw [Real.rpow_neg hκ.le, ← Real.sqrt_eq_rpow, Complex.coe_smul]
  exact unit_coupling hκ u

end QuantumNLS.Def021CouplingR41b

#print axioms QuantumNLS.Def021CouplingR41b.global_coupling_scaling
#print axioms QuantumNLS.Def021CouplingR41b.unit_coupling
#print axioms QuantumNLS.Def021CouplingR41b.unit_coupling_rpow

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def021CouplingR41b." ||
        n.toString.startsWith "_private.QuantumNLS.Def021CouplingR41b." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"R41b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
