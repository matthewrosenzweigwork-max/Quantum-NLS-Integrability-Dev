import QuantumNLS.GlobalCompatScalingR47a
import QuantumNLS.GlobalCompatEstimatesR47a

/-! Epsilon formulation of the full uniform C1 limit, simultaneously for
forward and inverse maps on every fixed bounded ball. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ComplexConjugate Topology
open Set Metric Filter
namespace QuantumNLS.GlobalCompatR47a
open PhysicalTensor (L2T)
open D01LocalPrimitive (K)
open Local021 (Setting)
open RF535Final (Local023Body)
variable {L d CL : ℝ} [Fact (0 < L)]
variable {Φl : ℝ → L2T L → K} {Ψl : ℝ → K → L2T L}
variable {Φ : ℝ → L2T L → K} {Ψ : ℝ → K → L2T L}

def UniformC1 (Φ : ℝ → L2T L → K) (Ψ : ℝ → K → L2T L) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε → ∃ κ0 : ℝ, 0 < κ0 ∧
    ∀ κ : ℝ, 0 < κ → κ < κ0 →
      (∀ u : L2T L, ‖u‖ ≤ R →
        ‖fderiv ℝ (Φ κ) u - Setting.Fcl L‖ ≤ ε ∧
        ‖Φ κ u - Setting.Fcl L u‖ ≤ ε) ∧
      (∀ z : K, ‖z‖ ≤ R →
        ‖fderiv ℝ (Ψ κ) z - ((Setting.Fcle L).symm : K →L[ℝ] L2T L)‖ ≤ ε ∧
        ‖Ψ κ z - (Setting.Fcle L).symm z‖ ≤ ε)

theorem uniform_C1 (hd : 0 < d) (hCL : 0 ≤ CL) (hl : Local023Body L d CL Φl Ψl)
    (hf : Family d Φl Ψl Φ Ψ) : UniformC1 Φ Ψ := by
  intro R hR ε hε
  let κ0 := min (d^2 / (R^2+1)) (ε / (CL*(R^2+R^3)+1))
  have hp : 0 < κ0 := lt_min (div_pos (sq_pos_of_pos hd) (by positivity)) (div_pos hε (by positivity))
  refine ⟨κ0, hp, ?_⟩
  intro κ hκ hk
  have ha : κ*(R^2+1) < d^2 := (lt_div_iff₀ (by positivity : 0 < R^2+1)).mp
    (hk.trans_le (min_le_left _ _))
  have hb : κ*(CL*(R^2+R^3)+1) < ε := (lt_div_iff₀ (by positivity : 0 < CL*(R^2+R^3)+1)).mp
    (hk.trans_le (min_le_right _ _))
  have hsmall : κ*R^2 < d^2 := by nlinarith
  have h2 : CL*κ*R^2 ≤ ε := by
    nlinarith [mul_nonneg (mul_nonneg hCL hκ.le) (pow_nonneg hR.le 3)]
  have h3 : (CL/3)*κ*R^3 ≤ ε := by
    have H : CL*κ*R^3 ≤ ε := by
      nlinarith [mul_nonneg (mul_nonneg hCL hκ.le) (sq_nonneg R)]
    nlinarith [mul_nonneg (mul_nonneg hCL hκ.le) (pow_nonneg hR.le 3)]
  obtain ⟨ha, hb⟩ := (hf κ hκ).ball_estimates hd hCL hl hsmall
  exact ⟨fun u hu => ⟨(ha u hu).1.trans h2, (ha u hu).2.trans h3⟩,
    fun z hz => ⟨(hb z hz).1.trans h2, (hb z hz).2.trans h3⟩⟩
end QuantumNLS.GlobalCompatR47a

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.GlobalCompatR47a." ||
        n.toString.startsWith "_private.QuantumNLS.GlobalCompatR47a." then
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
  Lean.logInfo m!"Round47 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
