import QuantumNLS.RootH1RatioCompanion
import QuantumNLS.RootH1RatioPhase

/-! The exact selected Cauchy identity for the constructed rough-input ratio. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioBounds
  QuantumNLS.RootH1RatioPhase
namespace QuantumNLS.RootH1RatioCauchy
variable {L : ℝ} [hLf : Fact (0 < L)]

theorem ratio_cauchy {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0) (hsmall : 16*κ*‖u‖^2 ≤ Y) :
    CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I) =
      -Complex.I*inner ℂ u (ratioL2 hY hlog hκ.le u hsmall) := by
  let J := inner ℂ u (ratioL2 hY hlog hκ.le u hsmall)
  let G := CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ u) ((Y:ℂ)*Complex.I)
  have hk : κ*‖u‖^2/Y ≤ 1/16 := by
    rw [div_le_iff₀ hY]
    linarith
  have hx : ‖(κ:ℂ)*J‖ ≤ 5/64 := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hκ.le]
    have hj : ‖J‖ ≤ ‖u‖*(5*‖u‖/(4*Y)) :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        (ratioL2_norm hY hlog hκ.le u hsmall) (norm_nonneg _))
    calc
      κ*‖J‖ ≤ κ*(‖u‖*(5*‖u‖/(4*Y))) := mul_le_mul_of_nonneg_left hj hκ.le
      _ = (5/4)*(κ*‖u‖^2/Y) := by ring
      _ ≤ (5/4)*(1/16) := mul_le_mul_of_nonneg_left hk (by norm_num)
      _ = _ := by norm_num
  have hy : ‖Complex.I*(κ:ℂ)*G‖ ≤ 1/16 := by
    rw [norm_mul,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_of_nonneg hκ.le,one_mul]
    calc
      _ ≤ κ*(‖u‖^2/Y) := mul_le_mul_of_nonneg_left (cauchy_bound hY κ u) hκ.le
      _ = κ*‖u‖^2/Y := by ring
      _ ≤ _ := hk
  have hb : (1/3:ℝ) ≤ Y*L/2 := by linarith [log_three_lower]
  have ht := RootH1RatioCompanion.ratio_trace hY hlog hκ.le u hsmall
  rw [phase_trace hY hκ hu] at ht
  have he : (κ:ℂ)*J = Complex.I*(κ:ℂ)*G := exp_pair_unique hb hx hy (by
    have hc : (((Y*L/2:ℝ):ℂ)) = (Y:ℂ)*L/2 := by push_cast; rfl
    rw [hc]
    exact ht.symm)
  have hκc : (κ:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ.ne'
  have hjg : J = Complex.I*G := mul_left_cancel₀ hκc (by linear_combination he)
  change G = -Complex.I*J
  rw [hjg]
  simp [← mul_assoc,Complex.I_mul_I]

#print axioms ratio_cauchy
end QuantumNLS.RootH1RatioCauchy

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioCauchy." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioCauchy." then
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
