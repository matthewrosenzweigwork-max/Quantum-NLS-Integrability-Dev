import QuantumNLS.RootH1RatioContraction
import QuantumNLS.RootH1RatioL2

/-! H¹ range and the quantitative L² bounds for the actual nonlinear fixed point. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open QuantumNLS.PhysicalTensor QuantumNLS.RootH1RatioOperator
  QuantumNLS.RootH1RatioNonlinear QuantumNLS.RootH1RatioContraction
namespace QuantumNLS.RootH1RatioBounds
variable {L : ℝ} [Fact (0 < L)]

def ratio {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y) : Linfty L :=
  Classical.choose (exists_unique_ratio hY hlog hκ u hsmall)

lemma ratio_spec {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y) :
    ‖ratio hY hlog hκ u hsmall‖ ≤ radius Y u ∧
    ratioMap hY hlog κ u (ratio hY hlog hκ u hsmall) = ratio hY hlog hκ u hsmall :=
  (Classical.choose_spec (exists_unique_ratio hY hlog hκ u hsmall)).1

lemma ratio_unique {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y)
    {s : Linfty L} (hs : ‖s‖ ≤ radius Y u) (hf : ratioMap hY hlog κ u s = s) :
    s = ratio hY hlog hκ u hsmall :=
  (Classical.choose_spec (exists_unique_ratio hY hlog hκ u hsmall)).2 s ⟨hs,hf⟩

def ratioL2 {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y) : L2T L :=
  RootH1RatioOperator.resolvent Y (forcing κ u (ratio hY hlog hκ u hsmall))

lemma ratioL2_ae {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y) :
    ratioL2 hY hlog hκ u hsmall =ᵐ[volume] ratio hY hlog hκ u hsmall := by
  have h := coe_infinityResolvent hY hlog (forcing κ u (ratio hY hlog hκ u hsmall))
  change ratioMap hY hlog κ u (ratio hY hlog hκ u hsmall) =ᵐ[volume]
    ratioL2 hY hlog hκ u hsmall at h
  rw [(ratio_spec hY hlog hκ u hsmall).2] at h
  exact h.symm

lemma ratio_H1 {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y) :
    (ratioL2 hY hlog hκ u hsmall, forcing κ u (ratio hY hlog hκ u hsmall)) ∈
      QuantumNLS.HaarResolvent.graphD L 1 ((Y:ℂ)*Complex.I) :=
  resolvent_range hY _

lemma ratio_small {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y) :
    κ * ‖ratio hY hlog hκ u hsmall‖^2 ≤ 1/4 :=
  ball_small hY hκ u hsmall (ratio_spec hY hlog hκ u hsmall).1

lemma ratioL2_norm {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y) :
    ‖ratioL2 hY hlog hκ u hsmall‖ ≤ 5*‖u‖/(4*Y) := by
  have hs := ratio_small hY hlog hκ u hsmall
  calc
    _ ≤ ‖forcing κ u (ratio hY hlog hκ u hsmall)‖/Y := RootH1RatioL2.resolvent_apply_norm hY _
    _ ≤ ((1+κ*‖ratio hY hlog hκ u hsmall‖^2)*‖u‖)/Y := by
      gcongr
      exact forcing_norm hκ u _
    _ ≤ ((5/4)*‖u‖)/Y := by gcongr; linarith
    _ = _ := by ring

lemma nonlinear_error {Y κ : ℝ} (hY : 0 < Y) (hlog : Real.log 3 ≤ Y*L)
    (hκ : 0 ≤ κ) (u : L2T L) (hsmall : 16*κ*‖u‖^2 ≤ Y) :
    ‖(Y:ℂ) • (ratioL2 hY hlog hκ u hsmall - RootH1RatioOperator.resolvent Y u)‖ ≤
      4*κ*‖u‖^3/Y := by
  let r := ratio hY hlog hκ u hsmall
  have he : ratioL2 hY hlog hκ u hsmall - RootH1RatioOperator.resolvent Y u =
      -(κ:ℂ) • RootH1RatioOperator.resolvent Y (cubic u r) := by
    change RootH1RatioOperator.resolvent Y (u-(κ:ℂ) • cubic u r) -
      RootH1RatioOperator.resolvent Y u = -(κ:ℂ) • RootH1RatioOperator.resolvent Y (cubic u r)
    rw [(RootH1RatioOperator.resolvent Y).map_sub, (RootH1RatioOperator.resolvent Y).map_smul (κ:ℂ)]
    module
  have hr : ‖r‖^2 ≤ 4*‖u‖^2/Y := by
    have hb := pow_le_pow_left₀ (norm_nonneg r) (ratio_spec hY hlog hκ u hsmall).1 2
    dsimp [radius] at hb
    rw [mul_pow, scale_sq hY] at hb
    convert hb using 1
    ring
  calc
    _ = Y*(κ*‖RootH1RatioOperator.resolvent Y (cubic u r)‖) := by
      rw [he, norm_smul, norm_smul, norm_neg, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hκ, Real.norm_of_nonneg hY.le]
    _ ≤ Y*(κ*(‖cubic u r‖/Y)) := by
      gcongr
      exact RootH1RatioL2.resolvent_apply_norm hY _
    _ = κ*‖cubic u r‖ := by field_simp
    _ ≤ κ*(‖r‖^2*‖u‖) := by gcongr; exact cubic_norm u r
    _ ≤ κ*((4*‖u‖^2/Y)*‖u‖) := by gcongr
    _ = _ := by ring

#print axioms ratio_spec
#print axioms ratio_unique
#print axioms ratioL2_ae
#print axioms ratio_H1
#print axioms ratio_small
#print axioms ratioL2_norm
#print axioms nonlinear_error
end QuantumNLS.RootH1RatioBounds

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioBounds." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioBounds." then
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
