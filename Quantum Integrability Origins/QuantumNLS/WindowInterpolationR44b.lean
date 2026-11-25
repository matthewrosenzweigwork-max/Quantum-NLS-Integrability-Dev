import Mathlib
import QuantumNLS.SobolevSpaces

open scoped NNReal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

/-! R-E59628C9: weighted Cauchy--Schwarz and the unchanged quarter-power rate.
The reciprocal positive weight is the genuine negative-order sequence space,
not a field Sobolev space at negative order. No hierarchy existence is used. -/
noncomputable section
set_option autoImplicit false
open scoped Topology
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
namespace QuantumNLS.WindowInterpolationR44b

def reciprocal (W : PosWeight) : PosWeight := ⟨fun j => (W.w j)⁻¹, fun j => inv_pos.mpr (W.pos j)⟩
def unitWeight : PosWeight := ⟨fun _ => 1, fun _ => zero_lt_one⟩

/-- Cauchy--Schwarz with exactly reciprocal weights. -/
theorem reciprocal_interpolation (W : PosWeight) (lo : WSeq (reciprocal W))
    (hi : WSeq W) (mid : WSeq unitWeight)
    (hl : lo.val = mid.val) (hh : hi.val = mid.val) :
    ‖mid‖ ^ 2 ≤ ‖lo‖ * ‖hi‖ := by
  let f : ℤ → ℝ := fun j => Real.sqrt ((W.w j)⁻¹) * ‖mid.val j‖
  let g : ℤ → ℝ := fun j => Real.sqrt (W.w j) * ‖mid.val j‖
  have hf : HasSum (fun j => f j ^ (2 : ℝ)) (‖lo‖ ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two, reciprocal, f, mul_pow, Real.sq_sqrt (inv_pos.mpr (W.pos _)).le,
      ← hl] using hasSum_norm_sq (reciprocal W) lo
  have hg : HasSum (fun j => g j ^ (2 : ℝ)) (‖hi‖ ^ (2 : ℝ)) := by
    simpa only [Real.rpow_two, g, mul_pow, Real.sq_sqrt (W.pos _).le, ← hh]
      using hasSum_norm_sq W hi
  obtain ⟨C, _, hC, hs⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg
    (show Real.HolderConjugate 2 2 by norm_num [Real.holderConjugate_iff])
    (norm_nonneg lo) (norm_nonneg hi) (fun j => by dsimp [f]; positivity)
    (fun j => by dsimp [g]; positivity) hf hg
  have he : ∀ j, f j * g j = unitWeight.w j * ‖mid.val j‖ ^ 2 := by
    intro j
    dsimp [f, g, unitWeight]
    rw [Real.sqrt_inv]
    have hp := Real.sqrt_pos.mpr (W.pos j)
    field_simp
  have hn : ‖mid‖ ^ 2 = C := (hasSum_norm_sq unitWeight mid).unique (hs.congr_fun fun j => (he j).symm)
  simpa only [hn] using hC

/-- Taking the square root of the negative-order half-power estimate loses
one half in the exponent, with no loss in its cutoff-independent constant. -/
theorem quarter_rate {a C B x : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hx : 0 ≤ x) (h : x ^ 2 ≤ (C * a ^ (-(1/2 : ℝ))) * B) :
    x ≤ Real.sqrt (C * B) * a ^ (-(1/4 : ℝ)) := by
  have he : (a ^ (-(1/4 : ℝ))) ^ 2 = a ^ (-(1/2 : ℝ)) := by
    rw [← Real.rpow_mul_natCast ha.le]
    congr 1
    norm_num
  have hsq : x ^ 2 ≤ (Real.sqrt (C * B) * a ^ (-(1/4 : ℝ))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hC hB), he]
    nlinarith [h]
  exact (sq_le_sq₀ hx (by positivity)).mp hsq

/-- All constants here may be uniform on a fixed initial class and time box. -/
theorem interpolated_rate (W : PosWeight) (lo : WSeq (reciprocal W))
    (hi : WSeq W) (mid : WSeq unitWeight) (hl : lo.val = mid.val) (hh : hi.val = mid.val)
    {a C B : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hlo : ‖lo‖ ≤ C * a ^ (-(1/2 : ℝ))) (hhi : ‖hi‖ ≤ B) :
    ‖mid‖ ≤ Real.sqrt (C * B) * a ^ (-(1/4 : ℝ)) := by
  apply quarter_rate ha hC hB (norm_nonneg _)
  exact (reciprocal_interpolation W lo hi mid hl hh).trans
    (mul_le_mul hlo hhi (norm_nonneg _) (by positivity))

end QuantumNLS.WindowInterpolationR44b

#print axioms QuantumNLS.WindowInterpolationR44b.reciprocal_interpolation
#print axioms QuantumNLS.WindowInterpolationR44b.quarter_rate
#print axioms QuantumNLS.WindowInterpolationR44b.interpolated_rate

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowInterpolationR44b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowInterpolationR44b." then
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R44b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
