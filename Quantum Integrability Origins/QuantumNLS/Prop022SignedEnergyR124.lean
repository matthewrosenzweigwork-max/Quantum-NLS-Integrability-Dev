import QuantumNLS.Prop022BlockEquationR124
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A signed-time, dimension-independent square-root energy estimate.
The regularization also covers zero energy and zero forcing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace QuantumNLS.Prop022SignedEnergyR124

/-- If |E'| <= 2 C sqrt(E), E >= 0 and E(s)=0, the sharp bound
sqrt(E(t)) <= C |t-s| holds for both time orientations. -/
theorem sqrt_energy_bound (E D : ℝ → ℝ) (s t C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ r, 0 ≤ E r) (hd : ∀ r, HasDerivAt E (D r) r)
    (hi : E s = 0)
    (hb : ∀ r ∈ uIcc s t, |D r| ≤ 2*C*Real.sqrt (E r)) :
    Real.sqrt (E t) ≤ C*|t-s| := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hp (r : ℝ) : 0 < E r + δ^2 := by nlinarith [hE r]
  have hr (r : ℝ) : HasDerivAt (fun z => Real.sqrt (E z + δ^2))
      (D r / (2*Real.sqrt (E r + δ^2))) r :=
    ((hd r).add_const (δ^2)).sqrt (ne_of_gt (hp r))
  have hbound (r : ℝ) (hm : r ∈ uIcc s t) :
      ‖D r / (2*Real.sqrt (E r + δ^2))‖ ≤ C := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos (by norm_num)
      (Real.sqrt_pos.mpr (hp r)))]
    apply (div_le_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr (hp r)))).mpr
    have hmono : Real.sqrt (E r) ≤ Real.sqrt (E r + δ^2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    exact (hb r hm).trans (by nlinarith)
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ uIcc s t) => (hr r).hasDerivWithinAt)
    hbound (convex_uIcc s t) (left_mem_uIcc : s ∈ uIcc s t)
    (right_mem_uIcc : t ∈ uIcc s t)
  rw [hi, zero_add, Real.sqrt_sq hδ.le, Real.norm_eq_abs, Real.norm_eq_abs] at he
  have hm : Real.sqrt (E t) ≤ Real.sqrt (E t + δ^2) := Real.sqrt_le_sqrt (by nlinarith)
  linarith [le_abs_self (Real.sqrt (E t + δ^2)-δ)]

end QuantumNLS.Prop022SignedEnergyR124
#print axioms QuantumNLS.Prop022SignedEnergyR124.sqrt_energy_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022SignedEnergyR124." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022SignedEnergyR124." then
      pending := pending.push n
  let roots := pending.size
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
  Lean.logInfo m!"R124 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
