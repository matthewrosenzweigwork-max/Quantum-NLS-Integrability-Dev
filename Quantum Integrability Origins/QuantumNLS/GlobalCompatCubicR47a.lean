import QuantumNLS.GlobalCompatSettingR47a

/-! The exact factor 1/3 obtained from the quadratic differential bound.
The scalar cubic comparison is a polynomial, so the fencing theorem applies
without any unproved integration or uniformity premise. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open Set Metric
namespace QuantumNLS.GlobalCompatR47a

theorem cubic_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (A : E →L[ℝ] F) {r C : ℝ} (_hr : 0 < r)
    (hf : ∀ u ∈ ball (0 : E) r, DifferentiableAt ℝ f u) (h0 : f 0 = 0)
    (hbd : ∀ u ∈ ball (0 : E) r, ‖fderiv ℝ f u - A‖ ≤ C * ‖u‖^2)
    {u : E} (hu : ‖u‖ < r) : ‖f u - A u‖ ≤ (C / 3) * ‖u‖^3 := by
  let g : ℝ → F := fun t => f (t • u) - A (t • u)
  let gp : ℝ → F := fun t => (fderiv ℝ f (t • u) - A) u
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • u ∈ ball (0 : E) r := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg u) ht.2).trans_lt hu
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (gp t) t := by
    simpa [g, gp, Function.comp_def] using
      ((hf _ (hmem t ht)).hasFDerivAt.sub A.hasFDerivAt).comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const u)
  have hcont : ContinuousOn g (Icc (0 : ℝ) 1) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hB (t : ℝ) : HasDerivAt (fun t : ℝ => (C / 3) * ‖u‖^3 * t^3)
      (C * ‖u‖^3 * t^2) t := by
    convert ((hasDerivAt_pow 3 t).const_mul ((C / 3) * ‖u‖^3)) using 1; ring
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖gp t‖ ≤ C * ‖u‖^3 * t^2 := by
    calc
      ‖gp t‖ ≤ ‖fderiv ℝ f (t • u) - A‖ * ‖u‖ := (fderiv ℝ f (t • u) - A).le_opNorm u
      _ ≤ (C * ‖t • u‖^2) * ‖u‖ := mul_le_mul_of_nonneg_right (hbd _ (hmem t ⟨ht.1, ht.2.le⟩)) (norm_nonneg u)
      _ = C * ‖u‖^3 * t^2 := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]; ring
  have H := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (B := fun t : ℝ => (C / 3) * ‖u‖^3 * t^3) (by simp [g, h0]) hB hb
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)
  simpa [g] using H

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
