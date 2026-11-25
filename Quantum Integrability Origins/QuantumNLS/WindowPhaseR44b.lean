import QuantumNLS.WindowInterpolationR44b

open scoped NNReal
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

/-! R-E59628C9: comparison of constant-action rotations, retaining zero
coordinates. This module proves estimates only; it constructs no hierarchy. -/
noncomputable section
set_option autoImplicit false
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.WindowInterpolationR44b
namespace QuantumNLS.WindowPhaseR44b

def rotate {W : PosWeight} (α : ℤ → ℝ) (z : WSeq W) : WSeq W :=
  WSeq.mk W (fun j => (Circle.exp (α j) : ℂ)*z.val j)
    (z.summable.congr fun j => by simp)

@[simp] theorem rotate_val {W : PosWeight} (α : ℤ → ℝ) (z : WSeq W) (j : ℤ) :
    (rotate α z).val j = (Circle.exp (α j) : ℂ)*z.val j := rfl

theorem norm_rotate {W : PosWeight} (α : ℤ → ℝ) (z : WSeq W) : ‖rotate α z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
  simp

theorem phase_difference (α β : ℝ) :
    ‖(Circle.exp α : ℂ) - (Circle.exp β : ℂ)‖ ≤ |α-β| := by
  have he : (Circle.exp α : ℂ) - (Circle.exp β : ℂ) =
      (Complex.exp (Complex.I * ((α-β : ℝ) : ℂ)) - 1) * (Circle.exp β : ℂ) := by
    rw [Circle.coe_exp, Circle.coe_exp]
    have hsum : Complex.I * ((α-β : ℝ) : ℂ) + (β : ℂ)*Complex.I = (α : ℂ)*Complex.I := by
      push_cast; ring
    rw [sub_mul, one_mul, ← Complex.exp_add, hsum]
  rw [he, norm_mul, Circle.norm_coe, mul_one]
  simpa only [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := α-β))

theorem phase_times_coordinate (α β : ℝ) (z : ℂ) :
    ‖(Circle.exp α : ℂ)*z - (Circle.exp β : ℂ)*z‖ ≤
      ‖(((α-β : ℝ) : ℂ)*z)‖ := by
  rw [← sub_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (phase_difference α β) (norm_nonneg z)

theorem norm_le_of_coordinates (W : PosWeight) (x y : WSeq W)
    (h : ∀ j, ‖x.val j‖ ≤ ‖y.val j‖) : ‖x‖ ≤ ‖y‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
  exact x.summable.tsum_le_tsum (fun j =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h j) 2) (W.pos j).le) y.summable

theorem rotation_difference (W : PosWeight) (z : WSeq W) (α β : ℤ → ℝ)
    (δ : WSeq (reciprocal W))
    (hδ : ∀ j, δ.val j = (((α j-β j : ℝ) : ℂ)*z.val j)) :
    ∃ e : WSeq (reciprocal W),
      e.val = (rotate α z - rotate β z).val ∧ ‖e‖ ≤ ‖δ‖ := by
  let v : ℤ → ℂ := fun j => (Circle.exp (α j) : ℂ)*z.val j -
    (Circle.exp (β j) : ℂ)*z.val j
  have hv : ∀ j, ‖v j‖ ≤ ‖δ.val j‖ := fun j => by
    rw [hδ j]
    exact phase_times_coordinate _ _ _
  have hs : Summable (fun j => (reciprocal W).w j * ‖v j‖^2) :=
    δ.summable.of_nonneg_of_le (fun j => by positivity [(reciprocal W).pos j])
      (fun j => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hv j) 2) ((reciprocal W).pos j).le)
  let e := WSeq.mk (reciprocal W) v hs
  exact ⟨e,rfl,norm_le_of_coordinates _ e δ hv⟩

theorem joint_error_norm {ι : Type*} (S : Finset ι) (W : PosWeight)
    (t C : ι → ℝ) (err : ι → WSeq (reciprocal W)) {a : ℝ}
    (h : ∀ r ∈ S, ‖err r‖ ≤ C r*a^(-(1/2 : ℝ))) :
    ‖∑ r ∈ S, t r • err r‖ ≤ (∑ r ∈ S, |t r| *C r)*a^(-(1/2 : ℝ)) := by
  calc ‖∑ r ∈ S, t r • err r‖ ≤ ∑ r ∈ S, ‖t r • err r‖ := norm_sum_le _ _
    _ = ∑ r ∈ S, |t r| *‖err r‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ r ∈ S, |t r| *(C r*a^(-(1/2 : ℝ))) :=
      Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left (h r hr) (abs_nonneg _)
    _ = _ := by simp only [← mul_assoc, Finset.sum_mul]

/-- A compact time box is bounded in each of its finitely many times. -/
theorem box_error_norm {ι : Type*} (S : Finset ι) (W : PosWeight)
    (t T C : ι → ℝ) (err : ι → WSeq (reciprocal W)) {a : ℝ} (ha : 0 ≤ a)
    (hC : ∀ r ∈ S, 0 ≤ C r) (ht : ∀ r ∈ S, |t r| ≤ T r)
    (h : ∀ r ∈ S, ‖err r‖ ≤ C r*a^(-(1/2 : ℝ))) :
    ‖∑ r ∈ S, t r • err r‖ ≤ (∑ r ∈ S, T r*C r)*a^(-(1/2 : ℝ)) := by
  apply (joint_error_norm S W t C err h).trans
  exact mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun r hr =>
    mul_le_mul_of_nonneg_right (ht r hr) (hC r hr)) (Real.rpow_nonneg ha _)

end QuantumNLS.WindowPhaseR44b

#print axioms QuantumNLS.WindowPhaseR44b.rotation_difference
#print axioms QuantumNLS.WindowPhaseR44b.box_error_norm

-- Recursive type/value audit of every own declaration, including generated declarations.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.WindowPhaseR44b." ||
        n.toString.startsWith "_private.QuantumNLS.WindowPhaseR44b." then
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
