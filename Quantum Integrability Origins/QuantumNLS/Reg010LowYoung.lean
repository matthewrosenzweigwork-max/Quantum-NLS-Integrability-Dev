import QuantumNLS.SobolevSpaces

/-! The discrete Young estimate used in the H^(1/3) to L4 embedding. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.Fourier
namespace QuantumNLS.Reg010LowYoung

/-- Young l^(4/3) * l^(4/3) -> l2, with the squared bound. -/
theorem young_four_thirds (a b : ℤ → ℝ) (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (ha : Summable (fun n => a n^(4/3:ℝ))) (hb : Summable (fun n => b n^(4/3:ℝ))) :
    (∀ n, Summable (fun k => a k*b (n-k))) ∧
    Summable (fun n => (∑' k, a k*b (n-k))^2) ∧
    (∑' n, (∑' k, a k*b (n-k))^2) ≤
      ((∑' k, a k^(4/3:ℝ))*(∑' k, b k^(4/3:ℝ)))^(3/2:ℝ) := by
  let A : ℤ → ℝ := fun k => a k^(4/3:ℝ)
  let B : ℤ → ℝ := fun k => b k^(4/3:ℝ)
  have hA0 : ∀ k, 0 ≤ A k := fun k => Real.rpow_nonneg (ha0 k) _
  have hB0 : ∀ k, 0 ≤ B k := fun k => Real.rpow_nonneg (hb0 k) _
  have hy := young_l1_l1 hA0 hB0 ha hb
  have pow23 (x : ℝ) (hx : 0≤x) : (x^(2/3:ℝ))^2 = x^(4/3:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have point : ∀ n, Summable (fun k => a k*b (n-k)) ∧
      (∑' k, a k*b (n-k))^2 ≤
        (∑' k, A k*B (n-k)) * Real.sqrt ((∑' k, A k)*(∑' k, B k)) := by
    intro n
    have hb' : Summable (fun k : ℤ => b (n-k)^(4/3:ℝ)) :=
      hb.comp_injective (Equiv.subLeft n).injective
    have hsmall := tsum_mul_sq_le
      (fun k => Real.rpow_nonneg (ha0 k) (2/3:ℝ))
      (fun k => Real.rpow_nonneg (hb0 (n-k)) (2/3:ℝ))
      (by simpa only [pow23 _ (ha0 _)] using ha)
      (by simpa only [pow23 _ (hb0 _)] using hb')
    simp only [pow23 _ (ha0 _), pow23 _ (hb0 _)] at hsmall
    have hbg : (∑' k, b (n-k)^(4/3:ℝ)) = ∑' k, B k :=
      (Equiv.subLeft n).tsum_eq (fun k => B k)
    rw [hbg] at hsmall
    have hf : Summable (fun k => (a k^(2/3:ℝ)*b (n-k)^(2/3:ℝ))^2) := by
      convert hy.1 n using 1
      funext k
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (ha0 k), ← Real.rpow_mul (hb0 (n-k))]
      norm_num [A,B]
    have hg : Summable (fun k => (a k^(1/3:ℝ)*b (n-k)^(1/3:ℝ))^2) := by
      convert hsmall.1 using 1
      funext k
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (ha0 k), ← Real.rpow_mul (hb0 (n-k))]
      norm_num
    have hbig := tsum_mul_sq_le
      (fun k => mul_nonneg (Real.rpow_nonneg (ha0 k) _) (Real.rpow_nonneg (hb0 (n-k)) _))
      (fun k => mul_nonneg (Real.rpow_nonneg (ha0 k) _) (Real.rpow_nonneg (hb0 (n-k)) _)) hf hg
    have he k : (a k^(2/3:ℝ)*b (n-k)^(2/3:ℝ)) *
        (a k^(1/3:ℝ)*b (n-k)^(1/3:ℝ)) = a k*b (n-k) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add' (ha0 k) (by norm_num : (2/3:ℝ)+1/3 ≠ 0),
        ← Real.rpow_add' (hb0 (n-k)) (by norm_num : (2/3:ℝ)+1/3 ≠ 0)]
      norm_num
    simp_rw [he] at hbig
    have hef : (∑' k, (a k^(2/3:ℝ)*b (n-k)^(2/3:ℝ))^2) = ∑' k, A k*B (n-k) := by
      apply tsum_congr
      intro k
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (ha0 k), ← Real.rpow_mul (hb0 (n-k))]
      norm_num [A,B]
    have heg : (∑' k, (a k^(1/3:ℝ)*b (n-k)^(1/3:ℝ))^2) =
        ∑' k, a k^(2/3:ℝ)*b (n-k)^(2/3:ℝ) := by
      apply tsum_congr
      intro k
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul (ha0 k), ← Real.rpow_mul (hb0 (n-k))]
      norm_num
    rw [hef,heg] at hbig
    have hsqrt := (Real.le_sqrt (tsum_nonneg (fun k => mul_nonneg (Real.rpow_nonneg (ha0 k) _) (Real.rpow_nonneg (hb0 (n-k)) _)))
      (mul_nonneg (tsum_nonneg hA0) (tsum_nonneg hB0))).mpr hsmall.2
    exact ⟨hbig.1,hbig.2.trans (mul_le_mul_of_nonneg_left hsqrt (tsum_nonneg (fun k => mul_nonneg (hA0 k) (hB0 (n-k)))))⟩
  have hmajor := hy.2.1.mul_right (Real.sqrt ((∑' k,A k)*(∑' k,B k)))
  have hsumm : Summable (fun n => (∑' k,a k*b (n-k))^2) :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => (point n).2) hmajor
  refine ⟨fun n => (point n).1, hsumm, ?_⟩
  calc
    _ ≤ ∑' n, (∑' k, A k*B (n-k))*Real.sqrt ((∑' k,A k)*(∑' k,B k)) :=
      hsumm.tsum_le_tsum (fun n => (point n).2) hmajor
    _ ≤ ((∑' k,A k)*(∑' k,B k))*Real.sqrt ((∑' k,A k)*(∑' k,B k)) := by
      rw [tsum_mul_right]
      exact mul_le_mul_of_nonneg_right hy.2.2 (Real.sqrt_nonneg _)
    _ = _ := by
      let z : ℝ := (∑' k,A k)*(∑' k,B k)
      have hz : 0≤z := mul_nonneg (tsum_nonneg hA0) (tsum_nonneg hB0)
      change z*Real.sqrt z = z^(3/2:ℝ)
      rw [Real.sqrt_eq_rpow]
      calc
        z*z^(1/2:ℝ) = z^((1:ℝ)+1/2) := by
          rw [Real.rpow_add' hz (by norm_num : (1:ℝ)+1/2 ≠ 0), Real.rpow_one]
        _ = _ := by norm_num


#print axioms young_four_thirds
end QuantumNLS.Reg010LowYoung

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowYoung." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowYoung." then
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
  Lean.logInfo m!"Round46 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
