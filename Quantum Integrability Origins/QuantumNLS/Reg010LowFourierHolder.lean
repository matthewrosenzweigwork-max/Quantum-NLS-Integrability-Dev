import QuantumNLS.Reg010LowFreeSobolev
import Mathlib.Analysis.PSeries

/-! The weighted Holder step in the one-third Sobolev embedding. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace QuantumNLS.Reg010LowFourierHolder
open QuantumNLS.Fourier QuantumNLS.Sobolev

/-- The exact inverse-square weight sum required by the source Holder proof. -/
theorem inverse_weight_summable (L : ℝ) (hL : 0 < L) :
    Summable (fun n : ℤ => (f04Weight L (1/3) n)^(-2:ℝ)) := by
  let a : ℝ := 2*Real.pi/L
  have ha : 0<a := by dsimp [a]; positivity
  have hg := (Real.summable_abs_int_rpow (by norm_num : (1:ℝ)<4/3)).mul_left (a^(-4/3:ℝ))
  norm_num only [neg_div] at hg
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [Filter.eventually_cofinite_ne (0:ℤ)] with n hn
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hf : freq L n = a*n := by dsimp [a,freq]; ring
  have hbase : 0 < |a*(n:ℝ)| := abs_pos.mpr (mul_ne_zero ha.ne' hn')
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (f04Weight_pos L (1/3) n).le _)]
  have he : (f04Weight L (1/3) n)^(-2:ℝ) = (1+(a*n)^2)^(-2/3:ℝ) := by
    rw [f04Weight,hf, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [he]
  calc
    _ ≤ ((a*n)^2)^(-2/3:ℝ) := Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero (mul_ne_zero ha.ne' hn'))
      (by linarith) (by norm_num)
    _ = a^(-(4/3:ℝ))*|(n:ℝ)|^(-(4/3:ℝ)) := by
      rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg _), abs_mul,
        abs_of_pos ha, Real.mul_rpow ha.le (abs_nonneg _)]
      norm_num

/-- Weighted Holder with the source exponents, with an explicit constant. -/
theorem weighted_holder {ι : Type*} (w : ι → ℝ) (hw : ∀ n, 0 < w n) (a : ι → ℂ)
    (he : Summable (fun n => w n*‖a n‖^2))
    (hi : Summable (fun n => (w n)^(-2:ℝ))) :
    Summable (fun n => ‖a n‖^(4/3:ℝ)) ∧
      (∑' n, ‖a n‖^(4/3:ℝ)) ≤
        (∑' n, w n*‖a n‖^2)^(2/3:ℝ) * (∑' n, (w n)^(-2:ℝ))^(1/3:ℝ) := by
  let f : ι → ℝ := fun n => (w n*‖a n‖^2)^(2/3:ℝ)
  let g : ι → ℝ := fun n => (w n)^(-2/3:ℝ)
  have hf0 : ∀ n, 0≤f n := fun n => Real.rpow_nonneg (mul_nonneg (hw n).le (sq_nonneg _)) _
  have hg0 : ∀ n, 0≤g n := fun n => Real.rpow_nonneg (hw n).le _
  have hf : Summable (fun n => f n^(3/2:ℝ)) := by
    convert he using 1
    funext n
    dsimp [f]
    rw [← Real.rpow_mul (mul_nonneg (hw n).le (sq_nonneg _))]
    norm_num
  have hg : Summable (fun n => g n^(3:ℝ)) := by
    convert hi using 1
    funext n
    dsimp [g]
    rw [← Real.rpow_mul (hw n).le]
    norm_num
  have hq : (3/2:ℝ).HolderConjugate 3 := by
    constructor <;> norm_num
  obtain ⟨h1,h2⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hq hf0 hg0 hf hg
  have heq n : f n*g n = ‖a n‖^(4/3:ℝ) := by
    dsimp [f,g]
    rw [Real.mul_rpow (hw n).le (sq_nonneg _), mul_assoc,
      mul_comm ((‖a n‖^2)^(2/3:ℝ)), ← mul_assoc,
      ← Real.rpow_add (hw n)]
    norm_num
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  simp_rw [heq] at h1 h2
  refine ⟨h1, ?_⟩
  have hef n : f n^(3/2:ℝ) = w n*‖a n‖^2 := by
    dsimp [f]
    rw [← Real.rpow_mul (mul_nonneg (hw n).le (sq_nonneg _))]
    norm_num
  have heg n : g n^(3:ℝ) = (w n)^(-2:ℝ) := by
    dsimp [g]
    rw [← Real.rpow_mul (hw n).le]
    norm_num
  simp_rw [hef,heg] at h2
  norm_num only [show (1:ℝ)/(3/2)=2/3 by norm_num] at h2
  exact h2

/-- The actual F04 one-third Fourier coefficients belong to l^(4/3). -/
theorem one_third_coefficients {L : ℝ} [Fact (0<L)] (u : H04sp L (1/3)) :
    Summable (fun n : ℤ => ‖fourierL2 L u.val n‖^(4/3:ℝ)) ∧
      (∑' n : ℤ, ‖fourierL2 L u.val n‖^(4/3:ℝ)) ≤
        (‖u‖^2)^(2/3:ℝ) *
          (∑' n : ℤ, (f04Weight L (1/3) n)^(-2:ℝ))^(1/3:ℝ) := by
  have he := u.summable
  change Summable (fun n : ℤ => f04Weight L (1/3) n*‖fourierL2 L u.val n‖^2) at he
  have h := weighted_holder (f04Weight L (1/3)) (f04Weight_pos L (1/3))
    (fun n => fourierL2 L u.val n) he (inverse_weight_summable L Fact.out)
  have hn := WField.norm_sq_eq_tsum L u
  change ‖u‖^2 = ∑' n : ℤ, f04Weight L (1/3) n*‖fourierL2 L u.val n‖^2 at hn
  rw [← hn] at h
  exact h

#print axioms inverse_weight_summable
#print axioms weighted_holder
#print axioms one_third_coefficients
end QuantumNLS.Reg010LowFourierHolder

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowFourierHolder." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowFourierHolder." then
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
