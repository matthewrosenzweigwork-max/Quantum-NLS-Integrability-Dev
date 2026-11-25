import QuantumNLS.Reg010LowYoung
import QuantumNLS.Reg010LowFourierHolder

/-! Parseval and discrete Young give the L4 estimate for trigonometric polynomials. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.Reg010LowPolynomial
open QuantumNLS.Fourier
variable {L : ℝ} [Fact (0<L)]

/-- The sharp report-normalized Fourier synthesis bound for absolutely
summable coefficients in l^(4/3). It applies in particular to every finite
Fourier polynomial. -/
theorem fourth_series_bound (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (ha43 : Summable (fun n => ‖a n‖^(4/3:ℝ))) :
    (∫ x : AddCircle L, ‖seriesRep L a x‖^4) ≤
      L⁻¹ * (∑' n : ℤ, ‖a n‖^(4/3:ℝ))^3 := by
  let A : ℝ := ∑' n : ℤ, ‖a n‖^(4/3:ℝ)
  have hA : 0≤A := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg _) _)
  let D : ℤ → ℝ := fun n => ∑' k, ‖a k‖*‖a (n-k)‖
  have hD : ∀ n, 0≤D n := fun n => tsum_nonneg (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hy := QuantumNLS.Reg010LowYoung.young_four_thirds (fun n => ‖a n‖) (fun n => ‖a n‖)
    (fun n => norm_nonneg _) (fun n => norm_nonneg _) ha43 ha43
  let P : AddCircle L → ℂ := fun x => seriesRep L a x*seriesRep L a x
  have hpc : Continuous P := (continuous_seriesRep ha).mul (continuous_seriesRep ha)
  have hp : Summable (fun n : ℤ => ‖coeff L P n‖^2) := (hasSum_sq_coeff L (memLp_of_continuous hpc)).summable
  have hpoint : ∀ n, ‖coeff L P n‖^2 ≤ L⁻¹ * (D n)^2 := by
    intro n
    have hb := norm_coeff_mul_le (L := L) ha ha n
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [mul_pow, inv_pow, Real.sq_sqrt (Fact.out : 0<L).le] at hs
    exact hs
  have he : (∫ x : AddCircle L, ‖seriesRep L a x‖^4) = ∑' n : ℤ, ‖coeff L P n‖^2 := by
    rw [tsum_sq_coeff L (memLp_of_continuous hpc)]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp [P]
    rw [norm_mul]
    ring
  rw [he]
  calc
    _ ≤ ∑' n, L⁻¹*(D n)^2 := hp.tsum_le_tsum hpoint (hy.2.1.mul_left _)
    _ = L⁻¹ * ∑' n, (D n)^2 := tsum_mul_left
    _ ≤ L⁻¹ * (A*A)^(3/2:ℝ) := mul_le_mul_of_nonneg_left hy.2.2 (inv_nonneg.mpr (Fact.out : 0<L).le)
    _ = L⁻¹*A^3 := by
      congr 1
      rw [← pow_two, ← Real.rpow_two, ← Real.rpow_mul hA]
      norm_num [Real.rpow_ofNat]

/-- The source H^(1/3) fourth-integral estimate for Fourier polynomials. -/
theorem fourth_sobolev_bound (a : ℤ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (he : Mem04 L (1/3) a) :
    (∫ x : AddCircle L, ‖seriesRep L a x‖^4) ≤
      (L⁻¹ * ∑' n : ℤ, (f04Weight L (1/3) n)^(-2:ℝ)) * (f04NormSq L (1/3) a)^2 := by
  have hh := QuantumNLS.Reg010LowFourierHolder.weighted_holder
    (f04Weight L (1/3)) (f04Weight_pos L (1/3)) a he
    (QuantumNLS.Reg010LowFourierHolder.inverse_weight_summable L Fact.out)
  have hb := fourth_series_bound (L := L) a ha hh.1
  let E : ℝ := f04NormSq L (1/3) a
  let S : ℝ := ∑' n : ℤ, (f04Weight L (1/3) n)^(-2:ℝ)
  have hE : 0≤E := tsum_nonneg (fun n => mul_nonneg (f04Weight_pos L (1/3) n).le (sq_nonneg _))
  have hS : 0≤S := tsum_nonneg (fun n => Real.rpow_nonneg (f04Weight_pos L (1/3) n).le _)
  have hp := pow_le_pow_left₀ (tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg _) _)) hh.2 3
  have hr : (E^(2/3:ℝ)*S^(1/3:ℝ))^3 = E^2*S := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hE, ← Real.rpow_mul hS]
    norm_num [Real.rpow_ofNat]
  change _ ≤ (E^(2/3:ℝ)*S^(1/3:ℝ))^3 at hp
  rw [hr] at hp
  exact hb.trans (by dsimp [E,S] at *; nlinarith [mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Fact.out : 0<L).le)])

#print axioms fourth_series_bound
#print axioms fourth_sobolev_bound
end QuantumNLS.Reg010LowPolynomial

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowPolynomial." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowPolynomial." then
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
