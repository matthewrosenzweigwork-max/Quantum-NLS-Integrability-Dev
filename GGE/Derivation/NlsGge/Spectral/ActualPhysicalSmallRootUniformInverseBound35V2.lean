import NlsGge.Spectral.ActualPhysicalUnitNormalizedHalfTraceUniformFrequencyBound35V1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot

/-- Explicit scalar error transfer, including totalized inverse conventions.
Applications must realize the quadratic-root identity and norm bound. -/
theorem smallQuadraticRoot_scaled_inverseErrorBound35
    (a δ b : ℂ) (hb : ‖b‖ ≤ 1) (hr : b+b⁻¹=2*δ) :
    ‖(b/a)⁻¹-1‖ ≤ 2*‖a*δ-(1/2 : ℂ)‖+‖a‖ := by
  have he : (b/a)⁻¹-1=2*(a*δ-(1/2 : ℂ))-a*b := by
    rw [inv_div,div_eq_mul_inv]
    linear_combination a*hr
  have hab : ‖a*b‖ ≤ ‖a‖ := by
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left hb (norm_nonneg a)
  rw [he]
  calc
    _ ≤ ‖2*(a*δ-(1/2 : ℂ))‖+‖a*b‖ := norm_sub_le _ _
    _ = 2*‖a*δ-(1/2 : ℂ)‖+‖a*b‖ := by rw [norm_mul]; norm_num
    _ ≤ _ := add_le_add (le_refl _) hab

/-- The actual scaled small multiplier has an inverse error bound uniform in
EVERY real frequency. No source operator or half trace is supplied by a
hypothesis; only a square root of that actual trace and its smallness are explicit.
The geometric-smallness premise is realized at large height by accepted34. -/
theorem actualPhysicalSmallRoot_scaled_uniformInverseErrorBound35
    (u : PhysicalL2) (x Y : ℝ) (hY : 0 < Y)
    (hA : ‖u‖*Real.sqrt (‖u‖^2/(4*Y)) < 1)
    (s : ℂ)
    (hs : s^2=actualPhysicalUnitHalfTrace32 u ((x : ℂ)+Complex.I*(Y : ℂ))^2-1)
    (hb : ‖actualPhysicalUnitHalfTrace32 u ((x : ℂ)+Complex.I*(Y : ℂ))+s‖ ≤ 1) :
    ‖((actualPhysicalUnitHalfTrace32 u ((x : ℂ)+Complex.I*(Y : ℂ))+s)/
        Complex.exp (Complex.I*((x : ℂ)+Complex.I*(Y : ℂ))))⁻¹-1‖ ≤
      2*((‖u‖*Real.sqrt (‖u‖^2/(4*Y)))/
        (1-‖u‖*Real.sqrt (‖u‖^2/(4*Y))))+Real.exp (-2*Y)+Real.exp (-Y) := by
  let z : ℂ := (x : ℂ)+Complex.I*(Y : ℂ)
  let δ : ℂ := actualPhysicalUnitHalfTrace32 u z
  let b : ℂ := δ+s
  let a : ℂ := Complex.exp (Complex.I*z)
  let D : ℝ := (‖u‖*Real.sqrt (‖u‖^2/(4*Y)))/
    (1-‖u‖*Real.sqrt (‖u‖^2/(4*Y)))
  have hp : b*(δ-s)=1 := by
    dsimp [b,δ,z]
    linear_combination -hs
  have hn : b ≠ 0 := by
    intro h
    rw [h,zero_mul] at hp
    exact zero_ne_one hp
  have hi : b⁻¹=δ-s := by
    apply mul_left_cancel₀ hn
    rw [mul_inv_cancel₀ hn,hp]
  have hr : b+b⁻¹=2*δ := by rw [hi]; dsimp [b]; ring
  have htrace : ‖a*δ-(1/2 : ℂ)‖ ≤ D+Real.exp (-2*Y)/2 := by
    have hbound := actualPhysicalUnitNormalizedHalfTrace_uniformFrequency_bound35 u x Y hY hA
    have he : a*δ-(1/2 : ℂ)=
        (a*δ-(1+Complex.exp (2*Complex.I*z))/2)+Complex.exp (2*Complex.I*z)/2 := by ring
    have hexp : ‖Complex.exp (2*Complex.I*z)‖=Real.exp (-2*Y) := by
      simp [z,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
    rw [he]
    calc
      _ ≤ ‖a*δ-(1+Complex.exp (2*Complex.I*z))/2‖+
          ‖Complex.exp (2*Complex.I*z)/2‖ := norm_add_le _ _
      _ ≤ D+Real.exp (-2*Y)/2 := by
        apply add_le_add
        · exact hbound
        · rw [norm_div,hexp]; norm_num
  have ha : ‖a‖=Real.exp (-Y) := by
    simp [a,z,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  change ‖(b/a)⁻¹-1‖ ≤ 2*D+Real.exp (-2*Y)+Real.exp (-Y)
  have hscalar := smallQuadraticRoot_scaled_inverseErrorBound35 a δ b hb hr
  rw [ha] at hscalar
  nlinarith

end NlsGge.SpectralFoundations
end
