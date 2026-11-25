import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support12

/- KSPS-012 SUPPORT3 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS012Support3.lean.
   Part A: the off-diagonal entries of the first Picard term and the scalar identity that turns the two
   oscillatory pieces of the first correction into a single oscillatory integral
     -e^{-2 i mu} endpointOsc mu (q F),  q t = int_t^1 e^{2 i mu s} u(s) ds. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Matrix
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPSVolterra

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem term1_01 (x : ℝ) (lam : ℂ) (p : PotPair) :
    term 1 x lam p 0 1 = Complex.I * Complex.exp (-(Complex.I * lam * (x : ℂ))) *
      ∫ t in (0 : ℝ)..x, Complex.exp (2 * Complex.I * lam * (t : ℂ)) * potRepFst38 p t := by
  show integrateMatrix 0 x (fun t => E lam (x - t) * R * phi p t * term 0 t lam p) 0 1 = _
  unfold integrateMatrix
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  beta_reduce
  have e : Complex.exp (-(Complex.I * lam * ((x : ℂ) - (t : ℂ)))) * Complex.exp (Complex.I * lam * (t : ℂ)) =
      Complex.exp (-(Complex.I * lam * (x : ℂ))) * Complex.exp (2 * Complex.I * lam * (t : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  simp [E, R, phi, term, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (Complex.I * potRepFst38 p t) * e

theorem term1_10 (x : ℝ) (lam : ℂ) (p : PotPair) :
    term 1 x lam p 1 0 = -Complex.I * Complex.exp (Complex.I * lam * (x : ℂ)) *
      ∫ t in (0 : ℝ)..x, Complex.exp (-(2 * Complex.I * lam * (t : ℂ))) * potRepSnd38 p t := by
  show integrateMatrix 0 x (fun t => E lam (x - t) * R * phi p t * term 0 t lam p) 1 0 = _
  unfold integrateMatrix
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  beta_reduce
  have e : Complex.exp (Complex.I * lam * ((x : ℂ) - (t : ℂ))) * Complex.exp (-(Complex.I * lam * (t : ℂ))) =
      Complex.exp (Complex.I * lam * (x : ℂ)) * Complex.exp (-(2 * Complex.I * lam * (t : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  simp [E, R, phi, term, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (Complex.I * potRepSnd38 p t) * e

/-- The scalar identity behind both diagonal components. `g s = e^{2 i mu s} u s`,
`G t = int_0^t g`, `q t = int_t^1 g`. -/
theorem scalar_diag_identity {mu : ℂ} (hmu : mu ≠ 0) {u F : ℝ → ℂ}
    (hu : IntervalIntegrable u volume 0 1) (hF : IntervalIntegrable F volume 0 1) :
    (2 * mu)⁻¹ *
      (-(2 * mu) * ((Complex.I * Complex.exp (-(Complex.I * mu * ((1 : ℝ) : ℂ))) *
          ∫ t in (0 : ℝ)..1, Complex.exp (2 * Complex.I * mu * (t : ℂ)) * u t) *
        (-Complex.I * ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) * F t)) +
      Complex.exp (-(Complex.I * mu * ((1 : ℝ) : ℂ))) * (2 * mu) *
        ∫ t in (0 : ℝ)..1, (Complex.I * Complex.exp (-(Complex.I * mu * (t : ℂ))) *
            ∫ s in (0 : ℝ)..t, Complex.exp (2 * Complex.I * mu * (s : ℂ)) * u s) *
          (-Complex.I * (Complex.exp (-(Complex.I * mu * (t : ℂ))) * F t))) =
    -Complex.exp (-(2 * Complex.I * mu)) *
      endpointOsc mu
        (fun t => (∫ s in t..1, Complex.exp (2 * Complex.I * mu * (s : ℂ)) * u s) * F t) := by
  set g : ℝ → ℂ := fun s => Complex.exp (2 * Complex.I * mu * (s : ℂ)) * u s with hg
  have hgi : IntervalIntegrable g volume 0 1 :=
    hu.continuousOn_mul (by fun_prop : Continuous fun s : ℝ =>
      Complex.exp (2 * Complex.I * mu * (s : ℂ))).continuousOn
  set G : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, g s with hG
  have hGc : ContinuousOn G (Set.Icc (0 : ℝ) 1) := by
    have hfU : IntegrableOn g (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le zero_le_one] using
        (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hgi
    have := intervalIntegral.continuousOn_primitive_interval hfU
    rw [Set.uIcc_of_le zero_le_one] at this
    exact this
  have hq : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∫ s in t..1, g s = G 1 - G t := by
    intro t ht
    have hac : IntervalIntegrable g volume 0 t := hgi.mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc le_rfl ht.2)
    exact (intervalIntegral.integral_interval_sub_left hgi hac).symm
  set W : ℂ := ∫ t in (0 : ℝ)..1, Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) * F t with hW
  have hexpc : Continuous fun t : ℝ => Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) := by fun_prop
  have hWi : IntervalIntegrable (fun t : ℝ => Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) * F t)
      volume 0 1 := hF.continuousOn_mul hexpc.continuousOn
  have hCi : IntervalIntegrable (fun t : ℝ => (Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) * G t) * F t)
      volume 0 1 := hF.continuousOn_mul (by
        rw [Set.uIcc_of_le zero_le_one]; exact hexpc.continuousOn.mul hGc)
  -- left integral
  have hL : ∫ t in (0 : ℝ)..1, (Complex.I * Complex.exp (-(Complex.I * mu * (t : ℂ))) * G t) *
      (-Complex.I * (Complex.exp (-(Complex.I * mu * (t : ℂ))) * F t)) =
      ∫ t in (0 : ℝ)..1, (Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) * G t) * F t := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    beta_reduce
    have e : Complex.exp (-(Complex.I * mu * (t : ℂ))) * Complex.exp (-(Complex.I * mu * (t : ℂ))) =
        Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h3 : (Complex.I * Complex.exp (-(Complex.I * mu * (t : ℂ))) * G t) *
        (-Complex.I * (Complex.exp (-(Complex.I * mu * (t : ℂ))) * F t)) =
        -(Complex.I * Complex.I) * (Complex.exp (-(Complex.I * mu * (t : ℂ))) *
          Complex.exp (-(Complex.I * mu * (t : ℂ)))) * (G t * F t) := by ring
    rw [h3, Complex.I_mul_I, e]; ring
  -- right integral
  have hR : endpointOsc mu
      (fun t => (∫ s in t..1, Complex.exp (2 * Complex.I * mu * (s : ℂ)) * u s) * F t) =
      Complex.exp (Complex.I * mu) * (G 1 * W -
        ∫ t in (0 : ℝ)..1, (Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) * G t) * F t) := by
    unfold endpointOsc
    have : ∀ t ∈ Set.uIcc (0 : ℝ) 1, Complex.exp (Complex.I * mu * ((1 - 2 * t : ℝ) : ℂ)) *
        ((∫ s in t..1, Complex.exp (2 * Complex.I * mu * (s : ℂ)) * u s) * F t) =
        Complex.exp (Complex.I * mu) * (G 1 * (Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) * F t) -
          (Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) * G t) * F t) := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      have h1 := hq t ht
      have e : Complex.exp (Complex.I * mu * ((1 - 2 * t : ℝ) : ℂ)) =
          Complex.exp (Complex.I * mu) * Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      show Complex.exp (Complex.I * mu * ((1 - 2 * t : ℝ) : ℂ)) *
        ((∫ s in t..1, g s) * F t) = _
      rw [h1, e]; ring
    rw [intervalIntegral.integral_congr this, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (hWi.const_mul _) hCi, intervalIntegral.integral_const_mul]
  rw [hL, hR]
  have e2 : Complex.exp (-(2 * Complex.I * mu)) * Complex.exp (Complex.I * mu) =
      Complex.exp (-(Complex.I * mu * ((1 : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hGdef : G 1 = ∫ t in (0 : ℝ)..1, Complex.exp (2 * Complex.I * mu * (t : ℂ)) * u t := rfl
  rw [← hGdef]
  have h2mu : (2 * mu) ≠ 0 := mul_ne_zero two_ne_zero hmu
  have hinv : (2 * mu)⁻¹ * (2 * mu) = 1 := inv_mul_cancel₀ h2mu
  generalize (∫ t in (0 : ℝ)..1, (Complex.exp (-(2 * Complex.I * mu * (t : ℂ))) * G t) * F t) = C
  generalize G 1 = G1
  generalize Complex.exp (-(Complex.I * mu * ((1 : ℝ) : ℂ))) = B at e2 ⊢
  linear_combination ((Complex.I * Complex.I * B * G1 * W + B * C)) * hinv +
    (G1 * W - C) * e2 + (B * G1 * W) * Complex.I_sq

end NlsGge.ThirdConsultation.KSPSWKB
