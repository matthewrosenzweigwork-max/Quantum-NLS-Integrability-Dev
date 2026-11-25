import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPS.KSPS003Support1
import NlsGge.ThirdConsultation.KSPS.KSPS003Support2

                                                                                                                    
                                                                                                                
                                                                                                                 
                                                                                                                    
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS
open NlsGge.ThirdConsultation.KSPS003Support

namespace NlsGge.ThirdConsultation.KSPS004Support

/-- Integration by parts for a W^{1,1} function vanishing at zero. -/
theorem main_ibp {κ : ℂ} (hκ : κ ≠ 0) {F F' : ℝ → ℂ} (hF : PrimOn F F') (h0 : F 0 = 0)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {B0 B1 : ℝ} (hB0 : ‖F x‖ ≤ B0)
    (hB1 : ∫ t in (0 : ℝ)..1, ‖F' t‖ ≤ B1) :
    ‖Complex.exp (-(Complex.I * κ * (x : ℂ))) *
        ∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * κ) * (t : ℂ)) * F t‖ ≤
      Real.exp (|κ.im| * x) * (B0 + B1) / (2 * ‖κ‖) := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = 2 * Complex.I * κ := ⟨_, rfl⟩
  rw [← hcdef]
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hκ
  have hx0 : 0 ≤ x := hx.1
  have hIp := ii_mono hF.1 hx
  have h := ibp_exp hF c hx
  rw [h0] at h
  set E : ℂ := Complex.exp (-(Complex.I * κ * (x : ℂ))) with hE
  set S : ℝ := Real.exp (|κ.im| * x) with hSdef
  have hS : 0 < S := Real.exp_pos _
  have hEc : ‖E * Complex.exp (c * (x : ℂ))‖ ≤ S := phase_le hcdef hx0 le_rfl
  have hK : ‖E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * F' t‖ ≤ S * B1 := by
    have e : E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * F' t =
        ∫ t in (0 : ℝ)..x, (E * Complex.exp (c * (t : ℂ))) * F' t := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun t _ => by ring)
    rw [e]
    refine (norm_int_mul_le hx0 (fun t ht => phase_le hcdef ht.1 ht.2) hIp).trans ?_
    exact mul_le_mul_of_nonneg_left ((int_norm_mono hF.1 hx).trans hB1) hS.le
  have hid : c * (E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * F t) =
      (E * Complex.exp (c * (x : ℂ))) * F x -
        E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * F' t := by
    linear_combination E * h
  have hnc : ‖c‖ = 2 * ‖κ‖ := by
    rw [hcdef]; simp [norm_mul]
  have hkpos : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hineq : ‖c‖ * ‖E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * F t‖ ≤ S * (B0 + B1) := by
    rw [← norm_mul, hid]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul hEc hB0 (norm_nonneg _) hS.le
    linarith
  rw [le_div_iff₀ (by positivity), hnc] at *
  nlinarith [hineq]

/-- Continuity of the nested Volterra expression on `[0,1]`. -/
theorem nested_cont (f : ℝ → ℂ) (hf : Continuous f) (c1 c2 : ℂ) {a b : ℝ → ℂ}
    (ha : IntervalIntegrable a volume 0 1) (hb : IntervalIntegrable b volume 0 1) :
    ContinuousOn (fun t : ℝ => f t * ∫ s in (0 : ℝ)..t, Complex.exp (c1 * (s : ℂ)) * a s *
      ∫ r in (0 : ℝ)..s, Complex.exp (c2 * (r : ℂ)) * b r) (Set.Icc (0 : ℝ) 1) := by
  have hU : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le zero_le_one
  have hE1 : Continuous fun s : ℝ => Complex.exp (c1 * (s : ℂ)) := by fun_prop
  have hE2 : Continuous fun s : ℝ => Complex.exp (c2 * (s : ℂ)) := by fun_prop
  have hgL : IntervalIntegrable (fun r : ℝ => Complex.exp (c2 * (r : ℂ)) * b r) volume 0 1 :=
    hb.continuousOn_mul hE2.continuousOn
  have hLc := primOn_continuousOn (primOn_integral hgL)
  have hea : IntervalIntegrable (fun s : ℝ => Complex.exp (c1 * (s : ℂ)) * a s) volume 0 1 :=
    ha.continuousOn_mul hE1.continuousOn
  have hG : IntervalIntegrable (fun s : ℝ => Complex.exp (c1 * (s : ℂ)) * a s *
      ∫ r in (0 : ℝ)..s, Complex.exp (c2 * (r : ℂ)) * b r) volume 0 1 :=
    hea.mul_continuousOn (by rw [hU]; exact hLc)
  exact hf.continuousOn.mul (primOn_continuousOn (primOn_integral hG))

theorem third_generic {κ : ℂ} (hκ : κ ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {pa pa' pb pb' ac Mf rem : ℝ → ℂ} (hpa : PrimOn pa pa') (hpb : PrimOn pb pb')
    (hac : ∀ᵐ t ∂volume, pa t = ac t)
    (hMc : ContinuousOn Mf (Set.Icc (0 : ℝ) 1)) {cc : ℂ} (hcc : ‖cc‖ ≤ 1 / (2 * ‖κ‖))
    (hdec : ∀ t ∈ Set.Icc (0 : ℝ) 1, Mf t = cc * Complex.exp (Complex.I * κ * (t : ℂ)) *
      (∫ s in (0 : ℝ)..t, pa s * pb s) + rem t)
    {R : ℝ} (hrem : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖rem t‖ ≤ R * Real.exp (|κ.im| * t))
    {Ma Va Mb : ℝ} (hMa : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖pa t‖ ≤ Ma)
    (hVa : ∫ t in (0 : ℝ)..1, ‖pa' t‖ ≤ Va) (hMb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖pb t‖ ≤ Mb) :
    ‖∫ t in (0 : ℝ)..x, Complex.exp (-(Complex.I * κ * ((x - t : ℝ) : ℂ))) * ac t * Mf t‖ ≤
      Real.exp (|κ.im| * x) *
        ((2 * (Ma * Ma * Mb) + Va * (Ma * Mb)) / (4 * ‖κ‖ ^ 2) + Ma * R) := by
  have hx0 : 0 ≤ x := hx.1
  have hsub := uIcc_sub hx
  have hU : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le zero_le_one
  have hcpa := primOn_continuousOn hpa
  have hcpb := primOn_continuousOn hpb
  have h01 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hMa0 : 0 ≤ Ma := (norm_nonneg _).trans (hMa 0 h01)
  have hMb0 : 0 ≤ Mb := (norm_nonneg _).trans (hMb 0 h01)
  have hR0 : 0 ≤ R := by
    have := (norm_nonneg _).trans (hrem 0 h01)
    simpa using this
  have hVa0 : 0 ≤ Va :=
    le_trans (intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _)) hVa
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  set S : ℝ := Real.exp (|κ.im| * x) with hSdef
  have hS : 0 < S := Real.exp_pos _
  -- the primitive Q of pa * pb and the product F = pa * Q
  have hg : IntervalIntegrable (fun s => pa s * pb s) volume 0 1 :=
    ContinuousOn.intervalIntegrable (by rw [hU]; exact hcpa.mul hcpb)
  have hQ : PrimOn (fun t => ∫ s in (0 : ℝ)..t, pa s * pb s) (fun s => pa s * pb s) :=
    primOn_integral hg
  have hcQ := primOn_continuousOn hQ
  have hF : PrimOn (fun t => pa t * ∫ s in (0 : ℝ)..t, pa s * pb s)
      (fun t => pa' t * (∫ s in (0 : ℝ)..t, pa s * pb s) + pa t * (pa t * pb t)) :=
    primOn_mul hpa hQ
  have hQb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖∫ s in (0 : ℝ)..t, pa s * pb s‖ ≤ Ma * Mb := by
    intro t ht
    have hpt : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖pa s * pb s‖ ≤ Ma * Mb := by
      intro s hs
      rw [Set.uIoc_of_le ht.1] at hs
      have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.trans ht.2⟩
      rw [norm_mul]
      exact mul_le_mul (hMa s hs') (hMb s hs') (norm_nonneg _) hMa0
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    refine h.trans ?_
    rw [sub_zero, abs_of_nonneg ht.1]
    exact mul_le_of_le_one_right (mul_nonneg hMa0 hMb0) ht.2
  have hB0 : ‖pa x * ∫ s in (0 : ℝ)..x, pa s * pb s‖ ≤ Ma * (Ma * Mb) := by
    rw [norm_mul]
    exact mul_le_mul (hMa x hx) (hQb x hx) (norm_nonneg _) hMa0
  have hB1 : ∫ t in (0 : ℝ)..1, ‖pa' t * (∫ s in (0 : ℝ)..t, pa s * pb s) +
      pa t * (pa t * pb t)‖ ≤ Va * (Ma * Mb) + Ma * (Ma * Mb) := by
    have hint : IntervalIntegrable (fun t => ‖pa' t‖ * (Ma * Mb) + Ma * (Ma * Mb)) volume 0 1 :=
      (hpa.1.norm.mul_const _).add intervalIntegrable_const
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖pa' t * (∫ s in (0 : ℝ)..t, pa s * pb s) +
        pa t * (pa t * pb t)‖ ≤ ‖pa' t‖ * (Ma * Mb) + Ma * (Ma * Mb) := by
      intro t ht
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hQb t ht) (norm_nonneg _)
      · rw [norm_mul, norm_mul]
        exact mul_le_mul (hMa t ht) (mul_le_mul (hMa t ht) (hMb t ht) (norm_nonneg _) hMa0)
          (by positivity) hMa0
    have hle := intervalIntegral.integral_mono_on zero_le_one hF.1.norm hint hpt
    have hval : ∫ t in (0 : ℝ)..1, (‖pa' t‖ * (Ma * Mb) + Ma * (Ma * Mb)) =
        (∫ t in (0 : ℝ)..1, ‖pa' t‖) * (Ma * Mb) + Ma * (Ma * Mb) := by
      rw [intervalIntegral.integral_add (hpa.1.norm.mul_const _) intervalIntegrable_const,
        intervalIntegral.integral_mul_const]
      simp
    refine hle.trans ?_
    rw [hval]
    exact add_le_add_left (mul_le_mul_of_nonneg_right hVa (mul_nonneg hMa0 hMb0)) _
  have hmain : ‖Complex.exp (-(Complex.I * κ * (x : ℂ))) *
        ∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * κ) * (t : ℂ)) *
          (pa t * ∫ s in (0 : ℝ)..t, pa s * pb s)‖ ≤
      S * ((Ma * (Ma * Mb)) + (Va * (Ma * Mb) + Ma * (Ma * Mb))) / (2 * ‖κ‖) :=
    main_ibp hκ hF (by simp) hx hB0 hB1
  -- transfer to the continuous representative
  have hA : ∫ t in (0 : ℝ)..x, Complex.exp (-(Complex.I * κ * ((x - t : ℝ) : ℂ))) * ac t * Mf t =
      ∫ t in (0 : ℝ)..x, Complex.exp (-(Complex.I * κ * ((x - t : ℝ) : ℂ))) * pa t * Mf t := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hac] with t ht _
    rw [ht]
  rw [hA]
  have hw : Continuous fun t : ℝ => Complex.exp (-(Complex.I * κ * ((x - t : ℝ) : ℂ))) := by
    fun_prop
  have hexp : Continuous fun t : ℝ => Complex.exp (Complex.I * κ * (t : ℂ)) := by fun_prop
  set f1 : ℝ → ℂ := fun t => Complex.exp (-(Complex.I * κ * ((x - t : ℝ) : ℂ))) * pa t * Mf t
    with hf1
  set fm : ℝ → ℂ := fun t => Complex.exp (-(Complex.I * κ * ((x - t : ℝ) : ℂ))) * pa t *
    (cc * Complex.exp (Complex.I * κ * (t : ℂ)) * ∫ s in (0 : ℝ)..t, pa s * pb s) with hfm
  have hc1 : ContinuousOn f1 (Set.Icc (0 : ℝ) 1) := (hw.continuousOn.mul hcpa).mul hMc
  have hcm : ContinuousOn fm (Set.Icc (0 : ℝ) 1) :=
    (hw.continuousOn.mul hcpa).mul ((continuousOn_const.mul hexp.continuousOn).mul hcQ)
  have hi1 : IntervalIntegrable f1 volume 0 x := (hc1.mono hsub).intervalIntegrable
  have hi2 : IntervalIntegrable fm volume 0 x := (hcm.mono hsub).intervalIntegrable
  have hsplit : ∫ t in (0 : ℝ)..x, f1 t =
      (∫ t in (0 : ℝ)..x, fm t) + ∫ t in (0 : ℝ)..x, (f1 t - fm t) := by
    rw [intervalIntegral.integral_sub hi1 hi2]; ring
  -- main part
  have hC : ‖∫ t in (0 : ℝ)..x, fm t‖ ≤
      S * ((Ma * (Ma * Mb)) + (Va * (Ma * Mb) + Ma * (Ma * Mb))) / (4 * ‖κ‖ ^ 2) := by
    have e : ∫ t in (0 : ℝ)..x, fm t =
        cc * (Complex.exp (-(Complex.I * κ * (x : ℂ))) *
          ∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * κ) * (t : ℂ)) *
            (pa t * ∫ s in (0 : ℝ)..t, pa s * pb s)) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      have hexpw : Complex.exp (-(Complex.I * κ * ((x - t : ℝ) : ℂ))) *
          Complex.exp (Complex.I * κ * (t : ℂ)) =
          Complex.exp (-(Complex.I * κ * (x : ℂ))) * Complex.exp ((2 * Complex.I * κ) * (t : ℂ)) := by
        rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
      simp only [hfm]
      linear_combination (cc * pa t * ∫ s in (0 : ℝ)..t, pa s * pb s) * hexpw
    rw [e, norm_mul]
    have hnn : 0 ≤ S * ((Ma * (Ma * Mb)) + (Va * (Ma * Mb) + Ma * (Ma * Mb))) / (2 * ‖κ‖) :=
      (norm_nonneg _).trans hmain
    calc ‖cc‖ * ‖Complex.exp (-(Complex.I * κ * (x : ℂ))) *
          ∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * κ) * (t : ℂ)) *
            (pa t * ∫ s in (0 : ℝ)..t, pa s * pb s)‖
        ≤ (1 / (2 * ‖κ‖)) * (S * ((Ma * (Ma * Mb)) + (Va * (Ma * Mb) + Ma * (Ma * Mb))) /
            (2 * ‖κ‖)) := mul_le_mul hcc hmain (norm_nonneg _) (by positivity)
      _ = S * ((Ma * (Ma * Mb)) + (Va * (Ma * Mb) + Ma * (Ma * Mb))) / (4 * ‖κ‖ ^ 2) := by
          field_simp; ring
  -- remainder part
  have hD : ‖∫ t in (0 : ℝ)..x, (f1 t - fm t)‖ ≤ S * (Ma * R) := by
    have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) x, ‖f1 t - fm t‖ ≤ S * (Ma * R) := by
      intro t ht
      rw [Set.uIoc_of_le hx0] at ht
      have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.trans hx.2⟩
      have hd : f1 t - fm t = Complex.exp (-(Complex.I * κ * ((x - t : ℝ) : ℂ))) * pa t * rem t := by
        simp only [hf1, hfm]
        rw [hdec t ht1]; ring
      rw [hd, norm_mul, norm_mul]
      have hw1 : ‖Complex.exp (-(Complex.I * κ * ((x - t : ℝ) : ℂ)))‖ ≤
          Real.exp (|κ.im| * (x - t)) := phase0_le κ (sub_nonneg.mpr ht.2)
      have hre : Real.exp (|κ.im| * (x - t)) * Real.exp (|κ.im| * t) = S := by
        rw [← Real.exp_add]; congr 1; ring
      calc ‖Complex.exp (-(Complex.I * κ * ((x - t : ℝ) : ℂ)))‖ * ‖pa t‖ * ‖rem t‖
          ≤ Real.exp (|κ.im| * (x - t)) * Ma * (R * Real.exp (|κ.im| * t)) :=
            mul_le_mul (mul_le_mul hw1 (hMa t ht1) (norm_nonneg _) (Real.exp_pos _).le)
              (hrem t ht1) (norm_nonneg _) (by positivity)
        _ = (Real.exp (|κ.im| * (x - t)) * Real.exp (|κ.im| * t)) * (Ma * R) := by ring
        _ = S * (Ma * R) := by rw [hre]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    refine h.trans ?_
    rw [sub_zero, abs_of_nonneg hx0]
    exact mul_le_of_le_one_right (mul_nonneg hS.le (mul_nonneg hMa0 hR0)) hx.2
  rw [hsplit]
  calc ‖(∫ t in (0 : ℝ)..x, fm t) + ∫ t in (0 : ℝ)..x, (f1 t - fm t)‖
      ≤ ‖∫ t in (0 : ℝ)..x, fm t‖ + ‖∫ t in (0 : ℝ)..x, (f1 t - fm t)‖ := norm_add_le _ _
    _ ≤ S * ((Ma * (Ma * Mb)) + (Va * (Ma * Mb) + Ma * (Ma * Mb))) / (4 * ‖κ‖ ^ 2) +
          S * (Ma * R) := add_le_add hC hD
    _ = S * ((2 * (Ma * Ma * Mb) + Va * (Ma * Mb)) / (4 * ‖κ‖ ^ 2) + Ma * R) := by ring

end NlsGge.ThirdConsultation.KSPS004Support
end
