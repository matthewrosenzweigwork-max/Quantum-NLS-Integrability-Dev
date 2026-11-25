import Mathlib
import NlsGge.Spectral.ComplexACPointwiseTestIntegrationByPartsV2

                                                                                                      
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter

namespace NlsGge.ThirdConsultation.KSPS003Support

/-- `f` is the primitive of the interval-integrable `g` on `[0,1]`. -/
def PrimOn (f g : ℝ → ℂ) : Prop :=
  IntervalIntegrable g volume 0 1 ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = f 0 + ∫ s in (0 : ℝ)..t, g s

theorem uIcc_sub {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Set.uIcc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) 1 := by
  rw [Set.uIcc_of_le hx.1]
  exact Set.Icc_subset_Icc le_rfl hx.2

theorem ii_mono {g : ℝ → ℂ} (h : IntervalIntegrable g volume 0 1) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : IntervalIntegrable g volume 0 x := by
  refine h.mono_set ?_
  rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le (by norm_num)]
  exact Set.Icc_subset_Icc le_rfl hx.2

theorem primOn_ac {f g : ℝ → ℂ} (h : PrimOn f g) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval f 0 x := by
  have hIx := ii_mono h.1 hx
  have hprimx : ∀ t ∈ Set.uIcc (0 : ℝ) x, f t = f 0 + ∫ s in (0 : ℝ)..t, g s :=
    fun t ht => h.2 t (uIcc_sub hx ht)
  have hp := NlsGge.SpectralFoundations.complex_intervalIntegral_primitive_absolutelyContinuousV2
    hIx (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) x)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f 0) 0 x :=
    (contDiffOn_const (c := f 0) (n := 1) (s := Set.uIcc (0 : ℝ) x)).absolutelyContinuousOnInterval
  have hs := hc.add hp
  exact hs.congr (fun t ht => (hprimx t ht).symm)

theorem primOn_continuousOn {f g : ℝ → ℂ} (h : PrimOn f g) : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
  have := (primOn_ac h (x := 1) ⟨zero_le_one, le_rfl⟩).continuousOn
  rwa [Set.uIcc_of_le zero_le_one] at this

theorem primOn_hasDerivAt_ae {f g : ℝ → ℂ} (h : PrimOn f g) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) x → HasDerivAt f (g t) t := by
  have hIx := ii_mono h.1 hx
  have hprimx : ∀ t ∈ Set.uIcc (0 : ℝ) x, f t = f 0 + ∫ s in (0 : ℝ)..t, g s :=
    fun t ht => h.2 t (uIcc_sub hx ht)
  have h0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by simp [ae_iff, measure_singleton]
  have h1 : ∀ᵐ y : ℝ ∂volume, y ≠ x := by simp [ae_iff, measure_singleton]
  filter_upwards [hIx.ae_hasDerivAt_integral, h0, h1] with y hy hy0 hy1 hmem
  have hd := (hy hmem 0 (Set.left_mem_uIcc : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) x)).const_add (f 0)
  refine hd.congr_of_eventuallyEq ?_
  rw [Set.uIcc_of_le hx.1] at hmem
  have hmem' : y ∈ Set.Ioo (0 : ℝ) x :=
    ⟨lt_of_le_of_ne hmem.1 (Ne.symm hy0), lt_of_le_of_ne hmem.2 hy1⟩
  filter_upwards [Ioo_mem_nhds hmem'.1 hmem'.2] with z hz
  exact hprimx z (by rw [Set.uIcc_of_le hx.1]; exact ⟨hz.1.le, hz.2.le⟩)

theorem primOn_mul {f1 g1 f2 g2 : ℝ → ℂ} (h1 : PrimOn f1 g1) (h2 : PrimOn f2 g2) :
    PrimOn (fun t => f1 t * f2 t) (fun t => g1 t * f2 t + f1 t * g2 t) := by
  have hc1 := primOn_continuousOn h1
  have hc2 := primOn_continuousOn h2
  have hU : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le zero_le_one
  refine ⟨?_, ?_⟩
  · refine (h1.1.mul_continuousOn (by rwa [hU])).add (h2.1.continuousOn_mul (by rwa [hU]))
  · intro t ht
    have hsub := uIcc_sub ht
    have hI1 := ii_mono h1.1 ht
    have hI2 := ii_mono h2.1 ht
    have hac1 := primOn_ac h1 ht
    have hac2 := primOn_ac h2 ht
    have hprod : AbsolutelyContinuousOnInterval (fun s => f1 s * f2 s) 0 t := by
      simpa only [Pi.smul_apply, smul_eq_mul] using! hac1.smul hac2
    have hint : IntervalIntegrable (fun s => g1 s * f2 s + f1 s * g2 s) volume 0 t :=
      (hI1.mul_continuousOn (hc2.mono hsub)).add (hI2.continuousOn_mul (hc1.mono hsub))
    have hder : ∀ᵐ s ∂volume, s ∈ Set.uIcc (0 : ℝ) t →
        HasDerivAt (fun r => f1 r * f2 r) (g1 s * f2 s + f1 s * g2 s) s := by
      filter_upwards [primOn_hasDerivAt_ae h1 ht, primOn_hasDerivAt_ae h2 ht] with s hs1 hs2 hmem
      exact (hs1 hmem).mul (hs2 hmem)
    exact NlsGge.SpectralFoundations.complex_absolutelyContinuous_eq_initial_add_integral_of_ae_hasDerivAt
      hprod hint hder t Set.right_mem_uIcc

theorem primOn_exp (c : ℂ) : PrimOn (fun t : ℝ => Complex.exp (c * (t : ℂ)))
    (fun t : ℝ => c * Complex.exp (c * (t : ℂ))) := by
  refine ⟨Continuous.intervalIntegrable (by fun_prop) _ _, fun t _ => ?_⟩
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) t, HasDerivAt (fun r : ℝ => Complex.exp (c * (r : ℂ)))
      (c * Complex.exp (c * (s : ℂ))) s := by
    intro s _
    have h1 : HasDerivAt (fun r : ℝ => c * (r : ℂ)) c s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul c
    have h2 := h1.cexp
    convert h2 using 1
    ring
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [this]
  simp

theorem primOn_integral {g : ℝ → ℂ} (hg : IntervalIntegrable g volume 0 1) :
    PrimOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s) g := by
  refine ⟨hg, fun t _ => ?_⟩
  simp

theorem ibp_exp {f g : ℝ → ℂ} (h : PrimOn f g) (ν : ℂ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ν * ∫ s in (0 : ℝ)..t, Complex.exp (ν * (s : ℂ)) * f s =
      Complex.exp (ν * (t : ℂ)) * f t - f 0 -
        ∫ s in (0 : ℝ)..t, Complex.exp (ν * (s : ℂ)) * g s := by
  have hm := (primOn_mul (primOn_exp ν) h).2 t ht
  have hsub := uIcc_sub ht
  have hc := primOn_continuousOn h
  have hI := ii_mono h.1 ht
  have hi1 : IntervalIntegrable (fun s : ℝ => ν * Complex.exp (ν * (s : ℂ)) * f s) volume 0 t :=
    ContinuousOn.intervalIntegrable
      ((by fun_prop : Continuous fun s : ℝ => ν * Complex.exp (ν * (s : ℂ))).continuousOn.mul
        (hc.mono hsub))
  have hi2 : IntervalIntegrable (fun s : ℝ => Complex.exp (ν * (s : ℂ)) * g s) volume 0 t :=
    hI.continuousOn_mul (by fun_prop : Continuous fun s : ℝ => Complex.exp (ν * (s : ℂ))).continuousOn
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hm
  rw [intervalIntegral.integral_add hi1 hi2] at hm
  have e1 : ∫ s in (0 : ℝ)..t, ν * Complex.exp (ν * (s : ℂ)) * f s =
      ν * ∫ s in (0 : ℝ)..t, Complex.exp (ν * (s : ℂ)) * f s := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  rw [e1] at hm
  linear_combination -hm

theorem remainder_identity {p p' q q' : ℝ → ℂ} (hp : PrimOn p p') (hq : PrimOn q q')
    {c : ℂ} (hc : c ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    c ^ 2 * ((∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p t *
        ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q s) +
      c⁻¹ * ∫ t in (0 : ℝ)..x, p t * q t) =
    q 0 * (Complex.exp (c * (x : ℂ)) * p x - p 0 -
        ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t) +
      (Complex.exp (c * (x : ℂ)) * p x * (∫ s in (0 : ℝ)..x, Complex.exp (-c * (s : ℂ)) * q' s)
        - (∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t *
            ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s)
        - ∫ t in (0 : ℝ)..x, p t * q' t) := by
  have hsub := uIcc_sub hx
  have hcp := primOn_continuousOn hp
  have hcq := primOn_continuousOn hq
  have hIp := ii_mono hp.1 hx
  have hIq := ii_mono hq.1 hx
  have hexpc : Continuous fun t : ℝ => Complex.exp (c * (t : ℂ)) := by fun_prop
  have hexpn : Continuous fun t : ℝ => Complex.exp (-c * (t : ℂ)) := by fun_prop
  have hgL : IntervalIntegrable (fun s : ℝ => Complex.exp (-c * (s : ℂ)) * q' s) volume 0 1 :=
    hq.1.continuousOn_mul hexpn.continuousOn
  have hLp : PrimOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s)
      (fun s : ℝ => Complex.exp (-c * (s : ℂ)) * q' s) := primOn_integral hgL
  have hcL := primOn_continuousOn hLp
  have hE : ∀ t : ℝ, Complex.exp (c * (t : ℂ)) * Complex.exp (-c * (t : ℂ)) = 1 := fun t => by
    rw [← Complex.exp_add, show c * (t : ℂ) + -c * (t : ℂ) = 0 by ring, Complex.exp_zero]
  have hinv : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  -- integrability facts on [0,x]
  have hi_ep : IntervalIntegrable (fun t : ℝ => Complex.exp (c * (t : ℂ)) * p t) volume 0 x :=
    ContinuousOn.intervalIntegrable (hexpc.continuousOn.mul (hcp.mono hsub))
  have hi_epL : IntervalIntegrable (fun t : ℝ => Complex.exp (c * (t : ℂ)) * p t *
      ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s) volume 0 x :=
    ContinuousOn.intervalIntegrable ((hexpc.continuousOn.mul (hcp.mono hsub)).mul (hcL.mono hsub))
  have hi_pq : IntervalIntegrable (fun t : ℝ => p t * q t) volume 0 x :=
    ContinuousOn.intervalIntegrable ((hcp.mono hsub).mul (hcq.mono hsub))
  have hi_pq' : IntervalIntegrable (fun t : ℝ => p t * q' t) volume 0 x :=
    hIq.continuousOn_mul (hcp.mono hsub)
  have hi_ep'L : IntervalIntegrable (fun t : ℝ => Complex.exp (c * (t : ℂ)) * p' t *
      ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s) volume 0 x :=
    (hIp.continuousOn_mul hexpc.continuousOn).mul_continuousOn (hcL.mono hsub)
  -- (b) c * D
  have hD : c * (∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p t *
        ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q s) =
      q 0 * (∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p t) +
        (∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p t *
          ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s) -
        ∫ t in (0 : ℝ)..x, p t * q t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hi_ep.const_mul (q 0)) hi_epL,
      ← intervalIntegral.integral_sub ((hi_ep.const_mul (q 0)).add hi_epL) hi_pq]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    have h := ibp_exp hq (-c) (hsub ht)
    linear_combination (-(Complex.exp (c * (t : ℂ)) * p t)) * h + (-(p t * q t)) * hE t
  have hH := ibp_exp hp c hx
  have hW : c * (∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p t *
          ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s) =
      Complex.exp (c * (x : ℂ)) * p x * (∫ s in (0 : ℝ)..x, Complex.exp (-c * (s : ℂ)) * q' s)
        - (∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t *
            ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s)
        - ∫ t in (0 : ℝ)..x, p t * q' t := by
    have hm := (primOn_mul (primOn_mul (primOn_exp c) hp) hLp).2 x hx
    beta_reduce at hm
    have hpt : ∀ t ∈ Set.uIcc (0 : ℝ) x,
        ((c * Complex.exp (c * (t : ℂ)) * p t + Complex.exp (c * (t : ℂ)) * p' t) *
            (∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s) +
          Complex.exp (c * (t : ℂ)) * p t * (Complex.exp (-c * (t : ℂ)) * q' t)) =
        c * (Complex.exp (c * (t : ℂ)) * p t *
            ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s) +
          Complex.exp (c * (t : ℂ)) * p' t *
            (∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s) +
          p t * q' t := by
      intro t _
      linear_combination (p t * q' t) * hE t
    rw [intervalIntegral.integral_congr hpt,
      intervalIntegral.integral_add (hi_epL.const_mul c |>.add hi_ep'L) hi_pq',
      intervalIntegral.integral_add (hi_epL.const_mul c) hi_ep'L,
      intervalIntegral.integral_const_mul] at hm
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
      intervalIntegral.integral_same, mul_zero] at hm
    linear_combination -hm
  linear_combination c * hD + q 0 * hH + hW +
    (c * ∫ t in (0 : ℝ)..x, p t * q t) * hinv

theorem phase_le {lam c : ℂ} (hc : c = 2 * Complex.I * lam) {x r : ℝ} (h0 : 0 ≤ r)
    (h1 : r ≤ x) :
    ‖Complex.exp (-(Complex.I * lam * (x : ℂ))) * Complex.exp (c * (r : ℂ))‖ ≤
      Real.exp (|lam.im| * x) := by
  subst hc
  rw [← Complex.exp_add, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre : (-(Complex.I * lam * (x : ℂ)) + 2 * Complex.I * lam * (r : ℂ)).re =
      lam.im * (x - 2 * r) := by
    simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [hre]
  have h2 : |x - 2 * r| ≤ x := by rw [abs_le]; constructor <;> linarith
  calc lam.im * (x - 2 * r) ≤ |lam.im * (x - 2 * r)| := le_abs_self _
    _ = |lam.im| * |x - 2 * r| := abs_mul _ _
    _ ≤ |lam.im| * x := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

theorem phase0_le (lam : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp (-(Complex.I * lam * (x : ℂ)))‖ ≤ Real.exp (|lam.im| * x) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have : (-(Complex.I * lam * (x : ℂ))).re = lam.im * x := by
    simp [Complex.mul_re, Complex.mul_im] <;> ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (le_abs_self _) hx

theorem phase_le' {lam c : ℂ} (hc : c = 2 * Complex.I * lam) {x t s : ℝ} (hs0 : 0 ≤ s)
    (hst : s ≤ t) (htx : t ≤ x) :
    ‖Complex.exp (-(Complex.I * lam * (x : ℂ))) *
      (Complex.exp (c * (t : ℂ)) * Complex.exp (-c * (s : ℂ)))‖ ≤ Real.exp (|lam.im| * x) := by
  have h := phase_le hc (x := x) (r := t - s) (by linarith) (by linarith)
  have e : Complex.exp (c * (t : ℂ)) * Complex.exp (-c * (s : ℂ)) =
      Complex.exp (c * ((t - s : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]
  exact h

theorem norm_int_mul_le {w k : ℝ → ℂ} {x B : ℝ} (hx0 : 0 ≤ x)
    (hw : ∀ t ∈ Set.Icc (0 : ℝ) x, ‖w t‖ ≤ B) (hk : IntervalIntegrable k volume 0 x) :
    ‖∫ t in (0 : ℝ)..x, w t * k t‖ ≤ B * ∫ t in (0 : ℝ)..x, ‖k t‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le hx0
    (f := fun t => w t * k t) (g := fun t => B * ‖k t‖)
    (Filter.Eventually.of_forall (fun t ht => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hw t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)))
    (hk.norm.const_mul B)
  rwa [intervalIntegral.integral_const_mul] at h

theorem int_norm_mono {g : ℝ → ℂ} (h : IntervalIntegrable g volume 0 1) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ t in (0 : ℝ)..x, ‖g t‖ ≤ ∫ t in (0 : ℝ)..1, ‖g t‖ :=
  intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
    (Filter.Eventually.of_forall fun t => norm_nonneg _) h.norm

theorem norm_aux (E X N c : ℂ) (hid : c ^ 2 * X = N) (B : ℝ) (hc : c ≠ 0)
    (h : ‖E * N‖ ≤ B) : ‖E * X‖ ≤ B / ‖c‖ ^ 2 := by
  have hpos : 0 < ‖c‖ ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  calc ‖E * X‖ * ‖c‖ ^ 2 = ‖E * (c ^ 2 * X)‖ := by
        simp only [norm_mul, norm_pow]; ring
    _ = ‖E * N‖ := by rw [hid]
    _ ≤ B := h

theorem norm_six (a b c d e f : ℂ) :
    ‖a - b - c + (d - e - f)‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + (‖d‖ + ‖e‖ + ‖f‖) := by
  have h1 := norm_sub_le (a - b) c
  have h2 := norm_sub_le a b
  have h3 := norm_sub_le (d - e) f
  have h4 := norm_sub_le d e
  have h5 := norm_add_le (a - b - c) (d - e - f)
  linarith

theorem remainder_bound {p p' q q' : ℝ → ℂ} (hp : PrimOn p p') (hq : PrimOn q q')
    {Mp Vp Mq Vq : ℝ}
    (hMp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖p t‖ ≤ Mp) (hVp : ∫ t in (0 : ℝ)..1, ‖p' t‖ ≤ Vp)
    (hMq : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖q t‖ ≤ Mq) (hVq : ∫ t in (0 : ℝ)..1, ‖q' t‖ ≤ Vq)
    {lam : ℂ} (hlam : lam ≠ 0) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖Complex.exp (-(Complex.I * lam * (x : ℂ))) *
      ((∫ t in (0 : ℝ)..x, Complex.exp ((2 * Complex.I * lam) * (t : ℂ)) * p t *
          ∫ s in (0 : ℝ)..t, Complex.exp (-(2 * Complex.I * lam) * (s : ℂ)) * q s) +
        (2 * Complex.I * lam)⁻¹ * ∫ t in (0 : ℝ)..x, p t * q t)‖ ≤
      2 * Real.exp (|lam.im| * x) * ((Mp + Vp) * (Mq + Vq)) / ‖2 * Complex.I * lam‖ ^ 2 := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = 2 * Complex.I * lam := ⟨_, rfl⟩
  rw [← hcdef]
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hlam
  have hid := remainder_identity hp hq hc0 hx
  have hsub := uIcc_sub hx
  have hIp := ii_mono hp.1 hx
  have hIq := ii_mono hq.1 hx
  have hS : 0 < Real.exp (|lam.im| * x) := Real.exp_pos _
  have hMp0 : 0 ≤ Mp := (norm_nonneg _).trans (hMp 0 ⟨le_rfl, zero_le_one⟩)
  have hMq0 : 0 ≤ Mq := (norm_nonneg _).trans (hMq 0 ⟨le_rfl, zero_le_one⟩)
  have hVp0 : 0 ≤ Vp := le_trans (intervalIntegral.integral_nonneg zero_le_one
    (fun t _ => norm_nonneg _)) hVp
  have hVq0 : 0 ≤ Vq := le_trans (intervalIntegral.integral_nonneg zero_le_one
    (fun t _ => norm_nonneg _)) hVq
  have hx0 : 0 ≤ x := hx.1
  set E : ℂ := Complex.exp (-(Complex.I * lam * (x : ℂ))) with hE
  set S : ℝ := Real.exp (|lam.im| * x) with hSdef
  have hEn : ‖E‖ ≤ S := phase0_le lam hx0
  have hEc : ‖E * Complex.exp (c * (x : ℂ))‖ ≤ S := phase_le hcdef hx0 le_rfl
  -- K
  have hK : ‖E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t‖ ≤ S * Vp := by
    have e : E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t =
        ∫ t in (0 : ℝ)..x, (E * Complex.exp (c * (t : ℂ))) * p' t := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun t _ => by ring)
    rw [e]
    refine (norm_int_mul_le hx0 (fun t ht => phase_le hcdef ht.1 ht.2) hIp).trans ?_
    exact mul_le_mul_of_nonneg_left ((int_norm_mono hp.1 hx).trans hVp) hS.le
  -- inner L bound
  have hLt : ∀ t ∈ Set.Icc (0 : ℝ) x,
      ‖E * Complex.exp (c * (t : ℂ)) * ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s‖ ≤
        S * Vq := by
    intro t ht
    have ht1 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
    have hIt := ii_mono hq.1 ht1
    have e : E * Complex.exp (c * (t : ℂ)) * ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s =
        ∫ s in (0 : ℝ)..t, (E * (Complex.exp (c * (t : ℂ)) * Complex.exp (-c * (s : ℂ)))) * q' s := by
      rw [mul_assoc, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun s _ => by ring)
    rw [e]
    refine (norm_int_mul_le ht.1 (fun s hs => phase_le' hcdef hs.1 hs.2 ht.2) hIt).trans ?_
    exact mul_le_mul_of_nonneg_left ((int_norm_mono hq.1 ht1).trans hVq) hS.le
  -- L at x
  have hLx : ‖E * Complex.exp (c * (x : ℂ)) * ∫ s in (0 : ℝ)..x, Complex.exp (-c * (s : ℂ)) * q' s‖ ≤
      S * Vq := hLt x ⟨hx0, le_rfl⟩
  -- W'
  have hW : ‖E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t *
      ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s‖ ≤ S * Vq * Vp := by
    have e : E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t *
        ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s =
        ∫ t in (0 : ℝ)..x, (E * Complex.exp (c * (t : ℂ)) *
          ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s) * p' t := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun t _ => by ring)
    rw [e]
    refine (norm_int_mul_le hx0 hLt hIp).trans ?_
    exact mul_le_mul_of_nonneg_left ((int_norm_mono hp.1 hx).trans hVp) (mul_nonneg hS.le hVq0)
  -- p q'
  have hPQ : ‖∫ t in (0 : ℝ)..x, p t * q' t‖ ≤ Mp * Vq := by
    refine (norm_int_mul_le hx0 (fun t ht => hMp t ⟨ht.1, ht.2.trans hx.2⟩) hIq).trans ?_
    exact mul_le_mul_of_nonneg_left ((int_norm_mono hq.1 hx).trans hVq) hMp0
  have hp0 : ‖p 0‖ ≤ Mp := hMp 0 ⟨le_rfl, zero_le_one⟩
  have hq0 : ‖q 0‖ ≤ Mq := hMq 0 ⟨le_rfl, zero_le_one⟩
  have hpx : ‖p x‖ ≤ Mp := hMp x hx
  -- assemble
  have hEN : E * (q 0 * (Complex.exp (c * (x : ℂ)) * p x - p 0 -
        ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t) +
      (Complex.exp (c * (x : ℂ)) * p x * (∫ s in (0 : ℝ)..x, Complex.exp (-c * (s : ℂ)) * q' s)
        - (∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t *
            ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s)
        - ∫ t in (0 : ℝ)..x, p t * q' t)) =
      (q 0 * (E * Complex.exp (c * (x : ℂ))) * p x) - (q 0 * p 0 * E) -
        (q 0 * (E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t)) +
      ((p x * (E * Complex.exp (c * (x : ℂ)) *
          ∫ s in (0 : ℝ)..x, Complex.exp (-c * (s : ℂ)) * q' s)) -
        (E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t *
          ∫ s in (0 : ℝ)..t, Complex.exp (-c * (s : ℂ)) * q' s) -
        (E * ∫ t in (0 : ℝ)..x, p t * q' t)) := by ring
  have hb1 : ‖q 0 * (E * Complex.exp (c * (x : ℂ))) * p x‖ ≤ Mq * S * Mp := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul hq0 hEc (norm_nonneg _) hMq0) hpx (norm_nonneg _)
      (mul_nonneg hMq0 hS.le)
  have hb2 : ‖q 0 * p 0 * E‖ ≤ Mq * Mp * S := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul hq0 hp0 (norm_nonneg _) hMq0) hEn (norm_nonneg _)
      (mul_nonneg hMq0 hMp0)
  have hb3 : ‖q 0 * (E * ∫ t in (0 : ℝ)..x, Complex.exp (c * (t : ℂ)) * p' t)‖ ≤ Mq * (S * Vp) := by
    rw [norm_mul]
    exact mul_le_mul hq0 hK (norm_nonneg _) hMq0
  have hb4 : ‖p x * (E * Complex.exp (c * (x : ℂ)) *
      ∫ s in (0 : ℝ)..x, Complex.exp (-c * (s : ℂ)) * q' s)‖ ≤ Mp * (S * Vq) := by
    rw [norm_mul]
    exact mul_le_mul hpx hLx (norm_nonneg _) hMp0
  have hb6 : ‖E * ∫ t in (0 : ℝ)..x, p t * q' t‖ ≤ S * (Mp * Vq) := by
    rw [norm_mul]
    exact mul_le_mul hEn hPQ (norm_nonneg _) hS.le
  refine norm_aux E _ _ c hid _ hc0 ?_
  rw [hEN]
  refine (norm_six _ _ _ _ _ _).trans ?_
  nlinarith [mul_nonneg hS.le (mul_nonneg hMq0 hVp0), mul_nonneg hS.le (mul_nonneg hVq0 hVp0),
    mul_nonneg hS.le (mul_nonneg hMp0 hMq0), mul_nonneg hS.le (mul_nonneg hMp0 hVq0)]

end NlsGge.ThirdConsultation.KSPS003Support
end
