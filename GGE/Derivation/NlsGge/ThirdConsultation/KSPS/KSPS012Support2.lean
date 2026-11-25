import Mathlib
import NlsGge.ThirdConsultation.KSPS.Perturbed008Support
import NlsGge.ThirdConsultation.KSPS.KSPS012Support1

/- KSPS-012 SUPPORT2 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS012Support2.lean.
   Bessel-type square summability of the double oscillatory integral
     T_n = int_0^1 e^{-2 i pi n t} c(t) (int_t^1 e^{2 i pi n s} g(s) ds) dt
   for c in L^2(0,1), g in L^1(0,1). Route: triangle Fubini (Support1), weighted Cauchy-Schwarz, and
   KSPS-008 Parseval (bco_sq_summable_le) at every upper limit s. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter

namespace NlsGge.ThirdConsultation.KSPS012Support2

/-- partial oscillatory integral `H_n(s) = int_0^s e^{-2 i pi n t} c(t) dt` -/
def Hn (c : ℝ → ℂ) (n : ℤ) (s : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..s, Complex.exp (-(2 * Real.pi * Complex.I * n * t)) * c t

theorem norm_bco_zero (c : ℝ → ℂ) (s : ℝ) (n : ℤ) :
    ‖NlsGge.ThirdConsultation.KSPS008Support.bco c s 0 n‖ = ‖Hn c n s‖ := by
  unfold NlsGge.ThirdConsultation.KSPS008Support.bco Hn
  have : ∀ t : ℝ, Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((s - 2 * t : ℝ) : ℂ)) *
      (((s - 2 * t : ℝ) : ℂ) ^ 0 * c t) =
      Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) *
        (Complex.exp (-(2 * Real.pi * Complex.I * n * t)) * c t) := by
    intro t
    simp only [pow_zero, one_mul]
    have e : Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * ((s - 2 * t : ℝ) : ℂ)) =
        Complex.exp (Complex.I * ((n : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) *
          Complex.exp (-(2 * Real.pi * Complex.I * n * t)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, norm_mul,
    NlsGge.ThirdConsultation.KSPS008Support.norm_phase, one_mul]

theorem Hn_continuousOn {c : ℝ → ℂ} (hc : IntervalIntegrable c volume 0 1) (n : ℤ) :
    ContinuousOn (Hn c n) (Set.Icc (0 : ℝ) 1) := by
  have hii : IntervalIntegrable (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * n * t)) * c t)
      volume 0 1 :=
    hc.continuousOn_mul (by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I * n * t))).continuousOn
  have hfU : IntegrableOn (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * n * t)) * c t)
      (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using
      (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hii
  have := intervalIntegral.continuousOn_primitive_interval hfU
  rw [Set.uIcc_of_le zero_le_one] at this
  exact this

theorem T_sq_summable {c g : ℝ → ℂ} (hcm : AEStronglyMeasurable c volume)
    (hc1 : IntervalIntegrable c volume 0 1)
    (hc2 : IntervalIntegrable (fun t => ‖c t‖ ^ 2) volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    Summable (fun n : ℤ => ‖∫ t in (0 : ℝ)..1,
      (Complex.exp (-(2 * Real.pi * Complex.I * n * t)) * c t) *
        ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * n * s) * g s‖ ^ 2) := by
  set A : ℝ := ∫ s in (0 : ℝ)..1, ‖g s‖ with hA
  set Cc : ℝ := ∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2 with hCc
  have hgn : IntervalIntegrable (fun s => ‖g s‖) volume 0 1 := hg.norm
  have hfi : ∀ n : ℤ, IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I * n * t)) * c t) volume 0 1 := fun n =>
    hc1.continuousOn_mul (by fun_prop : Continuous fun t : ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I * n * t))).continuousOn
  have hgi : ∀ n : ℤ, IntervalIntegrable
      (fun s : ℝ => Complex.exp (2 * Real.pi * Complex.I * n * s) * g s) volume 0 1 := fun n =>
    hg.continuousOn_mul (by fun_prop : Continuous fun s : ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * n * s)).continuousOn
  -- continuity of k_n = ‖H_n‖ on [0,1]
  have hk : ∀ n : ℤ, ContinuousOn (fun s => ‖Hn c n s‖) (Set.uIcc (0 : ℝ) 1) := fun n => by
    rw [Set.uIcc_of_le zero_le_one]
    exact (Hn_continuousOn hc1 n).norm
  have hk2 : ∀ n : ℤ, ContinuousOn (fun s => ‖Hn c n s‖ ^ 2) (Set.uIcc (0 : ℝ) 1) := fun n =>
    (hk n).pow 2
  have hIa : ∀ n : ℤ, IntervalIntegrable (fun s => ‖g s‖ * ‖Hn c n s‖) volume 0 1 := fun n =>
    hgn.mul_continuousOn (hk n)
  have hIa2 : ∀ n : ℤ, IntervalIntegrable (fun s => ‖g s‖ * ‖Hn c n s‖ ^ 2) volume 0 1 := fun n =>
    hgn.mul_continuousOn (hk2 n)
  -- single-index bound
  have hT : ∀ n : ℤ, ‖∫ t in (0 : ℝ)..1,
      (Complex.exp (-(2 * Real.pi * Complex.I * n * t)) * c t) *
        ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * n * s) * g s‖ ^ 2 ≤
      A * ∫ s in (0 : ℝ)..1, ‖g s‖ * ‖Hn c n s‖ ^ 2 := by
    intro n
    rw [NlsGge.ThirdConsultation.KSPS012Support1.fubini_tri (hfi n) (hgi n)]
    have h1 : ‖∫ s in (0 : ℝ)..1, (Complex.exp (2 * Real.pi * Complex.I * n * s) * g s) *
        ∫ t in (0 : ℝ)..s, Complex.exp (-(2 * Real.pi * Complex.I * n * t)) * c t‖ ≤
        ∫ s in (0 : ℝ)..1, ‖g s‖ * ‖Hn c n s‖ := by
      refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
      refine le_of_eq (intervalIntegral.integral_congr (fun s _ => ?_))
      show ‖(Complex.exp (2 * Real.pi * Complex.I * n * s) * g s) * Hn c n s‖ = _
      have hu : ‖Complex.exp (2 * Real.pi * Complex.I * n * s)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [norm_mul, norm_mul, hu, one_mul]
    have h2 := NlsGge.ThirdConsultation.KSPS012Support1.weighted_cs (a := fun s => ‖g s‖)
      (k := fun s => ‖Hn c n s‖) (fun t => norm_nonneg _) hgn (hIa n) (hIa2 n)
    calc _ ≤ (∫ s in (0 : ℝ)..1, ‖g s‖ * ‖Hn c n s‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  -- Bessel at every s
  have hB : ∀ (S : Finset ℤ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∑ n ∈ S, ‖Hn c n s‖ ^ 2 ≤ Cc := by
    intro S s hs
    have hb := NlsGge.ThirdConsultation.KSPS008Support.bco_sq_summable_le c hcm hc2 hs.1 hs.2 0
    calc ∑ n ∈ S, ‖Hn c n s‖ ^ 2
        = ∑ n ∈ S, ‖NlsGge.ThirdConsultation.KSPS008Support.bco c s 0 n‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [norm_bco_zero]
      _ ≤ ∑' n : ℤ, ‖NlsGge.ThirdConsultation.KSPS008Support.bco c s 0 n‖ ^ 2 :=
          hb.1.sum_le_tsum S (fun n _ => by positivity)
      _ ≤ Cc := hb.2
  refine summable_of_sum_le (c := A * (A * Cc)) (fun n => by positivity) (fun S => ?_)
  have hA0 : 0 ≤ A := intervalIntegral.integral_nonneg zero_le_one (fun t _ => norm_nonneg _)
  calc ∑ n ∈ S, ‖∫ t in (0 : ℝ)..1,
        (Complex.exp (-(2 * Real.pi * Complex.I * n * t)) * c t) *
          ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * n * s) * g s‖ ^ 2
      ≤ ∑ n ∈ S, A * ∫ s in (0 : ℝ)..1, ‖g s‖ * ‖Hn c n s‖ ^ 2 :=
        Finset.sum_le_sum (fun n _ => hT n)
    _ = A * ∫ s in (0 : ℝ)..1, ∑ n ∈ S, ‖g s‖ * ‖Hn c n s‖ ^ 2 := by
        rw [← Finset.mul_sum, intervalIntegral.integral_finset_sum (fun n _ => hIa2 n)]
    _ ≤ A * ∫ s in (0 : ℝ)..1, ‖g s‖ * Cc := by
        refine mul_le_mul_of_nonneg_left ?_ hA0
        have hsum : IntervalIntegrable (fun s => ∑ n ∈ S, ‖g s‖ * ‖Hn c n s‖ ^ 2) volume 0 1 := by
          have := IntervalIntegrable.sum S (fun n _ => hIa2 n)
          convert this using 1
          ext s
          simp [Finset.sum_apply]
        refine intervalIntegral.integral_mono_on zero_le_one hsum (hgn.mul_const _) (fun s hs => ?_)
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hB S s hs) (norm_nonneg _)
    _ = A * (A * Cc) := by
        rw [intervalIntegral.integral_mul_const]

end NlsGge.ThirdConsultation.KSPS012Support2
