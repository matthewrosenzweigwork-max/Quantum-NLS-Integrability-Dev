import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support7

/- KSPS012Q1 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/ThirdConsultation/KSPS/KSPS012Quant1.lean. Pro round-15 SUPPORT (never a packet).
   Finite-sum (explicit-constant) companions of KSPS012Support2.T_sq_summable and KSPS012Support7.Tz_sq_summable:
   the landed proof of T_sq_summable already bounds every finite sum by A·(A·Cc) (A = ∫₀¹‖g‖, Cc = ∫₀¹‖c‖²); here that
   bound is exported (body copied, final `summable_of_sum_le` step removed), and transported to Tz at σn·π.
   No hypothesis added. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS012Q1
open NlsGge.ThirdConsultation.KSPS012Support2

theorem T_sum_le {c g : ℝ → ℂ} (hcm : AEStronglyMeasurable c volume)
    (hc1 : IntervalIntegrable c volume 0 1)
    (hc2 : IntervalIntegrable (fun t => ‖c t‖ ^ 2) volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    ∀ S : Finset ℤ, ∑ n ∈ S, ‖∫ t in (0 : ℝ)..1,
      (Complex.exp (-(2 * Real.pi * Complex.I * n * t)) * c t) *
        ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * n * s) * g s‖ ^ 2 ≤
      (∫ s in (0 : ℝ)..1, ‖g s‖) * ((∫ s in (0 : ℝ)..1, ‖g s‖) * ∫ t in (0 : ℝ)..1, ‖c t‖ ^ 2) := by
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
  intro S
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

theorem Tz_sum_le (w v : PhysicalL2) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (F : Finset ℤ) :
    ∑ n ∈ F, ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz (coverRep38 w)
      (coverRep38 v) (((σ * n : ℤ) : ℂ) * (Real.pi : ℂ))‖ ^ 2 ≤
      (∫ s in (0 : ℝ)..1, ‖coverRep38 v s‖) * ((∫ s in (0 : ℝ)..1, ‖coverRep38 v s‖) *
        ∫ t in (0 : ℝ)..1, ‖coverRep38 w t‖ ^ 2) := by
  have h := T_sum_le (c := coverRep38 w)
    (g := coverRep38 v) (stronglyMeasurable_coverRep38 w).aestronglyMeasurable
    (intervalIntegrable_coverRep38_one w) (intervalIntegrable_coverRep38_sq_one w)
    (intervalIntegrable_coverRep38_one v)
  have hk : ∀ k : ℤ, NlsGge.ThirdConsultation.KSPS012Support5.Tz (coverRep38 w) (coverRep38 v)
      ((k : ℂ) * (Real.pi : ℂ)) = ∫ t in (0 : ℝ)..1,
        (Complex.exp (-(2 * Real.pi * Complex.I * k * t)) * coverRep38 w t) *
          ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * k * s) * coverRep38 v s := by
    intro k
    unfold NlsGge.ThirdConsultation.KSPS012Support5.Tz
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    beta_reduce
    have e1 : Complex.exp (-(2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (t : ℂ))) =
        Complex.exp (-(2 * Real.pi * Complex.I * k * t)) := by congr 1; ring
    have e2 : ∫ s in t..1, Complex.exp (2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) *
          coverRep38 v s =
        ∫ s in t..1, Complex.exp (2 * Real.pi * Complex.I * k * s) * coverRep38 v s := by
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      beta_reduce
      have : Complex.exp (2 * Complex.I * ((k : ℂ) * (Real.pi : ℂ)) * (s : ℂ)) =
          Complex.exp (2 * Real.pi * Complex.I * k * s) := by congr 1; ring
      rw [this]
    rw [e1, e2]
  have hS : ∀ S : Finset ℤ, ∑ k ∈ S, ‖NlsGge.ThirdConsultation.KSPS012Support5.Tz (coverRep38 w)
      (coverRep38 v) ((k : ℂ) * (Real.pi : ℂ))‖ ^ 2 ≤
      (∫ s in (0 : ℝ)..1, ‖coverRep38 v s‖) * ((∫ s in (0 : ℝ)..1, ‖coverRep38 v s‖) *
        ∫ t in (0 : ℝ)..1, ‖coverRep38 w t‖ ^ 2) := by
    intro S
    refine le_trans (le_of_eq ?_) (h S)
    exact Finset.sum_congr rfl (fun k _ => by rw [hk k])
  have hinj : Set.InjOn (fun n : ℤ => σ * n) F := by
    intro x _ y _ hxy
    rcases hσ with rfl | rfl <;> simp at hxy <;> exact hxy
  refine le_trans (le_of_eq ?_) (hS (F.image (fun n => σ * n)))
  rw [Finset.sum_image hinj]

end NlsGge.ThirdConsultation.KSPS012Q1
