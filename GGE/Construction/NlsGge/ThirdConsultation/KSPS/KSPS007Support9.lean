import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.ThirdConsultation.KSPS.KSPS007Support
import NlsGge.ThirdConsultation.KSPS.KSPS007Support4
import NlsGge.ThirdConsultation.KSPS.KSPS007Support5
import NlsGge.ThirdConsultation.KSPS.KSPS007Support6
import NlsGge.ThirdConsultation.KSPS.KSPS007Support7
import NlsGge.ThirdConsultation.KSPS.KSPS007Support8

                                                                                                                     
                                                                                                                  
                                                                                                       
                                                                                                              
                                
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.Atomic.G1011S2
open NlsGge.ThirdConsultation.KSPS007Support5
open scoped Matrix

namespace NlsGge.ThirdConsultation.KSPS007Support9

open NlsGge.ThirdConsultation.KSPS007Support6 NlsGge.ThirdConsultation.KSPS007Support7

theorem integrateVector_eq (F : ℝ → Fin 2 → ℂ) {x : ℝ} (hx : 0 ≤ x)
    (h : ∀ i, IntervalIntegrable (fun t => F t i) volume 0 x) :
    KSPSVolterra.integrateVector 0 x F = ∫ t in (0 : ℝ)..x, F t := by
  funext i
  exact (ivInt_apply hx h i).symm

theorem iv_Ig (f : PotPair) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {A : ℝ → Mt} (hA : Good A)
    (F : ℝ → Fin 2 → ℂ) (hF : ∀ t, F t = (A t).mulVec (KSPSVolterra.forcingValue f t)) :
    KSPSVolterra.integrateVector 0 x F = Ig f x A := by
  have h := integrateVector_eq F hx.1 (fun i => by
    have : (fun t => F t i) = fun t => ((A t).mulVec (KSPSVolterra.forcingValue f t)) i := by
      funext t; rw [hF t]
    rw [this]; exact hA.mulVec_ii f i hx)
  rw [h]
  unfold Ig
  exact intervalIntegral.integral_congr (fun t _ => hF t)

/-- the data entering the identity (all at fixed `phi`, `lam`, `x`) -/
theorem leading_eq (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    KSPSVolterra.forcingLeading φ lam f x =
      -Ig f x (fun t => KSPSVolterra.R * KSPSVolterra.E lam (x - t)) := by
  unfold KSPSVolterra.forcingLeading
  rw [iv_Ig f hx ((Good.const KSPSVolterra.R).mul (Good_E lam x))
    (fun t => KSPSVolterra.R *ᵥ (KSPSVolterra.E lam (x - t) *ᵥ KSPSVolterra.forcingValue f t))
    (fun t => by simp only [Matrix.mulVec_mulVec])]

theorem B1_eq (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    KSPSVolterra.forcingB1 φ lam f x =
      -(2 * lam) • Ig f x (fun t => KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) *
        (KSPSVolterra.R * KSPSVolterra.E lam (-t))) := by
  unfold KSPSVolterra.forcingB1
  have h1 : KSPSVolterra.integrateVector 0 x (fun t => KSPSVolterra.E lam (-t) *ᵥ KSPSVolterra.forcingValue f t) =
      Ig f x (fun t => KSPSVolterra.E lam (-t)) := iv_Ig f hx (Good_Eneg lam) _ (fun t => rfl)
  rw [h1, ← Ig_mul_left f hx KSPSVolterra.R (Good_Eneg lam), 
    ← Ig_mul_left f hx (KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ))
      ((Good.const KSPSVolterra.R).mul (Good_Eneg lam))]

theorem B2_eq (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    KSPSVolterra.forcingB2 φ lam f x =
      Ig f x (fun t => KSPSVolterra.integratedQuadratic φ x * KSPSVolterra.E lam (x - t)) := by
  unfold KSPSVolterra.forcingB2
  rw [iv_Ig f hx (Good_E lam x) _ (fun t => rfl), ← Ig_mul_left f hx _ (Good_E lam x)]

theorem B3_eq (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    KSPSVolterra.forcingB3 φ lam f x =
      Ig f x (fun t => KSPSVolterra.E lam x *
        ((2 * lam) • (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) * KSPSVolterra.R))) := by
  unfold KSPSVolterra.forcingB3
  have hG : Good (fun t => (2 * lam) • (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) * KSPSVolterra.R)) :=
    ((Good_M1 φ lam).mul (Good.const KSPSVolterra.R)).smul (2 * lam)
  rw [iv_Ig f hx hG (fun t => (2 * lam) • (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) *ᵥ
      (KSPSVolterra.R *ᵥ KSPSVolterra.forcingValue f t))) (fun t => by
    simp only [Matrix.smul_mulVec, Matrix.mulVec_mulVec]), ← Ig_mul_left f hx _ hG]

theorem B4_eq (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    KSPSVolterra.forcingB4 φ lam f x =
      -Ig f x (fun t => KSPSVolterra.E lam (x - t) * KSPSVolterra.integratedQuadratic φ t) := by
  unfold KSPSVolterra.forcingB4
  rw [iv_Ig f hx ((Good_E lam x).mul (Good_Q φ)) (fun t => KSPSVolterra.E lam (x - t) *ᵥ
      (KSPSVolterra.integratedQuadratic φ t *ᵥ KSPSVolterra.forcingValue f t)) (fun t => by
    simp only [Matrix.mulVec_mulVec])]

theorem first_corr_eq (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    KSPSVolterra.forcingFirstCorrection φ lam f x =
      Ig f x (fun t => (2 * lam)⁻¹ •
        (-(2 * lam) • (KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) *
              (KSPSVolterra.R * KSPSVolterra.E lam (-t))) +
          KSPSVolterra.integratedQuadratic φ x * KSPSVolterra.E lam (x - t) +
          KSPSVolterra.E lam x *
            ((2 * lam) • (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) * KSPSVolterra.R)) -
          KSPSVolterra.E lam (x - t) * KSPSVolterra.integratedQuadratic φ t)) := by
  have hG1 : Good (fun t => KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) *
      (KSPSVolterra.R * KSPSVolterra.E lam (-t))) :=
    (Good.const _).mul ((Good.const KSPSVolterra.R).mul (Good_Eneg lam))
  have hG2 : Good (fun t => KSPSVolterra.integratedQuadratic φ x * KSPSVolterra.E lam (x - t)) :=
    (Good.const _).mul (Good_E lam x)
  have hG3 : Good (fun t => KSPSVolterra.E lam x *
      ((2 * lam) • (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) * KSPSVolterra.R))) :=
    (Good.const _).mul (((Good_M1 φ lam).mul (Good.const KSPSVolterra.R)).smul _)
  have hG4 : Good (fun t => KSPSVolterra.E lam (x - t) * KSPSVolterra.integratedQuadratic φ t) :=
    (Good_E lam x).mul (Good_Q φ)
  rw [Ig_smul, Ig_sub f hx (((hG1.smul (-(2 * lam))).add hG2).add hG3) hG4,
    Ig_add f hx ((hG1.smul (-(2 * lam))).add hG2) hG3, Ig_add f hx (hG1.smul (-(2 * lam))) hG2,
    Ig_smul]
  unfold KSPSVolterra.forcingFirstCorrection
  rw [B1_eq φ lam f hx, B2_eq φ lam f hx, B3_eq φ lam f hx, B4_eq φ lam f hx]
  rw [sub_eq_add_neg]

/-- The matrix function whose `Ig` is `F x - leading - first correction`. -/
def Theta (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (x t : ℝ) : Mt :=
  -(KSPSVolterra.fundamental φ x lam * (KSPSVolterra.inverseFundamental φ t lam * KSPSVolterra.R)) +
    KSPSVolterra.R * KSPSVolterra.E lam (x - t) -
    (2 * lam)⁻¹ •
        (-(2 * lam) • (KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) *
              (KSPSVolterra.R * KSPSVolterra.E lam (-t))) +
          KSPSVolterra.integratedQuadratic φ x * KSPSVolterra.E lam (x - t) +
          KSPSVolterra.E lam x *
            ((2 * lam) • (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) * KSPSVolterra.R)) -
          KSPSVolterra.E lam (x - t) * KSPSVolterra.integratedQuadratic φ t)

theorem Good_Theta (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (x : ℝ) : Good (Theta φ lam x) := by
  have hN := ((Good_N φ lam).mul (Good.const KSPSVolterra.R))
  have hG1 : Good (fun t => KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) *
      (KSPSVolterra.R * KSPSVolterra.E lam (-t))) :=
    (Good.const _).mul ((Good.const KSPSVolterra.R).mul (Good_Eneg lam))
  have hG2 : Good (fun t => KSPSVolterra.integratedQuadratic φ x * KSPSVolterra.E lam (x - t)) :=
    (Good.const _).mul (Good_E lam x)
  have hG3 : Good (fun t => KSPSVolterra.E lam x *
      ((2 * lam) • (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) * KSPSVolterra.R))) :=
    (Good.const _).mul (((Good_M1 φ lam).mul (Good.const KSPSVolterra.R)).smul _)
  have hG4 : Good (fun t => KSPSVolterra.E lam (x - t) * KSPSVolterra.integratedQuadratic φ t) :=
    (Good_E lam x).mul (Good_Q φ)
  have hY : Good (fun t => KSPSVolterra.R * KSPSVolterra.E lam (x - t)) :=
    (Good.const _).mul (Good_E lam x)
  unfold Theta
  exact (((Good.const _).mul hN).neg.add hY).sub
    ((((hG1.smul (-(2 * lam))).add hG2).add hG3).sub hG4 |>.smul _)

theorem remainder_eq_Ig (φ : KSPSVolterra.SobolevC 1) (lam : ℂ) (f : PotPair)
    (F : ℝ → Fin 2 → ℂ) (hF : KSPSVolterra.ForcedZS φ lam f F) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    F x - KSPSVolterra.forcingLeading φ lam f x - KSPSVolterra.forcingFirstCorrection φ lam f x =
      Ig f x (Theta φ lam x) := by
  have hN := ((Good_N φ lam).mul (Good.const KSPSVolterra.R))
  have hX : Good (fun t => KSPSVolterra.fundamental φ x lam *
      (KSPSVolterra.inverseFundamental φ t lam * KSPSVolterra.R)) := (Good.const _).mul hN
  have hY : Good (fun t => KSPSVolterra.R * KSPSVolterra.E lam (x - t)) :=
    (Good.const _).mul (Good_E lam x)
  have hG1 : Good (fun t => KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) *
      (KSPSVolterra.R * KSPSVolterra.E lam (-t))) :=
    (Good.const _).mul ((Good.const KSPSVolterra.R).mul (Good_Eneg lam))
  have hG2 : Good (fun t => KSPSVolterra.integratedQuadratic φ x * KSPSVolterra.E lam (x - t)) :=
    (Good.const _).mul (Good_E lam x)
  have hG3 : Good (fun t => KSPSVolterra.E lam x *
      ((2 * lam) • (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) * KSPSVolterra.R))) :=
    (Good.const _).mul (((Good_M1 φ lam).mul (Good.const KSPSVolterra.R)).smul _)
  have hG4 : Good (fun t => KSPSVolterra.E lam (x - t) * KSPSVolterra.integratedQuadratic φ t) :=
    (Good_E lam x).mul (Good_Q φ)
  have hZ : Good (fun t => (2 * lam)⁻¹ •
        (-(2 * lam) • (KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) *
              (KSPSVolterra.R * KSPSVolterra.E lam (-t))) +
          KSPSVolterra.integratedQuadratic φ x * KSPSVolterra.E lam (x - t) +
          KSPSVolterra.E lam x *
            ((2 * lam) • (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) * KSPSVolterra.R)) -
          KSPSVolterra.E lam (x - t) * KSPSVolterra.integratedQuadratic φ t)) :=
    ((((hG1.smul (-(2 * lam))).add hG2).add hG3).sub hG4).smul _
  -- F x = - Ig (M x (N R))
  have hFx : F x = -Ig f x (fun t => KSPSVolterra.fundamental φ x lam *
      (KSPSVolterra.inverseFundamental φ t lam * KSPSVolterra.R)) := by
    have hI : (∫ s in (0 : ℝ)..x, (KSPSVolterra.inverseFundamental φ s lam).mulVec
        (KSPSVolterra.R.mulVec (KSPSVolterra.forcingValue f s))) =
        Ig f x (fun t => KSPSVolterra.inverseFundamental φ t lam * KSPSVolterra.R) := by
      unfold Ig
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      simp only [Matrix.mulVec_mulVec]
    rw [NlsGge.ThirdConsultation.KSPS007Support4.forced_eq_formula φ lam f F hF hx,
      zero_sub, Matrix.mulVec_neg, hI, ← Ig_mul_left f hx _ hN]
  rw [hFx, leading_eq φ lam f hx, first_corr_eq φ lam f hx]
  have e : Ig f x (Theta φ lam x) =
      -Ig f x (fun t => KSPSVolterra.fundamental φ x lam *
        (KSPSVolterra.inverseFundamental φ t lam * KSPSVolterra.R)) +
      Ig f x (fun t => KSPSVolterra.R * KSPSVolterra.E lam (x - t)) -
      Ig f x (fun t => (2 * lam)⁻¹ •
        (-(2 * lam) • (KSPSVolterra.term 1 x lam (KSPSVolterra.toPair φ) *
              (KSPSVolterra.R * KSPSVolterra.E lam (-t))) +
          KSPSVolterra.integratedQuadratic φ x * KSPSVolterra.E lam (x - t) +
          KSPSVolterra.E lam x *
            ((2 * lam) • (KSPSVolterra.term 1 t lam (KSPSVolterra.toPair φ) * KSPSVolterra.R)) -
          KSPSVolterra.E lam (x - t) * KSPSVolterra.integratedQuadratic φ t)) := by
    unfold Theta
    rw [Ig_sub f hx (hX.neg.add hY) hZ, Ig_add f hx hX.neg hY, Ig_neg]
  rw [e]
  abel

end NlsGge.ThirdConsultation.KSPS007Support9
