import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Host
import NlsGge.ThirdConsultation.KSPS.KSPS011Support2
import NlsGge.ThirdConsultation.KSPS.KSPS011Support3
import NlsGge.ThirdConsultation.KSPS.KSPS007Support9

/- KSPS-011 SUPPORT6 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS011Support6.lean.
   Step M2 (v): identification of the source remainder with the KSPS-007 forced solution.
   For phi : SobolevC N, phi' : SobolevC 1 with toPair phi' = toPotPair phi, and a PotPair f representing the source
   forcing vector a.e. on [0,1] (KSPS011Support5), on [0,1]
     sourceRemainderVector phi b lam = Fs (toPair phi') lam (forcingValue f)  (the G1-011 Duhamel solution),
   hence `ForcedZS phi' lam f (sourceRemainderVector phi b lam)`, which is exactly the hypothesis of KSPS-007
   `forced_solution_expansion`. Route: both sides are -Ig f x (M x * (adj M t * R)) (KSPS007Support5/9 calculus). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.Atomic.G1011S2
open NlsGge.ThirdConsultation.KSPS007Support5 NlsGge.ThirdConsultation.KSPS007Support4
open NlsGge.ThirdConsultation.KSPS007Support7
open scoped Matrix

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem ForcedZS_congr (φ : NlsGge.ThirdConsultation.KSPS.SobolevC 1) (lam : ℂ) (f : PotPair)
    {F G : ℝ → Fin 2 → ℂ} (h : ∀ x ∈ Icc (0 : ℝ) 1, F x = G x)
    (hG : NlsGge.ThirdConsultation.KSPSVolterra.ForcedZS φ lam f G) :
    NlsGge.ThirdConsultation.KSPSVolterra.ForcedZS φ lam f F := by
  obtain ⟨hc, h0, hE⟩ := hG
  refine ⟨hc.congr h, ?_, ?_⟩
  · rw [h 0 ⟨le_rfl, zero_le_one⟩]; exact h0
  · intro x hx
    rw [h x hx, hE x hx]
    unfold NlsGge.ThirdConsultation.KSPSVolterra.integrateVector
    funext i
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hx.1] at ht
    beta_reduce
    rw [h t ⟨ht.1, ht.2.trans hx.2⟩]

theorem sourceRemainderVector_eq_Ig {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (φ' : NlsGge.ThirdConsultation.KSPS.SobolevC 1)
    (hφ : NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ)
    (b : Bool) (lam : {z : ℂ // z ≠ 0}) (f : PotPair)
    (hf : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    sourceRemainderVector φ b lam x =
      -Ig f x (fun t => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ' x lam.1 *
        (NlsGge.ThirdConsultation.KSPSVolterra.inverseFundamental φ' t lam.1 *
          NlsGge.ThirdConsultation.KSPSVolterra.R)) := by
  have hA : Good (fun t => NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ' x lam.1 *
      (NlsGge.ThirdConsultation.KSPSVolterra.inverseFundamental φ' t lam.1 *
        NlsGge.ThirdConsultation.KSPSVolterra.R)) :=
    (Good.const _).mul ((Good_N φ' lam.1).mul (Good.const _))
  unfold sourceRemainderVector
  congr 1
  funext i
  have hint : ∀ j, IntervalIntegrable (fun t => (((NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ' x lam.1 *
      (NlsGge.ThirdConsultation.KSPSVolterra.inverseFundamental φ' t lam.1 *
        NlsGge.ThirdConsultation.KSPSVolterra.R)).mulVec
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingValue f t)) j)) volume 0 x :=
    fun j => hA.mulVec_ii f j hx
  show (∫ t in (0 : ℝ)..x, _) = (Ig f x _) i
  unfold Ig
  rw [ivInt_apply hx.1 hint i]
  refine intervalIntegral.integral_congr_ae ?_
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc (0 : ℝ) 1 →
      ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t :=
    (ae_restrict_iff' measurableSet_Icc).1 hf
  filter_upwards [hae] with t ht hΙ
  rw [uIoc_of_le hx.1] at hΙ
  have h1 := ht ⟨hΙ.1.le, hΙ.2.trans hx.2⟩
  rw [← h1]
  rw [NlsGge.ThirdConsultation.KSPSWKB.sourceFundamental_eq_fundamental φ φ' hφ x lam.1,
    NlsGge.ThirdConsultation.KSPSWKB.sourceFundamental_eq_fundamental φ φ' hφ t lam.1]
  unfold NlsGge.ThirdConsultation.KSPSVolterra.inverseFundamental
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rfl

theorem sourceRemainderVector_eq_Fs {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (φ' : NlsGge.ThirdConsultation.KSPS.SobolevC 1)
    (hφ : NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ)
    (b : Bool) (lam : {z : ℂ // z ≠ 0}) (f : PotPair)
    (hf : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    sourceRemainderVector φ b lam x =
      Fs (NlsGge.ThirdConsultation.KSPSVolterra.toPair φ') lam.1
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingValue f) x := by
  rw [sourceRemainderVector_eq_Ig φ φ' hφ b lam f hf hx,
    NlsGge.ThirdConsultation.KSPS007Support4.forced_eq_formula φ' lam.1 f _
      (NlsGge.ThirdConsultation.KSPS011Support3.Fs_forcedZS φ' lam.1 f) hx]
  have hA : Good (fun t => NlsGge.ThirdConsultation.KSPSVolterra.inverseFundamental φ' t lam.1 *
      NlsGge.ThirdConsultation.KSPSVolterra.R) := (Good_N φ' lam.1).mul (Good.const _)
  have e1 : (∫ s in (0 : ℝ)..x, (NlsGge.ThirdConsultation.KSPSVolterra.inverseFundamental φ' s lam.1).mulVec
      (NlsGge.ThirdConsultation.KSPSVolterra.R.mulVec (NlsGge.ThirdConsultation.KSPSVolterra.forcingValue f s))) =
      Ig f x (fun t => NlsGge.ThirdConsultation.KSPSVolterra.inverseFundamental φ' t lam.1 *
        NlsGge.ThirdConsultation.KSPSVolterra.R) := by
    unfold Ig
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [Matrix.mulVec_mulVec]
  rw [e1, zero_sub, Matrix.mulVec_neg, ← Ig_mul_left f hx _ hA]

theorem sourceRemainderVector_forcedZS {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (φ' : NlsGge.ThirdConsultation.KSPS.SobolevC 1)
    (hφ : NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ)
    (b : Bool) (lam : {z : ℂ // z ≠ 0}) (f : PotPair)
    (hf : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t) :
    NlsGge.ThirdConsultation.KSPSVolterra.ForcedZS φ' lam.1 f (sourceRemainderVector φ b lam) :=
  ForcedZS_congr φ' lam.1 f (fun x hx => sourceRemainderVector_eq_Fs φ φ' hφ b lam f hf hx)
    (NlsGge.ThirdConsultation.KSPS011Support3.Fs_forcedZS φ' lam.1 f)

end NlsGge.ThirdConsultation.KSPSWKB
