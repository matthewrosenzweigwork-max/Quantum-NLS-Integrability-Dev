import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Host
import NlsGge.ThirdConsultation.KSPSSupport.ANA01
import NlsGge.GK38.GradFundamentalL2

/- KSPS-011 SUPPORT5 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS011Support5.lean.
   Step M2 (ii)+(iii): for fixed lam != 0 the source forcing vector `sourceForcingVector` has both components in
   L2([0,1]) (KSPS-010 ANA01 + bounded continuous exponential), and it is represented, a.e. on [0,1], by a genuine
   PotPair f (via GK38.intervalKernelL2Class38), so that KSPS-007's `forcingValue f` can stand for it. No hypotheses on N. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem sourceForcingVector_memLp {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (b : Bool) (lam : {z : ℂ // z ≠ 0}) (i : Fin 2) :
    MemLp (fun t : ℝ => sourceForcingVector φ b lam t i) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hF := NlsGge.ThirdConsultation.KSPSSupport.h150_forcing_memLp φ b lam.1
  have hmono : (volume.restrict (Ioc (0 : ℝ) 1)) ≤ NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure :=
    Measure.restrict_mono Ioc_subset_Icc_self le_rfl
  refine MemLp.mono_measure (μ := NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure) hmono ?_
  have hg : ∀ s : ℂ, ContinuousOn (fun t : ℝ => Complex.exp (s * (t : ℂ))) (Icc (0 : ℝ) 1) :=
    fun s => (Continuous.continuousOn (by fun_prop))
  cases b
  · fin_cases i
    · simpa [sourceForcingVector] using (memLp_zero : MemLp (fun _ : ℝ => (0 : ℂ)) 2
        NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure)
    · have := NlsGge.ThirdConsultation.KSPSSupport.h150_memLp_mul_bdd _ _ hF (hg (-(Complex.I * lam.1)))
      simpa [sourceForcingVector] using this
  · fin_cases i
    · have := NlsGge.ThirdConsultation.KSPSSupport.h150_memLp_mul_bdd _ _ hF (hg (Complex.I * lam.1))
      simpa [sourceForcingVector, mul_assoc] using this
    · simpa [sourceForcingVector] using (memLp_zero : MemLp (fun _ : ℝ => (0 : ℂ)) 2
        NlsGge.ThirdConsultation.KSPSRiccati.intervalMeasure)

theorem exists_forcing_potPair {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (b : Bool) (lam : {z : ℂ // z ≠ 0}) :
    ∃ f : PotPair, ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t := by
  refine ⟨(intervalKernelL2Class38 _ (sourceForcingVector_memLp φ b lam 0),
    intervalKernelL2Class38 _ (sourceForcingVector_memLp φ b lam 1)), ?_⟩
  filter_upwards [coverRep_intervalKernelL2Class38 (sourceForcingVector_memLp φ b lam 0),
    coverRep_intervalKernelL2Class38 (sourceForcingVector_memLp φ b lam 1)] with t h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

end NlsGge.ThirdConsultation.KSPSWKB
