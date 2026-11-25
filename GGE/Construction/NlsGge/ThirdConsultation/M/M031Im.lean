import Mathlib
import NlsGge.Atomic.DM.DM016Eig
import NlsGge.Atomic.G1.G1104Sup
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.ThirdConsultation.M.M031Energy
import NlsGge.ThirdConsultation.M.M031L1
import NlsGge.ThirdConsultation.M.M031Sup
import NlsGge.ThirdConsultation.M.M031Num

   
                                                                                                   

                                                                                                       
                                                                                  
                                                                                                                 
                                                                                                                      
                                                                                           
                                                                                                                    
                                                                                  
  

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38 NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.DM002
open NlsGge.GKDefinitionDesign
open scoped ENNReal

namespace NlsGge.ThirdConsultation.M

/-- Native re-proof of KST029Bridge `physical_ext_of_ae_unit`. -/
theorem m031_physical_ext_of_ae_unit (u v : PhysicalL2)
    (h : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      u ((t : ℝ) : PhysicalCircle) = v ((t : ℝ) : PhysicalCircle)) : u = v := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext k
  rw [physicalFourierL2_apply, physicalFourierL2_apply]
  unfold physicalFourier
  rw [fourierCoeff_eq_intervalIntegral (u : PhysicalCircle → ℂ) k 0,
    fourierCoeff_eq_intervalIntegral (v : PhysicalCircle → ℂ) k 0]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have h' := (ae_restrict_iff' measurableSet_Ioc).1 h
  filter_upwards [h'] with t ht hmem
  have hmem' : t ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [zero_add, Set.uIoc_of_le zero_le_one] at hmem
    exact hmem
  rw [ht hmem']

/-- Native re-proof of KST029Bridge `unitPhysical_sourceIntervalClass`. -/
theorem m031_unitPhysical_sourceIntervalClass (p : PhysicalL2) :
    unitPhysical (sourceIntervalClass p) = p := by
  apply m031_physical_ext_of_ae_unit
  have h1 := unitPhysical_interval_ae (sourceIntervalClass p)
  have h2 := (NlsGge.Atomic.G1104Sup.sourceIntervalClass_spec p).2
  have h3 : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), coverRep38 p t = p ((t : ℝ) : PhysicalCircle) :=
    ae_restrict_of_ae (coverRep38_ae_phys p)
  filter_upwards [h1, h2, h3] with t e1 e2 e3
  exact e1.trans (e2.trans e3)

/-- (B), generic form: finite source-H1 energy bounds the imaginary part of every periodic label. -/
theorem lamSeq_abs_im_le_of_energy (ψ : PotPair)
    (hψ : MTwoMode.potentialCoefficientEnergy sourceH1Weight ψ ≠ ⊤) (k : ℤ) :
    |(lamSeq ψ k).im| ≤ MTwoMode.potentialCoefficientNorm sourceH1Weight ψ := by
  set x := lamSeq ψ k with hxdef
  set P : SourcePairL2 := intervalPotential ψ with hP
  have hPt : P true = sourceIntervalClass ψ.1 := by simp [hP, intervalPotential]
  have hPf : P false = sourceIntervalClass ψ.2 := by simp [hP, intervalPotential]
  have hroot : perChar (unitPhysical (P true), unitPhysical (P false)) x = 0 := by
    rw [hPt, hPf, m031_unitPhysical_sourceIntervalClass, m031_unitPhysical_sourceIntervalClass]
    exact (lamSeq_enumeration38 ψ).1 k
  obtain ⟨s, hs, g, hg0, htr, heig⟩ :=
    NlsGge.ThirdConsultation.DM.Support016.exists_eigenpair_of_perChar_zero P x hroot
  have hbc : ∃ bc : ZSBoundaryCondition, HasZSBoundaryCondition bc g := by
    rcases mul_self_eq_one_iff.1 hs with rfl | rfl
    · exact ⟨.periodic, fun b => by simpa using htr b⟩
    · exact ⟨.antiperiodic, fun b => by simpa using htr b⟩
  obtain ⟨bc, hbcg⟩ := hbc
  obtain ⟨hsum, hl1⟩ := coefficient_l1_le ψ hψ
  set A₁ := ∑' j : ℤ, ‖MTwoMode.potentialCoefficientPair ψ true j‖
  set A₂ := ∑' j : ℤ, ‖MTwoMode.potentialCoefficientPair ψ false j‖
  have hA₁ : 0 ≤ A₁ := tsum_nonneg (fun _ => norm_nonneg _)
  have hA₂ : 0 ≤ A₂ := tsum_nonneg (fun _ => norm_nonneg _)
  have hb₁ : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), ‖P true t‖ ≤ A₁ := by
    rw [hPt]
    exact sourceIntervalClass_ae_le ψ.1 (hsum true)
  have hb₂ : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)), ‖P false t‖ ≤ A₂ := by
    rw [hPf]
    exact sourceIntervalClass_ae_le ψ.2 (hsum false)
  have hE1 := zs_eigen_im_eq P bc g hbcg x heig
  have hE2 := zs_potential_inner_le P A₁ A₂ hA₁ hA₂ hb₁ hb₂ g
  set D := inner ℂ (h1PairValue g) (zsApply P g) - inner ℂ (h1PairValue g) (zsApply 0 g)
  have hN : 0 < ‖h1PairValue g‖ ^ 2 := by
    have := norm_pos_iff.2 hg0
    positivity
  have habs : |x.im| * ‖h1PairValue g‖ ^ 2 ≤ MTwoMode.potentialCoefficientNorm sourceH1Weight ψ *
      ‖h1PairValue g‖ ^ 2 := by
    calc |x.im| * ‖h1PairValue g‖ ^ 2 = |x.im * ‖h1PairValue g‖ ^ 2| := by
          rw [abs_mul, abs_of_pos hN]
      _ = |D.im| := by rw [hE1]
      _ ≤ ‖D‖ := Complex.abs_im_le_norm D
      _ ≤ (A₁ + A₂) / 2 * ‖h1PairValue g‖ ^ 2 := hE2
      _ ≤ MTwoMode.potentialCoefficientNorm sourceH1Weight ψ * ‖h1PairValue g‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hN.le
          linarith
  exact le_of_mul_le_mul_right habs hN

/-- (B) on the source carrier: `|Im λ_k| ≤ Q` for every label of `KSPS.toPotPair φ`. -/
theorem lamSeq_abs_im_le (φ : KSPS.SobolevC 1) (k : ℤ) :
    |(lamSeq (KSPS.toPotPair φ) k).im| ≤
      MTwoMode.potentialCoefficientNorm sourceH1Weight (KSPS.toPotPair φ) :=
  lamSeq_abs_im_le_of_energy _ (sourceH1_energy_ne_top φ) k

end NlsGge.ThirdConsultation.M

end
