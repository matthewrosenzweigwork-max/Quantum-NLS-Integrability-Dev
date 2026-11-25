import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Host
import NlsGge.ThirdConsultation.KSPS.KSPS007Support

                                                                                                                    
                                                                                                      
                                                                                                 
                                                                                                
                                                                                                           
                                                                                                 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Volterra NlsGge.Atomic.G1011S2

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem volterraTerm_eq_pot {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) (lam : ℂ)
    (k : ℕ) (x : ℝ) :
    NlsGge.ThirdConsultation.KSPS.volterraTerm k x lam φ =
      potentialVolterraTerm38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ) lam k x :=
  NlsGge.ThirdConsultation.KSPS007Support.term_eq_pot _ lam k x

theorem sourceFundamental_summable {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (lam : ℂ) {x : ℝ} (hx : 0 ≤ x) (i j : Fin 2) :
    Summable (fun k : ℕ => NlsGge.ThirdConsultation.KSPS.volterraTerm k x lam φ i j) := by
  simp only [volterraTerm_eq_pot]
  exact NlsGge.ThirdConsultation.KSPS007Support.summable_pot _ lam hx i j

theorem sourceFundamental_eq_Mf {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (lam : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    sourceFundamental φ x lam = Mf (NlsGge.ThirdConsultation.KSPS.toPotPair φ) lam x := by
  set p := NlsGge.ThirdConsultation.KSPS.toPotPair φ with hp
  have hS : Summable (fun n : ℕ => potentialVolterraTerm38 p lam n x) :=
    Pi.summable.2 fun i => Pi.summable.2 fun j =>
      NlsGge.ThirdConsultation.KSPS007Support.summable_pot p lam hx i j
  ext i j
  have hcont : Continuous (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) :=
    (continuous_id.matrix_elem i j)
  have h1 : HasSum (fun n : ℕ => potentialVolterraTerm38 p lam n x i j)
      ((∑' n : ℕ, potentialVolterraTerm38 p lam n x) i j) :=
    hS.hasSum.map (Matrix.entryLinearMap ℂ ℂ i j : PairMat38 →ₗ[ℂ] ℂ) hcont
  unfold sourceFundamental Mf
  simp only [volterraTerm_eq_pot]
  exact h1.tsum_eq

theorem sourceFundamental_det {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (lam : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    (sourceFundamental φ x lam).det = 1 := by
  rw [sourceFundamental_eq_Mf φ lam hx]
  exact NlsGge.Atomic.G1010.G1010_det _ lam hx

theorem sourceFundamental_continuousOn {N : ℕ} (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (lam : ℂ) (i j : Fin 2) :
    ContinuousOn (fun x : ℝ => sourceFundamental φ x lam i j) (Set.Icc (0 : ℝ) 1) := by
  have hAC := (NlsGge.Atomic.G1005.G1005_restricted (NlsGge.ThirdConsultation.KSPS.toPotPair φ) lam).2.2
    1 zero_le_one i j
  have hc := hAC.continuousOn
  rw [Set.uIcc_of_le zero_le_one] at hc
  refine hc.congr (fun x hx => ?_)
  rw [sourceFundamental_eq_Mf φ lam hx.1]
  rfl

theorem sourceFundamental_eq_fundamental {N : ℕ}
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (φ' : NlsGge.ThirdConsultation.KSPS.SobolevC 1)
    (h : NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' =
      NlsGge.ThirdConsultation.KSPS.toPotPair φ) (x : ℝ) (lam : ℂ) :
    sourceFundamental φ x lam = NlsGge.ThirdConsultation.KSPSVolterra.fundamental φ' x lam := by
  ext i j
  unfold sourceFundamental NlsGge.ThirdConsultation.KSPSVolterra.fundamental
  simp only [NlsGge.ThirdConsultation.KSPS.volterraTerm, h]

end NlsGge.ThirdConsultation.KSPSWKB
