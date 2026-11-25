import Mathlib
import NlsGge.Atomic.G1.G1081Host
import NlsGge.Atomic.G1.G1081Sup2
import NlsGge.Atomic.G1.G1081Sup5
import NlsGge.Atomic.G1.G1071
import NlsGge.GK38.PoissonMixedRealKappaBrackets
import NlsGge.GK38.DirichletRealDerivative
import NlsGge.GK38.GradEigenRealDirichlet

                                                                                                        
                                                                       
                                                                                                              
                                                                                                            
                                                                                                           
                                                                                                                      
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.PoissonSpectral38 NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G1082Sup1
noncomputable section

theorem dirInterpolation_self (φ : PotPair) (z : ℂ) (h : deriv (dirichletChar φ) z ≠ 0) :
    dirInterpolation38 φ z z = 1 := by
  unfold dirInterpolation38
  rw [dslope_same]
  exact div_self h

theorem dirInterpolation_other (φ : PotPair) (z w : ℂ) (hz : dirichletChar φ z = 0)
    (hw : dirichletChar φ w = 0) (hne : w ≠ z) :
    dirInterpolation38 φ z w = 0 := by
  unfold dirInterpolation38
  rw [dslope_of_ne _ hne, slope_def_field, hz, hw]
  simp

/-- The pairing of the Dirichlet eigenvalue gradient with the single-gap field. -/
theorem fderiv_gkMu_singleGapField (n m : ℤ) (v : PhysicalL2) :
    (fderiv ℝ (fun w : PhysicalL2 => gkMu w m) v) (singleGapField n v) =
      if m = n then -(antiDiscrim (realSlice v) (gkMu v n : ℂ)).re / 2 else 0 := by
  have hg : singleGapField n v =
      (kernelHamField38 (gradDiscrimCont38 (realSlice v) (gkMu v n : ℂ))).1 := rfl
  rw [hg, actual_mu_derivative_kernelHamField38 v m _
    (NlsGge.Atomic.G1081Sup2.realSymmetric_gradDiscrimCont v (gkMu v n))]
  rw [kernelPoisson_swap38]
  have hs : NlsGge.Atomic.G1070.simpleDirichlet (realSlice v) (muSeq (realSlice v) m) := by
    rw [muSeq_eq_gkMu38]
    exact ⟨gkMu_root38 v m, dirichlet_root_deriv_ne_zero38 v (gkMu v m) (gkMu_root38 v m)⟩
  have h71 := (G1_071 (realSlice v) m (gkMu v n : ℂ) hs).2
  rw [muSeq_eq_gkMu38] at h71
  have hk : kernelPoisson38 (gradDiscrimCont38 (realSlice v) (gkMu v n : ℂ))
      (dirEigenKernel38 (realSlice v) (gkMu v m : ℂ)) =
      antiDiscrim (realSlice v) (gkMu v m : ℂ) *
        dirInterpolation38 (realSlice v) (gkMu v m : ℂ) (gkMu v n : ℂ) / 2 := by
    rw [← h71]; ring
  rw [hk]
  by_cases hmn : m = n
  · subst hmn
    rw [if_pos rfl, dirInterpolation_self _ _
      (dirichlet_root_deriv_ne_zero38 v (gkMu v m) (gkMu_root38 v m))]
    simp [Complex.neg_re, neg_div]
  · rw [if_neg hmn, dirInterpolation_other _ _ _ (gkMu_root38 v m) (gkMu_root38 v n)
      (fun h => hmn (gkMu_injective38 v (Complex.ofReal_injective h)).symm)]
    simp

theorem hasDerivAt_gkMu_flow (n m : ℤ) (u : PhysicalL2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gkMu (singleGapFlow n s u) m)
      (if m = n then
        -(antiDiscrim (realSlice (singleGapFlow n t u))
          (gkMu (singleGapFlow n t u) n : ℂ)).re / 2 else 0) t := by
  have hF := NlsGge.Atomic.G1081Sup5.singleGapFlow_hasDerivAt n u t
  have hm := (GradEigen38.actual_dirichlet_label_hasFDerivAt (singleGapFlow n t u) m)
  have := hm.comp_hasDerivAt t hF
  rw [← fderiv_gkMu_singleGapField n m (singleGapFlow n t u), hm.fderiv]
  exact this

theorem gkMu_flow_other (n m : ℤ) (hmn : m ≠ n) (u : PhysicalL2) (t : ℝ) :
    gkMu (singleGapFlow n t u) m = gkMu u m := by
  have hd : ∀ s : ℝ, HasDerivAt (fun r : ℝ => gkMu (singleGapFlow n r u) m) 0 s := by
    intro s
    simpa [if_neg hmn] using hasDerivAt_gkMu_flow n m u s
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [NlsGge.Atomic.G1081Sup5.singleGapFlow_zero] using hc

theorem deriv_gkMu_flow_self (n : ℤ) (u : PhysicalL2) (t : ℝ) :
    deriv (fun r : ℝ => gkMu (singleGapFlow n r u) n) t =
      -(antiDiscrim (realSlice (singleGapFlow n t u))
        (gkMu (singleGapFlow n t u) n : ℂ)).re / 2 := by
  simpa using (hasDerivAt_gkMu_flow n n u t).deriv

end
end NlsGge.Atomic.G1082Sup1
