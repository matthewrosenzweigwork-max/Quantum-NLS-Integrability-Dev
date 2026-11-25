import Mathlib

                                                                                                                             
                                                                                                                         
                                                                                                                            
set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.PDE.PDE064Aux

theorem hasDerivAt_comp_of_analyticOnNhd
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : AnalyticOnNhd ℝ f Set.univ)
    (γ : ℝ → E) (v : E) (t0 : ℝ) (hγ : HasDerivAt γ v t0) :
    HasDerivAt (fun t : ℝ => f (γ t)) (fderiv ℝ f (γ t0) v) t0 :=
  ((hf (γ t0) (Set.mem_univ _)).differentiableAt.hasFDerivAt).comp_hasDerivAt t0 hγ

end NlsGge.ThirdConsultation.PDE.PDE064Aux
