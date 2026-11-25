import Mathlib
import NlsGge.Ramer.RamerLemma53

                                                                                                           
                                                                                              
                                                                                                     
                                                                                                                   
                                                                                                                  
                                                                                
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem continuousOn_invFunOn_add_finiteDim
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    (V : Submodule ℝ E₀) [FiniteDimensional ℝ V]
    (D : Set E₀) (hD : IsClosed D) (hb : Bornology.IsBounded D)
    (g : E₀ → E₀) (hg : ContinuousOn g D)
    (hr : ∀ x ∈ D, g x ∈ V)
    (hinj : Set.InjOn (fun x : E₀ => x + g x) D) :
    ContinuousOn (Function.invFunOn (fun x : E₀ => x + g x) D)
      ((fun x : E₀ => x + g x) '' D) :=
  NlsGge.Ramer.continuousOn_invFunOn_add_finiteDim hD hb hg V hr hinj

end
end NlsGge.ThirdConsultation.R
