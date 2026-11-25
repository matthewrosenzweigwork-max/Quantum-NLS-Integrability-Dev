import Mathlib
import NlsGge.Atomic.R.R023

                                                                                                                                                
                                                                                                                                                           
                                                                                                                                                                                                                                                                                                                                                                                                                                                            
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators RealInnerProductSpace
namespace NlsGge.ThirdConsultation.R
noncomputable section

theorem ramerJac_eq_production
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (K : RamerE c s → RamerH c) (x : RamerE c s) :
    ramerJac c s hs K x = NlsGge.Ramer.ramerJac c s hs K x :=
  (NlsGge.Ramer.ramerJac_eq c s hs K x).symm

theorem ramer_local_lower_bound
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (K : RamerE c s → RamerH c) (hK : ContDiff ℝ 2 K)
    (x₀ : RamerE c s)
    (hInv : IsUnit (1 + (hsDerivH c s hs K x₀).toCLM)) :
    ∃ U : Set (RamerE c s),
      IsOpen U ∧ x₀ ∈ U ∧
      (∀ x ∈ U, IsUnit (1 + (hsDerivH c s hs K x).toCLM)) ∧
      (∀ B : Set (RamerE c s),
        (∫⁻ x in U ∩ (TM c s hs K) ⁻¹' B,
          ENNReal.ofReal (ramerJac c s hs K x)
          ∂ramerGaussian c s) ≤ ramerGaussian c s B) := by
  obtain ⟨V, hVo, hxV, hU, hlb, -⟩ :=
    NlsGge.Ramer.ramer_local_lower_bound c s hs K hK x₀ hInv
  refine ⟨V, hVo, hxV, hU, fun B => ?_⟩
  have h := hlb B
  have e : (fun x : RamerE c s => ENNReal.ofReal (ramerJac c s hs K x)) =
      fun x => ENNReal.ofReal (NlsGge.Ramer.ramerJac c s hs K x) :=
    funext fun x => by rw [ramerJac_eq_production]
  rw [e]
  exact h

end
end NlsGge.ThirdConsultation.R
