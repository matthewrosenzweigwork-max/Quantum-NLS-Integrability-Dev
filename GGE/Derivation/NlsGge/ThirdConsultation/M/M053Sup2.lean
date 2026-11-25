import Mathlib
import NlsGge.Atomic.LIB.LIB006
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.IBP038Support

/- M-053 B1 support (proof development, AUTHOR; not reviewed).
   Target NlsGge/ThirdConsultation/M/M053Sup2.lean.  Weak Leibniz rule for physicalProduct on H^1 pairs,
   bridged from LIB006 `product_hasWeak` / `h1MulL2`. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

theorem physicalProduct_comm' (u v : PhysicalL2) : physicalProduct u v = physicalProduct v u := by
  have h : (fun x : PhysicalCircle => u x * v x) = fun x : PhysicalCircle => v x * u x :=
    funext fun x => mul_comm _ _
  unfold physicalProduct productInL2
  simp only [h]

theorem hasWeak_weakDerivative (f : PhysicalL2) (hf : physicalSobolev 1 f) :
    NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1 f (weakDerivative f) := by
  refine (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff_iff (T := 1)).mpr ?_
  intro n
  have h := physicalFourier_weakDerivative f hf n
  show physicalFourier (weakDerivative f) n = NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 *
    physicalFourier f n
  rw [h]
  simp [NlsGge.Atomic.LIB002.fourierMultiplier]

theorem weakDerivative_eq_of_hasWeak (u d : PhysicalL2) (hu : physicalSobolev 1 u)
    (h : NlsGge.Atomic.LIB002.HasWeakDerivativeL2 1 1 u d) : weakDerivative u = d := by
  apply physicalFourierL2.injective
  apply Subtype.ext
  funext n
  have h1 := (NlsGge.Atomic.LIB002.weakDerivative_fourierCoeff_iff (T := 1)).mp h n
  have h2 := physicalFourier_weakDerivative u hu n
  change physicalFourierL2 (weakDerivative u) n = physicalFourierL2 d n
  rw [physicalFourierL2_apply, physicalFourierL2_apply]
  have h1' : physicalFourier d n = NlsGge.Atomic.LIB002.fourierMultiplier 1 n ^ 1 * physicalFourier u n := h1
  rw [h2, h1']
  simp [NlsGge.Atomic.LIB002.fourierMultiplier]

theorem weakDerivative_physicalProduct (f g : PhysicalL2)
    (hf : physicalSobolev 1 f) (hg : physicalSobolev 1 g) :
    productInL2 f g ∧ physicalSobolev 1 (physicalProduct f g) ∧
      weakDerivative (physicalProduct f g) =
        physicalProduct (weakDerivative f) g + physicalProduct f (weakDerivative g) := by
  have hf' := (physicalSobolev_iff_ordinary 1 f).1 hf
  have hg' := (physicalSobolev_iff_ordinary 1 g).1 hg
  have hP := NlsGge.Atomic.LIB006.product_hasWeak f g (weakDerivative f) (weakDerivative g) hf' hg'
    (hasWeak_weakDerivative f hf) (hasWeak_weakDerivative g hg)
  have hS := (NlsGge.Atomic.LIB006.product_graph_bound f g hf' hg').1
  have e1 := physicalProduct_eq_h1MulL2 f g hf'
  have e2 := physicalProduct_eq_h1MulL2 g (weakDerivative f) hg'
  have e3 := physicalProduct_eq_h1MulL2 f (weakDerivative g) hf'
  refine ⟨productInL2_of_H1 f g hf, ?_, ?_⟩
  · rw [e1]; exact (physicalSobolev_iff_ordinary 1 _).2 hS
  · rw [e1] at *
    rw [physicalProduct_comm' (weakDerivative f) g, e2, e3]
    exact weakDerivative_eq_of_hasWeak _ _ ((physicalSobolev_iff_ordinary 1 _).2 hS) hP

end
end NlsGge.ThirdConsultation.M
