                                                                                                                           
                                                                                                                           
                                                                                                                      
                                                                                                                                         
                     
import Mathlib
import NlsGge.Atomic.T.T029
import NlsGge.Birkhoff.F11Claim38

set_option autoImplicit false

namespace NlsGge.ThirdConsultation.T
noncomputable section

def finiteChargeSymbol (J : ℕ) (t : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), t j * r ^ (2 * j)

theorem finiteChargeTilt_weightClass
    (cMinus cPlus : ℝ) (W : ℕ → ℝ) (J : ℕ) (t : ℕ → ℝ)
    (hW : WeightClass cMinus cPlus W)
    (ht : ∀ j : ℕ, j ≤ J →
      0 ≤ t j ∧ t j < NlsGge.coefficient W j) :
    ∃ lo : ℝ, 0 < lo ∧
      WeightClass lo cPlus (NlsGge.Birkhoff.tiltCoeff38 W J t) := by
  let cB : NlsGge.Pilot.BoundedCoefficients cMinus cPlus := ⟨W, hW⟩
  have ht' : NlsGge.Birkhoff.TiltAdmissible38 cB J t := ht
  exact ⟨NlsGge.Birkhoff.tiltLower38 cB J t, NlsGge.Birkhoff.tiltLower38_pos cB ht',
    NlsGge.Birkhoff.tiltCoeff_admitted38 cB ht'⟩

theorem finiteChargeTilt_symbol_identity
    (cMinus cPlus : ℝ) (W : ℕ → ℝ) (J : ℕ) (t : ℕ → ℝ)
    (hW : WeightClass cMinus cPlus W)
    (ht : ∀ j : ℕ, j ≤ J →
      0 ≤ t j ∧ t j < NlsGge.coefficient W j) (r : ℝ) :
    NlsGge.Weights.weight (NlsGge.Birkhoff.tiltCoeff38 W J t) r =
      NlsGge.Weights.weight W r - finiteChargeSymbol J t r := by
  let cB : NlsGge.Pilot.BoundedCoefficients cMinus cPlus := ⟨W, hW⟩
  have ht' : NlsGge.Birkhoff.TiltAdmissible38 cB J t := ht
  have hsym : finiteChargeSymbol J t r = NlsGge.Birkhoff.tiltPoly38 J t r := rfl
  rw [hsym]
  exact NlsGge.Birkhoff.weight_tilt38 cB ht' r

end
end NlsGge.ThirdConsultation.T
#print axioms NlsGge.ThirdConsultation.T.finiteChargeTilt_weightClass
#print axioms NlsGge.ThirdConsultation.T.finiteChargeTilt_symbol_identity
