import Mathlib
import NlsGge.Birkhoff.F05Identity38f
import NlsGge.Birkhoff.F07MassMoment38c
import NlsGge.Atomic.F.F014
import NlsGge.Atomic.F.F015
import NlsGge.Atomic.F.F023
import NlsGge.Atomic.F.F010Host

/- F024 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/F/F024.lean,
   namespace NlsGge.ThirdConsultation.F. PACKET F-024. STAGED AFTER F-014 and F-015 (proof development; root probe q329):
   uses f015 at the lowered vector.
   Head VERBATIM from followup13 definitions_design_20261027/STATEMENTS/F.md §F-024 (R14_AUDIT_F2 HOSTABLE:
   finiteNormalizer only, tiltProduct/lowerQuadratic landed F-023; BINDING_INDEX_FP80_17 retain_head_unchanged).
   Constant order as printed: δ with 0 < δ < β_{m-1} is fixed first; β' = lowerCoef38 m β δ depends on δ only.
   Route (printed: v2 C:eq:tiltedIntegral; existing conditional BirkhoffInput38.F07_tiltedIntegral38, not
   re-proved) at the ACTUAL inputs B = PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38:
     positivity of β' (lowerCoef_pos38); V' = V - δ(Q_{2m-2} - Σ b_n|û_n|²) (Vm_lower38, with chargeQuad38 _ (m-1)
     = lowerQuadratic definitionally, b_n = lowerChargeSymbol); integrability and ∫ = Z_m(β')/d_δ
     (F07_tiltedIntegral38: integrability is its conclusion); d_δ = tiltProduct (factorwise by f07RateLower38,
     ratePrime = a - δ b); Z_m(β') = finiteNormalizer m β' (F05_identity38 at β' against f015 at β': both compute
     ∫ e^{-V_m(β')} dγ_m^F(β')); 0 < Z_m(β') (F05_identity38) and 0 < d_δ (hasProd_dDelta38) before the quotient.
   No hypothesis added. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
open NlsGge.GKDefinitionDesign

/-- `Q_{2m-2}`'s quadratic part is `lowerQuadratic` (same series, `b_n = lowerChargeSymbol`). -/
theorem f024_chargeQuad_eq (m : ℕ) (u : Hm1 m) :
    chargeQuad38 _ (m - 1) u = lowerQuadratic m u := by
  unfold chargeQuad38 lowerQuadratic lowerChargeSymbol
  rfl

/-- `d_δ = tiltProduct`: the factors agree by `a'_n = a_{m,n} - δ b_n` (`f07RateLower38`). -/
theorem f024_dDelta_eq (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (δ : ℝ) :
    dDelta38 m β δ = tiltProduct m β δ := by
  unfold dDelta38 tiltProduct
  congr 1
  funext n
  rw [f07RateLower38 hm n]
  rfl

/-- **F-024 core** at inputs `B, O`, with the lowered normalizer identified through `hNf`. -/
theorem f024_of_inputs (B : BirkhoffInput38) (O : OneSmoothingInput38 B) (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) (δ : ℝ)
    (hδ : 0 < δ) (hδβ : δ < β (m - 1)) (Nf : ℝ) (hNf : ZM38 B m (lowerCoef38 m β δ) = Nf) :
    (∀ j ≤ m, 0 < lowerCoef38 m β δ j) ∧
    (∀ u : Hm1 m,
      Vm38 m (lowerCoef38 m β δ) u = Vm38 m β u -
        δ * (chargeSobolev38 m (m - 1) u - lowerQuadratic m u)) ∧
    Integrable (fun u => Real.exp
      (-Vm38 m β u + δ * chargeSobolev38 m (m - 1) u)) (gammaFM38 m β) ∧
    (∫ u, Real.exp (-Vm38 m β u + δ * chargeSobolev38 m (m - 1) u)
      ∂gammaFM38 m β) = Nf / tiltProduct m β δ ∧
    0 < Nf / tiltProduct m β δ := by
  have hβ' : ∀ j ≤ m, 0 < lowerCoef38 m β δ j := lowerCoef_pos38 hβ hδβ
  obtain ⟨hint, hI⟩ := B.F07_tiltedIntegral38 O hm hβ hδ.le hδβ
  have hd := (hasProd_dDelta38 hm hβ hδ.le hδβ).1
  have hZ' := (F05_identity38 B O hm hβ').1.1
  rw [f024_dDelta_eq m hm β δ] at hI hd
  rw [hNf] at hI hZ'
  refine ⟨hβ', fun u => ?_, hint, hI, div_pos hZ' hd⟩
  rw [Vm_lower38 hm u, f024_chargeQuad_eq m u]

/-- **F-024** (head verbatim). -/
theorem f024 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) (δ : ℝ)
    (hδ : 0 < δ) (hδβ : δ < β (m - 1)) :
    (∀ j ≤ m, 0 < lowerCoef38 m β δ j) ∧
    (∀ u : Hm1 m,
      Vm38 m (lowerCoef38 m β δ) u = Vm38 m β u -
        δ * (chargeSobolev38 m (m - 1) u - lowerQuadratic m u)) ∧
    Integrable (fun u => Real.exp
      (-Vm38 m β u + δ * chargeSobolev38 m (m - 1) u)) (gammaFM38 m β) ∧
    (∫ u, Real.exp (-Vm38 m β u + δ * chargeSobolev38 m (m - 1) u)
      ∂gammaFM38 m β) =
      finiteNormalizer m (lowerCoef38 m β δ) / tiltProduct m β δ ∧
    0 < finiteNormalizer m (lowerCoef38 m β δ) / tiltProduct m β δ := by
  have hβ' : ∀ j ≤ m, 0 < lowerCoef38 m β δ j := lowerCoef_pos38 hβ hδβ
  have hNf : ZM38 NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38 m (lowerCoef38 m β δ) =
      finiteNormalizer m (lowerCoef38 m β δ) :=
    ((F05_identity38 NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
      NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 hm hβ').2.2.1).symm.trans
      (f015 m hm (lowerCoef38 m β δ) hβ').2.2.1
  exact f024_of_inputs NlsGge.ThirdConsultation.PDE.actualBirkhoffInput38
    NlsGge.ThirdConsultation.PDE.actualOneSmoothingInput38 m hm β hβ δ hδ hδβ
    (finiteNormalizer m (lowerCoef38 m β δ)) hNf

end NlsGge.ThirdConsultation.F
