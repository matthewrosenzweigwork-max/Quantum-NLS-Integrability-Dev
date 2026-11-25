import Mathlib
import NlsGge.Schur.ActualSchurWirtinger38V1
import NlsGge.ThirdConsultation.S.SShared06

                                                                                                          
                                                                                                                    
                                                                                                                    
                                                                                                               
                                     
                                                                                           
                                                                                                                    
                                                                                                  
                                                                                                             
                                                              
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur
namespace NlsGge.ThirdConsultation.S

set_option backward.isDefEq.respectTransparency false in
/-- **S-061, Wirtinger averaging selects the first complex derivative** (Pro round 6 head, verbatim). -/
theorem realType_wirtinger_first_component
    (Q : SchurPair → ℂ) (n : ℤ) (u w : SchurH1)
    (hQ : DifferentiableAt ℂ Q (schurRealPair u)) :
    let q := fun v : SchurH1 => Q (schurRealPair v) - v n
    (1 / 2 : ℂ) * (fderiv ℝ q u w - Complex.I * fderiv ℝ q u (Complex.I • w)) =
      fderiv ℂ Q (schurRealPair u) (w, 0) - w n := by
  intro q
  -- Step 1: complex differentiability at the real point gives real differentiability of Q (restricted scalars).
  have hqR : HasFDerivAt Q ((fderiv ℂ Q (schurRealPair u)).restrictScalars ℝ)
      (actualRealTypeEmbedding38 u) :=
    hQ.hasFDerivAt.restrictScalars ℝ
  -- Step 2: compose with the real embedding u ↦ (u, ū) and subtract the n-th coordinate.
  have hι := actualRealTypeEmbedding38.hasFDerivAt (x := u)
  have h1 := HasFDerivAt.comp (g := Q) (f := fun v : SchurH1 => actualRealTypeEmbedding38 v) u hqR hι
  have h2 := ((actualH1CoordinateCLM38 n).restrictScalars ℝ).hasFDerivAt (x := u)
  have h := h1.sub h2
  -- Step 3: q is the same function as the composite, so q has the composite derivative at u.
  have h' := h.congr_of_eventuallyEq (f₁ := q) (Filter.Eventually.of_forall fun v => by
    simp only [q, Pi.sub_apply, Function.comp, schurRealPair, actualRealTypeEmbedding38_apply,
      ContinuousLinearMap.coe_restrictScalars', actualH1CoordinateCLM38_apply])
  -- Step 4: DifferentiableAt is obtained before any fderiv identity (totalization).
  have hdiff : DifferentiableAt ℝ q u := h'.differentiableAt
  rw [h'.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', actualRealTypeEmbedding38_apply,
    actualH1CoordinateCLM38_apply]
  -- Step 5: conjugation of I • w, then split the pairs into the first and second component.
  rw [actualH1Conj38_complex_smul]
  have hsplit1 : ((w, actualH1Conj38 w) : SchurPair) =
      (w, 0) + (0, actualH1Conj38 w) := by simp
  have hsplit2 : ((Complex.I • w, star Complex.I • actualH1Conj38 w) : SchurPair) =
      Complex.I • ((w, 0) : SchurPair) + star Complex.I • ((0, actualH1Conj38 w) : SchurPair) := by
    simp
  rw [hsplit1, hsplit2, map_add, map_add, map_smul, map_smul]
  -- Step 6: coordinate of I • w and the Wirtinger algebra; cancel the second component.
  have hIw : (Complex.I • w : SchurH1) n = Complex.I * w n := rfl
  rw [hIw, Complex.star_def, Complex.conj_I, smul_eq_mul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

end NlsGge.ThirdConsultation.S
end
