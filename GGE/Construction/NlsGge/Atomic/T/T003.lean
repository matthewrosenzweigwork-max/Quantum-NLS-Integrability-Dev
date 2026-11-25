import NlsGge.Hierarchy.FourierTilt38
import NlsGge.Birkhoff.F09Limit38b
import NlsGge.ThirdConsultation.T.ECarrier98

                                                                                             
                                                                                                                      
                                                                        
                                                                                                          
                                                                                                       
                                                                                                      
                                                                                                       
                                                                                                           
                                                                                                           

set_option autoImplicit false
open MeasureTheory NlsGge.Pilot NlsGge.Measure
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.T

theorem finiteFourier_h2Tilt_identity
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (h0 : δ < c.val 0) (h2 : 16 * δ < c.val 2) :
    ∃ (lower' : ℝ) (c' : BoundedCoefficients lower' upper),
      0 < lower' ∧ c'.val = NlsGge.AblowitzLadik.alTiltCoeff38 c.val δ ∧
      ∀ N : ℕ,
        Integrable
          (fun z : FourierPlane N =>
            fFourier38 c N z * Real.exp (δ * tiltG38 N z))
          (fullWeightFourierGaussian N c.val) ∧
        (∫ z : FourierPlane N,
          fFourier38 c N z * Real.exp (δ * tiltG38 N z)
          ∂fullWeightFourierGaussian N c.val) =
            (tiltD38 c.val δ N)⁻¹ * relativePartition38 c' N := by
  obtain ⟨lo', hpos, _, hadm⟩ := alTiltCoeff_admitted_general38 c hδ h0 h2
  let c' : BoundedCoefficients lo' upper := ⟨NlsGge.AblowitzLadik.alTiltCoeff38 c.val δ, hadm⟩
  exact ⟨lo', c', hpos, rfl, fun N =>
    ⟨integrable_fFourier_tilt38 c c' δ rfl N, fourierTilt_identity38 c c' δ rfl N⟩⟩

theorem finiteFourier_h2Tilt_identity_Es
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (h0 : δ < c.val 0) (h2 : 16 * δ < c.val 2) :
    ∃ (lower' : ℝ) (c' : BoundedCoefficients lower' upper),
      0 < lower' ∧ c'.val = NlsGge.AblowitzLadik.alTiltCoeff38 c.val δ ∧
      ∀ (s : ℝ), (1 : ℝ) / 2 < s → ∀ N : ℕ,
        Integrable
          (fun x : NlsGge.Birkhoff.ECarrier38 c s =>
            NlsGge.Birkhoff.fN38 c s N x *
              Real.exp (δ * tiltG38 N
                (NlsGge.Birkhoff.planeOfSeq38 N
                  (NlsGge.Ramer.coordE c s x))))
          (fullWeightedSequenceGaussian c s) ∧
        (∫ x : NlsGge.Birkhoff.ECarrier38 c s,
          NlsGge.Birkhoff.fN38 c s N x *
            Real.exp (δ * tiltG38 N
              (NlsGge.Birkhoff.planeOfSeq38 N
                (NlsGge.Ramer.coordE c s x)))
              ∂fullWeightedSequenceGaussian c s) =
                (tiltD38 c.val δ N)⁻¹ * relativePartition38 c' N := by
  obtain ⟨lo', hpos, _, hadm⟩ := alTiltCoeff_admitted_general38 c hδ h0 h2
  let c' : BoundedCoefficients lo' upper := ⟨NlsGge.AblowitzLadik.alTiltCoeff38 c.val δ, hadm⟩
  refine ⟨lo', c', hpos, rfl, fun s hs N => ?_⟩
  have hφi : Integrable (fun z : FourierPlane N => fFourier38 c N z * Real.exp (δ * tiltG38 N z))
      (fullWeightFourierGaussian N c.val) := integrable_fFourier_tilt38 c c' δ rfl N
  have heq : (fun x : NlsGge.Birkhoff.ECarrier38 c s =>
      NlsGge.Birkhoff.fN38 c s N x * Real.exp (δ * tiltG38 N
        (NlsGge.Birkhoff.planeOfSeq38 N (NlsGge.Ramer.coordE c s x)))) =
      fun x : NlsGge.Birkhoff.ECarrier38 c s =>
        (fun z : FourierPlane N => fFourier38 c N z * Real.exp (δ * tiltG38 N z))
          (NlsGge.Birkhoff.planeOfSeq38 N (NlsGge.Ramer.coordE c s x)) := by
    funext x
    rw [NlsGge.Birkhoff.fN38_eq_fNseq c s N x]
    rfl
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact NlsGge.ThirdConsultation.T.integrable_comp_planeCoord98 c s hs N _ hφi
  · rw [heq]
    exact (NlsGge.Birkhoff.integral_transfer38 c s hs N _ hφi.aestronglyMeasurable).trans
      (fourierTilt_identity38 c c' δ rfl N)

end NlsGge.ThirdConsultation.T
