import NlsGge.Birkhoff.F09Limit38b
import NlsGge.Birkhoff.W07Probability38
import NlsGge.Ramer.SpaceTransfer

/- ECARRIER98 host, module NlsGge.ThirdConsultation.T.ECarrier98 (author proof development; packaged by proof development;
   not reviewed, not accepted). Shared host for T-003, T-005, T-006, T-007.
   Owner: proof development. Holds only: definitional MeasurableSpace/BorelSpace instances for the carrier
   ECarrier38 c s (= FullWeightedHilbert c s by rfl; no ECarrier38 measurable structure existed), and
   transport lemmas from the Fourier plane to the E_s Gaussian through coordE and planeOfSeq38.
   Imports: F09Limit38b (integral_transfer38, norm_sq_eToSob2_projE38, measurable_planeOfSeq38),
   W07Probability38 (fN38_eq_fNseq, measurable_fNseq38, map_planeOfSeq38), SpaceTransfer (measurePreserving_coordE).
   B/O-free: uses only these three modules, none of which carries a BirkhoffInput38 or OneSmoothingInput38 premise. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.ThirdConsultation.T

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core

instance eCarrierMeasurableSpace98 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) :
    MeasurableSpace (ECarrier38 c s) :=
  inferInstanceAs (MeasurableSpace (FullWeightedHilbert c s))

instance eCarrierBorelSpace98 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) :
    BorelSpace (ECarrier38 c s) :=
  ⟨rfl⟩

theorem measurable_fN38_98 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) :
    Measurable (fN38 c s N) := by
  have h : fN38 c s N = fNseq38 c N ∘ NlsGge.Ramer.coordE c s :=
    funext fun x => fN38_eq_fNseq c s N x
  rw [h]
  exact (measurable_fNseq38 c N).comp (NlsGge.Ramer.measurable_coordE c s)

theorem normSq_projE98 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (x : ECarrier38 c s) :
    ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2 =
      planeH2NormSq38 N (planeOfSeq38 N (NlsGge.Ramer.coordE c s x)) := by
  have h := norm_sq_eToSob2_projE38 c s N x
  have e2 : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
  rw [e2] at h
  exact h

theorem fun_eq_planeCoord98 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (η : ℝ) :
    (fun x : ECarrier38 c s =>
        fN38 c s N x * Real.exp (η * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)) =
      fun x : ECarrier38 c s =>
        (fun z : FourierPlane N => fFourier38 c N z * Real.exp (η * planeH2NormSq38 N z))
          (planeOfSeq38 N (NlsGge.Ramer.coordE c s x)) := by
  funext x
  rw [normSq_projE98 c s N x, fN38_eq_fNseq c s N x]
  rfl

theorem integrable_comp_planeCoord98 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (N : ℕ) (φ : FourierPlane N → ℝ)
    (hφ : Integrable φ (fullWeightFourierGaussian N c.val)) :
    Integrable (fun x : ECarrier38 c s => φ (planeOfSeq38 N (NlsGge.Ramer.coordE c s x)))
      (fullWeightedSequenceGaussian c s) := by
  have hm : Measurable (fun x : FullWeightedHilbert c s =>
      planeOfSeq38 N (NlsGge.Ramer.coordE c s x)) :=
    (measurable_planeOfSeq38 N).comp (NlsGge.Ramer.measurable_coordE c s)
  have hmap : (fullWeightedSequenceGaussian c s).map
      (fun x : FullWeightedHilbert c s => planeOfSeq38 N (NlsGge.Ramer.coordE c s x)) =
      fullWeightFourierGaussian N c.val := by
    rw [show (fun x : FullWeightedHilbert c s => planeOfSeq38 N (NlsGge.Ramer.coordE c s x)) =
        planeOfSeq38 N ∘ NlsGge.Ramer.coordE c s from rfl,
      ← Measure.map_map (measurable_planeOfSeq38 N) (NlsGge.Ramer.measurable_coordE c s),
      (NlsGge.Ramer.measurePreserving_coordE c s hs).map_eq, map_planeOfSeq38 c N]
  have hφ' : AEStronglyMeasurable φ ((fullWeightedSequenceGaussian c s).map
      (fun x : FullWeightedHilbert c s => planeOfSeq38 N (NlsGge.Ramer.coordE c s x))) := by
    rw [hmap]; exact hφ.aestronglyMeasurable
  have key : Integrable (fun x : FullWeightedHilbert c s => φ (planeOfSeq38 N (NlsGge.Ramer.coordE c s x)))
      (fullWeightedSequenceGaussian c s) :=
    (integrable_map_measure hφ' hm.aemeasurable).1 (by rw [hmap]; exact hφ)
  exact key

end NlsGge.ThirdConsultation.T

-- end of the noncomputable section opened above
end
