import NlsGge.ThirdConsultation.Records.RecordsB
import NlsGge.Ramer.SpaceTransfer
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

   
                                            
                                                                 
                                                                             
                                                                        
                                                                            
                                                               
  
set_option autoImplicit false
noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.Records

/-- The canonical nonlinear energy is a measurable real random variable, and
it is the probability limit of the exact complete finite Fourier energy differences. -/
theorem W07_remark_concrete {lower upper : ℝ}
    (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    let fW : ECarrier38 c s → ℝ :=
      NlsGge.ThirdConsultation.R.actualRamerDensity c s hs
        (le_one_of_lt_three_quarters_W06_38 hs')
    AEStronglyMeasurable (fun x : ECarrier38 c s => -Real.log (fW x))
      (fullWeightedSequenceGaussian c s) ∧
    (∀ᵐ x ∂(fullWeightedSequenceGaussian c s), 0 < fW x) ∧
    (∀ (N : ℕ) (x : FullWeightedHilbert c s),
      spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x)) ≠ ⊤ ∧
      -Real.log (fN38 c s N x) =
        (spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal -
          Afin38 c N (NlsGge.Ramer.coordE c s x)) ∧
    TendstoInMeasure (fullWeightedSequenceGaussian c s)
      (fun (N : ℕ) (x : FullWeightedHilbert c s) =>
        (spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal -
          Afin38 c N (NlsGge.Ramer.coordE c s x)) atTop
      (fun x : ECarrier38 c s => -Real.log (fW x)) := by
  intro fW
  let γ : Measure (FullWeightedHilbert c s) := fullWeightedSequenceGaussian c s
  haveI : IsProbabilityMeasure γ :=
    inferInstanceAs (IsProbabilityMeasure (fullWeightedSequenceGaussian c s))
  have hfinite : ∀ (N : ℕ) (x : FullWeightedHilbert c s),
      spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x)) ≠ ⊤ :=
    fun N x => spectralEnergy_projE38_ne_top_W07 c N x
  have hId : ∀ (N : ℕ) (x : FullWeightedHilbert c s),
      -Real.log (fN38 c s N x) =
        (spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal -
          Afin38 c N (NlsGge.Ramer.coordE c s x) := by
    intro N x
    change -Real.log (Real.exp
      (-(spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal +
        Afin38 c N (NlsGge.Ramer.coordE c s x))) = _
    rw [Real.log_exp]
    ring
  have hint : Integrable fW γ := (W07_concrete c s hs hs').1.2.2.1
  have hconv : TendstoInMeasure γ (fun N x => fN38 c s N x) atTop fW :=
    (W07_concrete c s hs hs').1.2.2.2.2.1
  have hpos : ∀ x : FullWeightedHilbert c s, 0 < fW x :=
    (NlsGge.ThirdConsultation.R.actual_density_pushforward c s hs hs').1
  have hposAE : ∀ᵐ x ∂γ, 0 < fW x := Filter.Eventually.of_forall hpos
  have hV : AEStronglyMeasurable (fun x => -Real.log (fW x)) γ :=
    ((Real.measurable_log.comp_aemeasurable hint.aemeasurable).neg).aestronglyMeasurable
  have hmeas : ∀ N : ℕ,
      AEStronglyMeasurable (fun x : FullWeightedHilbert c s =>
        -Real.log (fN38 c s N x)) γ := by
    intro N
    exact ((Real.measurable_log.comp (measurable_fN38 c s N)).neg).aestronglyMeasurable
  have hlog : TendstoInMeasure γ
      (fun (N : ℕ) (x : FullWeightedHilbert c s) => -Real.log (fN38 c s N x))
      atTop (fun x => -Real.log (fW x)) := by
    apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).2
    intro ns hns
    obtain ⟨ms, hms, hae⟩ := (hconv.comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ms, hms, ?_⟩
    filter_upwards [hae, hposAE] with x hx hxpos
    exact (hx.log hxpos.ne').neg
  refine ⟨hV, hposAE, fun N x => ⟨hfinite N x, hId N x⟩, ?_⟩
  exact TendstoInMeasure.congr_left
    (fun N => Filter.Eventually.of_forall (hId N)) hlog

end NlsGge.ThirdConsultation.Records
end
