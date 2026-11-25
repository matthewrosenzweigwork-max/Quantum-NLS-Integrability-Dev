import NlsGge.Ramer.RamerStep2Fibrewise
import NlsGge.Ramer.SpaceTransfer

                                                                                                                                                                                                                                                       

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.ThirdConsultation.R.BindingR011

abbrev Head {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ) :=
  NlsGge.Ramer.actualCMHead c N

abbrev Tail (N : ℕ) := NlsGge.Ramer.TailSpace N

def γRaw {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) :
    Measure (ℤ → ℂ) :=
  NlsGge.Measure.fullWeightSequenceGaussian c.val

def γ {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    Measure (NlsGge.Pilot.FullWeightedHilbert c s) :=
  NlsGge.Measure.fullWeightedSequenceGaussian c s

def γHead {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ) :
    Measure (Head c N) :=
  NlsGge.Ramer.finiteStdGaussian (NlsGge.Ramer.actualCMHead c N)

def γTail {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ) :
    Measure (Tail N) :=
  (γRaw c).map (NlsGge.Ramer.tailPt N)

def headTailRaw {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ)
    (z : ℤ → ℂ) : Head c N × Tail N :=
  (NlsGge.Ramer.headPt c N z, NlsGge.Ramer.tailPt N z)

def headTail {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) (N : ℕ)
    (x : NlsGge.Pilot.FullWeightedHilbert c s) : Head c N × Tail N :=
  headTailRaw c N (NlsGge.Ramer.coordE c s x)

namespace R011Aux

theorem measurable_headTailRaw {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ) :
    Measurable (headTailRaw c N) :=
  (NlsGge.Ramer.measurable_headPt c N).prodMk (NlsGge.Ramer.measurable_tailPt N)

theorem map_headTailRaw {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ) :
    (γRaw c).map (headTailRaw c N) = (γHead c N).prod (γTail c N) := by
  show (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
      (fun z => (NlsGge.Ramer.headPt c N z, NlsGge.Ramer.tailPt N z)) = _
  exact NlsGge.Ramer.map_headPt_tailPt c N

theorem raw_integral {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ)
    (f : Head c N × Tail N → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (headTailRaw c N z) ∂(γRaw c)) =
      ∫⁻ t, ∫⁻ h, f (h, t) ∂(γHead c N) ∂(γTail c N) := by
  haveI : IsProbabilityMeasure (γRaw c) := by
    unfold γRaw
    infer_instance
  haveI : IsFiniteMeasure (γTail c N) := by
    unfold γTail
    infer_instance
  haveI : IsProbabilityMeasure (γHead c N) := by
    unfold γHead
    infer_instance
  rw [← lintegral_map hf (measurable_headTailRaw c N), map_headTailRaw c N]
  exact lintegral_prod_symm f hf.aemeasurable

end R011Aux

open R011Aux in
theorem gaussian_head_tail_map
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (N : ℕ) :
    (γ c s).map (headTail c s N) = (γHead c N).prod (γTail c N) := by
  have hmp' : (γ c s).map (NlsGge.Ramer.coordE c s) = γRaw c :=
    (NlsGge.Ramer.measurePreserving_coordE c s hs).map_eq
  show (γ c s).map (headTailRaw c N ∘ NlsGge.Ramer.coordE c s) = _
  rw [← Measure.map_map (measurable_headTailRaw c N) (NlsGge.Ramer.measurable_coordE c s), hmp']
  exact map_headTailRaw c N

open R011Aux in
theorem gaussian_head_tail_integral
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (N : ℕ)
    (f : Head c N × Tail N → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (headTail c s N x) ∂(γ c s)) =
      ∫⁻ t, ∫⁻ h, f (h, t) ∂(γHead c N) ∂(γTail c N) := by
  have hmp' : (γ c s).map (NlsGge.Ramer.coordE c s) = γRaw c :=
    (NlsGge.Ramer.measurePreserving_coordE c s hs).map_eq
  have hg : Measurable (fun z => f (headTailRaw c N z)) := hf.comp (measurable_headTailRaw c N)
  calc (∫⁻ x, f (headTail c s N x) ∂(γ c s))
      = ∫⁻ z, f (headTailRaw c N z) ∂((γ c s).map (NlsGge.Ramer.coordE c s)) :=
        (lintegral_map hg (NlsGge.Ramer.measurable_coordE c s)).symm
    _ = ∫⁻ z, f (headTailRaw c N z) ∂(γRaw c) := by rw [hmp']
    _ = _ := raw_integral c N f hf

open R011Aux in
theorem gaussian_head_tail_integral_raw
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (N : ℕ)
    (f : Head c N × Tail N → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (headTailRaw c N z) ∂(γRaw c)) =
      ∫⁻ t, ∫⁻ h, f (h, t) ∂(γHead c N) ∂(γTail c N) :=
  raw_integral c N f hf

end NlsGge.ThirdConsultation.R.BindingR011
end
