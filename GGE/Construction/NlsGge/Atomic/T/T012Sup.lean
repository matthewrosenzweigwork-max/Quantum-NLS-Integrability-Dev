import Mathlib
import NlsGge.Definitions.BorelWeighted
import NlsGge.Measure.CountableReconstruction
import NlsGge.Hierarchy.RelativePartition38
import NlsGge.Weights.Entire
import NlsGge.Birkhoff.W04WeightedSmoothing38
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.W07Probability38
import NlsGge.Birkhoff.W07Probability38e
import NlsGge.Birkhoff.W09Approx38
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Birkhoff.F09Limit38
import NlsGge.Birkhoff.F09Limit38f
import NlsGge.Birkhoff.H03Diagonal38b
import NlsGge.Birkhoff.W11Equivalence38
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.ThirdConsultation.I.I030Core
import NlsGge.Atomic.T.T005

                                                                                 
                                                                
                                                                          
                                                                                 
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.T.T012Sup
noncomputable section

theorem norm_physFS38_physOfE38
    {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s) :
    ‖physFS38 2 (physOfE38 c s x)‖ = ‖eToSob38 c s 2 x‖ := by
  rw [NlsGge.ThirdConsultation.I030Aux.norm_physFS38_eq, physH38_physOfE38]
  have htwo : (((1 + 1 : ℕ) : ℝ)) = (2 : ℝ) := by norm_num
  rw [htwo]

theorem expH2_withDensity_ECarrier98
    {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) (N : ℕ) (eta : ℝ)
    (hnum : Integrable
      (fun x : ECarrier38 c s => fN38 c s N x *
        Real.exp (eta * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2))
      (fullWeightedSequenceGaussian c s)) :
    Integrable
        (fun x : FullWeightedHilbert c s =>
          Real.exp (eta * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2))
        ((fullWeightedSequenceGaussian c s).withDensity
          (fun x : FullWeightedHilbert c s => ENNReal.ofReal (fN38 c s N x))) ∧
      (∫ x : FullWeightedHilbert c s,
        Real.exp (eta * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)
        ∂((fullWeightedSequenceGaussian c s).withDensity
          (fun x : FullWeightedHilbert c s => ENNReal.ofReal (fN38 c s N x)))) =
      ∫ x : FullWeightedHilbert c s, fN38 c s N x *
        Real.exp (eta * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)
        ∂fullWeightedSequenceGaussian c s := by
  have hnumFW : Integrable
      (fun x : FullWeightedHilbert c s => fN38 c s N x *
        Real.exp (eta * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2))
      (fullWeightedSequenceGaussian c s) := by
    exact hnum
  let F : FullWeightedHilbert c s → ℝ :=
    fun x => Real.exp (eta * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)
  let ρ : FullWeightedHilbert c s → ℝ≥0∞ := fun x => ENNReal.ofReal (fN38 c s N x)
  have hρ : Measurable ρ := (measurable_fN38 c s N).ennreal_ofReal
  have hρlt : ∀ᵐ x ∂fullWeightedSequenceGaussian c s, ρ x < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hweighted : Integrable
      (fun x : FullWeightedHilbert c s => F x * (ρ x).toReal)
      (fullWeightedSequenceGaussian c s) := by
    refine hnumFW.congr (Eventually.of_forall fun x => ?_)
    change fN38 c s N x * F x = F x * (ENNReal.ofReal (fN38 c s N x)).toReal
    rw [ENNReal.toReal_ofReal (fN38_pos c s N x).le]
    exact mul_comm _ _
  have hden : Integrable F ((fullWeightedSequenceGaussian c s).withDensity ρ) :=
    (integrable_withDensity_iff hρ hρlt).2 hweighted
  refine ⟨hden, ?_⟩
  change (∫ x : FullWeightedHilbert c s, F x
      ∂((fullWeightedSequenceGaussian c s).withDensity ρ)) =
    ∫ x : FullWeightedHilbert c s, fN38 c s N x * F x
      ∂fullWeightedSequenceGaussian c s
  calc
    _ = ∫ x : FullWeightedHilbert c s, (ρ x).toReal • F x
          ∂fullWeightedSequenceGaussian c s :=
      integral_withDensity_eq_integral_toReal_smul hρ hρlt F
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => by
      change (ENNReal.ofReal (fN38 c s N x)).toReal * F x = fN38 c s N x * F x
      rw [ENNReal.toReal_ofReal (fN38_pos c s N x).le])

theorem expH2_integrable_nuWN38_of_ECarrier98
    {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (N : ℕ) (eta : ℝ)
    (hE : Integrable
      (fun x : FullWeightedHilbert c s =>
        Real.exp (eta * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2))
      ((fullWeightedSequenceGaussian c s).withDensity
        (fun x : FullWeightedHilbert c s => ENNReal.ofReal (fN38 c s N x)))) :
    Integrable (fun u : PhysicalL2 => Real.exp (eta * ‖physFS38 2 u‖ ^ 2))
      (nuWN38 c N) := by
  let G : PhysicalL2 → ℝ := fun u => Real.exp (eta * ‖physFS38 2 u‖ ^ 2)
  have hG : Measurable G :=
    Real.measurable_exp.comp (((measurable_physFS38 2).norm.pow_const 2).const_mul eta)
  have hψ : Measurable
      (fun x : FullWeightedHilbert c s => physOfE38 c s (projE38 c s N x)) :=
    measurable_physProj38 c s N
  have hcomp : Integrable
      (fun x : FullWeightedHilbert c s => G (physOfE38 c s (projE38 c s N x)))
      ((fullWeightedSequenceGaussian c s).withDensity
        (fun x : FullWeightedHilbert c s => ENNReal.ofReal (fN38 c s N x))) := by
    refine hE.congr (Eventually.of_forall fun x => ?_)
    exact (congrArg (fun t : ℝ => Real.exp (eta * t ^ 2))
      (norm_physFS38_physOfE38 c s (projE38 c s N x))).symm
  have hmap : Integrable G
      (((fullWeightedSequenceGaussian c s).withDensity
        (fun x : FullWeightedHilbert c s => ENNReal.ofReal (fN38 c s N x))).map
        (fun x : FullWeightedHilbert c s => physOfE38 c s (projE38 c s N x))) :=
    (integrable_map_measure hG.aestronglyMeasurable hψ.aemeasurable).2 hcomp
  have hscaled := hmap.smul_measure
    (c := ENNReal.ofReal (1 / relativePartition38 c N)) ENNReal.ofReal_ne_top
  exact (nuWN38_eq_map c s hs N).symm ▸ hscaled

theorem expH2_numerator_bound_FullWeighted_of_ECarrier98
    {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) (N : ℕ) (eta C0 : ℝ)
    (hnum : (∫ x : ECarrier38 c s, fN38 c s N x *
      Real.exp (eta * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)
      ∂fullWeightedSequenceGaussian c s) ≤ C0) :
    (0 ≤ ∫ x : FullWeightedHilbert c s,
      Real.exp (eta * ‖physFS38 2 (physOfE38 c s (projE38 c s N x))‖ ^ 2) *
        fN38 c s N x ∂fullWeightedSequenceGaussian c s) ∧
    (∫ x : FullWeightedHilbert c s,
      Real.exp (eta * ‖physFS38 2 (physOfE38 c s (projE38 c s N x))‖ ^ 2) *
        fN38 c s N x ∂fullWeightedSequenceGaussian c s) ≤ C0 := by
  have hnumFW : (∫ x : FullWeightedHilbert c s, fN38 c s N x *
      Real.exp (eta * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2)
      ∂fullWeightedSequenceGaussian c s) ≤ C0 := by
    exact hnum
  refine ⟨integral_nonneg (fun x =>
    mul_nonneg (Real.exp_pos _).le (fN38_pos c s N x).le), ?_⟩
  have heq (x : FullWeightedHilbert c s) :
      Real.exp (eta * ‖physFS38 2 (physOfE38 c s (projE38 c s N x))‖ ^ 2) *
        fN38 c s N x =
      fN38 c s N x * Real.exp (eta * ‖eToSob38 c s 2 (projE38 c s N x)‖ ^ 2) :=
    (congrArg (fun t : ℝ => t * fN38 c s N x)
      (congrArg (fun t : ℝ => Real.exp (eta * t ^ 2))
        (norm_physFS38_physOfE38 c s (projE38 c s N x)))).trans (mul_comm _ _)
  exact (integral_congr_ae (Eventually.of_forall heq)).trans_le hnumFW

end
end NlsGge.ThirdConsultation.T.T012Sup
