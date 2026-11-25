import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.G1.Round5

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.HierarchyRiccati.Core

namespace NlsGge.GKDefinitionDesign

def reflC (r : ℝ) (z : SobolevCarrier38 r) : SobolevCarrier38 r :=
  carrierMk38 r (fun n : ℤ => -carrierCoe38 r z (-n))
    ((mem_seqSobolev38_iff r _).2
      (sobolevSquareSummable_reflection r (carrierCoe38 r z)
        ((mem_seqSobolev38_iff r _).1 (carrierCoe38_mem r z))))

theorem reflC_coe (r : ℝ) (z : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (reflC r z) n = -carrierCoe38 r z (-n) := rfl

theorem carrierCoe38_add (r : ℝ) (x y : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (x + y) n = carrierCoe38 r x n + carrierCoe38 r y n := rfl

theorem carrierCoe38_smul (r : ℝ) (c : ℝ) (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (c • x) n = (c : ℂ) * carrierCoe38 r x n := by
  change ((c : ℝ) • (carrierCoe38 r x)) n = _
  simp [Complex.real_smul]

theorem reflC_norm (r : ℝ) (z : SobolevCarrier38 r) : ‖reflC r z‖ = ‖z‖ := by
  have h1 : ‖z‖ ^ 2 = ∑' n : ℤ, sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2 :=
    weightedHilbert_norm_sq (sobolevModeWeight r)
      (show WeightedHilbert (sobolevModeWeight r) from z)
  have h2 : ‖reflC r z‖ ^ 2 =
      ∑' n : ℤ, sobolevModeWeight r n * ‖-carrierCoe38 r z (-n)‖ ^ 2 :=
    weightedHilbert_norm_sq (sobolevModeWeight r)
      (show WeightedHilbert (sobolevModeWeight r) from reflC r z)
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [h2, h1]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n => sobolevModeWeight r n * ‖carrierCoe38 r z n‖ ^ 2)]
  refine tsum_congr (fun n => ?_)
  simp only [Equiv.neg_apply, norm_neg]
  have : sobolevModeWeight r (-n) = sobolevModeWeight r n := by
    simp [sobolevModeWeight, japaneseBracket]
  rw [this]

def reflLin (r : ℝ) : SobolevCarrier38 r →ₗ[ℝ] SobolevCarrier38 r where
  toFun := reflC r
  map_add' x y := by
    apply carrierExt38; funext n
    rw [reflC_coe, carrierCoe38_add, carrierCoe38_add, reflC_coe, reflC_coe]; ring
  map_smul' c x := by
    apply carrierExt38; funext n
    rw [reflC_coe, RingHom.id_apply, carrierCoe38_smul, carrierCoe38_smul, reflC_coe]; ring

def reflCLM (r : ℝ) : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 r :=
  (reflLin r).mkContinuous 1 (fun z => by
    change ‖reflC r z‖ ≤ 1 * ‖z‖
    rw [reflC_norm, one_mul])

theorem reflCLM_apply (r : ℝ) (z : SobolevCarrier38 r) : reflCLM r z = reflC r z := rfl

/-- The continuous-representative CLM on the completion. -/
def iotaCLM : PhysicalSobolev38 ((1 : ℕ) : ℝ) →L[ℝ] C(PhysicalCircle, ℂ) :=
  ((liftCLM38 (riccatiSobolevLowerJetContinuousRepresentativeCLMRecovery30Eighth 1 0
      (by simp))).comp (reflCLM ((1 : ℕ) : ℝ))).comp
    (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).toContinuousLinearEquiv.toContinuousLinearMap

theorem iotaCLM_apply (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) :
    iotaCLM u = physicalSobolevContinuous38 1 le_rfl u := rfl

end NlsGge.GKDefinitionDesign
end
