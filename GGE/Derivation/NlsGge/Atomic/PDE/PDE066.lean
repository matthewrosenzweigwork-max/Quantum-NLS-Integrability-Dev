import Mathlib
import NlsGge.ThirdConsultation.PDE.Round14InverseRotation
import NlsGge.ThirdConsultation.PDE.PDE066Core
import NlsGge.ThirdConsultation.PDE.BirkhoffRaw
import NlsGge.ThirdConsultation.Common.Actions
import NlsGge.Atomic.PDE.PDE065
import NlsGge.Atomic.G6.G6027
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6029

/- PDE-066 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/PDE/PDE066.lean,
   namespace NlsGge.ThirdConsultation.PDE. Head VERBATIM from Pro r14 '### PDE-066'.
   Opens: Pro's prelude plus `open NlsGge.ThirdConsultation.Common` (repair 22 addendum: actualPhi, actions,
   FiniteSupportSequence are COMMON names).
   Proof (source strategy "uniqueness identifies finite-gap rotations with nlsFlowL2"): z0 := actualPhi u.
   (1) u ∈ H¹: finite support of physicalBirkhoff u ↔ finiteGap u ⇒ all Sobolev (landed G6029).
   (2) inverseRotationPhysical z0 hfin solves the actual NLS (PDE-065, h783, second conjunct).
   (3) Its value at 0 is u: G6027 3 (embed ∘ inverseBirkhoffSobolev = physicalInverseBirkhoff ∘ sequenceSobolevEmbed),
       rotation at t = 0 is z0, G6013 left inverse.
   (4) PDE066Aux.flow_eq_of_solution (landed PDE-034 uniqueness) ⇒ curve t = nlsFlowL2 t u.
   (5) actualPhi of the curve = rotationSequence z0 t (G6027 3 + G6013 right inverse + seqEmbed_coe); coefficient n is
       the displayed rotation by definition.
   MAIN-ONLY (G6027/G6013/G6029 closures; PDE-065 not yet drafted; Round14Rotation -> Round14ActionFreq). -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem actual_finitegap_rotation
    (u : PhysicalL2) (hfin : FiniteSupportSequence (actualPhi u))
    (t : ℝ) (n : ℤ) :
  actualPhi (nlsFlowL2 t u) n =
    Complex.exp (-Complex.I *
      ((t * actualOmega n (actions (actualPhi u)) : ℝ) : ℂ)) * actualPhi u n := by
  obtain ⟨-, -, -, -, -, hinvB⟩ := G6027 3 (by norm_num)
  obtain ⟨-, -, -, -, hL, hR⟩ := G6013
  have hG29 : ∀ u : PhysicalL2,
      ((Function.support (physicalBirkhoff u : ℤ → ℂ)).Finite ↔ finiteGap u) ∧
      (finiteGap u → ∀ m : ℕ, fourierSeq38 u ∈ seqSobolev38 (m : ℝ)) :=
    fun u => ⟨(G6029 u).1, (G6029 u).2.1⟩
  have h65 := fun (z0 : Lib.L2Z) (hz : FiniteSupportSequence z0) =>
    (inverse_rotation_is_actual_nls z0 hz).2
  have hgap : finiteGap u := (hG29 u).1.1 hfin
  have hu : SobolevSquareSummable 1 (physicalFourier u) := by
    have h := (fourierSeq38_mem_iff _ u).1 ((hG29 u).2 hgap 1)
    rwa [Nat.cast_one] at h
  have hcurve : ∀ s : ℝ, actualPhi (inverseRotationPhysical (actualPhi u) hfin s) =
      sequenceSobolevEmbed 3 (rotationCurve ((3 : ℕ) : ℝ) (actualPhi u) hfin s) := by
    intro s
    show physicalBirkhoff (physicalSobolevEmbed 3
      (inverseBirkhoffSobolev 3 (rotationCurve ((3 : ℕ) : ℝ) (actualPhi u) hfin s))) = _
    rw [(hinvB _).2]
    exact hR _
  have hcoef : ∀ (s : ℝ) (k : ℤ),
      (sequenceSobolevEmbed 3 (rotationCurve ((3 : ℕ) : ℝ) (actualPhi u) hfin s) : ℤ → ℂ) k =
        rotationSequence (actualPhi u) s k := fun s k => by
    rw [PDE066Aux.seqEmbed_coe]
    rfl
  have hstart : sequenceSobolevEmbed 3 (rotationCurve ((3 : ℕ) : ℝ) (actualPhi u) hfin 0) =
      actualPhi u := by
    apply lp.ext
    funext k
    rw [hcoef]
    simp [rotationSequence]
  have h0 : inverseRotationPhysical (actualPhi u) hfin 0 = u := by
    show physicalSobolevEmbed 3
      (inverseBirkhoffSobolev 3 (rotationCurve ((3 : ℕ) : ℝ) (actualPhi u) hfin 0)) = u
    rw [(hinvB _).2, hstart]
    exact hL u
  have heq := PDE066Aux.flow_eq_of_solution _ (h65 (actualPhi u) hfin) u h0 hu t
  rw [← heq, hcurve, hcoef]
  rfl

end NlsGge.ThirdConsultation.PDE
