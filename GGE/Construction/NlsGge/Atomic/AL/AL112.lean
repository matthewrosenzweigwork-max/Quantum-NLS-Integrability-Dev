import NlsGge.Sobolev.SourceWeighted
import NlsGge.Hierarchy.ALTilt38
import NlsGge.Hierarchy.ALFiniteMeasure38

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        
                                                                                                             
                                                                                                               
                                                                                
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.Analysis
open NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik
open NlsGge.Weights

namespace NlsGge.ThirdConsultation.AL
noncomputable section

theorem al112 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ lower / 64) :
    AdmittedCoefficients (3 * lower / 4) upper (alTiltCoeff38 c.val delta) ∧
    alTiltCoeff38 c.val delta 0 = c.val 0 - delta ∧
    alTiltCoeff38 c.val delta 2 = c.val 2 - 16 * delta ∧
    (∀ j : ℕ, j ≠ 0 → j ≠ 2 → alTiltCoeff38 c.val delta j = c.val j) ∧
    (∀ r : ℝ, weight (alTiltCoeff38 c.val delta) r =
      weight c.val r - delta * (1 + r ^ 4)) ∧
    ∀ (L : ℕ) [NeZero L], (3 * lower / 4)⁻¹ < (L : ℝ) →
      let h : ℝ := (L : ℝ)⁻¹
      Integrable (alIntegrand38 (L := L) (alTiltCoeff38 c.val delta) h) ∧
      0 < alPartition38 L (alTiltCoeff38 c.val delta) h ∧
      IsProbabilityMeasure (alEta38 L (alTiltCoeff38 c.val delta) h) ∧
      Integrable (alReweight38 (L := L) (alTiltCoeff38 c.val delta) h)
        (alGauss38 (L := L) (alTiltCoeff38 c.val delta) h) ∧
      0 < alZ38 (L := L) (alTiltCoeff38 c.val delta) h ∧
      alPartition38 L (alTiltCoeff38 c.val delta) h =
        h ^ L * (∏ k : ZMod L,
          Real.pi / alRate38 (alTiltCoeff38 c.val delta) h k.valMinAbs) *
          alZ38 (L := L) (alTiltCoeff38 c.val delta) h := by
  have hadm : AdmittedCoefficients (3 * lower / 4) upper (alTiltCoeff38 c.val delta) :=
    alTiltCoeff_admitted38 c.2 hdelta0 hdelta
  refine ⟨hadm, ?_, ?_, ?_, ?_, ?_⟩
  · simp [alTiltCoeff38]
  · simp [alTiltCoeff38]
  · intro j hj0 hj2
    simp [alTiltCoeff38, hj0, hj2]
  · intro r
    exact weight_tilt38 c.2 delta r
  · intro L _ hL
    intro h
    have hh : h = (L : ℝ)⁻¹ := rfl
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have hh0 : 0 < h := by rw [hh]; positivity
    obtain ⟨hint, hpos, -, -, hrew, -, hZ, hid, -⟩ :=
      alGaussianNormalizer_bundled38 (L := L) hadm hh hL
    exact ⟨hint, hpos, isProbabilityMeasure_alEta38 hadm hh0, hrew, hZ, hid⟩

