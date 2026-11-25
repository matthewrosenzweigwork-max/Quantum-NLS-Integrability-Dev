import NlsGge.Ramer.LocalBump
import NlsGge.Ramer.General.HeadLawG

/-!
# Local bump truncation over a `RamerSetting`

Generalized concrete part of `NlsGge/Ramer/LocalBump.lean`: the generic lemma
`NlsGge.Ramer.exists_bumped_field_generic` is imported unchanged and instantiated at `S.E → S.H`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Ramer.General.RamerSetting

variable (S : RamerSetting)

theorem exists_bumped_field
    (K : S.E → S.H) (hK : ContDiff ℝ 2 K) (x₀ : S.E) :
    ∃ r > 0, ∃ G : S.E → S.H, ∃ B : ℝ,
      ContDiff ℝ 2 G ∧ (∀ x, ‖G x‖ ≤ B) ∧ (∀ x, ‖fderiv ℝ G x‖ ≤ B) ∧
      Set.EqOn G K (Metric.ball x₀ r) :=
  NlsGge.Ramer.exists_bumped_field_generic K hK x₀

end NlsGge.Ramer.General.RamerSetting
