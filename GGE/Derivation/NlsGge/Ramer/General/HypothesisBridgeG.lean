import NlsGge.Ramer.General.DivergenceIdentificationGlobalG
import NlsGge.Ramer.HypothesisBridge

/-!
# From the v2 hypotheses to Ramer's hypotheses (1)–(3), over a `RamerSetting`

Concrete part of `NlsGge/Ramer/HypothesisBridge.lean` over an arbitrary
`S : RamerSetting`. The abstract part (`hs_comp_left`, `hasFDerivAt_H_direction`,
`exists_inverse_id_add_HDeriv`, `ramer_hypotheses_of_v2`, generic `E`, `H`) is imported unchanged
from `NlsGge.Ramer`. Injectivity, density of range and the Hilbert–Schmidt property of the
inclusion are `S.incl_injective`, `S.incl_denseRange`, `S.incl_hs` (G0).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace NlsGge.Ramer.General.RamerSetting

variable (S : NlsGge.Ramer.General.RamerSetting)

/-- **Concrete bridge over `S`.** For `E = S.E`, `H = S.H`, any homeomorphism
`T = id + i ∘ K` with inverse `id + i ∘ K'`, where `K, K' : S.E → S.H` are `C¹`, satisfies all of
Ramer's hypotheses (2)–(3) on `U = S.E`. (Old: `actual_ramer_hypotheses_of_v2`.) -/
theorem actual_ramer_hypotheses_of_v2 {ι : Type*} (b : HilbertBasis ι ℝ S.H)
    (T : S.E ≃ₜ S.E) (K K' : S.E → S.H)
    (hT : ∀ x, T x = x + S.incl (K x))
    (hTs : ∀ y, T.symm y = y + S.incl (K' y))
    (hK : ContDiff ℝ 1 K) (hK' : ContDiff ℝ 1 K') :
    Continuous K ∧
    (∀ x, HasFDerivAt (fun h => K (x + S.incl h)) ((fderiv ℝ K x).comp S.incl) 0) ∧
    (∀ x, Summable (fun n => ‖fderiv ℝ K x (S.incl (b n))‖ ^ 2)) ∧
    (∀ x y, Summable (fun n =>
        ‖fderiv ℝ K y (S.incl (b n)) - fderiv ℝ K x (S.incl (b n))‖ ^ 2)) ∧
    (∀ x, Tendsto (fun y => ∑' n,
        ‖fderiv ℝ K y (S.incl (b n)) - fderiv ℝ K x (S.incl (b n))‖ ^ 2) (𝓝 x) (𝓝 0)) ∧
    (∀ x, ∃ L : S.H ≃L[ℝ] S.H,
      (∀ h, L h = h + fderiv ℝ K x (S.incl h)) ∧
      (∀ h, L.symm h = h + fderiv ℝ K' (T x) (S.incl h))) := by
  obtain ⟨h1, h2, h3, h4s, h4, h5⟩ := NlsGge.Ramer.ramer_hypotheses_of_v2 S.incl
    S.incl_injective b (S.incl_hs b) T K K' hT hTs hK hK'
  exact ⟨h1, h2, fun x => (h3 x).1, h4s, h4, h5⟩

end NlsGge.Ramer.General.RamerSetting
