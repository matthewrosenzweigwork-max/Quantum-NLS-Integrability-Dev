import NlsGge.Spectral.ComplexQuadraticInsideUnitRootUnique36V1
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
/-- Conditional scalar API: a strictly inside-unit root is continuous when
its coefficients are continuous and all unit-boundary roots are excluded.
Neither root existence nor the physical exclusion is assumed completed. -/
theorem complexQuadraticSmallRoot_continuous36V2
    {T : Type*} [TopologicalSpace T] (d r : T → ℂ)
    (hd : Continuous d)
    (hr : ∀ t, r t ^ 2 - 2 * d t * r t + 1 = 0)
    (hn : ∀ t, ‖r t‖ < 1)
    (hb : ∀ t v, v ^ 2 - 2 * d t * v + 1 = 0 → ‖v‖ ≠ 1) :
    Continuous r := by
  let K : Set ℂ := Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall (0 : ℂ) 1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : T → K := fun t => ⟨r t, by
    change r t ∈ Metric.closedBall (0 : ℂ) 1
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hn t).le⟩
  have hgraph : f.graph =
      {p : T × K | (p.2 : ℂ)^2 - 2 * d p.1 * (p.2 : ℂ) + 1 = 0} := by
    ext p
    change (f p.1 = p.2) ↔ _
    constructor
    · intro he
      have hv : r p.1 = (p.2 : ℂ) := congrArg Subtype.val he
      change (p.2 : ℂ)^2 - 2 * d p.1 * (p.2 : ℂ) + 1 = 0
      simpa only [hv] using hr p.1
    · intro he
      have hle : ‖(p.2 : ℂ)‖ ≤ 1 := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right] using p.2.property
      have hlt : ‖(p.2 : ℂ)‖ < 1 := lt_of_le_of_ne hle (hb p.1 p.2 he)
      apply Subtype.ext
      exact complexQuadratic_insideUnitRoot_unique36V1
        (d p.1) (r p.1) p.2 (hr p.1) he (hn p.1) hlt
  have hv : Continuous (fun p : T × K => (p.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  have hg : IsClosed f.graph := by
    rw [hgraph]
    exact isClosed_eq ((hv.pow 2).sub
      ((continuous_const.mul (hd.comp continuous_fst)).mul hv) |>.add continuous_const)
      continuous_const
  exact continuous_subtype_val.comp (continuous_of_isClosed_graph hg)
end NlsGge.SpectralFoundations
end
