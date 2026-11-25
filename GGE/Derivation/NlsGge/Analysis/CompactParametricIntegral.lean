import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
open Set MeasureTheory
namespace NlsGge.Analysis.CompactParametricIntegral
noncomputable section

/-- Joint continuity on a closed rectangle earns integrability of every slice and
continuity of its genuine interval integral, including boundary parameter values. -/
theorem continuousOn_rectangle_integral {H : ℝ → ℝ → ℂ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hH : ContinuousOn (Function.uncurry H) (Icc a b ×ˢ Icc c d)) :
    (∀ t ∈ Icc a b, IntervalIntegrable (H t) volume c d) ∧
      ContinuousOn (fun t => ∫ θ in c..d, H t θ) (Icc a b) := by
  let P : ℝ → ℝ := fun t => (projIcc a b hab t : ℝ)
  let Q : ℝ → ℝ := fun θ => (projIcc c d hcd θ : ℝ)
  have hP : Continuous P := continuous_subtype_val.comp continuous_projIcc
  have hQ : Continuous Q := continuous_subtype_val.comp continuous_projIcc
  have hmap : Continuous (fun p : ℝ × ℝ => (P p.1, Q p.2)) :=
    (hP.comp continuous_fst).prodMk (hQ.comp continuous_snd)
  have hglobal : Continuous (fun p : ℝ × ℝ => H (P p.1) (Q p.2)) :=
    hH.comp_continuous hmap (fun p => ⟨(projIcc a b hab p.1).2, (projIcc c d hcd p.2).2⟩)
  have hp : ∀ t ∈ Icc a b, P t = t := by
    intro t ht
    simp only [P, projIcc_of_mem hab ht]
  have hq : ∀ θ ∈ Icc c d, Q θ = θ := by
    intro θ hθ
    simp only [Q, projIcc_of_mem hcd hθ]
  have hc : Continuous (fun t => ∫ θ in c..d, H (P t) (Q θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hglobal c d
  constructor
  · intro t ht
    apply ContinuousOn.intervalIntegrable_of_Icc hcd
    exact hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ⟨ht, hθ⟩)
  · apply hc.continuousOn.congr
    intro t ht
    apply intervalIntegral.integral_congr
    intro θ hθ
    rw [uIcc_of_le hcd] at hθ
    change H t θ = H (P t) (Q θ)
    rw [hp t ht, hq θ hθ]


theorem closed_endpoint_of_positive_constant {g : ℝ → ℂ} {K : ℂ}
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hK : ∀ t ∈ Ioc (0 : ℝ) 1, g t = K) : g 0 = K := by
  have he : EqOn g (fun _ => K) (Ioc (0 : ℝ) 1) := hK
  have hc := he.of_subset_closure hg continuousOn_const Ioc_subset_Icc_self
    (show Icc (0 : ℝ) 1 ⊆ closure (Ioc (0 : ℝ) 1) by rw [closure_Ioc zero_ne_one])
  exact hc ⟨le_rfl, zero_le_one⟩

end
end NlsGge.Analysis.CompactParametricIntegral
