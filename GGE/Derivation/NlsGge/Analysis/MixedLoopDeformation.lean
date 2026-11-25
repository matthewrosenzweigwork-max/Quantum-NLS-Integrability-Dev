import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
open Set Metric MeasureTheory Filter
open scoped Topology
namespace NlsGge.Analysis.MixedLoopDeformation
noncomputable section

theorem slices_integrable {H D : ℝ → ℝ → ℂ} {U V : Set ℝ}
    (hV : Icc (0 : ℝ) (2 * Real.pi) ⊆ V)
    (hH : ContinuousOn (Function.uncurry H) (U ×ˢ V))
    (hD : ContinuousOn (Function.uncurry D) (U ×ˢ V)) :
    ∀ t ∈ U, IntervalIntegrable (H t) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (D t) volume 0 (2 * Real.pi) := by
  intro t ht
  have hp : Continuous (fun θ : ℝ => (t, θ)) := continuous_const.prodMk continuous_id
  have hm : MapsTo (fun θ : ℝ => (t, θ)) (Icc 0 (2 * Real.pi)) (U ×ˢ V) :=
    fun θ hθ => ⟨ht, hV hθ⟩
  constructor
  · exact (show ContinuousOn (H t) (uIcc 0 (2 * Real.pi)) by
      simpa only [uIcc_of_le Real.two_pi_pos.le, Function.comp_def, Function.uncurry_def] using
        hH.comp hp.continuousOn hm).intervalIntegrable
  · exact (show ContinuousOn (D t) (uIcc 0 (2 * Real.pi)) by
      simpa only [uIcc_of_le Real.two_pi_pos.le, Function.comp_def, Function.uncurry_def] using
        hD.comp hp.continuousOn hm).intervalIntegrable

theorem local_derivative_bound {D : ℝ → ℝ → ℂ} {U V : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (ht : t ∈ U) (hV : Icc (0 : ℝ) (2 * Real.pi) ⊆ V)
    (hD : ContinuousOn (Function.uncurry D) (U ×ˢ V)) :
    ∃ ε B : ℝ, 0 < ε ∧ closedBall t ε ⊆ U ∧
      ∀ s ∈ closedBall t ε, ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), ‖D s θ‖ ≤ B := by
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.mp hU t ht
  have he := half_pos hδ
  have hc : closedBall t (δ / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hδ)).trans hb
  let K : Set (ℝ × ℝ) := closedBall t (δ / 2) ×ˢ Icc (0 : ℝ) (2 * Real.pi)
  have hK : IsCompact K := (isCompact_closedBall t (δ / 2)).prod isCompact_Icc
  have hne : K.Nonempty := ⟨(t, 0), mem_closedBall_self he.le, le_rfl, Real.two_pi_pos.le⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖D p.1 p.2‖) K :=
    (hD.mono (fun p hp => ⟨hc hp.1, hV hp.2⟩)).norm
  obtain ⟨p, hp, hm⟩ := hK.exists_isMaxOn hne hcont
  refine ⟨δ / 2, ‖D p.1 p.2‖, he, hc, ?_⟩
  intro s hs θ hθ
  have hle : (fun q : ℝ × ℝ => ‖D q.1 q.2‖) (s, θ) ≤ ‖D p.1 p.2‖ :=
    hm (show (s, θ) ∈ K from ⟨hs, hθ⟩)
  exact hle

theorem parameter_derivative {H D : ℝ → ℝ → ℂ} {U V : Set ℝ} {t : ℝ}
    (hU : IsOpen U) (ht : t ∈ U) (hV : Icc (0 : ℝ) (2 * Real.pi) ⊆ V)
    (hH : ContinuousOn (Function.uncurry H) (U ×ˢ V))
    (hD : ContinuousOn (Function.uncurry D) (U ×ˢ V))
    (hd : ∀ s ∈ U, ∀ θ ∈ V, HasDerivAt (fun v : ℝ => H v θ) (D s θ) s) :
    HasDerivAt (fun s : ℝ => ∫ θ in (0 : ℝ)..2 * Real.pi, H s θ)
      (∫ θ in (0 : ℝ)..2 * Real.pi, D t θ) t := by
  obtain ⟨ε, B, he, hc, hb⟩ := local_derivative_bound hU ht hV hD
  have hi := slices_integrable hV hH hD
  have hm : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (H s)
      (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) := by
    filter_upwards [hU.mem_nhds ht] with s hs
    simpa only [uIoc_of_le Real.two_pi_pos.le] using (hi s hs).1.aestronglyMeasurable
  have hθ : ∀ θ ∈ uIoc (0 : ℝ) (2 * Real.pi), θ ∈ Icc (0 : ℝ) (2 * Real.pi) := by
    intro θ h
    rw [uIoc_of_le Real.two_pi_pos.le] at h
    exact ⟨h.1.le, h.2⟩
  have hbound : ∀ᵐ θ ∂volume, θ ∈ uIoc (0 : ℝ) (2 * Real.pi) →
      ∀ s ∈ ball t ε, ‖D s θ‖ ≤ B :=
    Eventually.of_forall (fun θ h s hs => hb s (ball_subset_closedBall hs) θ (hθ θ h))
  have hderiv : ∀ᵐ θ ∂volume, θ ∈ uIoc (0 : ℝ) (2 * Real.pi) →
      ∀ s ∈ ball t ε, HasDerivAt (fun v : ℝ => H v θ) (D s θ) s :=
    Eventually.of_forall (fun θ h s hs => hd s (hc (ball_subset_closedBall hs)) θ (hV (hθ θ h)))
  have hmeas : AEStronglyMeasurable (D t)
      (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) := by
    simpa only [uIoc_of_le Real.two_pi_pos.le] using (hi t ht).2.aestronglyMeasurable
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds t he) hm (hi t ht).1 hmeas hbound
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume 0 (2 * Real.pi))
    hderiv).2

theorem integral_eq_of_mixed_derivative {H D P : ℝ → ℝ → ℂ} {U V : Set ℝ}
    (hU : IsOpen U) (htU : Icc (0 : ℝ) 1 ⊆ U)
    (hV : Icc (0 : ℝ) (2 * Real.pi) ⊆ V)
    (hH : ContinuousOn (Function.uncurry H) (U ×ˢ V))
    (hD : ContinuousOn (Function.uncurry D) (U ×ˢ V))
    (hT : ∀ t ∈ U, ∀ θ ∈ V, HasDerivAt (fun s : ℝ => H s θ) (D t θ) t)
    (hθ : ∀ t ∈ U, ∀ θ ∈ V, HasDerivAt (P t) (D t θ) θ)
    (hp : ∀ t ∈ U, P t (2 * Real.pi) = P t 0) :
    IntervalIntegrable (H 0) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (H 1) volume 0 (2 * Real.pi) ∧
      (∫ θ in (0 : ℝ)..2 * Real.pi, H 0 θ) =
        ∫ θ in (0 : ℝ)..2 * Real.pi, H 1 θ := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hi := slices_integrable hV hH hD
  let F : ℝ → ℂ := fun t => ∫ θ in (0 : ℝ)..2 * Real.pi, H t θ
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt F 0 t := by
    intro t ht
    have hder : ∀ θ ∈ uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt (P t) (D t θ) θ := by
      intro θ h
      rw [uIcc_of_le Real.two_pi_pos.le] at h
      exact hθ t (htU ht) θ (hV h)
    have hz : (∫ θ in (0 : ℝ)..2 * Real.pi, D t θ) = 0 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hi t (htU ht)).2, hp t (htU ht), sub_self]
    simpa only [F, hz] using parameter_derivative hU (htU ht) hV hH hD hT
  have hn := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := F) (f' := fun _ => (0 : ℂ)) (C := 0)
    (fun t ht => (hd t ht).hasDerivWithinAt) (by intro t ht; simp)
    (convex_Icc (0 : ℝ) 1) h0 h1
  have heq : F 0 = F 1 := by
    have hz : F 1 - F 0 = 0 := norm_eq_zero.mp
      (le_antisymm (by simpa only [zero_mul] using hn) (norm_nonneg _))
    exact (sub_eq_zero.mp hz).symm
  exact ⟨(hi 0 (htU h0)).1, (hi 1 (htU h1)).1, heq⟩

end
end NlsGge.Analysis.MixedLoopDeformation
