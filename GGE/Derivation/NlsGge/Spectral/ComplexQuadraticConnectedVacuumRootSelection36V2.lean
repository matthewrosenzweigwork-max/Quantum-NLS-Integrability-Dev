import NlsGge.Spectral.ComplexQuadraticNearbyVacuumRootDistance36V1
import Mathlib.Topology.Connected.Basic
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations

/-- Connected selection resolves the two-disk ambiguity, including overlapping
vacuum disks. The actual physical coupling continuity remains to be realized. -/
theorem connectedVacuumRootDistance36V2
    (s : Set ℝ) (hs : IsPreconnected s) (w : ℝ → ℂ)
    (hw : ContinuousOn w s) (a b : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hclose : ∀ t ∈ s, min ‖w t-a‖ ‖w t-b‖ ≤ r)
    (t₀ : ℝ) (ht₀ : t₀ ∈ s) (hstart : w t₀=a) :
    ∀ t ∈ s, ‖w t-a‖ ≤ 3*r := by
  have htri (t : ℝ) : ‖a-b‖ ≤ ‖w t-a‖+‖w t-b‖ := by
    simpa only [dist_eq_norm, norm_sub_rev (a) (w t)] using dist_triangle a (w t) b
  by_cases hsep : ‖a-b‖ ≤ 2*r
  · intro t ht
    rcases (min_le_iff.mp (hclose t ht)) with ha | hb
    · linarith
    · have hh : ‖w t-a‖ ≤ ‖w t-b‖+‖a-b‖ := by
        simpa only [dist_eq_norm, norm_sub_rev b a] using dist_triangle (w t) b a
      linarith
  · have hsep' : 2*r < ‖a-b‖ := lt_of_not_ge hsep
    have hcont : ContinuousOn (fun t => ‖w t-a‖) s :=
      (hw.sub continuousOn_const).norm
    have hne : ∀ t ∈ s, ‖w t-a‖ ≠ ‖a-b‖/2 := by
      intro t ht he
      rcases (min_le_iff.mp (hclose t ht)) with ha | hb
      · linarith
      · have hh := htri t
        linarith
    have hbelow : ∀ t ∈ s, ‖w t-a‖ < ‖a-b‖/2 := by
      intro t ht
      apply hs.gt_of_ne hcont hne _ ht
      refine ⟨t₀, ht₀, ?_⟩
      rw [hstart, sub_self, norm_zero]
      linarith
    intro t ht
    rcases (min_le_iff.mp (hclose t ht)) with ha | hb
    · linarith
    · have hh := htri t
      have hh' := hbelow t ht
      linarith

/-- Characteristic-polynomial stability along a continuous concrete-eligible
coupling path. This is a conditional intermediate, not E02 completion. -/
theorem complexQuadratic_connectedVacuumRootDistance36V2
    (s : Set ℝ) (hs : IsPreconnected s) (d w : ℝ → ℂ)
    (hw : ContinuousOn w s) (d₀ a b : ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hab : a*b=1) (hsum : a+b=2*d₀)
    (hroot : ∀ t ∈ s, (w t)^2-2*d t*w t+1=0)
    (hwnorm : ∀ t ∈ s, ‖w t‖ ≤ 1)
    (htrace : ∀ t ∈ s, ‖d t-d₀‖ ≤ δ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ s) (hstart : w t₀=a) :
    ∀ t ∈ s, ‖w t-a‖ ≤ 3*Real.sqrt (2*δ) := by
  apply connectedVacuumRootDistance36V2 s hs w hw a b
    (Real.sqrt (2*δ)) (Real.sqrt_nonneg _) _ t₀ ht₀ hstart
  intro t ht
  exact (complexQuadratic_minRootDistance36V1 (d t) d₀ (w t) a b
    hab hsum (hroot t ht) (hwnorm t ht)).trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (htrace t ht) (by norm_num)))
end NlsGge.SpectralFoundations
end
