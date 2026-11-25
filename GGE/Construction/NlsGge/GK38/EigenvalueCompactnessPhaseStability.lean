import NlsGge.GK38.EigenvalueCompactnessPhaseMetric
import Mathlib.Topology.Order.IntermediateValue

/-! # S7/D2: uniform stability of normalized clockwise phase lifts

The independently reviewed IVT route excludes extra branches using connectedness.
Only the one limiting nonzero curve supplies a positive lower norm bound.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem normalizedPhase_close_lifts38 (g g₀ : Time38 → ℂ) (θ θ₀ : Time38 → ℝ)
    (hg : NormalizedPhase38 g θ) (h₀ : NormalizedPhase38 g₀ θ₀)
    (η : ℝ) (hη : 0 < η) (_hπ : η < Real.pi)
    (hc : ∀ t : Time38, ‖g t / (‖g t‖ : ℂ) - g₀ t / (‖g₀ t‖ : ℂ)‖ <
      min ‖Complex.exp (-Complex.I * (η : ℂ)) - 1‖
        ‖Complex.exp (-Complex.I * ((-η : ℝ) : ℂ)) - 1‖) :
    ∀ t : Time38, |θ t - θ₀ t| < η := by
  let : PreconnectedSpace Time38 := Subtype.preconnectedSpace isPreconnected_Icc
  let t₀ : Time38 := ⟨0, le_rfl, zero_le_one⟩
  let d : Time38 → ℝ := fun t => θ t - θ₀ t
  have hd : Continuous d := hg.2.1.sub h₀.2.1
  have hz : d t₀ = 0 := by simp only [d, t₀, hg.2.2.1, h₀.2.2.1, sub_self]
  have hch : ∀ s : Time38, ‖Complex.exp (-Complex.I * (d s : ℂ)) - 1‖ <
      min ‖Complex.exp (-Complex.I * (η : ℂ)) - 1‖
        ‖Complex.exp (-Complex.I * ((-η : ℝ) : ℂ)) - 1‖ := by
    intro s
    have he := hc s
    rw [(hg.2.2.2 s).2, (h₀.2.2.2 s).2, phase_exponential_distance38] at he
    exact he
  intro t
  change |d t| < η
  by_contra hbad
  have hb : η ≤ |d t| := le_of_not_gt hbad
  by_cases hp : 0 ≤ d t
  · have he : η ≤ d t := by rwa [abs_of_nonneg hp] at hb
    obtain ⟨s, hs⟩ := (intermediate_value_univ t₀ t hd) (show η ∈ Icc (d t₀) (d t) by
      rw [hz]; exact ⟨hη.le, he⟩)
    have h := hch s
    rw [hs] at h
    exact (not_lt_of_ge (min_le_left _ _)) h
  · have he : d t ≤ -η := by rw [abs_of_neg (lt_of_not_ge hp)] at hb; linarith
    obtain ⟨s, hs⟩ := (intermediate_value_univ t t₀ hd) (show -η ∈ Icc (d t) (d t₀) by
      rw [hz]; exact ⟨he, by linarith⟩)
    have h := hch s
    rw [hs] at h
    exact (not_lt_of_ge (min_le_right _ _)) h

theorem normalizedPhase_uniform_stability38 (g : ℕ → Time38 → ℂ) (g₀ : Time38 → ℂ)
    (θ : ℕ → Time38 → ℝ) (θ₀ : Time38 → ℝ)
    (hg : ∀ k, NormalizedPhase38 (g k) (θ k)) (h₀ : NormalizedPhase38 g₀ θ₀)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : Time38, ‖g k t - g₀ t‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : Time38, |θ k t - θ₀ t| < ε := by
  obtain ⟨t₀, _, hmin⟩ := (isCompact_univ : IsCompact (univ : Set Time38)).exists_isMinOn
    (show (univ : Set Time38).Nonempty from ⟨⟨0, le_rfl, zero_le_one⟩, mem_univ _⟩)
    h₀.1.norm.continuousOn
  let β := ‖g₀ t₀‖
  have hβ : 0 < β := norm_pos_iff.mpr (h₀.2.2.2 t₀).1
  have hβt : ∀ t : Time38, β ≤ ‖g₀ t‖ := fun t => hmin (mem_univ t)
  intro ε hε
  let η := min (ε / 2) (Real.pi / 2)
  have hη : 0 < η := lt_min (half_pos hε) (half_pos Real.pi_pos)
  have hηπ : η < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hηε : η ≤ ε := (min_le_left _ _).trans (by linarith)
  let σ := min ‖Complex.exp (-Complex.I * (η : ℂ)) - 1‖
    ‖Complex.exp (-Complex.I * ((-η : ℝ) : ℂ)) - 1‖
  have hσ : 0 < σ := lt_min (phase_chord_positive38 η hη hηπ).1 (phase_chord_positive38 η hη hηπ).2
  let δ := β * σ / 4
  have hδ : 0 < δ := div_pos (mul_pos hβ hσ) (by norm_num)
  filter_upwards [hu δ hδ] with k hk
  have hc : ∀ t : Time38, ‖g k t / (‖g k t‖ : ℂ) - g₀ t / (‖g₀ t‖ : ℂ)‖ < σ := by
    intro t
    calc
      _ ≤ 2 * ‖g k t - g₀ t‖ / ‖g₀ t‖ := complex_normalization_distance38 _ _
        ((hg k).2.2.2 t).1 (h₀.2.2.2 t).1
      _ ≤ 2 * ‖g k t - g₀ t‖ / β := div_le_div_of_nonneg_left (by positivity) hβ (hβt t)
      _ < σ := (div_lt_iff₀ hβ).mpr (by have hh := hk t; dsimp [δ] at hh; nlinarith)
  exact fun t => (normalizedPhase_close_lifts38 _ _ _ _ (hg k) h₀ η hη hηπ hc t).trans_le hηε


theorem normalizedPhase_unique38 (g : Time38 → ℂ) (θ θ₀ : Time38 → ℝ)
    (hg : NormalizedPhase38 g θ) (h₀ : NormalizedPhase38 g θ₀) : θ = θ₀ := by
  have hu := normalizedPhase_uniform_stability38 (fun _ : ℕ => g) g (fun _ => θ) θ₀
    (fun _ => hg) h₀ (fun ε hε => Filter.Eventually.of_forall (fun _ _ => by simpa using hε))
  funext t
  have hh : |θ t - θ₀ t| ≤ 0 := le_of_forall_pos_lt_add fun ε hε => by
    obtain ⟨k, hk⟩ := (hu ε hε).exists
    simpa only [zero_add] using hk t
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))

end
end NlsGge.GK38
