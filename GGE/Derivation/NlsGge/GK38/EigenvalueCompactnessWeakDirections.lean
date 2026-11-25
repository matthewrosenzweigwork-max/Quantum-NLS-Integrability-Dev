import NlsGge.GK38.EigenvalueCompactnessPhaseIntegrable
import NlsGge.GK38.DirichletRealWeakMatrix

/-! # S7: varying unit directions under actual weak matrix convergence -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem normalizedFirst_entry38 (u : PhysicalL2) (x : ℝ) (a : ℂ) (ha : a ≠ 0)
    (t : Time38) : normalizedFirst38 u x a t =
      fundPair (realSlice u) (x : ℂ) t 0 0 +
        fundPair (realSlice u) (x : ℂ) t 0 1 * (star a / a) := by
  simp only [normalizedFirst38, realInitial38, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

theorem normalizedFirst_varyingWeak_uniform38 {u : ℕ → PhysicalL2} {u₀ : PhysicalL2}
    {x : ℕ → ℝ} {x₀ : ℝ} {a : ℕ → ℂ} {a₀ : ℂ}
    (hw : IsWeakLim u u₀) (hx : Tendsto x atTop (𝓝 x₀))
    (ha : Tendsto a atTop (𝓝 a₀)) (hunit : ∀ k, ‖a k‖ = 1) (hunit₀ : ‖a₀‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ t : Time38,
      ‖normalizedFirst38 (u k) (x k) (a k) t - normalizedFirst38 u₀ x₀ a₀ t‖ < ε := by
  have hne : ∀ k, a k ≠ 0 := fun k => unit_direction_ne_zero38 (a k) (hunit k)
  have hne₀ := unit_direction_ne_zero38 a₀ hunit₀
  have hr : Tendsto (fun k => star (a k) / a k) atTop (𝓝 (star a₀ / a₀)) :=
    ha.star.div ha hne₀
  let B := ‖fundContP (realSlice u₀) (x₀ : ℂ)‖
  have hB : 0 ≤ B := norm_nonneg _
  have hδ : 0 < ε / (3 * (B + 1)) := div_pos hε (by positivity)
  have hs : ∀ᶠ k in atTop, ‖star (a k) / a k - star a₀ / a₀‖ < ε / (3 * (B + 1)) := by
    simpa only [mem_ball, dist_eq_norm] using hr.eventually (ball_mem_nhds _ hδ)
  have hxC : Tendsto (fun k => (x k : ℂ)) atTop (𝓝 (x₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hx
  filter_upwards [hs, fundPair_realSlice_varyingWeak_uniform38 hw hxC (by positivity : 0 < ε / 3)] with k hk hf
  intro t
  rw [normalizedFirst_entry38 _ _ _ (hne k), normalizedFirst_entry38 _ _ _ hne₀]
  let A := fundPair (realSlice (u k)) (x k : ℂ) t 0 0
  let D := fundPair (realSlice (u k)) (x k : ℂ) t 0 1
  let A₀ := fundPair (realSlice u₀) (x₀ : ℂ) t 0 0
  let D₀ := fundPair (realSlice u₀) (x₀ : ℂ) t 0 1
  let r := star (a k) / a k
  let r₀ := star a₀ / a₀
  have hb : ‖D₀‖ ≤ B :=
    (norm_le_pi_norm _ 1).trans ((norm_le_pi_norm _ 0).trans
      ((fundContP (realSlice u₀) (x₀ : ℂ)).norm_coe_le_norm t))
  have hu : ‖r‖ = 1 := by simp [r, hunit k]
  have hsplit : A + D * r - (A₀ + D₀ * r₀) =
      (A - A₀) + (D - D₀) * r + D₀ * (r - r₀) := by ring
  rw [hsplit]
  have hbound := (norm_add_le ((A-A₀)+(D-D₀)*r) (D₀*(r-r₀))).trans
    (add_le_add (norm_add_le (A-A₀) ((D-D₀)*r)) le_rfl)
  rw [norm_mul, norm_mul, hu, mul_one] at hbound
  have htail : ‖D₀‖ * ‖r-r₀‖ < ε / 3 := by
    have hp := mul_lt_mul_of_pos_left hk (by positivity : 0 < B + 1)
    have he : (B + 1) * (ε / (3 * (B + 1))) = ε / 3 := by field_simp
    rw [he] at hp
    exact (mul_le_mul_of_nonneg_right (hb.trans (by linarith)) (norm_nonneg _)).trans_lt hp
  have hA := hf t 0 0
  have hD := hf t 0 1
  change ‖A-A₀‖ < ε/3 at hA
  change ‖D-D₀‖ < ε/3 at hD
  linarith

end
end NlsGge.GK38
