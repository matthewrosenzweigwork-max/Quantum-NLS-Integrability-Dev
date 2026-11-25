import NlsGge.GK38.PairAsymptoticsForce
import NlsGge.GK38.PairRealBridge

/-! # F5: locally uniform scalar asymptotics of the full discriminant -/

set_option autoImplicit false

open Filter Topology MeasureTheory Set Metric

namespace NlsGge.GK38

noncomputable section

/-- GK Theorem 2.2, entrywise and uniformly in time and a potential neighbourhood. -/
theorem fundPair_asymp (φ₀ : PotPair) {ε : ℝ} (hε : 0 < ε) :
    ∃ U ∈ 𝓝 φ₀, ∃ R : ℝ, ∀ φ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
      ∀ t : Icc (0 : ℝ) 1, ∀ i j : Fin 2,
        ‖fundPair φ z t i j - freeFund z t i j‖ ≤
          ε * Real.exp (|z.im| * (t : ℝ)) := by
  let B : ℝ := 2 * (‖φ₀‖ + 1)
  let δ : ℝ := ε / Real.exp B
  have hδ : 0 < δ := div_pos hε (Real.exp_pos _)
  obtain ⟨U, hU, R, hR⟩ := pairForce38_decay φ₀ hδ
  refine ⟨U ∩ ball φ₀ 1, inter_mem hU (ball_mem_nhds _ zero_lt_one), R,
    fun φ hφ z hz t i j => ?_⟩
  have hφnorm : ‖φ‖ ≤ ‖φ₀‖ + 1 := by
    have hdist := (mem_ball_iff_norm.mp hφ.2).le
    have htri := norm_add_le (φ - φ₀) φ₀
    rw [sub_add_cancel] at htri
    linarith
  have hprim : potPrim38 φ t ≤ B :=
    (potPrim38_le_one φ t.2).trans
      ((potL1Norm38_le_two_mul φ).trans (by dsimp [B]; linarith))
  have hb := norm_volterra_solution_entry_le_weighted φ z (pairForce38 φ z)
    (fundContP φ z - freeFundP z) δ hδ.le
    (fun s hs i j => by simpa only [mul_comm] using hR φ hφ.1 z hz ⟨s, hs⟩ i j)
    (fundCont_sub_free_eq φ z) t i j
  change ‖fundPair φ z t i j - freeFund z t i j‖ ≤ _ at hb
  refine hb.trans ?_
  rw [Real.exp_add]
  have hc : Real.exp (potPrim38 φ t) * δ ≤ ε := by
    calc Real.exp (potPrim38 φ t) * δ ≤ Real.exp B * δ :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hprim) hδ.le
      _ = ε := by dsimp [δ]; field_simp
  calc (Real.exp (|z.im| * (t : ℝ)) * Real.exp (potPrim38 φ t)) * δ
      = Real.exp (|z.im| * (t : ℝ)) * (Real.exp (potPrim38 φ t) * δ) := mul_assoc _ _ _
    _ ≤ Real.exp (|z.im| * (t : ℝ)) * ε :=
      mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

/-- GK Theorem 2.2, full-trace normalization `Δ = 2cos + o(exp |Im z|)`. -/
theorem discrim_asymp (φ₀ : PotPair) : ∀ ε > 0, ∃ U ∈ 𝓝 φ₀, ∃ R : ℝ,
    ∀ φ ∈ U, ∀ z : ℂ, R ≤ ‖z‖ →
      ‖discrim φ z - 2 * Complex.cos z‖ ≤ ε * Real.exp |z.im| := by
  intro ε hε
  obtain ⟨U, hU, R, hR⟩ := fundPair_asymp φ₀ (half_pos hε)
  refine ⟨U, hU, R, fun φ hφ z hz => ?_⟩
  let t : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  have h0 := hR φ hφ z hz t 0 0
  have h1 := hR φ hφ z hz t 1 1
  have hfree : freeE z 1 0 0 + freeE z 1 1 1 = 2 * Complex.cos z := by
    have hh := discrim_eq 0 z
    rw [monodromyPair_zero_potential, discrim_zero] at hh
    exact hh.symm
  have heq : discrim φ z - 2 * Complex.cos z =
      (fundPair φ z t 0 0 - freeFund z t 0 0) +
      (fundPair φ z t 1 1 - freeFund z t 1 1) := by
    rw [discrim_eq, monodromyPair_eq_fundPair, ← hfree]
    simp only [t, freeFund_apply]
    ring
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  have hh := add_le_add h0 h1
  simp only [t, mul_one] at hh
  convert hh using 1 <;> ring

end

end NlsGge.GK38
