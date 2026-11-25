import NlsGge.GK38.PairCompactForcing
import NlsGge.GK38.PairAsymptoticsVolterra

/-! # F6: fundamental entries under weak convergence

Source: GK, Chapter I, Proposition 1.2. The inhomogeneous Volterra equation
propagates the uniformly small forcing, with bounds derived from weak convergence.
-/
set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38
noncomputable section

/-- The fundamental difference solves an inhomogeneous Volterra equation. -/
theorem fundContP_sub_eq_volterra38 (φ ψ : PotPair) (z : ℂ) :
    fundContP φ z - fundContP ψ z =
      volterraP (φ - ψ) z (fundContP ψ z) +
        volterraP φ z (fundContP φ z - fundContP ψ z) := by
  calc
    fundContP φ z - fundContP ψ z =
        volterraP φ z (fundContP φ z) - volterraP ψ z (fundContP ψ z) := by
      conv_lhs => rw [fundCont_eq_add φ z, fundCont_eq_add ψ z]
      abel
    _ = _ := by rw [volterraP_sub, sub_apply, map_sub]; abel

/-- Uniform weak convergence of every fundamental entry over a compact spectral set
and the entire time interval, simultaneously over all four entries. -/
theorem fundPair_weakContinuous_uniform38 {φ : ℕ → PotPair} {φ₀ : PotPair}
    (hw : IsWeakLimComp φ φ₀) {K : Set ℂ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ z ∈ K, ∀ t : Set.Icc (0 : ℝ) 1, ∀ i j : Fin 2,
      ‖fundPair (φ k) z t i j - fundPair φ₀ z t i j‖ < ε := by
  obtain ⟨B, hB, hb⟩ := weakLimComp_bounded38 hw
  have hcont : Continuous (fun z : ℂ => |z.im|) := Complex.continuous_im.abs
  obtain ⟨A₀, hA₀⟩ := hK.bddAbove_image hcont.continuousOn
  let A : ℝ := max A₀ 0
  have hA : ∀ z ∈ K, |z.im| ≤ A := fun z hz =>
    (hA₀ (Set.mem_image_of_mem _ hz)).trans (le_max_left _ _)
  let C : ℝ := Real.exp (A + 2 * B)
  have hC : 0 < C := Real.exp_pos _
  let δ : ℝ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [weakLimComp_volterra_forcing38 hw hK hδ] with k hk z hz t i j
  let H : PairCont38 := volterraP (φ k - φ₀) z (fundContP φ₀ z)
  let D : PairCont38 := fundContP (φ k) z - fundContP φ₀ z
  have hH : ∀ s : ℝ, ∀ hs : s ∈ Set.Icc (0 : ℝ) 1, ∀ a b : Fin 2,
      ‖H ⟨s, hs⟩ a b‖ ≤ Real.exp (|z.im| * s) * δ := by
    intro s hs a b
    refine (hk z hz ⟨s, hs⟩ a b).le.trans ?_
    have he : 1 ≤ Real.exp (|z.im| * s) :=
      Real.one_le_exp (mul_nonneg (abs_nonneg _) hs.1)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he hδ.le
  have hD : D = H + volterraP (φ k) z D := fundContP_sub_eq_volterra38 (φ k) φ₀ z
  have hd := norm_volterra_solution_entry_le_weighted (φ k) z H D δ hδ.le hH hD t i j
  have hp : potPrim38 (φ k) t ≤ 2 * B :=
    (potPrim38_le_one (φ k) t.2).trans ((potL1Norm38_le_two_mul (φ k)).trans
      (mul_le_mul_of_nonneg_left (hb k) (by norm_num)))
  have he : Real.exp (|z.im| * (t : ℝ) + potPrim38 (φ k) t) ≤ C := by
    apply Real.exp_le_exp.mpr
    have him : |z.im| * (t : ℝ) ≤ A :=
      (mul_le_of_le_one_right (abs_nonneg _) t.2.2).trans (hA z hz)
    linarith
  have hbound : ‖D t i j‖ ≤ ε / 2 := by
    refine hd.trans ((mul_le_mul_of_nonneg_right he hδ.le).trans_eq ?_)
    dsimp [δ]
    field_simp
  change ‖D t i j‖ < ε
  exact hbound.trans_lt (by linarith)

/-- Fixed-time entries converge locally uniformly in the full complex plane. -/
theorem fundPair_weakContinuous_entry38 {φ : ℕ → PotPair} {φ₀ : PotPair}
    (hw : IsWeakLimComp φ φ₀) (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    TendstoLocallyUniformly (fun k z => fundPair (φ k) z t i j)
      (fun z => fundPair φ₀ z t i j) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [fundPair_weakContinuous_uniform38 hw hK hε] with k hk z hz
  rw [dist_eq_norm, norm_sub_rev]
  exact hk z hz t i j

end
end NlsGge.GK38
