import NlsGge.GK38.DirichletCharDefs
import NlsGge.GK38.PairAsymptoticsSeq

/-! # D1: scalar and sampled-sequence characteristic residuals

Book equation (5.2) and the quantitative input to Proposition 5.3. -/
set_option autoImplicit false
open Filter Topology Set
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_residual_eq38 (φ : PotPair) (z : ℂ) :
    dirichletChar φ z - Complex.sin z =
      ((monodromyPair φ z - freeE z 1) 1 0 + (monodromyPair φ z - freeE z 1) 1 1 -
        (monodromyPair φ z - freeE z 1) 0 0 - (monodromyPair φ z - freeE z 1) 0 1) /
          (2 * Complex.I) := by
  rw [← dirichletChar_zero z, dirichletChar_eq, dirichletChar_eq, monodromyPair_zero_potential]
  simp only [Matrix.sub_apply]
  ring

/-- The four-entry functional has norm at most two in the elementwise matrix norm. -/
theorem norm_dirichletResidual_le38 (φ : PotPair) (z : ℂ) :
    ‖dirichletChar φ z - Complex.sin z‖ ≤ 2 * ‖monodromyPair φ z - freeE z 1‖ := by
  let D := monodromyPair φ z - freeE z 1
  have h10 := Matrix.norm_entry_le_entrywise_sup_norm D (i := 1) (j := 0)
  have h11 := Matrix.norm_entry_le_entrywise_sup_norm D (i := 1) (j := 1)
  have h00 := Matrix.norm_entry_le_entrywise_sup_norm D (i := 0) (j := 0)
  have h01 := Matrix.norm_entry_le_entrywise_sup_norm D (i := 0) (j := 1)
  have hn : ‖D 1 0 + D 1 1 - D 0 0 - D 0 1‖ ≤ 4 * ‖D‖ := by
    have hh := norm_sub_le (D 1 0 + D 1 1 - D 0 0) (D 0 1)
    have hh' := norm_sub_le (D 1 0 + D 1 1) (D 0 0)
    have hh'' := norm_add_le (D 1 0) (D 1 1)
    linarith
  rw [dirichlet_residual_eq38, norm_div, norm_mul, Complex.norm_two, Complex.norm_I, mul_one]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  change ‖D 1 0 + D 1 1 - D 0 0 - D 0 1‖ ≤ _
  nlinarith

/-- Locally uniform scalar asymptotics, with the exact positive free sine normalization. -/
theorem dirichletChar_asymp (φ₀ : PotPair) :
  ∀ ε : ℝ, 0 < ε → ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ R : ℝ,
    ∀ φ : PotPair, φ ∈ U → ∀ z : ℂ, R ≤ ‖z‖ →
      ‖dirichletChar φ z - Complex.sin z‖ ≤ ε * Real.exp |z.im| := by
  intro ε hε
  obtain ⟨U, hU, R, hR⟩ := fundPair_asymp φ₀ (half_pos hε)
  refine ⟨U, hU, R, fun φ hφ z hz => ?_⟩
  have hnorm : ‖monodromyPair φ z - freeE z 1‖ ≤ ε / 2 * Real.exp |z.im| := by
    apply (Matrix.norm_le_iff (by positivity)).mpr
    intro i j
    simpa only [monodromyPair_eq_fundPair, freeFund_apply, Matrix.sub_apply, mul_one] using
      hR φ hφ z hz ⟨1, zero_le_one, le_rfl⟩ i j
  exact (norm_dirichletResidual_le38 φ z).trans (by nlinarith)

/-- One nonnegative constant precedes every bounded potential and sampled complex sequence. -/
theorem dirichletChar_seq_l2_38 (R c : ℝ) :
  ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
    (∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
    Summable (fun n : ℤ => ‖dirichletChar φ (υ n) - Complex.sin (υ n)‖ ^ 2) ∧
      (∑' n : ℤ, ‖dirichletChar φ (υ n) - Complex.sin (υ n)‖ ^ 2) ≤ C := by
  obtain ⟨B, hB⟩ := fundPair_seq_l2 R c
  refine ⟨4 * max B 0, by positivity, fun φ hφ υ hshift => ?_⟩
  obtain ⟨hs, ht⟩ := hB φ hφ υ hshift ⟨1, zero_le_one, le_rfl⟩
  have hpoint (n : ℤ) : ‖dirichletChar φ (υ n) - Complex.sin (υ n)‖ ^ 2 ≤
      4 * ‖fundPair φ (υ n) ⟨1, zero_le_one, le_rfl⟩ -
        freeFund (υ n) ⟨1, zero_le_one, le_rfl⟩‖ ^ 2 := by
    have hh := norm_dirichletResidual_le38 φ (υ n)
    rw [monodromyPair_eq_fundPair] at hh
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
    simpa only [mul_pow, freeFund_apply, show (2 : ℝ) ^ 2 = 4 from by norm_num] using hsq
  have hfin (T : Finset ℤ) : ∑ n ∈ T, ‖dirichletChar φ (υ n) - Complex.sin (υ n)‖ ^ 2 ≤ 4 * max B 0 := by
    calc _ ≤ ∑ n ∈ T, 4 * ‖fundPair φ (υ n) ⟨1, zero_le_one, le_rfl⟩ -
          freeFund (υ n) ⟨1, zero_le_one, le_rfl⟩‖ ^ 2 := Finset.sum_le_sum (fun n _ => hpoint n)
      _ = 4 * (∑ n ∈ T, ‖fundPair φ (υ n) ⟨1, zero_le_one, le_rfl⟩ -
          freeFund (υ n) ⟨1, zero_le_one, le_rfl⟩‖ ^ 2) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((hs.sum_le_tsum T (fun n _ => sq_nonneg _)).trans (ht.trans (le_max_left _ _))) (by norm_num)
  have hres := summable_of_sum_le (fun n : ℤ => sq_nonneg ‖dirichletChar φ (υ n) - Complex.sin (υ n)‖) hfin
  exact ⟨hres, hres.tsum_le_of_sum_le hfin⟩

end
end NlsGge.GK38
