import NlsGge.GK38.GradFundamentalGradientPointwise

/-! # K1: both exact uniform gradient square-sequence estimates.
GK Chapter I, Lemma4.3. Constants precede potentials, arbitrary complex shifted
sequences and every closed-interval time. Finite windows precede summability/tsum.
-/
set_option autoImplicit false
open Set
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

/-- Transfer a concrete cubic residual bound to a uniform fixed-time square sum. -/
theorem k1GradientMassSeq38 (G : PotPair → ℂ → Icc (0 : ℝ) 1 → ℝ)
    (hG0 : ∀ φ z t, 0 ≤ G φ z t)
    (hG : ∀ r d : ℝ, 0 ≤ r → 0 ≤ d → ∀ φ z, ‖φ‖ ≤ r → |z.im| ≤ d →
      ∀ t : Icc (0 : ℝ) 1, G φ z t ≤ 256 * (Real.exp (d + 2 * r)) ^ 4 *
        (‖fundPair φ z t - freeFund z t‖ ^ 2 +
          ‖fundPair φ z ⟨1, zero_le_one, le_rfl⟩ - freeFund z ⟨1, zero_le_one, le_rfl⟩‖ ^ 2))
    (R c : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
        (∀ n, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
        ∀ t : Icc (0 : ℝ) 1, k1SquareBound38 (fun n => G φ (υ n) t) C := by
  obtain ⟨B, hB⟩ := fundPair_seq_l2 R c
  let r : ℝ := max R 0
  let d : ℝ := max c 0
  let H : ℝ := Real.exp (d + 2 * r)
  let B' : ℝ := max B 0
  refine ⟨512 * H ^ 4 * B', by dsimp [B']; positivity, fun φ hφ υ hυ t => ?_⟩
  have hr : 0 ≤ r := le_max_right _ _
  have hd : 0 ≤ d := le_max_right _ _
  have hφr : ‖φ‖ ≤ r := hφ.trans (le_max_left _ _)
  have him (n : ℤ) : |(υ n).im| ≤ d := by
    have he : (υ n - (n : ℂ) * (Real.pi : ℂ)).im = (υ n).im := by simp
    rw [← he]
    exact (Complex.abs_im_le_norm _).trans ((hυ n).trans (le_max_left _ _))
  apply k1SquareBound38_of_finite (fun n => hG0 φ (υ n) t)
  intro T
  have hf (s : Icc (0 : ℝ) 1) :
      ∑ n ∈ T, ‖fundPair φ (υ n) s - freeFund (υ n) s‖ ^ 2 ≤ B' := by
    obtain ⟨hs, ht⟩ := hB φ hφ υ hυ s
    exact (hs.sum_le_tsum T (fun _ _ => sq_nonneg _)).trans (ht.trans (le_max_left _ _))
  calc
    _ ≤ ∑ n ∈ T, 256 * H ^ 4 *
        (‖fundPair φ (υ n) t - freeFund (υ n) t‖ ^ 2 +
          ‖fundPair φ (υ n) ⟨1, zero_le_one, le_rfl⟩ -
            freeFund (υ n) ⟨1, zero_le_one, le_rfl⟩‖ ^ 2) :=
      Finset.sum_le_sum fun n _ => hG r d hr hd φ (υ n) hφr (him n) t
    _ = (256 * H ^ 4) * ((∑ n ∈ T, ‖fundPair φ (υ n) t - freeFund (υ n) t‖ ^ 2) +
        ∑ n ∈ T, ‖fundPair φ (υ n) ⟨1, zero_le_one, le_rfl⟩ -
          freeFund (υ n) ⟨1, zero_le_one, le_rfl⟩‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (256 * H ^ 4) * (B' + B') :=
      mul_le_mul_of_nonneg_left (add_le_add (hf t) (hf ⟨1, zero_le_one, le_rfl⟩)) (by positivity)
    _ = _ := by ring

/-- The third exact Lemma4.3 estimate, including both vector components. -/
theorem gradDiscrim_l2 (R c : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
      (∀ n, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      ∀ t : Icc (0 : ℝ) 1, k1SquareBound38 (fun n =>
        ‖(Complex.I • gradDiscrim38 φ (υ n) t) 0‖ ^ 2 +
          ‖(Complex.I • gradDiscrim38 φ (υ n) t) 1‖ ^ 2) C :=
  k1GradientMassSeq38 k1GradDiscrimMass38 (fun _ _ _ => by unfold k1GradDiscrimMass38; positivity)
    (fun r d hr hd φ z hφ hz t => (k1GradientMassPointwise38 r d hr hd φ z hφ hz t).1) R c

/-- The fourth exact Lemma4.3 estimate retains the actual complex shifted phase. -/
theorem gradAntiDiscrim_l2 (R c : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
      (∀ n, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      ∀ t : Icc (0 : ℝ) 1, k1SquareBound38 (fun n =>
        ‖(Complex.I • gradAntiDiscrim38 φ (υ n) t -
          ![-Complex.exp (-Complex.I * υ n * (1 - 2 * (t : ℝ))),
            Complex.exp (Complex.I * υ n * (1 - 2 * (t : ℝ)))]) 0‖ ^ 2 +
        ‖(Complex.I • gradAntiDiscrim38 φ (υ n) t -
          ![-Complex.exp (-Complex.I * υ n * (1 - 2 * (t : ℝ))),
            Complex.exp (Complex.I * υ n * (1 - 2 * (t : ℝ)))]) 1‖ ^ 2) C :=
  k1GradientMassSeq38 k1GradAntiMass38 (fun _ _ _ => by unfold k1GradAntiMass38; positivity)
    (fun r d hr hd φ z hφ hz t => (k1GradientMassPointwise38 r d hr hd φ z hφ hz t).2) R c

end
end NlsGge.GK38
