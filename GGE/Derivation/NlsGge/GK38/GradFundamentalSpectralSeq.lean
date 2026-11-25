import NlsGge.GK38.GradFundamentalDefs

/-!
# K1: uniform square sums of the spectral derivatives

Grébert–Kappeler, Chapter I, Lemma 4.3, the two scalar claims. Finite spectral
windows are estimated in a Euclidean space before summability is established.
This module uses F5 and analyticity without the potential-gradient machinery.
-/

set_option autoImplicit false
open Filter Topology MeasureTheory Set Metric
open scoped Matrix.Norms.Elementwise
namespace NlsGge.GK38
noncomputable section

/-- Cauchy's estimate on a whole finite spectral window. -/
theorem k1Cauchy38_sum_sq_deriv_le (f : ℤ → ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ n, Differentiable ℂ (f n))
    (hb : ∀ w ∈ sphere (0 : ℂ) 1, ∀ T : Finset ℤ, ∑ n ∈ T, ‖f n w‖ ^ 2 ≤ B)
    (T : Finset ℤ) : ∑ n ∈ T, ‖deriv (f n) 0‖ ^ 2 ≤ B := by
  classical
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : T => ℂ)).symm
  let F : ℂ → EuclideanSpace ℂ T := fun w => e (fun n : T => f n w)
  have hd (w : ℂ) : HasDerivAt F (e (fun n : T => deriv (f n) w)) w :=
    e.hasFDerivAt.comp_hasDerivAt w (hasDerivAt_pi.mpr (fun n => (hf n w).hasDerivAt))
  have hF : Differentiable ℂ F := fun w => (hd w).differentiableAt
  have hs : ∀ w ∈ sphere (0 : ℂ) 1, ‖F w‖ ≤ Real.sqrt B := by
    intro w hw
    apply le_of_sq_le_sq ?_ (Real.sqrt_nonneg B)
    rw [Real.sq_sqrt hB, EuclideanSpace.norm_sq_eq]
    simpa only [F, e, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
      Finset.sum_coe_sort T (fun n : ℤ => ‖f n w‖ ^ 2)] using hb w hw T
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : 0 < (1 : ℝ)) hF.diffContOnCl hs
  rw [(hd 0).deriv, div_one] at h
  have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [Real.sq_sqrt hB, EuclideanSpace.norm_sq_eq] at hh
  simpa only [e, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
    Finset.sum_coe_sort T (fun n : ℤ => ‖deriv (f n) 0‖ ^ 2)] using hh


/-- F5 transfers a scalar residual bounded by two matrix errors to its derivative. -/
theorem k1SpectralResidual38_l2 (F : PotPair → ℂ → ℂ)
    (hF : ∀ φ, Differentiable ℂ (F φ))
    (hval : ∀ φ z, ‖F φ z‖ ≤
      2 * ‖fundPair φ z ⟨1, by norm_num, le_rfl⟩ - freeFund z ⟨1, by norm_num, le_rfl⟩‖)
    (R c : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
        (∀ n, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
        k1SquareBound38 (fun n => ‖deriv (F φ) (υ n)‖ ^ 2) C := by
  obtain ⟨B, hB⟩ := fundPair_seq_l2 R (c + 1)
  let B' : ℝ := max B 0
  have hB' : 0 ≤ B' := le_max_right _ _
  refine ⟨4 * B', by positivity, fun φ hφ υ hυ => ?_⟩
  have hfinite (T : Finset ℤ) : ∑ n ∈ T, ‖deriv (F φ) (υ n)‖ ^ 2 ≤ 4 * B' := by
    let f : ℤ → ℂ → ℂ := fun n w => F φ (υ n + w)
    have hf : ∀ n, Differentiable ℂ (f n) := fun n =>
      (hF φ).comp ((differentiable_const (υ n)).add differentiable_id)
    have hb : ∀ w ∈ sphere (0 : ℂ) 1, ∀ S : Finset ℤ,
        ∑ n ∈ S, ‖f n w‖ ^ 2 ≤ 4 * B' := by
      intro w hw S
      have hn : ‖w‖ = 1 := by simpa using mem_sphere_iff_norm.mp hw
      have hshift : ∀ n : ℤ, ‖υ n + w - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c + 1 := by
        intro n
        have he : υ n + w - (n : ℂ) * (Real.pi : ℂ) =
            (υ n - (n : ℂ) * (Real.pi : ℂ)) + w := by ring
        rw [he]
        exact (norm_add_le _ _).trans (by rw [hn]; linarith [hυ n])
      obtain ⟨hs, ht⟩ := hB φ hφ (fun n => υ n + w) hshift ⟨1, by norm_num, le_rfl⟩
      calc _ ≤ ∑ n ∈ S, 4 *
            ‖fundPair φ (υ n + w) ⟨1, by norm_num, le_rfl⟩ -
              freeFund (υ n + w) ⟨1, by norm_num, le_rfl⟩‖ ^ 2 := by
              apply Finset.sum_le_sum
              intro n _
              have hp := pow_le_pow_left₀ (norm_nonneg _) (hval φ (υ n + w)) 2
              simpa only [f, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hp
        _ = 4 * (∑ n ∈ S,
            ‖fundPair φ (υ n + w) ⟨1, by norm_num, le_rfl⟩ -
              freeFund (υ n + w) ⟨1, by norm_num, le_rfl⟩‖ ^ 2) := by rw [Finset.mul_sum]
        _ ≤ 4 * B' := mul_le_mul_of_nonneg_left
          ((hs.sum_le_tsum S (fun n _ => sq_nonneg _)).trans (ht.trans (le_max_left _ _)))
          (by norm_num)
    have hd (n : ℤ) : deriv (f n) 0 = deriv (F φ) (υ n) := by
      have hout : HasDerivAt (F φ) (deriv (F φ) (υ n)) (υ n + 0) := by
        simpa only [add_zero] using (hF φ (υ n)).hasDerivAt
      have h := hout.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add (υ n))
      simpa only [f, Function.comp_def, add_zero, mul_one] using h.deriv
    simpa only [hd] using k1Cauchy38_sum_sq_deriv_le f (4 * B') (by positivity) hf hb T
  exact k1SquareBound38_of_finite (fun n => sq_nonneg _) hfinite


/-- The trace residual is bounded by two entries of the matrix residual. -/
theorem norm_discrimResidual38_le (φ : PotPair) (z : ℂ) :
    ‖discrim φ z - 2 * Complex.cos z‖ ≤
      2 * ‖fundPair φ z ⟨1, zero_le_one, le_rfl⟩ -
        freeFund z ⟨1, zero_le_one, le_rfl⟩‖ := by
  let t : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  have hfree : freeE z 1 0 0 + freeE z 1 1 1 = 2 * Complex.cos z := by
    have h := discrim_eq 0 z
    rw [monodromyPair_zero_potential, discrim_zero] at h
    exact h.symm
  have heq : discrim φ z - 2 * Complex.cos z =
      (fundPair φ z t - freeFund z t) 0 0 +
        (fundPair φ z t - freeFund z t) 1 1 := by
    rw [discrim_eq, monodromyPair_eq_fundPair, ← hfree]
    simp only [t, freeFund_apply, Matrix.sub_apply]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (by
    have h0 := Matrix.norm_entry_le_entrywise_sup_norm (fundPair φ z t - freeFund z t)
      (i := 0) (j := 0)
    have h1 := Matrix.norm_entry_le_entrywise_sup_norm (fundPair φ z t - freeFund z t)
      (i := 1) (j := 1)
    linarith)

/-- The antitrace is bounded by the two off-diagonal matrix residuals. -/
theorem norm_antiDiscrim38_le (φ : PotPair) (z : ℂ) :
    ‖antiDiscrim φ z‖ ≤
      2 * ‖fundPair φ z ⟨1, zero_le_one, le_rfl⟩ -
        freeFund z ⟨1, zero_le_one, le_rfl⟩‖ := by
  let t : Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩
  have heq : antiDiscrim φ z = (fundPair φ z t - freeFund z t) 0 1 +
      (fundPair φ z t - freeFund z t) 1 0 := by
    simp [antiDiscrim, monodromyPair_eq_fundPair, t, freeFund_apply, freeE]
  rw [heq]
  exact (norm_add_le _ _).trans (by
    have h0 := Matrix.norm_entry_le_entrywise_sup_norm (fundPair φ z t - freeFund z t)
      (i := 0) (j := 1)
    have h1 := Matrix.norm_entry_le_entrywise_sup_norm (fundPair φ z t - freeFund z t)
      (i := 1) (j := 0)
    linarith)

/-- GK Lemma 4.3: the full spectral derivative trace residual has a uniform square sum. -/
theorem discrimDeriv_l2 (R c : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
      (∀ n, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      k1SquareBound38
        (fun n => ‖deriv (discrim φ) (υ n) + 2 * Complex.sin (υ n)‖ ^ 2) C := by
  have hd (φ : PotPair) : Differentiable ℂ (discrim φ) := fun z =>
    (analyticOnNhd_discrim_z φ z (mem_univ _)).differentiableAt
  obtain ⟨C, hC, h⟩ := k1SpectralResidual38_l2
    (fun φ z => discrim φ z - 2 * Complex.cos z)
    (fun φ => (hd φ).sub (by fun_prop)) norm_discrimResidual38_le R c
  refine ⟨C, hC, fun φ hφ υ hυ => ?_⟩
  have heq (z : ℂ) :
      deriv (fun w => discrim φ w - 2 * Complex.cos w) z =
        deriv (discrim φ) z + 2 * Complex.sin z := by
    have hh := ((hd φ z).hasDerivAt.sub ((Complex.hasDerivAt_cos z).const_mul 2)).deriv
    convert hh using 1 <;> ring
  simpa only [heq] using h φ hφ υ hυ

/-- GK Lemma 4.3: the antidiscriminant spectral derivative has a uniform square sum. -/
theorem antiDiscrimDeriv_l2 (R c : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
      (∀ n, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      k1SquareBound38 (fun n => ‖deriv (antiDiscrim φ) (υ n)‖ ^ 2) C :=
  k1SpectralResidual38_l2 antiDiscrim
    (fun φ z => (analyticOnNhd_antiDiscrim_z φ z (mem_univ _)).differentiableAt)
    norm_antiDiscrim38_le R c

end
end NlsGge.GK38
