import NlsGge.GK38.PairAsymptoticsSeqTime

/-!
# F5: sequence asymptotics of the fundamental matrix

Grébert–Kappeler Theorem 2.4. The norm is the elementwise maximum norm used by the accepted
F2 API. All bounds are uniform over the potential ball, bounded complex frequency
perturbations, and the closed unit time interval.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace NlsGge.GK38

noncomputable section

theorem seqTimeMass38_force_sum_le (φ : PotPair) {c : ℝ} (hc : 0 ≤ c)
    (υ : ℤ → ℂ) (hυ : ∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c)
    (T : Finset ℤ) :
    ∑ n ∈ T, seqTimeMass38 (pairForce38 φ (υ n)) ≤ Real.exp c ^ 2 * potNormSq38 φ := by
  have hi : ∀ n : ℤ, IntervalIntegrable (seqMass38 (pairForce38 φ (υ n))) volume 0 1 :=
    fun n => (continuous_seqMass38 _).intervalIntegrable 0 1
  have hct : Continuous (fun s : ℝ => ∑ n ∈ T, seqMass38 (pairForce38 φ (υ n)) s) :=
    continuous_finsetSum T (fun n _ => continuous_seqMass38 _)
  have he : (∑ n ∈ T, seqTimeMass38 (pairForce38 φ (υ n))) =
      ∫ s in (0 : ℝ)..1, ∑ n ∈ T, seqMass38 (pairForce38 φ (υ n)) s := by
    exact (intervalIntegral.integral_finsetSum (fun n _ => hi n)).symm
  rw [he]
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one (hct.intervalIntegrable 0 1)
    (intervalIntegrable_const (c := Real.exp c ^ 2 * potNormSq38 φ))
    (fun s hs => seqMass38_force_sum_le φ hc υ hυ hs T)
  simpa using h

theorem seqGamma38_force_sum_le (φ : PotPair) {c : ℝ} (hc : 0 ≤ c)
    (υ : ℤ → ℂ) (hυ : ∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c)
    (T : Finset ℤ) :
    ∑ n ∈ T, seqGamma38 φ (pairForce38 φ (υ n)) ^ 2 ≤
      2 * potNormSq38 φ * (Real.exp c ^ 2 * potNormSq38 φ) := by
  simp_rw [seqGamma38_sq]
  rw [← Finset.mul_sum]
  exact mul_le_mul (seqPotMass38_le φ) (seqTimeMass38_force_sum_le φ hc υ hυ T)
    (Finset.sum_nonneg (fun n _ => seqTimeMass38_nonneg _))
    (by positivity [potNormSq38_nonneg φ])

theorem seqRemainder38_sq_le (φ : PotPair) (z : ℂ) (t : Set.Icc (0 : ℝ) 1) :
    ‖fundPair φ z t - freeFund z t‖ ^ 2 ≤
      2 * seqMass38 (pairForce38 φ z) t +
        2 * (Real.exp (|z.im| * (t : ℝ) + potPrim38 φ t) *
          seqGamma38 φ (pairForce38 φ z)) ^ 2 := by
  let F : PairCont38 := pairForce38 φ z
  let D : PairCont38 := fundContP φ z - freeFundP z
  let G : PairCont38 := volterraP φ z D
  let γ : ℝ := seqGamma38 φ F
  have hD : D = F + G := fundCont_sub_free_eq φ z
  have hG : G = volterraP φ z F + volterraP φ z G := by
    change volterraP φ z D = _
    rw [hD, map_add]
  have hg : ∀ i j : Fin 2, ‖G t i j‖ ≤
      Real.exp (|z.im| * (t : ℝ) + potPrim38 φ t) * γ := fun i j =>
    norm_volterra_solution_entry_le_weighted φ z (volterraP φ z F) G γ
      (seqGamma38_nonneg φ F)
      (fun s hs i j => norm_volterraP_entry_time_le φ z F ⟨s, hs⟩ i j) hG t i j
  let A : ℝ := Real.exp (|z.im| * (t : ℝ) + potPrim38 φ t) * γ
  have hA : 0 ≤ A := mul_nonneg (Real.exp_pos _).le (seqGamma38_nonneg φ F)
  have hnorm : ‖fundPair φ z t - freeFund z t‖ ≤ Real.sqrt (seqMass38 F t) + A := by
    apply (Matrix.norm_le_iff (add_nonneg (Real.sqrt_nonneg _) hA)).mpr
    intro i j
    have he := congrArg (fun N : PairCont38 => N t i j) hD
    change (fundPair φ z t - freeFund z t) i j = F t i j + G t i j at he
    rw [he]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hg i j))
    have h := seqEntry38_le_sqrt F (t : ℝ) i j
    rwa [ext38_of_mem _ t.2] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have he := Real.sq_sqrt (seqMass38_nonneg F t)
  have hb : (Real.sqrt (seqMass38 F t) + A) ^ 2 ≤ 2 * seqMass38 F t + 2 * A ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (seqMass38 F t) - A)]
  exact hs.trans hb


/-- Theorem 2.4: one bound for the full potential ball, all bounded complex frequency
perturbations, and every time in the closed unit interval. -/
theorem fundPair_seq_l2 (R c : ℝ) :
    ∃ C : ℝ, ∀ φ : PotPair, ‖φ‖ ≤ R → ∀ υ : ℤ → ℂ,
      (∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
      ∀ t : Set.Icc (0 : ℝ) 1,
        Summable (fun n : ℤ => ‖fundPair φ (υ n) t - freeFund (υ n) t‖ ^ 2) ∧
        ∑' n : ℤ, ‖fundPair φ (υ n) t - freeFund (υ n) t‖ ^ 2 ≤ C := by
  let r : ℝ := max R 0
  let d : ℝ := max c 0
  let B : ℝ := 2 * Real.exp d ^ 2 * r ^ 2
  let A : ℝ := Real.exp (d + 2 * r)
  have hr : 0 ≤ r := le_max_right _ _
  have hd : 0 ≤ d := le_max_right _ _
  refine ⟨2 * B + 2 * A ^ 2 * (4 * r ^ 2 * B), fun φ hφ υ hυ t => ?_⟩
  have hφr : ‖φ‖ ≤ r := hφ.trans (le_max_left _ _)
  have hp : potNormSq38 φ ≤ 2 * r ^ 2 :=
    (potNormSq38_le φ).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hφr 2) (by norm_num))
  have hv : ∀ n : ℤ, ‖υ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ d :=
    fun n => (hυ n).trans (le_max_left _ _)
  have hB : Real.exp d ^ 2 * potNormSq38 φ ≤ B := by
    unfold B
    have h := mul_le_mul_of_nonneg_left hp (sq_nonneg (Real.exp d))
    nlinarith
  have hF : ∀ T : Finset ℤ, ∑ n ∈ T, seqMass38 (pairForce38 φ (υ n)) t ≤ B :=
    fun T => (seqMass38_force_sum_le φ hd υ hv t.2 T).trans hB
  have hγ : ∀ T : Finset ℤ, ∑ n ∈ T, seqGamma38 φ (pairForce38 φ (υ n)) ^ 2 ≤ 4 * r ^ 2 * B := by
    intro T
    refine (seqGamma38_force_sum_le φ hd υ hv T).trans ?_
    exact mul_le_mul (by nlinarith [hp]) hB
      (mul_nonneg (sq_nonneg _) (potNormSq38_nonneg φ)) (by positivity)
  have him : ∀ n : ℤ, |(υ n).im| ≤ d := by
    intro n
    have he : (υ n - (n : ℂ) * (Real.pi : ℂ)).im = (υ n).im := by simp
    rw [← he]
    exact (Complex.abs_im_le_norm _).trans (hv n)
  have hpot : potPrim38 φ (t : ℝ) ≤ 2 * r :=
    (potPrim38_le_one φ t.2).trans ((potL1Norm38_le_two_mul φ).trans
      (mul_le_mul_of_nonneg_left hφr (by norm_num)))
  have hAmp : ∀ n : ℤ, Real.exp (|(υ n).im| * (t : ℝ) + potPrim38 φ t) ≤ A := by
    intro n
    apply Real.exp_le_exp.mpr
    have hmul : |(υ n).im| * (t : ℝ) ≤ d :=
      (mul_le_mul_of_nonneg_right (him n) t.2.1).trans
        (mul_le_of_le_one_right hd t.2.2)
    linarith
  have hpoint : ∀ n : ℤ, ‖fundPair φ (υ n) t - freeFund (υ n) t‖ ^ 2 ≤
      2 * seqMass38 (pairForce38 φ (υ n)) t +
        2 * A ^ 2 * seqGamma38 φ (pairForce38 φ (υ n)) ^ 2 := by
    intro n
    have hg0 := seqGamma38_nonneg φ (pairForce38 φ (υ n))
    have hsq := pow_le_pow_left₀
      (mul_nonneg (Real.exp_pos _).le hg0)
      (mul_le_mul_of_nonneg_right (hAmp n) hg0) 2
    refine (seqRemainder38_sq_le φ (υ n) t).trans ?_
    calc _ ≤ 2 * seqMass38 (pairForce38 φ (υ n)) t +
          2 * (A * seqGamma38 φ (pairForce38 φ (υ n))) ^ 2 :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 2 by norm_num))
      _ = _ := by ring
  have hfin : ∀ T : Finset ℤ,
      ∑ n ∈ T, ‖fundPair φ (υ n) t - freeFund (υ n) t‖ ^ 2 ≤
        2 * B + 2 * A ^ 2 * (4 * r ^ 2 * B) := by
    intro T
    calc _ ≤ ∑ n ∈ T, (2 * seqMass38 (pairForce38 φ (υ n)) t +
          2 * A ^ 2 * seqGamma38 φ (pairForce38 φ (υ n)) ^ 2) :=
            Finset.sum_le_sum (fun n _ => hpoint n)
      _ = 2 * (∑ n ∈ T, seqMass38 (pairForce38 φ (υ n)) t) +
          (2 * A ^ 2) * (∑ n ∈ T, seqGamma38 φ (pairForce38 φ (υ n)) ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hF T) (by norm_num))
        (mul_le_mul_of_nonneg_left (hγ T) (by positivity))
  have hs := summable_of_sum_le
    (fun n : ℤ => sq_nonneg ‖fundPair φ (υ n) t - freeFund (υ n) t‖) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

end

end NlsGge.GK38
