import NlsGge.GK38.PairVolterraOp

/-!
# F2 (part 3): the estimate `‖𝒱ⁿ‖ ≤ e^{|Im z|} ‖φ‖₁ⁿ / n!`

Source: Grébert-Kappeler book, Chapter I, section 1, proof of Theorem 1.1 (the Volterra iteration;
GKP Lemma 2.1 has the same bound).  The pointwise estimate is

`‖(𝒱ⁿ N)(t)‖ ≤ e^{|Im z| t} W(t)ⁿ / n! ‖N‖`, `W(t) = ∫₀ᵗ (|φ₁| + |φ₂|)`,

proved by induction; the induction step needs `∫₀ᵗ w W ⁿ = W(t)ⁿ⁺¹/(n+1)` for the primitive `W` of an
`L¹` function `w`.  This is the fundamental theorem of calculus for the absolutely continuous
function `Wⁿ⁺¹` (Mathlib's `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`, with the
Lebesgue differentiation theorem `IntervalIntegrable.ae_hasDerivAt_integral`).
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

/-! ### The primitive of an `L¹` function and its powers -/

/-- `∫₀ᵗ w · (∫₀ˢ w)ⁿ ds = (∫₀ᵗ w)ⁿ⁺¹ / (n+1)`. -/
theorem integral_mul_primitive_pow {w : ℝ → ℝ} {t : ℝ}
    (hw : IntervalIntegrable w volume 0 t) (n : ℕ) :
    ∫ s in (0 : ℝ)..t, w s * (∫ r in (0 : ℝ)..s, w r) ^ n =
      (∫ r in (0 : ℝ)..t, w r) ^ (n + 1) / (n + 1) := by
  set W : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, w r with hWdef
  have h0t : (0 : ℝ) ∈ Set.uIcc 0 t := Set.left_mem_uIcc
  have hAC : AbsolutelyContinuousOnInterval W 0 t :=
    hw.absolutelyContinuousOnInterval_intervalIntegral h0t
  have hACp : ∀ m : ℕ, AbsolutelyContinuousOnInterval (fun s => W s ^ (m + 1)) 0 t := by
    intro m
    induction m with
    | zero => simpa using hAC
    | succ m ih =>
      have := ih.fun_mul hAC
      simpa [pow_succ] using this
  set F : ℝ → ℝ := fun s => ((n : ℝ) + 1)⁻¹ * W s ^ (n + 1) with hF
  have hFac : AbsolutelyContinuousOnInterval F 0 t := (hACp n).const_mul _
  have hFTC := hFac.integral_deriv_eq_sub
  have hF0 : F 0 = 0 := by simp [hF, hWdef]
  have hderiv : ∫ s in (0 : ℝ)..t, deriv F s = ∫ s in (0 : ℝ)..t, w s * W s ^ n := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hw.ae_hasDerivAt_integral] with x hx hxI
    have hxu : x ∈ Set.uIcc 0 t := Set.uIoc_subset_uIcc hxI
    have hW := hx hxu 0 h0t
    have hFd : HasDerivAt F (((n : ℝ) + 1)⁻¹ * (((n + 1 : ℕ) : ℝ) * W x ^ n * w x)) x :=
      ((hW.pow (n + 1)).const_mul _)
    rw [hFd.deriv]
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [← hderiv, hFTC, hF0, sub_zero]
  simp only [hF]
  ring

/-- The primitive `W(t) = ∫₀ᵗ (|φ₁| + |φ₂|)`; `W(1) = potL1Norm38 φ`. -/
def potPrim38 (φ : PotPair) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, potW38 φ s

theorem potPrim38_one (φ : PotPair) : potPrim38 φ 1 = potL1Norm38 φ := rfl

theorem potPrim38_nonneg (φ : PotPair) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ potPrim38 φ t :=
  intervalIntegral.integral_nonneg ht fun s _ => potW38_nonneg φ s

theorem potPrim38_le_one (φ : PotPair) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    potPrim38 φ t ≤ potL1Norm38 φ :=
  intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (Filter.Eventually.of_forall fun s => potW38_nonneg φ s) (intervalIntegrable_potW38 φ)

theorem continuousOn_potPrim38 (φ : PotPair) : ContinuousOn (potPrim38 φ) (Set.Icc (0 : ℝ) 1) := by
  have h := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1) (f := potW38 φ)
    (by rw [Set.uIcc_of_le zero_le_one]
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
          (intervalIntegrable_potW38 φ))
  rwa [Set.uIcc_of_le zero_le_one] at h

/-! ### The iterated estimate -/

/-- Weighted iterate estimate: if `|N(s)_{ij}| ≤ e^{|Im z| s} γ` then
`|(𝒱ⁿ N)(t)_{ij}| ≤ e^{|Im z| t} W(t)ⁿ/n! γ`. -/
theorem norm_volterra_pow_entry_le_weighted (φ : PotPair) (z : ℂ) (n : ℕ) (N : PairCont38) (γ : ℝ)
    (hN : ∀ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2),
      ‖N ⟨s, hs⟩ i j‖ ≤ Real.exp (|z.im| * s) * γ) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖((volterraP φ z ^ n) N) ⟨t, ht⟩ i j‖ ≤
      Real.exp (|z.im| * t) * (potPrim38 φ t ^ n / n.factorial) * γ := by
  induction n generalizing t i j with
  | zero =>
    simp only [pow_zero, one_apply_eq_self, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    exact hN t ht i j
  | succ n ih =>
    set M : PairCont38 := (volterraP φ z ^ n) N with hM
    have hpow : (volterraP φ z ^ (n + 1)) N = volterraP φ z M := by
      rw [pow_succ', mul_apply_eq_comp]
    rw [hpow, volterraP_apply]
    set a : ℝ := |z.im| with ha
    set β : ℝ → ℝ := fun s => Real.exp (a * s) * (potPrim38 φ s ^ n / n.factorial) * γ with hβdef
    have hβ : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i j, ‖ext38 M s i j‖ ≤ β s := fun s hs i j => by
      rw [ext38_of_mem M hs]; exact ih hs i j
    have hβc : ContinuousOn β (Set.uIcc 0 1) := by
      rw [Set.uIcc_of_le zero_le_one]
      have h1 : ContinuousOn (fun s : ℝ => Real.exp (a * s)) (Set.Icc 0 1) := by fun_prop
      have h2 := continuousOn_potPrim38 φ
      simp only [hβdef]
      exact ((h1.mul ((h2.pow n).div_const _)).mul continuousOn_const)
    have hint : IntervalIntegrable (fun s => potW38 φ s * β s) volume 0 1 :=
      (intervalIntegrable_potW38 φ).mul_continuousOn hβc
    refine (norm_volterraFun_entry_le φ z M β hβ hint ht i j).trans (le_of_eq ?_)
    have hcalc : ∀ s ∈ Set.uIcc (0 : ℝ) t, Real.exp (a * (t - s)) * (potW38 φ s * β s) =
        (Real.exp (a * t) * γ / n.factorial) * (potW38 φ s * potPrim38 φ s ^ n) := by
      intro s _
      have h : Real.exp (a * (t - s)) * Real.exp (a * s) = Real.exp (a * t) := by
        rw [← Real.exp_add]; ring_nf
      simp only [hβdef]
      have hf : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      linear_combination (potW38 φ s * potPrim38 φ s ^ n * γ) * h
    rw [intervalIntegral.integral_congr hcalc, intervalIntegral.integral_const_mul]
    have hw : IntervalIntegrable (potW38 φ) volume 0 t :=
      (intervalIntegrable_potW38 φ).mono_set (uIcc_zero_subset ht)
    have hkey := integral_mul_primitive_pow hw n
    have : ∫ s in (0 : ℝ)..t, potW38 φ s * potPrim38 φ s ^ n =
        potPrim38 φ t ^ (n + 1) / (n + 1) := hkey
    rw [this, Nat.factorial_succ]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp


theorem norm_volterra_pow_entry_le (φ : PotPair) (z : ℂ) (n : ℕ) (N : PairCont38) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖((volterraP φ z ^ n) N) ⟨t, ht⟩ i j‖ ≤
      Real.exp (|z.im| * t) * (potPrim38 φ t ^ n / n.factorial) * ‖N‖ := by
  refine norm_volterra_pow_entry_le_weighted φ z n N ‖N‖ (fun s hs i j => ?_) ht i j
  have h1 : 1 ≤ Real.exp (|z.im| * s) := Real.one_le_exp (mul_nonneg (abs_nonneg _) hs.1)
  exact ((norm_le_pi_norm (N ⟨s, hs⟩ i) j).trans ((norm_le_pi_norm (N ⟨s, hs⟩) i).trans
      (N.norm_coe_le_norm ⟨s, hs⟩))).trans (le_mul_of_one_le_left (norm_nonneg _) h1)

/-- `‖𝒱ⁿ‖ ≤ e^{|Im z|} ‖φ‖₁ⁿ / n!` (book Theorem 1.1, proof; `‖φ‖₁ = potL1Norm38 φ`). -/
theorem norm_volterraP_pow_le (φ : PotPair) (z : ℂ) (n : ℕ) :
    ‖volterraP φ z ^ n‖ ≤ Real.exp |z.im| * (potL1Norm38 φ ^ n / n.factorial) := by
  have hL := potL1Norm38_nonneg φ
  have hC : 0 ≤ Real.exp |z.im| * (potL1Norm38 φ ^ n / n.factorial) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun N => ?_
  have hC' : 0 ≤ Real.exp |z.im| * (potL1Norm38 φ ^ n / n.factorial) * ‖N‖ := by positivity
  refine (ContinuousMap.norm_le _ hC').2 fun t => ?_
  refine (pi_norm_le_iff_of_nonneg hC').2 fun i => (pi_norm_le_iff_of_nonneg hC').2 fun j => ?_
  refine (norm_volterra_pow_entry_le φ z n N t.2 i j).trans ?_
  have h1 : Real.exp (|z.im| * (t : ℝ)) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (mul_le_of_le_one_right (abs_nonneg _) t.2.2)
  have h2 : potPrim38 φ t ^ n ≤ potL1Norm38 φ ^ n :=
    pow_le_pow_left₀ (potPrim38_nonneg φ t.2.1) (potPrim38_le_one φ t.2) n
  have hf : (0 : ℝ) < n.factorial := by positivity
  have h3 : potPrim38 φ t ^ n / n.factorial ≤ potL1Norm38 φ ^ n / n.factorial :=
    div_le_div_of_nonneg_right h2 hf.le
  have h4 : 0 ≤ potPrim38 φ t ^ n / n.factorial := by
    have := potPrim38_nonneg φ t.2.1; positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h3 h4 (Real.exp_nonneg _)) (norm_nonneg _)

/-- Some power of the Volterra operator is a strict contraction. -/
theorem exists_norm_volterraP_pow_lt_one (φ : PotPair) (z : ℂ) :
    ∃ n : ℕ, ‖volterraP φ z ^ n‖ < 1 := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (potL1Norm38 φ)).const_mul
    (Real.exp |z.im|)
  rw [mul_zero] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
  exact ⟨n, (norm_volterraP_pow_le φ z n).trans_lt hn⟩

/-- Neumann series step: `1 - 𝒱` is invertible (via `1 - 𝒱ⁿ = (1 - 𝒱)(1 + 𝒱 + ⋯ + 𝒱ⁿ⁻¹)`). -/
theorem isUnit_one_sub_volterraP (φ : PotPair) (z : ℂ) : IsUnit (1 - volterraP φ z) := by
  obtain ⟨n, hn⟩ := exists_norm_volterraP_pow_lt_one φ z
  have h1 : IsUnit (1 - volterraP φ z ^ n) := ⟨Units.oneSub (volterraP φ z ^ n) hn, Units.val_oneSub (volterraP φ z ^ n) hn⟩
  have h2 : (1 - volterraP φ z) * ∑ i ∈ Finset.range n, volterraP φ z ^ i =
      1 - volterraP φ z ^ n := mul_neg_geom_sum (R := PairCont38 →L[ℂ] PairCont38) _ _
  rw [← h2] at h1
  have hc : Commute (1 - volterraP φ z) (∑ i ∈ Finset.range n, volterraP φ z ^ i) :=
    Commute.sum_right _ _ _ fun i _ =>
      Commute.sub_left (R := PairCont38 →L[ℂ] PairCont38) (Commute.one_left _)
        (Commute.self_pow _ _)
  exact ((Commute.isUnit_mul_iff hc).mp h1).1

end

end NlsGge.GK38
