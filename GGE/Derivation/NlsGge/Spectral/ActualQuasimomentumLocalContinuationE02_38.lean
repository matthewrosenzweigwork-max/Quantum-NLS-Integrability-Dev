import NlsGge.Spectral.ActualQuasimomentumE02_38
import NlsGge.Spectral.ActualQuasimomentumFullInfinityE02_38
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # E02.38: local analytic continuation of the actual quasimomentum across the real axis
at a point where `Δh² ≠ 1`.

Local analytic logarithm, square root, then `K₀ = -i log (Δh + √(Δh² - 1))`; the sign and the
integer ambiguity are fixed on the connected upper half-ball. -/

/-- A nonvanishing analytic function has an analytic logarithm on a small ball. -/
theorem exists_local_analytic_log_E02_38 (f : ℂ → ℂ) (c : ℂ) (hf : AnalyticAt ℂ f c)
    (h0 : f c ≠ 0) :
    ∃ r > 0, ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (Metric.ball c r) ∧
      ∀ z ∈ Metric.ball c r, Complex.exp (L z) = f z := by
  have hcont : ContinuousAt (fun z => ‖f z / f c - 1‖) c :=
    ((hf.continuousAt.div_const _).sub continuousAt_const).norm
  have h1 : ‖f c / f c - 1‖ < 1 := by simp [h0]
  have hev : ∀ᶠ z in 𝓝 c, ‖f z / f c - 1‖ < 1 :=
    hcont.eventually_lt continuousAt_const h1
  have hev2 := hev.and hf.eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev2
  have hslit : ∀ z ∈ Metric.ball c r, f z / f c ∈ Complex.slitPlane := by
    intro z hz
    have := Complex.mem_slitPlane_of_norm_lt_one (hball z hz).1
    simpa using this
  refine ⟨r, hr, fun z => Complex.log (f c) + Complex.log (f z / f c), ?_, ?_⟩
  · intro z hz
    have hfz : AnalyticAt ℂ f z := (hball z hz).2
    have h2 : AnalyticAt ℂ (fun w => f w / f c) z := hfz.div analyticAt_const (by simp [h0])
    exact analyticAt_const.add (h2.clog (hslit z hz))
  · intro z hz
    have hne : f z / f c ≠ 0 := Complex.slitPlane_ne_zero (hslit z hz)
    have hfz : f z ≠ 0 := by
      intro h; apply hne; rw [h]; simp
    rw [Complex.exp_add, Complex.exp_log h0, Complex.exp_log hne]
    field_simp

/-- A nonvanishing analytic function has an analytic square root on a small ball. -/
theorem exists_local_analytic_sqrt_E02_38 (f : ℂ → ℂ) (c : ℂ) (hf : AnalyticAt ℂ f c)
    (h0 : f c ≠ 0) :
    ∃ r > 0, ∃ S : ℂ → ℂ, AnalyticOnNhd ℂ S (Metric.ball c r) ∧
      ∀ z ∈ Metric.ball c r, S z ^ 2 = f z ∧ S z ≠ 0 := by
  obtain ⟨r, hr, L, hL, hE⟩ := exists_local_analytic_log_E02_38 f c hf h0
  refine ⟨r, hr, fun z => Complex.exp (L z / 2), ?_, ?_⟩
  · intro z hz
    exact ((hL z hz).div analyticAt_const (by norm_num)).cexp
  · intro z hz
    refine ⟨?_, Complex.exp_ne_zero _⟩
    rw [← Complex.exp_nat_mul, ← hE z hz]
    congr 1
    push_cast
    ring

/-- Local analytic branch of the solution of `cos K = Δ` where `Δ² ≠ 1`:
an analytic `K₀` on a ball with `exp(i K₀) = W`, `W (2Δ - W) = 1`, `W ≠ 2Δ - W`. -/
theorem exists_local_cos_inverse_E02_38 (Δ : ℂ → ℂ) (hΔ : AnalyticOnNhd ℂ Δ univ) (c : ℂ)
    (h : Δ c ^ 2 ≠ 1) :
    ∃ r > 0, ∃ W K₀ : ℂ → ℂ, AnalyticOnNhd ℂ W (Metric.ball c r) ∧
      AnalyticOnNhd ℂ K₀ (Metric.ball c r) ∧
      (∀ z ∈ Metric.ball c r, W z * (2 * Δ z - W z) = 1) ∧
      (∀ z ∈ Metric.ball c r, W z ≠ 2 * Δ z - W z) ∧
      (∀ z ∈ Metric.ball c r, Complex.exp (Complex.I * K₀ z) = W z) := by
  have hD : AnalyticAt ℂ (fun z => Δ z ^ 2 - 1) c :=
    ((hΔ c (mem_univ _)).pow 2).sub analyticAt_const
  have hD0 : Δ c ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr h
  obtain ⟨r₁, hr₁, S, hS, hS2⟩ := exists_local_analytic_sqrt_E02_38 _ c hD hD0
  have hWan : AnalyticOnNhd ℂ (fun z => Δ z + S z) (Metric.ball c r₁) := by
    intro z hz
    exact (hΔ z (mem_univ _)).add (hS z hz)
  have hprod : ∀ z ∈ Metric.ball c r₁, (Δ z + S z) * (2 * Δ z - (Δ z + S z)) = 1 := by
    intro z hz
    have := (hS2 z hz).1
    linear_combination -this
  have hW0 : Δ c + S c ≠ 0 := by
    intro h0
    have := hprod c (Metric.mem_ball_self hr₁)
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  obtain ⟨r₂, hr₂, L, hL, hE⟩ := exists_local_analytic_log_E02_38 _ c
    (hWan c (Metric.mem_ball_self hr₁)) hW0
  have hsub : Metric.ball c (min r₁ r₂) ⊆ Metric.ball c r₁ := Metric.ball_subset_ball (min_le_left _ _)
  have hsub2 : Metric.ball c (min r₁ r₂) ⊆ Metric.ball c r₂ := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z => Δ z + S z, fun z => -Complex.I * L z,
    hWan.mono hsub, ?_, fun z hz => hprod z (hsub hz), ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.mul (hL z (hsub2 hz))
  · intro z hz heq
    have hS0 := (hS2 z (hsub hz)).2
    apply hS0
    linear_combination heq / 2
  · intro z hz
    have : Complex.I * (-Complex.I * L z) = L z := by
      rw [← mul_assoc, mul_neg, Complex.I_mul_I]; ring
    rw [this]
    exact hE z (hsub2 hz)

/-- Fixing the `2π`-ambiguity on the connected upper half-ball. -/
theorem local_continuation_of_exp_eq_E02_38 (c : ℂ) (r : ℝ) (k K₁ : ℂ → ℂ)
    (hk : ContinuousOn k {z : ℂ | 0 < z.im})
    (hK₁ : AnalyticOnNhd ℂ K₁ (Metric.ball c r))
    (hexp : ∀ z ∈ Metric.ball c r, 0 < z.im → Complex.exp (k z * Complex.I) =
      Complex.exp (K₁ z * Complex.I)) :
    ∃ K : ℂ → ℂ, AnalyticOnNhd ℂ K (Metric.ball c r) ∧
      ∀ z ∈ Metric.ball c r, 0 < z.im → K z = k z := by
  set U : Set ℂ := Metric.ball c r ∩ {z : ℂ | 0 < z.im} with hU
  have hUc : IsPreconnected U := by
    have : Convex ℝ U := by
      refine (convex_ball c r).inter ?_
      exact convex_halfSpace_im_gt 0
    exact this.isPreconnected
  have hkU : ContinuousOn k U := hk.mono inter_subset_right
  have hKU : ContinuousOn K₁ U := hK₁.continuousOn.mono inter_subset_left
  obtain ⟨m, hm⟩ := complexLogarithm_integer_constant_preconnected_E02_38 U hUc
    (fun z => (k z - K₁ z) * Complex.I)
    ((hkU.sub hKU).mul continuousOn_const)
    (by
      intro z hz
      rw [sub_mul, Complex.exp_sub, hexp z hz.1 hz.2]
      exact div_self (Complex.exp_ne_zero _))
  refine ⟨fun z => K₁ z + (m:ℂ) * (2 * Real.pi), ?_, ?_⟩
  · intro z hz
    exact (hK₁ z hz).add analyticAt_const
  · intro z hz hzi
    have h := hm z ⟨hz, hzi⟩
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h2 : k z - K₁ z = (m:ℂ) * (2 * Real.pi) := by
      apply mul_right_cancel₀ hI
      rw [h]; ring
    show K₁ z + (m:ℂ) * (2 * Real.pi) = k z
    rw [← h2]; ring

theorem exists_analytic_continuation_actualQuasimomentum_E02_38 (u : PhysicalL2) (x₀ : ℝ)
    (h : actualPhysicalUnitHalfTrace32 u x₀ ^ 2 ≠ 1) :
    ∃ r > 0, ∃ K : ℂ → ℂ, AnalyticOnNhd ℂ K (Metric.ball (x₀:ℂ) r) ∧
      ∀ z ∈ Metric.ball (x₀:ℂ) r, 0 < z.im → K z = actualQuasimomentumE02_38 u z := by
  set Δ := actualPhysicalUnitHalfTrace32 u with hΔdef
  set k := actualQuasimomentumE02_38 u with hkdef
  obtain ⟨hkan, hcos, him, -⟩ := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  obtain ⟨r, hr, W, K₀, hW, hK₀, hprod, hne, hexp⟩ :=
    exists_local_cos_inverse_E02_38 Δ (analyticOnNhd_actualPhysicalUnitHalfTrace32 u) (x₀:ℂ) h
  refine ⟨r, hr, ?_⟩
  set B : Set ℂ := Metric.ball (x₀:ℂ) r with hB
  set U : Set ℂ := B ∩ {z : ℂ | 0 < z.im} with hU
  have hUc : IsPreconnected U := by
    have : Convex ℝ U := (convex_ball _ r).inter (convex_halfSpace_im_gt 0)
    exact this.isPreconnected
  -- exp (i k) is one of the two roots
  have hroot : ∀ z ∈ U, Complex.exp (k z * Complex.I) = W z ∨
      Complex.exp (k z * Complex.I) = 2 * Δ z - W z := by
    intro z hz
    have hc : Complex.cos (k z) = Δ z := hcos z hz.2
    have hV : Complex.exp (k z * Complex.I) * Complex.exp (-k z * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    have h2 : 2 * Δ z = Complex.exp (k z * Complex.I) + Complex.exp (-k z * Complex.I) := by
      rw [← hc, Complex.cos]; ring
    have hp := hprod z hz.1
    have : (Complex.exp (k z * Complex.I) - W z) *
        (Complex.exp (k z * Complex.I) - (2 * Δ z - W z)) = 0 := by
      linear_combination hp - hV + (-(Complex.exp (k z * Complex.I))) * h2
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (sub_eq_zero.mp h1)
  have hnorm : ∀ z ∈ U, ‖Complex.exp (k z * Complex.I)‖ < 1 := by
    intro z hz
    rw [Complex.norm_exp]
    have := him z hz.2
    have : (k z * Complex.I).re = -(k z).im := by simp
    rw [this]
    exact Real.exp_lt_one_iff.mpr (by have := him z hz.2; linarith)
  have hWne : ∀ z ∈ B, W z ≠ 0 := by
    intro z hz h0
    have := hprod z hz
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  -- the two roots have reciprocal norms
  have hrecip : ∀ z ∈ B, ‖2 * Δ z - W z‖ * ‖W z‖ = 1 := by
    intro z hz
    rw [← norm_mul, mul_comm, hprod z hz]; simp
  have hWc : ContinuousOn (fun z => ‖W z‖) B := hW.continuousOn.norm
  set u₁ : Set ℂ := B ∩ (fun z => ‖W z‖) ⁻¹' Set.Iio 1 with hu₁
  set v₁ : Set ℂ := B ∩ (fun z => ‖W z‖) ⁻¹' Set.Ioi 1 with hv₁
  have hu₁o : IsOpen u₁ := hWc.isOpen_inter_preimage Metric.isOpen_ball isOpen_Iio
  have hv₁o : IsOpen v₁ := hWc.isOpen_inter_preimage Metric.isOpen_ball isOpen_Ioi
  have hdisj : Disjoint u₁ v₁ := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have a := hz1.2
    have b := hz2.2
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi] at a b
    linarith
  have hcover : U ⊆ u₁ ∪ v₁ := by
    intro z hz
    have hn := hnorm z hz
    have hr1 := hrecip z hz.1
    rcases lt_trichotomy ‖W z‖ 1 with h1 | h1 | h1
    · exact Or.inl ⟨hz.1, h1⟩
    · exfalso
      rcases hroot z hz with h2 | h2
      · rw [h2, h1] at hn; exact lt_irrefl _ hn
      · rw [h2] at hn
        rw [h1, mul_one] at hr1
        rw [hr1] at hn; exact lt_irrefl _ hn
    · exact Or.inr ⟨hz.1, h1⟩
  have hkc : ContinuousOn k {z : ℂ | 0 < z.im} := hkan.continuousOn
  rcases hUc.subset_or_subset hu₁o hv₁o hdisj hcover with hsub | hsub
  · obtain ⟨K, hK, hKe⟩ := local_continuation_of_exp_eq_E02_38 (x₀:ℂ) r k K₀ hkc hK₀ (by
      intro z hz hzi
      have hz' : z ∈ U := ⟨hz, hzi⟩
      have hlt := (hsub hz').2
      simp only [Set.mem_preimage, Set.mem_Iio] at hlt
      rw [mul_comm (K₀ z), hexp z hz]
      rcases hroot z hz' with h2 | h2
      · exact h2
      · exfalso
        have hr1 := hrecip z hz
        have := hnorm z hz'
        rw [h2] at this
        nlinarith [norm_nonneg (W z)])
    exact ⟨K, hK, hKe⟩
  · obtain ⟨K, hK, hKe⟩ := local_continuation_of_exp_eq_E02_38 (x₀:ℂ) r k (fun z => -K₀ z) hkc
      (fun z hz => (hK₀ z hz).neg) (by
      intro z hz hzi
      have hz' : z ∈ U := ⟨hz, hzi⟩
      have hgt := (hsub hz').2
      simp only [Set.mem_preimage, Set.mem_Ioi] at hgt
      have hWz := hWne z hz
      have hWi : 2 * Δ z - W z = (W z)⁻¹ := by
        exact eq_inv_of_mul_eq_one_right (hprod z hz)
      have hexp' : Complex.exp (-K₀ z * Complex.I) = (W z)⁻¹ := by
        rw [neg_mul, Complex.exp_neg, mul_comm, hexp z hz]
      rw [hexp']
      rcases hroot z hz' with h2 | h2
      · exfalso
        have := hnorm z hz'
        rw [h2] at this
        linarith
      · rw [h2, hWi])
    exact ⟨K, hK, hKe⟩

end NlsGge.SpectralFoundations
