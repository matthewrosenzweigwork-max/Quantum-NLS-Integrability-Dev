import QuantumNLS.LOCAL009R23DiagonalAnalytic
import QuantumNLS.Prop020Diag

/-! A closed spectral disk strictly inside the specified inverse domain.
The stronger margin is derived anew from the frozen quantitative estimates. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
noncomputable section
open Complex Set Metric
open scoped InnerProductSpace
namespace QuantumNLS.LOCAL009R23TransferSpectrum
open QuantumNLS.Ext025A7 QuantumNLS.LOCAL009R22Transfer
  QuantumNLS.LOCAL009R22Cauchy QuantumNLS.LOCAL009R22Inverse
  QuantumNLS.TransferProductCorrection QuantumNLS.LOCAL009R23DiagonalAnalytic

theorem transfer_strict_spectral_margin {κ L M d ε : ℝ}
    (hκ : 0 < κ) (hM : 0 < M) (hd : 0 < d)
    (hsmall : κ * M / d ≤ 1 / 10000)
    {N : ℕ} (hN : 0 < N) (hε : 0 ≤ ε) (hεM : ε ≤ M)
    (hbudget : ε * N ≤ M) (q : Fin N → ℝ) {z : ℂ}
    (hsep : ∀ j, d ≤ ‖z - (q j : ℂ)‖)
    (hexp : ‖Complex.exp (I * z * L)‖ ≤ 8)
    (hgap : 1 / 2 ≤ ‖1 - Complex.exp (I * z * L)‖) :
    ‖transferS (κ * ε) L q z - spectralMap κ L z 0‖ <
      7 / 10 * ‖spectralLinear κ L z‖ * (2 * M / d) := by
  let η := κ * M / d
  let R := 2 * M / d
  let G := sourceG ε q z
  let F := spectralMap κ L z G
  let D := ‖spectralLinear κ L z‖
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by dsimp [η]; linarith
  have hR : 0 < R := by dsimp [R]; positivity
  have hkr : κ * R ≤ 1 / 1000 := by
    calc
      κ * R = 2 * (κ * M / d) := by dsimp [R]; ring
      _ ≤ 1 / 1000 := by linarith
  have hG : ‖G‖ ≤ M/d := norm_sourceG_le hε hd hbudget q hsep
  have hGc : G ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff]
    calc
      ‖G‖ ≤ M/d := hG
      _ ≤ 2 * (M/d) := by linarith [div_pos hM hd]
      _ = R := by dsimp [R]; ring
  have hzero : (0 : ℂ) ∈ closedBall (0 : ℂ) R := by simp [hR.le]
  have hquarter : ∀ w ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤ D/4 :=
    fun w hw => local009_quarter_from_source hκ hkr hexp hgap hw
  have hderiv : ∀ w ∈ closedBall (0 : ℂ) R,
      ‖deriv (spectralMap κ L z) w‖ ≤ 5/4 * D := by
    intro w hw
    rw [(spectralMap_hasDerivAt κ L z w).deriv]
    have hn : ‖spectralDerivative κ L z w‖ ≤
        ‖spectralDerivative κ L z w - spectralLinear κ L z‖ + D := by
      simpa only [sub_add_cancel] using norm_add_le
        (spectralDerivative κ L z w - spectralLinear κ L z) (spectralLinear κ L z)
    linarith [hquarter w hw]
  have hfwd := (convex_closedBall (0 : ℂ) R).norm_image_sub_le_of_norm_deriv_le
    (fun w _ => (spectralMap_hasDerivAt κ L z w).differentiableAt)
    hderiv hzero hGc
  simp only [sub_zero] at hfwd
  have hforward : ‖F - spectralMap κ L z 0‖ ≤ 5/8 * D * R := by
    calc
      _ ≤ 5/4 * D * ‖G‖ := hfwd
      _ ≤ 5/4 * D * (M/d) := mul_le_mul_of_nonneg_left hG (by dsimp [D]; positivity)
      _ = _ := by dsimp [R]; ring
  have hE : Real.exp (1 / 10) ≤ 3 :=
    (Real.exp_le_exp.mpr (by norm_num : (1/10 : ℝ) ≤ 1)).trans Real.exp_one_lt_three.le
  have hEη : Real.exp (κ * (M/d)) ≤ 3 := by
    have heq : κ * (M/d) = η := by dsimp [η]; ring
    rw [heq]
    exact (Real.exp_le_exp.mpr hη1).trans Real.exp_one_lt_three.le
  have hF : ‖F‖ ≤ 27 := by
    have hnorm := spectralMap_norm_le hκ.le hG (by norm_num : (0 : ℝ) ≤ 8) hexp
    dsimp [F]
    nlinarith
  have hP : ‖deriv (sourceG ε q) z‖ ≤ M/d^2 := norm_deriv_sourceG_le hε hd hbudget q hsep
  have hp := transfer_second_order_separated hκ.le hM hd (by linarith) hN hε hbudget q hsep
    (by norm_num : (0 : ℝ) ≤ 8) hexp
  simp only [show (1+8 : ℝ) = 9 by norm_num] at hp
  have hη3 : η^3 ≤ η^2 := by
    nlinarith [mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hη1)]
  have hη4 : η^4 ≤ η^2 := by
    have hs : η^2 ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg η) (sub_nonneg.mpr hs)]
  have hC : transferConstant κ M d * ε^2 ≤ 54 * η^2 := by
    calc
      _ ≤ transferConstant κ M d * M^2 := by
        apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε hεM 2)
        unfold transferConstant
        positivity
      _ = Real.exp (1/10) * 9 * (η^4 + η^3) := by
        unfold transferConstant η
        ring
      _ ≤ 3 * 9 * (η^4 + η^3) := by gcongr
      _ ≤ 54 * η^2 := by nlinarith
  have hα : 0 ≤ κ^2 * ε / 2 := by positivity
  have hcorrection : ‖(κ^2 * ε / 2 : ℝ) * F * deriv (sourceG ε q) z‖ ≤
      27/2 * η^2 := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα]
    calc
      _ ≤ (κ^2 * M / 2) * 27 * (M/d^2) := by gcongr
      _ = _ := by dsimp [η]; ring
  have herror : ‖transferS (κ * ε) L q z - F‖ ≤ 100 * η^2 := by
    have hn := norm_sub_le
      (transferS (κ * ε) L q z - (F - (κ^2 * ε / 2 : ℝ) * F * deriv (sourceG ε q) z))
      ((κ^2 * ε / 2 : ℝ) * F * deriv (sourceG ε q) z)
    have heq : (transferS (κ * ε) L q z - (F -
        (κ^2 * ε / 2 : ℝ) * F * deriv (sourceG ε q) z)) -
        ((κ^2 * ε / 2 : ℝ) * F * deriv (sourceG ε q) z) =
        transferS (κ * ε) L q z - F := by ring
    rw [heq] at hn
    have hpp : ‖transferS (κ * ε) L q z - (F -
        (κ^2 * ε / 2 : ℝ) * F * deriv (sourceG ε q) z)‖ ≤
        transferConstant κ M d * ε^2 := hp
    nlinarith [sq_nonneg η]
  have hD : κ/2 ≤ D := by
    dsimp [D]
    rw [spectralLinear_norm, abs_of_pos hκ]
    nlinarith
  have hDR : η ≤ D * R := by
    calc
      η = (κ/2) * R := by dsimp [η, R]; ring
      _ ≤ D * R := mul_le_mul_of_nonneg_right hD hR.le
  have herrorSmall : 100 * η^2 < η/16 := by
    have hs : η ≤ 1/10000 := hsmall
    nlinarith [mul_le_mul_of_nonneg_left hs hη.le]
  have hn := norm_add_le (transferS (κ * ε) L q z - F) (F - spectralMap κ L z 0)
  rw [sub_add_sub_cancel] at hn
  change ‖transferS (κ * ε) L q z - spectralMap κ L z 0‖ < 7/10 * D * R
  nlinarith


variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Spectral control from all diagonals, including accumulation points. -/
theorem spectrum_disk (b : HilbertBasis ι ℂ H) (S : H →L[ℂ] H)
    (s : ι → ℂ) (he : ∀ i, S (b i) = s i • b i)
    {center : ℂ} {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ‖s i-center‖ ≤ B)
    {y : ℂ} (hy : y ∈ spectrum ℂ S) : ‖y-center‖ ≤ B := by
  have hn : ‖S - algebraMap ℂ (H →L[ℂ] H) center‖ ≤ B := by
    apply norm_le_of_eigen b _ (fun i => s i-center) _ hB hb
    intro i
    simp [Algebra.algebraMap_eq_smul_one, he, sub_smul]
  have hm : y-center ∈ spectrum ℂ (S-algebraMap ℂ (H →L[ℂ] H) center) := by
    rw [← spectrum.sub_singleton_eq]
    exact Set.sub_mem_sub hy (mem_singleton center)
  apply (spectrum.norm_le_norm_mul_of_mem hm).trans
  calc
    _ ≤ ‖S - algebraMap ℂ (H →L[ℂ] H) center‖ * 1 := by
      gcongr
      exact ContinuousLinearMap.norm_id_le
    _ ≤ B := by simpa using hn

/-- The actual CFC inverse, rather than a definition by desired diagonals. -/
theorem inverse_cfc_eigen (b : HilbertBasis ι ℂ H) (S : H →L[ℂ] H)
    (s : ι → ℂ) (he : ∀ i, S (b i) = s i • b i)
    {κ L R : ℝ} {U : Set ℂ} (hκ : 0 < κ) (hR : 0 < R)
    (hsmall : κ*R ≤ 1/1000) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (I*z*L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1/2 ≤ ‖1-Complex.exp (I*z*L)‖)
    {z : ℂ} (hz : z ∈ U)
    (hmargin : ∀ i, ‖s i-spectralMap κ L z 0‖ ≤
      7/10*‖spectralLinear κ L z‖*R) (i : ι) :
    cfc (spectralInverse κ L R z) S (b i) =
      spectralInverse κ L R z (s i) • b i := by
  have hnormal : IsStarNormal S := ⟨QuantumNLS.NormalityBridge.IsDiag.normal
    (fun i => ⟨s i,he i⟩ : QuantumNLS.NormalityBridge.IsDiag b S)⟩
  have hD : 0 < ‖spectralLinear κ L z‖ := by
    rw [spectralLinear_norm, abs_of_pos hκ]
    have := hgap z hz
    positivity
  have hc : ContinuousOn (spectralInverse κ L R z) (spectrum ℂ S) := by
    intro y hy
    have hb := spectrum_disk b S s he (by positivity : 0 ≤ 7/10*‖spectralLinear κ L z‖*R) hmargin hy
    have hm : ‖y-spectralMap κ L z 0‖ < 3/4*‖spectralLinear κ L z‖*R := by
      nlinarith [mul_pos hD hR]
    have ha := (local009_application κ L hκ hR hsmall hU hexp hgap hz hm).2.2.2.1
    exact (ha.comp (analyticAt_const.prod analyticAt_id)).continuousAt.continuousWithinAt
  exact QuantumNLS.Prop020Diag.cfc_eigen hnormal (he i) (b.orthonormal.ne_zero i) _ hc

end QuantumNLS.LOCAL009R23TransferSpectrum
