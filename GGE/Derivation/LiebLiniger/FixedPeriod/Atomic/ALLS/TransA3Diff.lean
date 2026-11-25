import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA3Kernel

/-! # Track A, step A3: difference-norm characterization of `h^{r+σ}` over the base `h^r`

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.

For a real base exponent `r` and `0 < σ < 1`, the (squared) rotation-difference seminorm of
`x ∈ h^r` is the extended nonnegative real

  `diffSemi r σ x = ∫⁻ θ in (0, π], ‖S_θ x - x‖²_{h^r} θ^{-1-2σ} dθ`

(`S_θ = rotC38 r θ`, `(S_θ x)_n = e^{inθ} x_n`).  Main results:

* `diffSemi_eq_tsum` (Parseval + Tonelli): `diffSemi r σ x = Σ_n ⟨n⟩^{2r} |x_n|² · diffKernel σ n`;
* `diffSemi_incl_le`: for `x ∈ h^{r+σ}`, `diffSemi r σ x ≤ kernelUp σ · ‖x‖²_{h^{r+σ}}`;
* `mem_of_diffSemi_ne_top`, `norm_sq_le_of_diffSemi`: if `y ∈ h^r` has finite seminorm then
  `y ∈ h^{r+σ}` and `‖y‖²_{h^{r+σ}} ≤ ‖y‖²_{h^r} + kernelLow σ⁻¹ · diffSemi r σ y`
  (zero mode controlled by the base norm);
* `norm_rot_sub_sq_le`: the small-angle bound `‖S_θ x - x‖²_{h^r} ≤ 4 θ^{2σ} ‖x‖²_{h^{r+σ}}`.

Pro report "Difference norms" (with `θ = 2πa`, one-sided integral); translation audit §3. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ENNReal

namespace NlsGge.ALLS.TransA

/-- The squared rotation-difference seminorm over the base `h^r`. -/
def diffSemi (r σ : ℝ) (x : SobolevCarrier38 r) : ℝ≥0∞ :=
  ∫⁻ θ in Ioc 0 Real.pi, ENNReal.ofReal (‖rotC38 r θ x - x‖ ^ 2 * θ ^ (-1 - 2 * σ))

theorem carrierCoe38_sub_apply (r : ℝ) (x y : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (x - y) n = carrierCoe38 r x n - carrierCoe38 r y n := rfl

/-- Parseval for the rotation difference. -/
theorem hasSum_norm_rot_sub_sq (r θ : ℝ) (x : SobolevCarrier38 r) :
    HasSum (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2 *
      ‖rotPhase38 θ n - 1‖ ^ 2) (‖rotC38 r θ x - x‖ ^ 2) := by
  have h := carrier_hasSum_norm_sq38 r (rotC38 r θ x - x)
  convert h using 2 with n
  rw [carrierCoe38_sub_apply, rotC38_coe, rotSeq38_apply,
    show rotPhase38 θ n * carrierCoe38 r x n - carrierCoe38 r x n =
      (rotPhase38 θ n - 1) * carrierCoe38 r x n by ring, norm_mul, mul_pow]
  ring

theorem measurable_kernel_integrand (σ : ℝ) (n : ℤ) :
    Measurable fun θ : ℝ => ENNReal.ofReal (‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ (-1 - 2 * σ)) := by
  have hc : Continuous fun θ : ℝ => ‖rotPhase38 θ n - 1‖ ^ 2 := by
    unfold rotPhase38; fun_prop
  exact (hc.measurable.mul (measurable_id.pow_const _)).ennreal_ofReal

/-- **Parseval + Tonelli**: `diffSemi r σ x = Σ_n ⟨n⟩^{2r}|x_n|² · diffKernel σ n`. -/
theorem diffSemi_eq_tsum (r σ : ℝ) (x : SobolevCarrier38 r) :
    diffSemi r σ x = ∑' n : ℤ,
      ENNReal.ofReal (sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2) * diffKernel σ n := by
  unfold diffSemi
  have hpt : ∀ θ ∈ Ioc (0 : ℝ) Real.pi,
      ENNReal.ofReal (‖rotC38 r θ x - x‖ ^ 2 * θ ^ (-1 - 2 * σ)) =
        ∑' n : ℤ, ENNReal.ofReal (sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2) *
          ENNReal.ofReal (‖rotPhase38 θ n - 1‖ ^ 2 * θ ^ (-1 - 2 * σ)) := by
    intro θ hθ
    have hθ0 : 0 ≤ θ ^ (-1 - 2 * σ) := Real.rpow_nonneg hθ.1.le _
    have hs := (hasSum_norm_rot_sub_sq r θ x).mul_right (θ ^ (-1 - 2 * σ))
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (mul_nonneg (mul_nonneg
      (sobolevModeWeight_pos r n).le (sq_nonneg _)) (sq_nonneg _)) hθ0) hs.summable]
    congr 1
    funext n
    rw [← ENNReal.ofReal_mul (mul_nonneg (sobolevModeWeight_pos r n).le (sq_nonneg _))]
    congr 1
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioc hpt, lintegral_tsum]
  · congr 1
    funext n
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  · intro n
    exact ((measurable_kernel_integrand σ n).const_mul _).aemeasurable

/-! ### Weight comparisons -/

theorem sobolevModeWeight_add (r σ : ℝ) (n : ℤ) :
    sobolevModeWeight (r + σ) n = sobolevModeWeight r n * sobolevModeWeight σ n := by
  unfold sobolevModeWeight
  rw [show 2 * (r + σ) = 2 * r + 2 * σ by ring]
  exact Real.rpow_add (japaneseBracket_pos n) _ _

theorem abs_le_japaneseBracket (n : ℤ) : |(n : ℝ)| ≤ japaneseBracket n := by
  unfold japaneseBracket
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- `|n|^{2σ} ≤ ⟨n⟩^{2σ}`. -/
theorem abs_rpow_le_weight {σ : ℝ} (hσ : 0 ≤ σ) (n : ℤ) :
    |(n : ℝ)| ^ (2 * σ) ≤ sobolevModeWeight σ n := by
  unfold sobolevModeWeight
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_le_japaneseBracket n) (by linarith)

/-- `⟨n⟩^{2σ} ≤ 1 + |n|^{2σ}` for `0 ≤ σ ≤ 1`. -/
theorem weight_le_one_add {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (n : ℤ) :
    sobolevModeWeight σ n ≤ 1 + |(n : ℝ)| ^ (2 * σ) := by
  have e : sobolevModeWeight σ n = (1 + (n : ℝ) ^ 2) ^ σ := by
    unfold sobolevModeWeight japaneseBracket
    show Real.sqrt (1 + (n : ℝ) ^ 2) ^ (2 * σ) = _
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    ring_nf
  have e2 : |(n : ℝ)| ^ (2 * σ) = ((n : ℝ) ^ 2) ^ σ := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  rw [e, e2]
  have h := NNReal.rpow_add_le_add_rpow (1 : NNReal) (Real.toNNReal ((n : ℝ) ^ 2)) hσ0 hσ1
  rw [NNReal.one_rpow] at h
  have h' := NNReal.coe_le_coe.2 h
  rw [NNReal.coe_rpow, NNReal.coe_add, NNReal.coe_add, NNReal.coe_rpow, NNReal.coe_one,
    Real.coe_toNNReal _ (sq_nonneg _)] at h'
  exact h'

/-! ### The two inequalities of the characterization -/

/-- **Upper half**: for `x ∈ h^{r+σ}`, `diffSemi r σ x ≤ kernelUp σ ‖x‖²_{h^{r+σ}}`. -/
theorem diffSemi_incl_le {r σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (x : SobolevCarrier38 (r + σ)) :
    diffSemi r σ (carrierIncl38 (by linarith : r ≤ r + σ) x) ≤
      ENNReal.ofReal (kernelUp σ * ‖x‖ ^ 2) := by
  rw [diffSemi_eq_tsum]
  have hx := carrier_hasSum_norm_sq38 (r + σ) x
  have hs := hx.mul_left (kernelUp σ)
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (kernelUp_pos hσ0 hσ1).le
    (mul_nonneg (sobolevModeWeight_pos _ n).le (sq_nonneg _))) hs.summable]
  refine ENNReal.tsum_le_tsum fun n => ?_
  rw [carrierCoe38_incl38]
  calc ENNReal.ofReal (sobolevModeWeight r n * ‖carrierCoe38 (r + σ) x n‖ ^ 2) * diffKernel σ n
      ≤ ENNReal.ofReal (sobolevModeWeight r n * ‖carrierCoe38 (r + σ) x n‖ ^ 2) *
          ENNReal.ofReal (kernelUp σ * |(n : ℝ)| ^ (2 * σ)) := by
        gcongr; exact diffKernel_le hσ0 hσ1 n
    _ = ENNReal.ofReal (kernelUp σ * (sobolevModeWeight r n * |(n : ℝ)| ^ (2 * σ) *
          ‖carrierCoe38 (r + σ) x n‖ ^ 2)) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (sobolevModeWeight_pos _ n).le (sq_nonneg _))]
        congr 1; ring
    _ ≤ ENNReal.ofReal (kernelUp σ * (sobolevModeWeight (r + σ) n *
          ‖carrierCoe38 (r + σ) x n‖ ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        have hk := (kernelUp_pos hσ0 hσ1).le
        rw [sobolevModeWeight_add]
        have := abs_rpow_le_weight hσ0.le n
        have hw := (sobolevModeWeight_pos r n).le
        gcongr

/-- Termwise lower comparison used for the lower half. -/
theorem term_le_of_kernel {r σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (y : ℤ → ℂ) (n : ℤ) :
    ENNReal.ofReal (sobolevModeWeight (r + σ) n * ‖y n‖ ^ 2) ≤
      ENNReal.ofReal (sobolevModeWeight r n * ‖y n‖ ^ 2) +
        ENNReal.ofReal (kernelLow σ)⁻¹ *
          (ENNReal.ofReal (sobolevModeWeight r n * ‖y n‖ ^ 2) * diffKernel σ n) := by
  have hw := (sobolevModeWeight_pos r n).le
  have hy := sq_nonneg ‖y n‖
  have hsplit : sobolevModeWeight (r + σ) n * ‖y n‖ ^ 2 ≤
      sobolevModeWeight r n * ‖y n‖ ^ 2 + sobolevModeWeight r n * ‖y n‖ ^ 2 * |(n : ℝ)| ^ (2 * σ) := by
    rw [sobolevModeWeight_add]
    have := weight_le_one_add hσ0.le hσ1.le n
    nlinarith [mul_nonneg hw hy]
  calc ENNReal.ofReal (sobolevModeWeight (r + σ) n * ‖y n‖ ^ 2)
      ≤ ENNReal.ofReal (sobolevModeWeight r n * ‖y n‖ ^ 2) +
          ENNReal.ofReal (sobolevModeWeight r n * ‖y n‖ ^ 2 * |(n : ℝ)| ^ (2 * σ)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal hsplit
    _ ≤ _ := by
        gcongr
        rcases eq_or_ne n 0 with rfl | hn
        · simp [Real.zero_rpow (by linarith : 2 * σ ≠ 0)]
        have hk := le_diffKernel hσ0 hn
        have hkl := kernelLow_pos σ
        rw [ENNReal.ofReal_mul (by positivity)]
        calc ENNReal.ofReal (sobolevModeWeight r n * ‖y n‖ ^ 2) *
              ENNReal.ofReal (|(n : ℝ)| ^ (2 * σ))
            = ENNReal.ofReal (kernelLow σ)⁻¹ * (ENNReal.ofReal (sobolevModeWeight r n * ‖y n‖ ^ 2) *
                ENNReal.ofReal (kernelLow σ * |(n : ℝ)| ^ (2 * σ))) := by
              rw [show ENNReal.ofReal (kernelLow σ)⁻¹ *
                  (ENNReal.ofReal (sobolevModeWeight r n * ‖y n‖ ^ 2) *
                    ENNReal.ofReal (kernelLow σ * |(n : ℝ)| ^ (2 * σ))) =
                  ENNReal.ofReal (sobolevModeWeight r n * ‖y n‖ ^ 2) *
                    ENNReal.ofReal ((kernelLow σ)⁻¹ * (kernelLow σ * |(n : ℝ)| ^ (2 * σ))) by
                  rw [ENNReal.ofReal_mul (inv_nonneg.2 hkl.le)]; ring]
              rw [← mul_assoc, inv_mul_cancel₀ hkl.ne', one_mul]
          _ ≤ _ := by gcongr

/-- The lower half as a statement about sums. -/
theorem tsum_weight_le {r σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (y : SobolevCarrier38 r) :
    ∑' n : ℤ, ENNReal.ofReal (sobolevModeWeight (r + σ) n * ‖carrierCoe38 r y n‖ ^ 2) ≤
      ENNReal.ofReal (‖y‖ ^ 2) + ENNReal.ofReal (kernelLow σ)⁻¹ * diffSemi r σ y := by
  have hy := carrier_hasSum_norm_sq38 r y
  rw [diffSemi_eq_tsum, ← hy.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (sobolevModeWeight_pos _ n).le (sq_nonneg _)) hy.summable,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun n => term_le_of_kernel hσ0 hσ1 _ n

/-- **Lower half, membership**: finite seminorm over `h^r` gives membership in `h^{r+σ}`. -/
theorem mem_of_diffSemi_ne_top {r σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (y : SobolevCarrier38 r)
    (hfin : diffSemi r σ y ≠ ⊤) : carrierCoe38 r y ∈ seqSobolev38 (r + σ) := by
  have hle := tsum_weight_le hσ0 hσ1 y
  have hne : ∑' n : ℤ, ENNReal.ofReal (sobolevModeWeight (r + σ) n * ‖carrierCoe38 r y n‖ ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top (by simp) hfin⟩) hle
  have hs := ENNReal.summable_toReal hne
  rw [mem_seqSobolev38_iff]
  refine hs.congr fun n => ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (sobolevModeWeight_pos _ n).le (sq_nonneg _))]
  rfl

/-- **Lower half, norm bound**: `‖y‖²_{h^{r+σ}} ≤ ‖y‖²_{h^r} + kernelLow σ⁻¹ · diffSemi r σ y`. -/
theorem norm_sq_le_of_diffSemi {r σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (y : SobolevCarrier38 r)
    (hy : carrierCoe38 r y ∈ seqSobolev38 (r + σ)) :
    ENNReal.ofReal (‖carrierMk38 (r + σ) (carrierCoe38 r y) hy‖ ^ 2) ≤
      ENNReal.ofReal (‖y‖ ^ 2) + ENNReal.ofReal (kernelLow σ)⁻¹ * diffSemi r σ y := by
  have h := carrier_hasSum_norm_sq38 (r + σ) (carrierMk38 (r + σ) (carrierCoe38 r y) hy)
  have hc : carrierCoe38 (r + σ) (carrierMk38 (r + σ) (carrierCoe38 r y) hy) = carrierCoe38 r y :=
    carrierCoe38_mk _ _ _
  have h2 : HasSum (fun n : ℤ => sobolevModeWeight (r + σ) n * ‖carrierCoe38 r y n‖ ^ 2)
      (‖carrierMk38 (r + σ) (carrierCoe38 r y) hy‖ ^ 2) := by
    rw [hc] at h; exact h
  have e : ENNReal.ofReal (‖carrierMk38 (r + σ) (carrierCoe38 r y) hy‖ ^ 2) =
      ∑' n : ℤ, ENNReal.ofReal (sobolevModeWeight (r + σ) n * ‖carrierCoe38 r y n‖ ^ 2) := by
    rw [← h2.tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (sobolevModeWeight_pos _ n).le (sq_nonneg _)) h2.summable
  exact e.le.trans (tsum_weight_le hσ0 hσ1 y)

/-! ### Small-angle bound -/

/-- `‖e^{inθ} - 1‖² ≤ 4 θ^{2σ} |n|^{2σ}` for `θ ≥ 0`, `0 ≤ σ ≤ 1`. -/
theorem norm_rotPhase38_sub_one_sq_le_rpow {σ θ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hθ : 0 ≤ θ)
    (n : ℤ) : ‖rotPhase38 θ n - 1‖ ^ 2 ≤ 4 * θ ^ (2 * σ) * |(n : ℝ)| ^ (2 * σ) := by
  set t : ℝ := ‖rotPhase38 θ n - 1‖ ^ 2 with ht
  have ht0 : 0 ≤ t := sq_nonneg _
  have ht4 : t ≤ 4 := by
    have := norm_rotPhase38_sub_one_le_two θ n
    rw [ht]; nlinarith [norm_nonneg (rotPhase38 θ n - 1)]
  have htn : t ≤ (|(n : ℝ)| * θ) ^ 2 := by
    have := norm_rotPhase38_sub_one_le θ n
    rw [abs_of_nonneg hθ] at this
    rw [ht]; exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hsplit : t = t ^ (1 - σ) * t ^ σ := by
    rw [← Real.rpow_add' ht0 (by norm_num), sub_add_cancel, Real.rpow_one]
  have h1 : t ^ (1 - σ) ≤ 4 := by
    calc t ^ (1 - σ) ≤ 4 ^ (1 - σ) := Real.rpow_le_rpow ht0 ht4 (by linarith)
      _ ≤ 4 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one 4
  have h2 : t ^ σ ≤ θ ^ (2 * σ) * |(n : ℝ)| ^ (2 * σ) := by
    calc t ^ σ ≤ ((|(n : ℝ)| * θ) ^ 2) ^ σ := Real.rpow_le_rpow ht0 htn hσ0
      _ = θ ^ (2 * σ) * |(n : ℝ)| ^ (2 * σ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (abs_nonneg _) hθ]
        push_cast; ring_nf
  have h20 : 0 ≤ t ^ σ := Real.rpow_nonneg ht0 _
  rw [hsplit]
  calc t ^ (1 - σ) * t ^ σ ≤ 4 * t ^ σ := by gcongr
    _ ≤ 4 * (θ ^ (2 * σ) * |(n : ℝ)| ^ (2 * σ)) := by gcongr
    _ = _ := by ring

/-- **Small-angle bound**: `‖S_θ x - x‖²_{h^r} ≤ 4 θ^{2σ} ‖x‖²_{h^{r+σ}}` for `θ ≥ 0`. -/
theorem norm_rot_sub_sq_le {r σ θ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hθ : 0 ≤ θ)
    (x : SobolevCarrier38 (r + σ)) :
    ‖rotC38 r θ (carrierIncl38 (by linarith : r ≤ r + σ) x) -
        carrierIncl38 (by linarith : r ≤ r + σ) x‖ ^ 2 ≤ 4 * θ ^ (2 * σ) * ‖x‖ ^ 2 := by
  have h1 := hasSum_norm_rot_sub_sq r θ (carrierIncl38 (by linarith : r ≤ r + σ) x)
  have h2 := (carrier_hasSum_norm_sq38 (r + σ) x).mul_left (4 * θ ^ (2 * σ))
  refine hasSum_le (fun n => ?_) h1 h2
  rw [carrierCoe38_incl38, sobolevModeWeight_add]
  have hw := (sobolevModeWeight_pos r n).le
  have hk := norm_rotPhase38_sub_one_sq_le_rpow hσ0.le hσ1.le hθ n
  have ha := abs_rpow_le_weight hσ0.le n
  have hθp : 0 ≤ θ ^ (2 * σ) := Real.rpow_nonneg hθ _
  have hx := sq_nonneg ‖carrierCoe38 (r + σ) x n‖
  calc sobolevModeWeight r n * ‖carrierCoe38 (r + σ) x n‖ ^ 2 * ‖rotPhase38 θ n - 1‖ ^ 2
      ≤ sobolevModeWeight r n * ‖carrierCoe38 (r + σ) x n‖ ^ 2 *
          (4 * θ ^ (2 * σ) * |(n : ℝ)| ^ (2 * σ)) := by gcongr
    _ ≤ sobolevModeWeight r n * ‖carrierCoe38 (r + σ) x n‖ ^ 2 *
          (4 * θ ^ (2 * σ) * sobolevModeWeight σ n) := by gcongr
    _ = 4 * θ ^ (2 * σ) * (sobolevModeWeight r n * sobolevModeWeight σ n *
          ‖carrierCoe38 (r + σ) x n‖ ^ 2) := by ring

end NlsGge.ALLS.TransA
