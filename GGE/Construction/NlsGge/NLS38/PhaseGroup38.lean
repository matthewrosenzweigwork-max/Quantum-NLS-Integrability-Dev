import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.NLS38.SeqConv38

/-! # A3: the dispersive phase group on the Sobolev carriers (GWP plan, §7 Part A)

`(phase t x)_n = e^{-i t (2π n)²} x_n` is a strongly continuous unitary group on every `h^r`
(`SobolevCarrier38 r`), jointly continuous in `(t, x)`, and for `y ∈ h^{r+2}` the curve
`t ↦ phase t y ∈ h^r` is differentiable with derivative `-iΛ phase t y` (`lam`).
Everything is B-free. The only external input is the Sobolev plumbing of `BirkhoffAPI38`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open Filter Topology

/-- `disp` is A0's `NlsGge.NLS38.disp` (`SeqConv38a`); only its sign is needed here. -/
theorem disp_nonneg_phase (n : ℤ) : 0 ≤ disp n := sq_nonneg _

/-- The dispersive phase factor. -/
def phase (t : ℝ) (x : ℤ → ℂ) : ℤ → ℂ :=
  fun n => Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) * x n

theorem norm_phaseFactor (a : ℝ) : ‖Complex.exp (-(Complex.I * (a : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_phase_apply (t : ℝ) (x : ℤ → ℂ) (n : ℤ) : ‖phase t x n‖ = ‖x n‖ := by
  unfold phase
  rw [norm_mul, norm_phaseFactor, one_mul]

theorem phase_zero_apply (x : ℤ → ℂ) : phase 0 x = x := by
  funext n; simp [phase]

theorem phase_add_apply (s t : ℝ) (x : ℤ → ℂ) : phase (s + t) x = phase s (phase t x) := by
  funext n
  simp only [phase]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem phase_neg_phase_apply (t : ℝ) (x : ℤ → ℂ) : phase (-t) (phase t x) = x := by
  rw [← phase_add_apply, neg_add_cancel, phase_zero_apply]

theorem phase_phase_neg_apply (t : ℝ) (x : ℤ → ℂ) : phase t (phase (-t) x) = x := by
  rw [← phase_add_apply, add_neg_cancel, phase_zero_apply]

theorem phase_zero : phase 0 = id := funext phase_zero_apply

/-- Group law: `phase (s + t) = phase s ∘ phase t`. -/
theorem phase_add (s t : ℝ) : phase (s + t) = phase s ∘ phase t :=
  funext (phase_add_apply s t)

theorem phase_neg_phase (t : ℝ) : phase (-t) ∘ phase t = id := funext (phase_neg_phase_apply t)

theorem phase_phase_neg (t : ℝ) : phase t ∘ phase (-t) = id := funext (phase_phase_neg_apply t)

/-- The zero mode is not rotated. -/
theorem phase_apply_zero (t : ℝ) (x : ℤ → ℂ) : phase t x 0 = x 0 := by
  simp [phase, disp]

/-- Modes `n` and `-n` rotate with the same phase. -/
theorem phase_neg_index (t : ℝ) (x : ℤ → ℂ) (n : ℤ) :
    phase t x (-n) = Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) * x (-n) := by
  simp [phase, disp]

theorem phase_mem_seqSobolev38 (r t : ℝ) {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 r) :
    phase t x ∈ seqSobolev38 r := by
  rw [mem_seqSobolev38_iff] at hx ⊢
  unfold SobolevSquareSummable at hx ⊢
  refine hx.congr (fun n => ?_)
  rw [norm_phase_apply]

/-- The phase group as a real-linear isometry of `h^r`. -/
def phaseC (r t : ℝ) : SobolevCarrier38 r →ₗᵢ[ℝ] SobolevCarrier38 r where
  toFun x := carrierMk38 r (phase t (carrierCoe38 r x)) (phase_mem_seqSobolev38 r t (carrierCoe38_mem r x))
  map_add' x y := carrierExt38 (funext fun n => by
    show Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) * (carrierCoe38 r x n + carrierCoe38 r y n) =
      Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) * carrierCoe38 r x n +
      Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) * carrierCoe38 r y n
    ring)
  map_smul' c x := carrierExt38 (funext fun n => by
    show Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) * ((c : ℂ) * carrierCoe38 r x n) =
      (c : ℂ) * (Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) * carrierCoe38 r x n)
    ring)
  norm_map' x := by
    have h1 := carrier_hasSum_norm_sq38 r (carrierMk38 r (phase t (carrierCoe38 r x))
      (phase_mem_seqSobolev38 r t (carrierCoe38_mem r x)))
    have h2 := carrier_hasSum_norm_sq38 r x
    have : (fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r (carrierMk38 r (phase t (carrierCoe38 r x))
        (phase_mem_seqSobolev38 r t (carrierCoe38_mem r x))) n‖ ^ 2) =
        fun n : ℤ => sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2 := by
      funext n
      rw [carrierCoe38_mk, norm_phase_apply]
    rw [this] at h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.unique h2)

theorem carrierCoe38_phaseC (r t : ℝ) (x : SobolevCarrier38 r) :
    carrierCoe38 r (phaseC r t x) = phase t (carrierCoe38 r x) := rfl

theorem carrierCoe38_phaseC_apply (r t : ℝ) (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (phaseC r t x) n =
      Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) * carrierCoe38 r x n := rfl

theorem norm_phaseC (r t : ℝ) (x : SobolevCarrier38 r) : ‖phaseC r t x‖ = ‖x‖ :=
  (phaseC r t).norm_map x

theorem phaseC_zero (r : ℝ) (x : SobolevCarrier38 r) : phaseC r 0 x = x :=
  carrierExt38 (by rw [carrierCoe38_phaseC, phase_zero_apply])

theorem phaseC_add (r s t : ℝ) (x : SobolevCarrier38 r) :
    phaseC r (s + t) x = phaseC r s (phaseC r t x) :=
  carrierExt38 (by simp only [carrierCoe38_phaseC, phase_add_apply])

theorem phaseC_neg_phaseC (r t : ℝ) (x : SobolevCarrier38 r) :
    phaseC r (-t) (phaseC r t x) = x := by
  rw [← phaseC_add, neg_add_cancel, phaseC_zero]

theorem phaseC_phaseC_neg (r t : ℝ) (x : SobolevCarrier38 r) :
    phaseC r t (phaseC r (-t) x) = x := by
  rw [← phaseC_add, add_neg_cancel, phaseC_zero]

/-! ## Dominated-convergence criterion for convergence in `h^r` -/

theorem tendsto_carrier_of_dominated {ι : Type*} {l : Filter ι} (r : ℝ)
    (F : ι → SobolevCarrier38 r) (z : SobolevCarrier38 r) (bound : ℤ → ℝ) (hb : Summable bound)
    (hle : ∀ᶠ k in l, ∀ n, sobolevModeWeight r n *
      ‖carrierCoe38 r (F k) n - carrierCoe38 r z n‖ ^ 2 ≤ bound n)
    (hlim : ∀ n, Tendsto (fun k => carrierCoe38 r (F k) n) l (𝓝 (carrierCoe38 r z n))) :
    Tendsto F l (𝓝 z) := by
  have hsq : Tendsto (fun k => ‖F k - z‖ ^ 2) l (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := l)
      (f := fun k n => sobolevModeWeight r n * ‖carrierCoe38 r (F k) n - carrierCoe38 r z n‖ ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := bound) hb ?_ ?_
    · have e : ∀ k, ‖F k - z‖ ^ 2 =
          ∑' n, sobolevModeWeight r n * ‖carrierCoe38 r (F k) n - carrierCoe38 r z n‖ ^ 2 :=
        fun k => (carrier_hasSum_norm_sq38 r (F k - z)).tsum_eq.symm
      simp only [e]
      simpa using h
    · intro n
      have h1 := ((hlim n).sub_const (carrierCoe38 r z n)).norm.pow 2
      have h2 := h1.const_mul (sobolevModeWeight r n)
      simpa using h2
    · filter_upwards [hle] with k hk n
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sobolevModeWeight_pos r n).le (sq_nonneg _))]
      exact hk n
  have h3 := hsq.sqrt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.sqrt_sq (norm_nonneg _)] using h3

/-! ## Strong and joint continuity -/

theorem norm_exp_sub_le_two (a b : ℝ) :
    ‖Complex.exp (-(Complex.I * (a : ℂ))) - Complex.exp (-(Complex.I * (b : ℂ)))‖ ≤ 2 := by
  calc _ ≤ ‖Complex.exp (-(Complex.I * (a : ℂ)))‖ + ‖Complex.exp (-(Complex.I * (b : ℂ)))‖ :=
        norm_sub_le _ _
    _ = 2 := by rw [norm_phaseFactor, norm_phaseFactor]; norm_num

theorem tendsto_phaseC_apply (r : ℝ) (y : SobolevCarrier38 r) (t0 : ℝ) :
    Tendsto (fun t => phaseC r t y) (𝓝 t0) (𝓝 (phaseC r t0 y)) := by
  refine tendsto_carrier_of_dominated r _ _
    (fun n => 4 * (sobolevModeWeight r n * ‖carrierCoe38 r y n‖ ^ 2))
    ((carrier_hasSum_norm_sq38 r y).summable.mul_left 4) (Eventually.of_forall fun t n => ?_)
    (fun n => ?_)
  · have h1 : ‖carrierCoe38 r (phaseC r t y) n - carrierCoe38 r (phaseC r t0 y) n‖ ≤
        2 * ‖carrierCoe38 r y n‖ := by
      have e : carrierCoe38 r (phaseC r t y) n - carrierCoe38 r (phaseC r t0 y) n =
          (Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) -
            Complex.exp (-(Complex.I * ((t0 * disp n : ℝ) : ℂ)))) * carrierCoe38 r y n := by
        simp only [carrierCoe38_phaseC_apply]; ring
      rw [e, norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_exp_sub_le_two _ _) (norm_nonneg _)
    have h2 : ‖carrierCoe38 r (phaseC r t y) n - carrierCoe38 r (phaseC r t0 y) n‖ ^ 2 ≤
        (2 * ‖carrierCoe38 r y n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hw := (sobolevModeWeight_pos r n).le
    calc _ ≤ sobolevModeWeight r n * (2 * ‖carrierCoe38 r y n‖) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 hw
      _ = _ := by ring
  · have hc : Continuous fun t : ℝ =>
        Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) * carrierCoe38 r y n := by fun_prop
    exact hc.tendsto t0

theorem continuous_phaseC_apply (r : ℝ) (y : SobolevCarrier38 r) :
    Continuous fun t : ℝ => phaseC r t y :=
  continuous_iff_continuousAt.2 fun t0 => tendsto_phaseC_apply r y t0

theorem continuous_phaseC (r : ℝ) :
    Continuous fun p : ℝ × SobolevCarrier38 r => phaseC r p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t0, x0⟩
  have h1 : Tendsto (fun p : ℝ × SobolevCarrier38 r => phaseC r p.1 (p.2 - x0)) (𝓝 (t0, x0)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_phaseC]
    have h : Tendsto (fun p : ℝ × SobolevCarrier38 r => p.2 - x0) (𝓝 (t0, x0)) (𝓝 (x0 - x0)) :=
      (continuous_snd.tendsto _).sub_const x0
    simpa using h.norm
  have h2 : Tendsto (fun p : ℝ × SobolevCarrier38 r => phaseC r p.1 x0) (𝓝 (t0, x0))
      (𝓝 (phaseC r t0 x0)) :=
    (tendsto_phaseC_apply r x0 t0).comp (continuous_fst.tendsto _)
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine h3.congr (fun p => ?_)
  rw [← map_add, sub_add_cancel]

/-! ## The generator `-iΛ : h^{r+2} → h^r` and differentiability -/

theorem sobolevModeWeight_add_two (r : ℝ) (n : ℤ) :
    sobolevModeWeight (r + 2) n = sobolevModeWeight r n * (1 + (n : ℝ) ^ 2) ^ 2 := by
  simp only [sobolevModeWeight, Real.rpow_eq_pow]
  have h2 : 2 * (r + 2) = 2 * r + 4 := by ring
  rw [h2, Real.rpow_add (japaneseBracket_pos n)]
  congr 1
  have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
  rw [h4, Real.rpow_natCast]
  unfold japaneseBracket
  have h := Real.sq_sqrt (show 0 ≤ 1 + (n : ℝ) ^ 2 by positivity)
  calc _ = ((Real.sqrt (1 + (n : ℝ) ^ 2)) ^ 2) ^ 2 := by ring
    _ = _ := by rw [h]

theorem disp_sq_le (n : ℤ) : disp n ^ 2 ≤ (4 * Real.pi ^ 2) ^ 2 * (1 + (n : ℝ) ^ 2) ^ 2 := by
  have h : disp n = 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by unfold disp; ring
  rw [h, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  have : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  nlinarith

theorem weight_mul_disp_sq_le (r : ℝ) (n : ℤ) :
    sobolevModeWeight r n * disp n ^ 2 ≤ (4 * Real.pi ^ 2) ^ 2 * sobolevModeWeight (r + 2) n := by
  rw [sobolevModeWeight_add_two]
  have := mul_le_mul_of_nonneg_left (disp_sq_le n) (sobolevModeWeight_pos r n).le
  linarith

theorem lam_mem (r : ℝ) (y : SobolevCarrier38 (r + 2)) :
    (fun n : ℤ => -(Complex.I * ((disp n : ℝ) : ℂ)) * carrierCoe38 (r + 2) y n) ∈ seqSobolev38 r := by
  rw [mem_seqSobolev38_iff]
  unfold SobolevSquareSummable
  have hs : Summable fun n : ℤ => (4 * Real.pi ^ 2) ^ 2 *
      (sobolevModeWeight (r + 2) n * ‖carrierCoe38 (r + 2) y n‖ ^ 2) :=
    (carrier_hasSum_norm_sq38 (r + 2) y).summable.mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · exact mul_nonneg (Real.rpow_nonneg (japaneseBracket_pos n).le _) (sq_nonneg _)
  · have e : Real.rpow (japaneseBracket n) (2 * r) = sobolevModeWeight r n := rfl
    rw [e, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (disp_nonneg_phase n), mul_pow, ← mul_assoc]
    have := weight_mul_disp_sq_le r n
    calc _ = (sobolevModeWeight r n * disp n ^ 2) * ‖carrierCoe38 (r + 2) y n‖ ^ 2 := by ring
      _ ≤ ((4 * Real.pi ^ 2) ^ 2 * sobolevModeWeight (r + 2) n) * ‖carrierCoe38 (r + 2) y n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = _ := by ring

/-- `-iΛ : h^{r+2} → h^r`, `(lam r y)_n = -(i (2π n)²) y_n`. -/
def lam (r : ℝ) (y : SobolevCarrier38 (r + 2)) : SobolevCarrier38 r :=
  carrierMk38 r (fun n : ℤ => -(Complex.I * ((disp n : ℝ) : ℂ)) * carrierCoe38 (r + 2) y n)
    (lam_mem r y)

theorem carrierCoe38_lam (r : ℝ) (y : SobolevCarrier38 (r + 2)) (n : ℤ) :
    carrierCoe38 r (lam r y) n = -(Complex.I * ((disp n : ℝ) : ℂ)) * carrierCoe38 (r + 2) y n := rfl

theorem norm_lam_le (r : ℝ) (y : SobolevCarrier38 (r + 2)) :
    ‖lam r y‖ ≤ 4 * Real.pi ^ 2 * ‖y‖ := by
  have h1 := carrier_hasSum_norm_sq38 r (lam r y)
  have h2 := (carrier_hasSum_norm_sq38 (r + 2) y).mul_left ((4 * Real.pi ^ 2) ^ 2)
  have hle := hasSum_le (fun n => ?_) h1 h2
  · refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [mul_pow]; exact hle
  · rw [carrierCoe38_lam, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (disp_nonneg_phase n), mul_pow]
    have := weight_mul_disp_sq_le r n
    calc _ = (sobolevModeWeight r n * disp n ^ 2) * ‖carrierCoe38 (r + 2) y n‖ ^ 2 := by ring
      _ ≤ ((4 * Real.pi ^ 2) ^ 2 * sobolevModeWeight (r + 2) n) * ‖carrierCoe38 (r + 2) y n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = _ := by ring

/-- Per-coordinate Lipschitz bound `|e^{-isd} - e^{-itd}| ≤ |s - t| d`. -/
theorem norm_phaseFactor_sub_le (s t d : ℝ) (hd : 0 ≤ d) :
    ‖Complex.exp (-(Complex.I * ((s * d : ℝ) : ℂ))) - Complex.exp (-(Complex.I * ((t * d : ℝ) : ℂ)))‖
      ≤ |s - t| * d := by
  have e : Complex.exp (-(Complex.I * ((s * d : ℝ) : ℂ))) - Complex.exp (-(Complex.I * ((t * d : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * ((t * d : ℝ) : ℂ))) *
        (Complex.exp (Complex.I * (((-((s - t) * d)) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, norm_phaseFactor, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hd]

theorem hasDerivAt_phaseFactor (d t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(Complex.I * ((s * d : ℝ) : ℂ))))
      (-(Complex.I * (d : ℂ)) * Complex.exp (-(Complex.I * ((t * d : ℝ) : ℂ)))) t := by
  have h1 : HasDerivAt (fun s : ℝ => ((s * d : ℝ) : ℂ)) (d : ℂ) t := by
    simpa using (((hasDerivAt_id t).mul_const d).ofReal_comp)
  have h3 := ((h1.const_mul Complex.I).neg).cexp
  exact h3.congr_deriv (by simp only [Pi.neg_apply]; ring)

/-- Fixed-vector differentiability of the phase curve into the lower Sobolev space. -/
theorem hasDerivAt_phaseC_apply (r : ℝ) (y : SobolevCarrier38 (r + 2)) (t : ℝ) :
    HasDerivAt (fun s => carrierIncl38 (by linarith : r ≤ r + 2) (phaseC (r + 2) s y))
      (lam r (phaseC (r + 2) t y)) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hcoord : ∀ s n, carrierCoe38 r (slope (fun s => carrierIncl38 (by linarith : r ≤ r + 2)
      (phaseC (r + 2) s y)) t s) n =
      (((s - t)⁻¹ : ℝ) : ℂ) * ((Complex.exp (-(Complex.I * ((s * disp n : ℝ) : ℂ))) -
        Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ)))) * carrierCoe38 (r + 2) y n) := by
    intro s n
    rw [slope_def_module]
    show (((s - t)⁻¹ : ℝ) : ℂ) * (carrierCoe38 r (carrierIncl38 (by linarith : r ≤ r + 2)
        (phaseC (r + 2) s y)) n - carrierCoe38 r (carrierIncl38 (by linarith : r ≤ r + 2)
        (phaseC (r + 2) t y)) n) = _
    rw [carrierCoe38_incl38, carrierCoe38_incl38]
    simp only [carrierCoe38_phaseC_apply]
    ring
  refine tendsto_carrier_of_dominated r _ _
    (fun n => 4 * ((4 * Real.pi ^ 2) ^ 2 * (sobolevModeWeight (r + 2) n * ‖carrierCoe38 (r + 2) y n‖ ^ 2)))
    (((carrier_hasSum_norm_sq38 (r + 2) y).summable.mul_left _).mul_left 4) ?_ (fun n => ?_)
  · filter_upwards [self_mem_nhdsWithin] with s hs n
    have hst : s - t ≠ 0 := sub_ne_zero.2 hs
    rw [hcoord, carrierCoe38_lam]
    have hb : ‖(((s - t)⁻¹ : ℝ) : ℂ) * ((Complex.exp (-(Complex.I * ((s * disp n : ℝ) : ℂ))) -
        Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ)))) * carrierCoe38 (r + 2) y n) -
        -(Complex.I * ((disp n : ℝ) : ℂ)) * carrierCoe38 (r + 2) (phaseC (r + 2) t y) n‖ ≤
        2 * disp n * ‖carrierCoe38 (r + 2) y n‖ := by
      refine (norm_sub_le _ _).trans ?_
      have a1 : ‖(((s - t)⁻¹ : ℝ) : ℂ) * ((Complex.exp (-(Complex.I * ((s * disp n : ℝ) : ℂ))) -
          Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ)))) * carrierCoe38 (r + 2) y n)‖ ≤
          disp n * ‖carrierCoe38 (r + 2) y n‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv]
        have := norm_phaseFactor_sub_le s t (disp n) (disp_nonneg_phase n)
        have hpos : 0 < |s - t| := abs_pos.2 hst
        calc |s - t|⁻¹ * (‖Complex.exp (-(Complex.I * ((s * disp n : ℝ) : ℂ))) -
              Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ)))‖ * ‖carrierCoe38 (r + 2) y n‖)
            ≤ |s - t|⁻¹ * ((|s - t| * disp n) * ‖carrierCoe38 (r + 2) y n‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (norm_nonneg _))
                (inv_nonneg.2 hpos.le)
          _ = disp n * ‖carrierCoe38 (r + 2) y n‖ := by field_simp
      have a2 : ‖-(Complex.I * ((disp n : ℝ) : ℂ)) * carrierCoe38 (r + 2) (phaseC (r + 2) t y) n‖ =
          disp n * ‖carrierCoe38 (r + 2) y n‖ := by
        rw [norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (disp_nonneg_phase n), carrierCoe38_phaseC_apply, norm_mul, norm_phaseFactor,
          one_mul]
      linarith
    have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hw := weight_mul_disp_sq_le r n
    have hwp := (sobolevModeWeight_pos r n).le
    calc _ ≤ sobolevModeWeight r n * (2 * disp n * ‖carrierCoe38 (r + 2) y n‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hb2 hwp
      _ = 4 * ((sobolevModeWeight r n * disp n ^ 2) * ‖carrierCoe38 (r + 2) y n‖ ^ 2) := by ring
      _ ≤ 4 * (((4 * Real.pi ^ 2) ^ 2 * sobolevModeWeight (r + 2) n) *
            ‖carrierCoe38 (r + 2) y n‖ ^ 2) := by
          gcongr
      _ = _ := by ring
  · have hd := (hasDerivAt_phaseFactor (disp n) t).mul_const (carrierCoe38 (r + 2) y n)
    have hsl := hasDerivAt_iff_tendsto_slope.1 hd
    have e1 : (fun s => carrierCoe38 r (slope (fun s => carrierIncl38 (by linarith : r ≤ r + 2)
        (phaseC (r + 2) s y)) t s) n) =
        slope (fun s : ℝ => Complex.exp (-(Complex.I * ((s * disp n : ℝ) : ℂ))) *
          carrierCoe38 (r + 2) y n) t := by
      funext s
      rw [hcoord, slope_def_module, Complex.real_smul]
      ring
    have e2 : carrierCoe38 r (lam r (phaseC (r + 2) t y)) n =
        -(Complex.I * (disp n : ℂ)) * Complex.exp (-(Complex.I * ((t * disp n : ℝ) : ℂ))) *
          carrierCoe38 (r + 2) y n := by
      rw [carrierCoe38_lam, carrierCoe38_phaseC_apply]; push_cast; ring
    rw [e1, e2]
    exact hsl

/-- **Derivative of the interaction-picture curve.** For `γ : ℝ → h^{r+2}` differentiable at `t`,
the curve `s ↦ phase s (γ s) ∈ h^r` is differentiable with derivative
`phase t γ' + (-iΛ) phase t γ(t)`. -/
theorem hasDerivAt_phaseC_comp (r : ℝ) {γ : ℝ → SobolevCarrier38 (r + 2)}
    {γ' : SobolevCarrier38 (r + 2)} {t : ℝ} (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => carrierIncl38 (by linarith) (phaseC (r + 2) s (γ s)))
      (carrierIncl38 (by linarith) (phaseC (r + 2) t γ') + lam r (phaseC (r + 2) t (γ t))) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  set ι : SobolevCarrier38 (r + 2) →L[ℝ] SobolevCarrier38 r := carrierIncl38 (by linarith) with hι
  have e : ∀ s, slope (fun s => ι (phaseC (r + 2) s (γ s))) t s =
      ι (phaseC (r + 2) s (slope γ t s)) +
        slope (fun s => ι (phaseC (r + 2) s (γ t))) t s := by
    intro s
    simp only [slope_def_module, map_smul, map_sub, smul_sub]
    abel
  have h1 : Tendsto (fun s => ι (phaseC (r + 2) s (slope γ t s))) (𝓝[≠] t)
      (𝓝 (ι (phaseC (r + 2) t γ'))) := by
    have hc : Continuous fun p : ℝ × SobolevCarrier38 (r + 2) => ι (phaseC (r + 2) p.1 p.2) :=
      ι.continuous.comp (continuous_phaseC (r + 2))
    have ht : Tendsto (fun s : ℝ => s) (𝓝[≠] t) (𝓝 t) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hs := hasDerivAt_iff_tendsto_slope.1 hγ
    have hp := ht.prodMk_nhds hs
    have hq := (hc.tendsto (t, γ')).comp hp
    exact hq
  have h2 := hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_phaseC_apply r (γ t) t)
  have e' : slope (fun s => ι (phaseC (r + 2) s (γ s))) t = fun s =>
      ι (phaseC (r + 2) s (slope γ t s)) + slope (fun s => ι (phaseC (r + 2) s (γ t))) t s :=
    funext e
  rw [e']
  exact h1.add h2

end NlsGge.NLS38
