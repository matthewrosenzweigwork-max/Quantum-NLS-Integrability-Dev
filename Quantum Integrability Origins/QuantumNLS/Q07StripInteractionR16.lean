import QuantumNLS.Q07RealCutsR15
import QuantumNLS.GP05AcceptedBridgeR16
import QuantumNLS.L1TransferHolomorphic

/-! The actual interaction transfer: entire spectral dependence, strip-uniform
bounds and high-energy decay at every fixed imaginary part. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory ComplexConjugate
open scoped Interval
open QuantumNLS.LinearFundamental
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer
  QuantumNLS.RootInteractionL1 QuantumNLS.RootDiscriminantBound
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance Q07StripInteractionR16Pseudo : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance Q07StripInteractionR16ENorm : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
namespace QuantumNLS.Q07StripInteractionR16
open Q07RealCutsR15
variable {L κ : ℝ}

def spectral (t y : ℝ) : ℂ := (t : ℂ) + Complex.I * (y : ℂ)
@[simp] theorem spectral_im (t y : ℝ) : (spectral t y).im = y := by simp [spectral]
@[simp] theorem spectral_re (t y : ℝ) : (spectral t y).re = t := by simp [spectral]

def interaction (κ : ℝ) (u : Profile L) (z : ℂ) : Mat2 :=
  transfer (Bc κ (fun x => u x) z) L

def control (κ h : ℝ) (u : Profile L) : ℝ := Real.sqrt κ * Real.exp (h*L) * ‖u‖

theorem integral_bound (hL : 0 ≤ L) (u : Profile L) {z : ℂ} {h : ℝ} (hz : |z.im| ≤ h) :
    (∫ x in (0 : ℝ)..L, ‖Bc κ (fun x => u x) z x‖) ≤ control κ h u := by
  refine (integral_norm_Bc_le hL (integrable_profile hL u) κ z).trans ?_
  rw [integral_norm_profile hL]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz hL))
      (Real.sqrt_nonneg _)) (norm_nonneg _)

theorem norm_interaction_le (hL : 0 ≤ L) (u : Profile L) {z : ℂ} {h : ℝ} (hz : |z.im| ≤ h) :
    ‖interaction κ u z‖ ≤ Real.exp (control κ h u) := by
  have hb := L1Stability.norm_transfer_le hL (intervalIntegrable_Bc (integrable_profile hL u) κ z)
    (x := L) ⟨hL, le_rfl⟩
  exact hb.trans ((mul_le_mul norm_one_mat2_le (Real.exp_le_exp.mpr (integral_bound hL u hz))
    (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _))

theorem differentiable_interaction (hL : 0 ≤ L) (u : Profile L) :
    Differentiable ℂ (interaction κ u) := by
  apply L1TransferHolomorphic.differentiable_transfer hL
    (fun z => intervalIntegrable_Bc (integrable_profile hL u) κ z)
  · intro x _
    apply differentiable_pi.mpr
    intro i
    apply differentiable_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> simp [Bc, E1c, E2c, a1c] <;> fun_prop
  · intro z₀
    refine ⟨fun x => Real.sqrt κ * ‖u x‖ * Real.exp ((|z₀.im|+2)*L),
      ((integrable_profile hL u).norm.const_mul _).mul_const _, ?_⟩
    intro z hz x hx
    refine (norm_Bc_le κ (fun x => u x) z hx).trans ?_
    have hi : |z.im| ≤ |z₀.im|+2 := by
      have hh := Complex.abs_im_le_norm (z-z₀)
      have hd : ‖z-z₀‖ ≤ 2 := by simpa only [mem_closedBall, dist_eq_norm] using hz
      simp only [Complex.sub_im] at hh
      linarith [abs_sub_abs_le_abs_sub z.im z₀.im]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hi hL)) (by positivity)
  · exact ⟨hL, le_rfl⟩

/-- The accepted Banach bridge is used directly for the actual interaction. -/
theorem analytic_interaction (hL : 0 ≤ L) (u : Profile L) (z : ℂ) :
    AnalyticAt ℂ (interaction κ u) z :=
  GP05AcceptedBridgeR16.banachHolomorphicBridge univ _ isOpen_univ
    (differentiable_interaction hL u).differentiableOn z (mem_univ _)

/-- Cauchy on the unit spectral ball supplies a uniform full derivative bound
on the strip, independent of the real part. -/
theorem deriv_bound (hL : 0 ≤ L) (u : Profile L) {h : ℝ} {z : ℂ} (hz : |z.im| ≤ h) :
    ‖deriv (interaction κ u) z‖ ≤ 2 * Real.exp (control κ (h+1) u) := by
  have hd : DiffContOnCl ℂ (interaction κ u) (ball z (1/2)) :=
    (differentiable_interaction hL u).differentiableOn.diffContOnCl
  have hb : ∀ w ∈ sphere z (1/2), ‖interaction κ u w‖ ≤ Real.exp (control κ (h+1) u) := by
    intro w hw
    apply norm_interaction_le hL u
    have hi := Complex.abs_im_le_norm (w-z)
    have hd : ‖w-z‖ = 1/2 := by simpa only [mem_sphere, dist_eq_norm] using hw
    simp only [Complex.sub_im] at hi
    linarith [abs_sub_abs_le_abs_sub w.im z.im]
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1/2) hd hb
  calc
    _ ≤ Real.exp (control κ (h+1) u)/(1/2) := hh
    _ = _ := by ring

theorem spectral_sub_le (hL : 0 ≤ L) (u : Profile L) {h : ℝ} (t : ℝ)
    {y y' : ℝ} (hy : |y| ≤ h) (hy' : |y'| ≤ h) :
    ‖interaction κ u (spectral t y) - interaction κ u (spectral t y')‖ ≤
      (2 * Real.exp (control κ (h+1) u)) * |y-y'| := by
  let S : Set ℂ := {z | |z.im| ≤ h}
  have hc : Convex ℝ S := by
    intro z hz w hw a b ha hb hab
    change |(a • z+b • w).im| ≤ h
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, zero_mul, add_zero]
    calc
      |a*z.im+b*w.im| ≤ |a*z.im|+|b*w.im| := abs_add_le _ _
      _ = a*|z.im|+b*|w.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a*h+b*h := add_le_add (mul_le_mul_of_nonneg_left hz ha) (mul_le_mul_of_nonneg_left hw hb)
      _ = h := by rw [← add_mul, hab, one_mul]
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z (_ : z ∈ S) => differentiable_interaction (κ := κ) hL u z)
    (fun z (hz : z ∈ S) => deriv_bound (κ := κ) hL u hz) hc
    (show spectral t y' ∈ S by simpa [S]) (show spectral t y ∈ S by simpa [S])
  convert hh using 1
  rw [show spectral t y - spectral t y' = Complex.I * ((y-y' : ℝ) : ℂ) by
    simp only [spectral, Complex.ofReal_sub]; ring]
  simp [-Complex.ofReal_sub]

theorem dyson_bound (hL : 0 ≤ L) (u : Profile L) (y t : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) L) :
    ‖dyson (Bc κ (fun x => u x) (spectral t y)) n x‖ ≤
      control κ |y| u ^ n / (n.factorial : ℝ) := by
  have hB := intervalIntegrable_Bc (integrable_profile hL u) κ (spectral t y)
  have hI := integral_bound (κ := κ) hL u (z := spectral t y) (by simp : |(spectral t y).im| ≤ |y|)
  have hi := intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
    (ae_of_all _ fun s => norm_nonneg (Bc κ (fun x => u x) (spectral t y) s)) hB.norm
  have hb := norm_dyson_le_control hL hB n x hx
  refine hb.trans ?_
  calc
    _ ≤ 1 * control κ |y| u ^ n / (n.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul norm_one_mat2_le
        (pow_le_pow_left₀ (intervalIntegral.integral_nonneg hx.1 (fun s _ => norm_nonneg _))
          (hi.trans hI) n)
          (pow_nonneg (intervalIntegral.integral_nonneg hx.1 (fun s _ => norm_nonneg _)) n) zero_le_one
    _ = _ := by ring

/-- Scalar oscillatory factors of the first interaction term. -/
theorem E1_spectral_sq (t y x : ℝ) :
    E1c (spectral t y) x * E1c (spectral t y) x =
      Complex.exp (-(y : ℂ)*x) * Complex.exp (Complex.I * ((1*t : ℝ) : ℂ) * x) := by
  simp only [E1c, a1c, spectral, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp [sub_eq_add_neg]

theorem E2_spectral_sq (t y x : ℝ) :
    E2c (spectral t y) x * E2c (spectral t y) x =
      Complex.exp ((y : ℂ)*x) * Complex.exp (Complex.I * ((-1*t : ℝ) : ℂ) * x) := by
  simp only [E2c, a1c, spectral, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  simp

theorem dyson_one_tendsto (hL : 0 ≤ L) (u : ℝ → ℂ) (hu : IntervalIntegrable u volume 0 L) (y : ℝ) :
    Tendsto (fun t : ℝ => dyson (Bc κ (fun x => u x) (spectral t y)) 1 L)
      (cocompact ℝ) (𝓝 0) := by
  have hd : ∀ t, dyson (Bc κ (fun x => u x) (spectral t y)) 1 L =
      ∫ x in (0 : ℝ)..L, Bc κ (fun x => u x) (spectral t y) x := by
    intro t; simp [dyson]
  simp_rw [hd]
  have h01 : Tendsto (fun t : ℝ => ∫ x in (0 : ℝ)..L,
      Bc κ (fun x => u x) (spectral t y) x 0 1) (cocompact ℝ) (𝓝 0) := by
    have := RootTraceAsymptotics.tendsto_osc
      (fun x => (Real.sqrt κ : ℂ) * conj (u x) * Complex.exp (-(y : ℂ)*x)) hL
      (c := 1) one_ne_zero
    refine this.congr (fun t => ?_)
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Bc, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, E1_spectral_sq]
    ring
  have h10 : Tendsto (fun t : ℝ => ∫ x in (0 : ℝ)..L,
      Bc κ (fun x => u x) (spectral t y) x 1 0) (cocompact ℝ) (𝓝 0) := by
    have := RootTraceAsymptotics.tendsto_osc
      (fun x => (Real.sqrt κ : ℂ) * u x * Complex.exp ((y : ℂ)*x)) hL
      (c := -1) (by norm_num)
    refine this.congr (fun t => ?_)
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Bc, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, E2_spectral_sq]
    ring
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hn01 := tendsto_zero_iff_norm_tendsto_zero.1 h01
  have hn10 := tendsto_zero_iff_norm_tendsto_zero.1 h10
  refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) (by simpa using hn01.add hn10)
  rw [sub_zero]
  refine norm_le_of_row_sums _ (by positivity) (fun i => ?_)
  rw [L1TraceGeometry.integral_entry (intervalIntegrable_Bc hu κ _) i 0,
    L1TraceGeometry.integral_entry (intervalIntegrable_Bc hu κ _) i 1]
  fin_cases i <;> simp [Bc]


/-- Every nonconstant Dyson term decays for fixed imaginary part, by scalar
Riemann--Lebesgue followed by dominated convergence in the outer variable. -/
theorem dyson_tendsto (hL : 0 ≤ L) (u : Profile L) (y : ℝ) :
    ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) L,
      Tendsto (fun t : ℝ => dyson (Bc κ (fun x => u x) (spectral t y)) (n+1) x)
        (cocompact ℝ) (𝓝 0)
  | 0 => fun x hx => dyson_one_tendsto hx.1 (fun x => u x)
      ((integrable_profile hL u).mono_set (by
        rw [uIcc_of_le hx.1, uIcc_of_le hL]
        exact Icc_subset_Icc_right hx.2)) y
  | n+1 => fun x hx => by
    have : (cocompact ℝ).IsCountablyGenerated := by
      rw [cocompact_eq_atBot_atTop]; infer_instance
    have hdys : ∀ t : ℝ, dyson (Bc κ (fun x => u x) (spectral t y)) (n+1+1) x =
        ∫ s in (0 : ℝ)..x, Bc κ (fun x => u x) (spectral t y) s *
          dyson (Bc κ (fun x => u x) (spectral t y)) (n+1) s := fun t => rfl
    simp_rw [hdys]
    have hIoc : Ι (0 : ℝ) x = Ioc 0 x := by rw [uIoc_of_le hx.1]
    have hsub : uIcc (0 : ℝ) x ⊆ uIcc 0 L := by
      rw [uIcc_of_le hx.1, uIcc_of_le hL]; exact Icc_subset_Icc_right hx.2
    have hsL : ∀ s ∈ Ι (0 : ℝ) x, s ∈ Icc (0 : ℝ) L := fun s hs => by
      rw [hIoc] at hs; exact ⟨hs.1.le, hs.2.trans hx.2⟩
    let b : ℝ → ℝ := fun s => Real.sqrt κ * ‖u s‖ * Real.exp (|y| * L)
    have hb : ∀ t s, s ∈ Icc (0 : ℝ) L →
        ‖Bc κ (fun x => u x) (spectral t y) s‖ ≤ b s := by
      intro t s hs
      simpa only [spectral_im, b] using norm_Bc_le κ (fun x => u x) (spectral t y) hs
    have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (a := 0) (b := x) (l := cocompact ℝ)
      (F := fun t s => Bc κ (fun x => u x) (spectral t y) s *
        dyson (Bc κ (fun x => u x) (spectral t y)) (n+1) s) (f := fun _ => (0 : Mat2))
      (fun s => b s * (control κ |y| u ^ (n+1) / ((n+1).factorial : ℝ)))
      (Eventually.of_forall fun t => by
        rw [hIoc]
        exact ((integrable_dyson_product
          (intervalIntegrable_Bc (integrable_profile hL u) κ (spectral t y)) (n+1)).mono_set hsub).1.aestronglyMeasurable)
      (Eventually.of_forall fun t => ae_of_all _ fun s hs =>
        (norm_mul_le _ _).trans (mul_le_mul (hb t s (hsL s hs))
          (dyson_bound hL u y t (n+1) (hsL s hs)) (norm_nonneg _) (by dsimp [b]; positivity)))
      (((((integrable_profile hL u).mono_set hsub).norm.const_mul _).mul_const _).mul_const _)
      (ae_of_all _ fun s hs => by
        have hih := dyson_tendsto hL u y n s (hsL s hs)
        refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
        refine squeeze_zero (fun t => norm_nonneg _) (fun t => (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (hb t s (hsL s hs)) (norm_nonneg _))) ?_
        simpa using (tendsto_zero_iff_norm_tendsto_zero.1 hih).const_mul (b s))
    have hzero : (∫ s in (0 : ℝ)..x, (fun _ => (0 : Mat2)) s) = 0 := intervalIntegral.integral_zero
    rw [hzero] at this
    exact this

/-- The actual interaction transfer tends to the identity at each fixed
imaginary part; no strip asymptotic is a premise. -/
theorem interaction_tendsto (hL : 0 ≤ L) (u : Profile L) (y : ℝ) :
    Tendsto (fun t : ℝ => interaction κ u (spectral t y)) (cocompact ℝ) (𝓝 1) := by
  have hx : L ∈ Icc (0 : ℝ) L := ⟨hL, le_rfl⟩
  have hs : ∀ t : ℝ, Summable (fun n : ℕ => dyson (Bc κ (fun x => u x) (spectral t y)) n L) :=
    fun t => Summable.of_norm_bounded (Real.summable_pow_div_factorial (control κ |y| u))
      (fun n => dyson_bound hL u y t n hx)
  have he : ∀ t : ℝ, interaction κ u (spectral t y) =
      1 + ∑' n : ℕ, dyson (Bc κ (fun x => u x) (spectral t y)) (n+1) L := by
    intro t
    exact (hs t).tsum_eq_zero_add
  simp_rw [he]
  have hbs : Summable (fun n : ℕ => control κ |y| u ^ (n+1) / ((n+1).factorial : ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial (control κ |y| u))
  have hh : Tendsto (fun t : ℝ => ∑' n : ℕ, dyson (Bc κ (fun x => u x) (spectral t y)) (n+1) L)
      (cocompact ℝ) (𝓝 (∑' _n : ℕ, (0 : Mat2))) := tendsto_tsum_of_dominated_convergence
    (bound := fun n : ℕ => control κ |y| u ^ (n+1) / ((n+1).factorial : ℝ))
    hbs (fun n => dyson_tendsto hL u y n L hx)
    (Eventually.of_forall fun t n => dyson_bound hL u y t (n+1) hx)
  simp only [tsum_zero] at hh
  simpa only [add_zero] using hh.const_add (1 : Mat2)

end QuantumNLS.Q07StripInteractionR16
