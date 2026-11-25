import Mathlib
import QuantumNLS.Local007AlgB

/-! LOCAL-020 stage S8c: rotation invariance of the explicit mass expression `Phi`.

`shiftL d` is the composition `g ↦ g(· + d)` on the Banach algebra `A = ℝ →ᵇ ℂ`, a continuous ring automorphism.
With `ε = ±1` and `ι(θ + d) = ε ι(θ)` one has for every building block of `Local007AlgB`:
`Θ(DEl F a τ) = DEl (ΘF) (εa) τ` and `Θ(KEl a τ) = ε KEl (εa) τ`.  Hence for `d = π`
`Phi c L (Θ_π F) (-a) τ = Phi c L F a τ` whenever `F` is `2π`-periodic. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open BoundedContinuousFunction
namespace QuantumNLS.Local020PhiRot
open QuantumNLS.Local007AlgB

def shiftC (d : ℝ) : C(ℝ, ℝ) := ⟨fun θ => θ + d, by fun_prop⟩

def shiftL (d : ℝ) : A →L[ℝ] A := BoundedContinuousFunction.compContinuousCLM ℂ ℝ (shiftC d)

@[simp] theorem shiftL_apply (d : ℝ) (g : A) (θ : ℝ) : shiftL d g θ = g (θ + d) := by
  simp only [shiftL, BoundedContinuousFunction.compContinuousCLM_apply]
  rfl

theorem shiftL_mul (d : ℝ) (g h : A) : shiftL d (g * h) = shiftL d g * shiftL d h := by
  ext θ; simp [mul_apply]

theorem shiftL_one (d : ℝ) : shiftL d 1 = 1 := by
  ext θ; simp

theorem shiftL_pow (d : ℝ) (g : A) (n : ℕ) : shiftL d (g ^ n) = (shiftL d g) ^ n := by
  induction n with
  | zero => simpa using shiftL_one d
  | succ n ih => rw [pow_succ, shiftL_mul, ih, pow_succ]

theorem shiftL_shiftL (d e : ℝ) (g : A) : shiftL d (shiftL e g) = shiftL (d + e) g := by
  ext θ; simp [add_assoc, add_comm e d]

theorem shiftL_zero (g : A) : shiftL 0 g = g := by ext θ; simp

def shiftE (d : ℝ) : A ≃L[ℝ] A :=
  ContinuousLinearEquiv.equivOfInverse (shiftL d) (shiftL (-d))
    (fun g => by rw [shiftL_shiftL, neg_add_cancel, shiftL_zero])
    (fun g => by rw [shiftL_shiftL, add_neg_cancel, shiftL_zero])

theorem shiftE_apply (d : ℝ) (g : A) : shiftE d g = shiftL d g := rfl

theorem shiftL_inverse (d : ℝ) (x : A) : shiftL d (Ring.inverse x) = Ring.inverse (shiftL d x) := by
  by_cases hx : IsUnit x
  · have h1 := Ring.mul_inverse_cancel x hx
    have h2 := Ring.inverse_mul_cancel x hx
    let u : Aˣ := ⟨shiftL d x, shiftL d (Ring.inverse x), by rw [← shiftL_mul, h1, shiftL_one],
      by rw [← shiftL_mul, h2, shiftL_one]⟩
    have : Ring.inverse (u : A) = ((u⁻¹ : Aˣ) : A) := Ring.inverse_unit u
    exact this.symm
  · rw [Ring.inverse_non_unit x hx, map_zero]
    have : ¬ IsUnit (shiftL d x) := by
      intro hu
      apply hx
      obtain ⟨y, hy1, hy2⟩ := isUnit_iff_exists.1 hu
      refine isUnit_iff_exists.2 ⟨shiftL (-d) y, ?_, ?_⟩
      · have := congrArg (shiftL (-d)) hy1
        rwa [shiftL_mul, shiftL_shiftL, neg_add_cancel, shiftL_zero, shiftL_one] at this
      · have := congrArg (shiftL (-d)) hy2
        rwa [shiftL_mul, shiftL_shiftL, neg_add_cancel, shiftL_zero, shiftL_one] at this
    rw [Ring.inverse_non_unit _ this]

theorem shiftL_ofScalars (d : ℝ) (c : ℕ → ℝ) (y : A) :
    shiftL d ((FormalMultilinearSeries.ofScalars A c).sum y) =
      (FormalMultilinearSeries.ofScalars A c).sum (shiftL d y) := by
  unfold FormalMultilinearSeries.sum
  simp only [FormalMultilinearSeries.ofScalars_apply_eq]
  have := (shiftE d).map_tsum (L := SummationFilter.unconditional ℕ) (f := fun n => c n • y ^ n)
  simp only [shiftE_apply] at this
  rw [this]
  refine tsum_congr fun n => ?_
  rw [map_smul, shiftL_pow]

theorem inverse_neg (x : A) : Ring.inverse (-x) = -Ring.inverse x := by
  by_cases hx : IsUnit x
  · have h1 := Ring.mul_inverse_cancel x hx
    have h2 := Ring.inverse_mul_cancel x hx
    let u : Aˣ := ⟨-x, -Ring.inverse x, by simpa using h1, by simpa using h2⟩
    have : Ring.inverse (u : A) = ((u⁻¹ : Aˣ) : A) := Ring.inverse_unit u
    exact this
  · have h' : ¬ IsUnit (-x) := fun h => hx (by simpa using h.neg)
    rw [Ring.inverse_non_unit _ hx, Ring.inverse_non_unit _ h', neg_zero]

theorem inverse_eps (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (x : A) : Ring.inverse (ε • x) = ε • Ring.inverse x := by
  rcases hε with rfl | rfl
  · simp
  · simp [inverse_neg]

section Blocks

variable {c L d ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hι : shiftL d (iota c) = ε • iota c)
include hε hι

theorem sq_eps : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num

theorem shift_wEl (a : ℝ) : shiftL d (wEl c a) = ε • wEl c (ε * a) := by
  have h1 : ∀ θ, iota c (θ + d) = ε * iota c θ := fun θ => by
    have := congrArg (fun g : A => g θ) hι
    simpa using this
  have h2 := sq_eps hε hι
  ext θ
  simp only [wEl, shiftL_apply, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.coe_one, Pi.one_apply, h1, smul_eq_mul, Complex.real_smul]
  push_cast
  linear_combination ((a : ℂ)) * (by exact_mod_cast h2 : (ε : ℂ) * ε = 1)

theorem shift_PEl (a τ : ℝ) : shiftL d (PEl c a τ) = PEl c (ε * a) τ := by
  have h2 := sq_eps hε hι
  unfold PEl
  rw [map_sub, shiftL_mul, shift_wEl hε hι, map_smul, shiftL_one]
  ext θ
  simp only [BoundedContinuousFunction.sub_apply, mul_apply, BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.coe_one, Pi.one_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  linear_combination (wEl c (ε * a) θ * wEl c (ε * a) θ) * (by exact_mod_cast h2 : (ε : ℂ) * ε = 1)

theorem shift_fEl (F : A) : shiftL d (fEl F) = fEl (shiftL d F) := by
  unfold fEl
  rw [map_sub, shiftL_mul, map_smul, shiftL_one]

theorem shift_HEl (F : A) (a τ : ℝ) : shiftL d (HEl c F a τ) = HEl c (shiftL d F) (ε * a) τ := by
  unfold HEl
  rw [shiftL_mul, shift_fEl hε hι, shiftL_inverse, shift_PEl hε hι]

theorem shift_YEl (F : A) (a τ : ℝ) : shiftL d (YEl c L F a τ) = YEl c L (shiftL d F) (ε * a) τ := by
  unfold YEl
  rw [map_sub, map_smul, shift_HEl hε hι, shiftL_one]

theorem shift_SEl (F : A) (a τ : ℝ) : shiftL d (SEl c L F a τ) = SEl c L (shiftL d F) (ε * a) τ := by
  unfold SEl
  rw [map_smul, show binomialSeries A (1 / 2 : ℝ) = FormalMultilinearSeries.ofScalars A (fun n => Ring.choose (1 / 2 : ℝ) n) from rfl,
    shiftL_ofScalars, shift_YEl hε hι]

theorem shift_WEl (F : A) : shiftL d (WEl F) = WEl (shiftL d F) := by
  unfold WEl
  rw [shiftL_ofScalars, map_smul, shift_fEl hε hι]

theorem shift_DEl (F : A) (a τ : ℝ) : shiftL d (DEl c L F a τ) = DEl c L (shiftL d F) (ε * a) τ := by
  unfold DEl
  rw [map_smul, shiftL_mul, shift_SEl hε hι, shift_WEl hε hι]

theorem shift_KEl (a τ : ℝ) : shiftL d (KEl c a τ) = ε • KEl c (ε * a) τ := by
  have h2 := sq_eps hε hι
  unfold KEl
  rw [shiftL_mul, shiftL_inverse, shift_wEl hε hι, inverse_eps ε hε, shiftL_ofScalars, map_smul, shiftL_mul,
    shiftL_inverse, shift_wEl hε hι, inverse_eps ε hε]
  rw [smul_mul_smul_comm, show ε * ε = 1 from h2, one_smul, smul_mul_assoc]

theorem shift_integrand (F : A) (a τ : ℝ) :
    shiftL d (iota c * DEl c L F a τ * KEl c a τ) =
      iota c * DEl c L (shiftL d F) (ε * a) τ * KEl c (ε * a) τ := by
  have h2 := sq_eps hε hι
  rw [shiftL_mul, shiftL_mul, hι, shift_DEl hε hι, shift_KEl hε hι]
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, h2, one_smul]

end Blocks

theorem shiftL_iota_pi (c : ℝ) : shiftL Real.pi (iota c) = (-1 : ℝ) • iota c := by
  ext θ
  simp only [shiftL_apply, iota_apply, BoundedContinuousFunction.smul_apply, Complex.real_smul]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem shiftL_iota_2pi (c : ℝ) : shiftL (2 * Real.pi) (iota c) = (1 : ℝ) • iota c := by
  ext θ
  simp only [shiftL_apply, iota_apply, BoundedContinuousFunction.smul_apply, Complex.real_smul]
  push_cast
  rw [add_mul, Complex.exp_add]
  have : Complex.exp (2 * (Real.pi : ℂ) * Complex.I) = 1 := Complex.exp_two_pi_mul_I
  rw [this]; ring

theorem intCLM_shift_pi (g : A) (hg : shiftL (2 * Real.pi) g = g) :
    intCLM (shiftL Real.pi g) = intCLM g := by
  have hper : Function.Periodic g (2 * Real.pi) := fun θ => by
    have := congrArg (fun h : A => h θ) hg
    simpa using this
  simp only [intCLM_apply, shiftL_apply]
  rw [intervalIntegral.integral_comp_add_right (fun θ => g θ) Real.pi, zero_add]
  have := hper.intervalIntegral_add_eq Real.pi 0
  rw [zero_add] at this
  rw [show 2 * Real.pi + Real.pi = Real.pi + 2 * Real.pi by ring, this]

/-- **Rotation invariance of `Phi`.** -/
theorem Phi_rot (c L : ℝ) (F : A) (hF : shiftL (2 * Real.pi) F = F) (a τ : ℝ) :
    Phi c L (shiftL Real.pi F) (-a) τ = Phi c L F a τ := by
  have h1 : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have hm : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  have h2 := shift_integrand (c := c) (L := L) (d := 2 * Real.pi) (ε := 1) h1 (by simpa using shiftL_iota_2pi c) F a τ
  rw [hF, one_mul] at h2
  have hπ := shift_integrand (c := c) (L := L) (d := Real.pi) (ε := -1) hm (shiftL_iota_pi c) F a τ
  rw [neg_one_mul] at hπ
  unfold Phi
  rw [← hπ, intCLM_shift_pi _ h2]

end QuantumNLS.Local020PhiRot

#print axioms QuantumNLS.Local020PhiRot.Phi_rot
