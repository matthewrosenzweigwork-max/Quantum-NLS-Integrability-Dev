import Mathlib
import QuantumNLS.Local007Factor

/-! LOCAL-007 stage A2: the Banach-algebra calculus (algebra `ℝ →ᵇ ℂ`, functions of the contour angle).

All objects are explicit analytic expressions in `(F, a, τ) ∈ (ℝ →ᵇ ℂ) × ℝ × ℝ`:
`w = ι - a`, `P = w² - τ`, `f = F² - 4`, `H = f P⁻¹`, `Y = -H/L² - 1`, `S = L (1+Y)^{1/2}` (binomial series),
`W = Ω(f/4)` (`Ω(s) = Σ c_j s^j`, `c_j = C(-1/2, j)/(2j+1)`), `D = S W / 2`,
`K = w⁻¹ M(τ w⁻²)` (`M(x) = Σ m_j x^j`, `m_j = ∫_{-1}^{1} s^{2j} √(1-s²) ds`),
`Phi = (4/(πL)) (1/2π) ∫_0^{2π} (ι D K)(θ) dθ`.
`analyticAt_Phi`: `Phi` is real analytic at the free point `(F0, 0, 0)`, `F0(θ) = 2 cos(L c e^{iθ}/2)`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open BoundedContinuousFunction Metric Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.Local007AlgB

abbrev A := ℝ →ᵇ ℂ

/-! ### Elements -/

def iota (c : ℝ) : A :=
  ofNormedAddCommGroup (fun θ : ℝ => (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) (by fun_prop) |c|
    (fun θ => by rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, mul_one])

def iotaInv (c : ℝ) : A :=
  ofNormedAddCommGroup (fun θ : ℝ => (c : ℂ)⁻¹ * Complex.exp (-((θ : ℂ) * Complex.I))) (by fun_prop) |c|⁻¹
    (fun θ => by
      have e : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, e, Complex.norm_exp_ofReal_mul_I, mul_one])

@[simp] theorem iota_apply (c θ : ℝ) : iota c θ = (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := rfl
@[simp] theorem iotaInv_apply (c θ : ℝ) :
    iotaInv c θ = (c : ℂ)⁻¹ * Complex.exp (-((θ : ℂ) * Complex.I)) := rfl

theorem iota_mul_inv {c : ℝ} (hc : c ≠ 0) : iota c * iotaInv c = 1 := by
  ext θ
  simp only [mul_apply, iota_apply, iotaInv_apply]
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  rw [show (c : ℂ) * Complex.exp (θ * Complex.I) * ((c : ℂ)⁻¹ * Complex.exp (-(θ * Complex.I))) =
    ((c : ℂ) * (c : ℂ)⁻¹) * (Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I))) by ring,
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_inv_cancel₀ hc', mul_one]
  rfl

theorem iotaInv_mul {c : ℝ} (hc : c ≠ 0) : iotaInv c * iota c = 1 := by
  rw [mul_comm]; exact iota_mul_inv hc

/-- `ι - a` is a unit for `a = 0`. -/
def iotaUnit {c : ℝ} (hc : c ≠ 0) : Aˣ := ⟨iota c, iotaInv c, iota_mul_inv hc, iotaInv_mul hc⟩

/-! ### Analytic inverse and series sums -/

theorem analyticAt_ringInv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → A} {x : E}
    (hg : AnalyticAt ℝ g x) (u : Aˣ) (hu : g x = (u : A)) :
    AnalyticAt ℝ (fun y => Ring.inverse (g y)) x := by
  have h := (analyticAt_inverse (𝕜 := ℝ) u)
  rw [← hu] at h
  exact h.comp hg

theorem ofScalars_norm_eq (c : ℕ → ℝ) (n : ℕ) :
    ‖FormalMultilinearSeries.ofScalars A c n‖ = ‖c n‖ :=
  by rw [FormalMultilinearSeries.ofScalars_norm]

theorem radius_ofScalars_ge {c d : ℕ → ℝ} (h : ∀ n, |c n| ≤ |d n|) :
    (FormalMultilinearSeries.ofScalars ℝ d).radius ≤ (FormalMultilinearSeries.ofScalars A c).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨C, -, hC⟩ := (FormalMultilinearSeries.ofScalars ℝ d).norm_mul_pow_le_of_lt_radius hr
  refine FormalMultilinearSeries.le_radius_of_bound _ C fun n => ?_
  rw [ofScalars_norm_eq]
  have := hC n
  rw [FormalMultilinearSeries.ofScalars_norm] at this
  exact (mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using h n) (by positivity)).trans this

theorem hasFPowerSeriesOnBall_sum {p : FormalMultilinearSeries ℝ A A} (h : 1 ≤ p.radius) :
    HasFPowerSeriesOnBall p.sum p 0 1 :=
  ⟨h, one_pos, fun {y} hy => by
    rw [zero_add]
    exact p.hasSum (lt_of_lt_of_le hy h)⟩

theorem analyticAt_sum_of_norm {p : FormalMultilinearSeries ℝ A A} (h : 1 ≤ p.radius) {y : A}
    (hy : ‖y‖ < 1) : AnalyticAt ℝ p.sum y := by
  refine (hasFPowerSeriesOnBall_sum h).analyticAt_of_mem ?_
  rw [Metric.mem_eball, edist_zero_right]
  have : ((‖y‖₊ : ℝ≥0) : ℝ≥0∞) < 1 := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 hy
  exact this

/-! ### The series -/

def cOm (j : ℕ) : ℝ := Ring.choose (-1 / 2 : ℝ) j / (2 * j + 1)

def cM (j : ℕ) : ℝ := ∫ s in (-1 : ℝ)..1, s ^ (2 * j) * Real.sqrt (1 - s ^ 2)

theorem radius_Om : 1 ≤ (FormalMultilinearSeries.ofScalars A cOm).radius := by
  have h1 : 1 ≤ (binomialSeries ℝ (-1 / 2 : ℝ)).radius := binomialSeries_radius_ge_one
  refine h1.trans (radius_ofScalars_ge (c := cOm) (d := fun j => Ring.choose (-1 / 2 : ℝ) j) ?_)
  intro n
  unfold cOm
  rw [abs_div]
  have : (1 : ℝ) ≤ |(2 * (n : ℝ) + 1)| := by
    rw [abs_of_nonneg (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact div_le_self (abs_nonneg _) this

theorem radius_binom : 1 ≤ (binomialSeries A (1 / 2 : ℝ)).radius := by
  have h1 : 1 ≤ (binomialSeries ℝ (1 / 2 : ℝ)).radius := binomialSeries_radius_ge_one
  exact h1.trans (radius_ofScalars_ge (c := fun j => Ring.choose (1 / 2 : ℝ) j)
    (d := fun j => Ring.choose (1 / 2 : ℝ) j) (fun n => le_rfl))

theorem abs_cM_le (j : ℕ) : |cM j| ≤ Real.pi / 2 := by
  have hint : ∀ s ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ s ^ (2 * j) * Real.sqrt (1 - s ^ 2) := fun s _ => mul_nonneg (by rw [pow_mul]; positivity) (Real.sqrt_nonneg _)
  have h0 : 0 ≤ cM j := intervalIntegral.integral_nonneg (by norm_num) hint
  rw [abs_of_nonneg h0, cM]
  have := intervalIntegral.integral_mono_on (a := (-1 : ℝ)) (b := 1) (by norm_num)
    (f := fun s => s ^ (2 * j) * Real.sqrt (1 - s ^ 2)) (g := fun s => Real.sqrt (1 - s ^ 2))
    (Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by fun_prop) _ _) (Continuous.intervalIntegrable (μ := MeasureTheory.volume) (by fun_prop) _ _)
    (fun s hs => by
      have h1 : s ^ (2 * j) ≤ 1 := by
        rw [pow_mul]; exact pow_le_one₀ (by positivity) (by nlinarith [hs.1, hs.2])
      nlinarith [Real.sqrt_nonneg (1 - s ^ 2)])
  rw [integral_sqrt_one_sub_sq] at this
  exact this

theorem radius_M : 1 ≤ (FormalMultilinearSeries.ofScalars A cM).radius := by
  have : ((1 : ℝ≥0) : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars A cM).radius :=
    FormalMultilinearSeries.le_radius_of_bound _ (Real.pi / 2) fun n => by
      rw [ofScalars_norm_eq]; simpa [Real.norm_eq_abs] using abs_cM_le n
  simpa using this

/-! ### The expressions -/

variable (c L : ℝ)

def wEl (a : ℝ) : A := iota c - a • (1 : A)
def PEl (a τ : ℝ) : A := wEl c a * wEl c a - τ • (1 : A)
def fEl (F : A) : A := F * F - (4 : ℝ) • (1 : A)
def HEl (F : A) (a τ : ℝ) : A := fEl F * Ring.inverse (PEl c a τ)
def YEl (F : A) (a τ : ℝ) : A := (-(L ^ 2)⁻¹) • HEl c F a τ - 1
def SEl (F : A) (a τ : ℝ) : A := L • (binomialSeries A (1 / 2 : ℝ)).sum (YEl c L F a τ)
def WEl (F : A) : A := (FormalMultilinearSeries.ofScalars A cOm).sum ((1 / 4 : ℝ) • fEl F)
def DEl (F : A) (a τ : ℝ) : A := (1 / 2 : ℝ) • (SEl c L F a τ * WEl F)
def KEl (a τ : ℝ) : A :=
  Ring.inverse (wEl c a) *
    (FormalMultilinearSeries.ofScalars A cM).sum (τ • (Ring.inverse (wEl c a) * Ring.inverse (wEl c a)))

/-- Integration over the angle as a bounded real-linear functional. -/
def intCLM : A →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ
      map_add' := fun g h => by
        simp only [BoundedContinuousFunction.add_apply]
        exact intervalIntegral.integral_add (g.continuous.intervalIntegrable _ _)
          (h.continuous.intervalIntegrable _ _)
      map_smul' := fun a g => by
        simp only [BoundedContinuousFunction.smul_apply, RingHom.id_apply]
        exact intervalIntegral.integral_smul a _ }
    (2 * Real.pi) (fun g => by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2 * Real.pi)
        (f := fun θ => g θ) (C := ‖g‖) (fun θ _ => g.norm_coe_le_norm θ)
      rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at this
      calc _ ≤ ‖g‖ * (2 * Real.pi) := this
        _ = 2 * Real.pi * ‖g‖ := by ring)

theorem intCLM_apply (g : A) : intCLM g = ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ := rfl

def Phi (F : A) (a τ : ℝ) : ℂ :=
  ((4 / (Real.pi * L) * (1 / (2 * Real.pi)) : ℝ) : ℂ) * intCLM (iota c * DEl c L F a τ * KEl c a τ)

/-- The free element `F0(θ) = 2 cos(L c e^{iθ} / 2)`. -/
def F0 : A :=
  ofNormedAddCommGroup (fun θ : ℝ => 2 * Complex.cos ((L : ℂ) * ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) / 2))
    (by fun_prop) (2 * Real.exp (|L| * |c|)) (fun θ => by
      rw [Complex.two_cos]
      refine (norm_add_le _ _).trans ?_
      have hn : ‖(L : ℂ) * ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) / 2‖ ≤ |L| * |c| := by
        rw [norm_div, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Complex.norm_real,
          Complex.norm_two, Real.norm_eq_abs, Real.norm_eq_abs]
        have : 0 ≤ |L| * |c| := by positivity
        linarith
      have h1 := Complex.norm_exp_le_exp_norm ((L : ℂ) * ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) / 2 * Complex.I)
      have h2 := Complex.norm_exp_le_exp_norm (-((L : ℂ) * ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) / 2) * Complex.I)
      rw [norm_mul, Complex.norm_I, mul_one] at h1
      rw [norm_mul, Complex.norm_I, mul_one, norm_neg] at h2
      have e : Real.exp ‖(L : ℂ) * ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) / 2‖ ≤ Real.exp (|L| * |c|) :=
        Real.exp_le_exp.2 hn
      linarith)

theorem F0_apply (θ : ℝ) :
    F0 c L θ = 2 * Complex.cos ((L : ℂ) * ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) / 2) := rfl


section main
variable {c L}

theorem pinv0 (hc : c ≠ 0) : Ring.inverse (PEl c 0 0) = iotaInv c * iotaInv c := by
  have hPe : PEl c 0 0 = iota c * iota c := by simp [PEl, wEl]
  set u := iotaUnit hc with hu
  have h1 : iota c * iota c = ((u * u : Aˣ) : A) := by simp [hu, iotaUnit]
  rw [hPe, h1, Ring.inverse_unit, mul_inv_rev]
  rfl

theorem winv0 (hc : c ≠ 0) : Ring.inverse (wEl c 0) = iotaInv c := by
  have h1 : wEl c 0 = ((iotaUnit hc : Aˣ) : A) := by simp [wEl, iotaUnit]
  rw [h1, Ring.inverse_unit]; rfl

theorem xi_mul_inv (hc : c ≠ 0) (θ : ℝ) :
    (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * ((c : ℂ)⁻¹ * Complex.exp (-((θ : ℂ) * Complex.I))) = 1 := by
  have := congrArg (fun f : A => f θ) (iota_mul_inv hc)
  simpa using this

theorem Y0_apply (hc : c ≠ 0) (hL : 0 < L) (θ : ℝ) :
    YEl c L (F0 c L) 0 0 θ =
      -(Local007Factor.H0 L ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) + (L : ℂ) ^ 2) / (L : ℂ) ^ 2 := by
  set ξ : ℂ := (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) with hξ
  set ξi : ℂ := (c : ℂ)⁻¹ * Complex.exp (-((θ : ℂ) * Complex.I)) with hξi
  have hprod : ξ * ξi = 1 := xi_mul_inv hc θ
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  have hf0 := Local007Factor.f0_eq L ξ
  have e1 : YEl c L (F0 c L) 0 0 θ = ((-(L ^ 2)⁻¹ : ℝ) : ℂ) *
      ((F0 c L θ * F0 c L θ - ((4 : ℝ) : ℂ) * 1) * (ξi * ξi)) - 1 := by
    rw [YEl, HEl, fEl, pinv0 hc]
    rfl
  have h4 : ((4 : ℝ) : ℂ) * 1 = 4 := by norm_num
  rw [h4] at e1
  rw [e1, F0_apply]
  have hF : (2 * Complex.cos ((L : ℂ) * ξ / 2)) * (2 * Complex.cos ((L : ℂ) * ξ / 2)) - 4 =
      ξ ^ 2 * Local007Factor.H0 L ξ := by rw [← hf0]; ring
  rw [hF]
  have h2 : ξ ^ 2 * Local007Factor.H0 L ξ * (ξi * ξi) = Local007Factor.H0 L ξ := by
    have : ξ ^ 2 * (ξi * ξi) = 1 := by
      calc ξ ^ 2 * (ξi * ξi) = (ξ * ξi) * (ξ * ξi) := by ring
        _ = 1 := by rw [hprod]; norm_num
    calc ξ ^ 2 * Local007Factor.H0 L ξ * (ξi * ξi) = (ξ ^ 2 * (ξi * ξi)) * Local007Factor.H0 L ξ := by ring
      _ = _ := by rw [this, one_mul]
  rw [h2]
  push_cast
  field_simp
  ring

theorem Y0_norm (hc : 0 < c) (hL : 0 < L) (hcL : c * L ≤ 1 / 8) : ‖YEl c L (F0 c L) 0 0‖ < 1 := by
  have : ‖YEl c L (F0 c L) 0 0‖ ≤ 1 / 100 := by
    refine (BoundedContinuousFunction.norm_le (by norm_num)).2 fun θ => ?_
    rw [Y0_apply hc.ne' hL θ, norm_div, norm_neg]
    have hξ : ‖(c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ 1 / (4 * L) := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hc.le, mul_one]
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h1 := Local007Factor.norm_H0_add hL hξ
    have h2 : ‖(L : ℂ) ^ 2‖ = L ^ 2 := by rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hL.le]
    rw [h2, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem fEl_apply (hc : c ≠ 0) (hL : 0 < L) (θ : ℝ) :
    fEl (F0 c L) θ = ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 *
      Local007Factor.H0 L ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hf0 := Local007Factor.f0_eq L ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
  have e : fEl (F0 c L) θ = F0 c L θ * F0 c L θ - ((4 : ℝ) : ℂ) * 1 := rfl
  rw [e, F0_apply, ← hf0]
  push_cast; ring

theorem fEl_norm (hc : 0 < c) (hL : 0 < L) (hcL : c * L ≤ 1 / 8) :
    ‖(1 / 4 : ℝ) • fEl (F0 c L)‖ < 1 := by
  have : ‖(1 / 4 : ℝ) • fEl (F0 c L)‖ ≤ 1 / 100 := by
    refine (BoundedContinuousFunction.norm_le (by norm_num)).2 fun θ => ?_
    simp only [BoundedContinuousFunction.smul_apply]
    rw [fEl_apply hc.ne' hL θ, norm_smul, Real.norm_eq_abs]
    have hξ : ‖(c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = c := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hc.le, mul_one]
    have hξ' : c ≤ 1 / (4 * L) := by rw [le_div_iff₀ (by positivity)]; nlinarith
    have h1 := Local007Factor.norm_H0_add hL (hξ.le.trans hξ')
    have h2 : ‖(L : ℂ) ^ 2‖ = L ^ 2 := by rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hL.le]
    have h3 : ‖Local007Factor.H0 L ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ (101 / 100) * L ^ 2 := by
      have h4 : ‖Local007Factor.H0 L ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
          ‖Local007Factor.H0 L ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) + (L : ℂ) ^ 2‖ + ‖(L : ℂ) ^ 2‖ := by
        calc _ = ‖(Local007Factor.H0 L ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) + (L : ℂ) ^ 2) - (L : ℂ) ^ 2‖ := by
              rw [add_sub_cancel_right]
          _ ≤ _ := norm_sub_le _ _
      rw [h2] at h4; linarith
    rw [norm_mul, norm_pow, hξ]
    have hc2 : c ^ 2 * L ^ 2 ≤ 1 / 64 := by nlinarith [mul_pos hc hL]
    have : c ^ 2 * ‖Local007Factor.H0 L ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ (101 / 100) * (1 / 64) := by
      calc _ ≤ c ^ 2 * ((101 / 100) * L ^ 2) := by gcongr
        _ = (101 / 100) * (c ^ 2 * L ^ 2) := by ring
        _ ≤ _ := by gcongr
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    nlinarith
  linarith

theorem analyticAt_Phi (hc : 0 < c) (hL : 0 < L) (hcL : c * L ≤ 1 / 8) :
    AnalyticAt ℝ (fun p : A × ℝ × ℝ => Phi c L p.1 p.2.1 p.2.2) (F0 c L, 0, 0) := by
  have hc0 : c ≠ 0 := hc.ne'
  set p0 : A × ℝ × ℝ := (F0 c L, 0, 0) with hp0
  have hF : AnalyticAt ℝ (fun p : A × ℝ × ℝ => p.1) p0 := analyticAt_fst
  have ha : AnalyticAt ℝ (fun p : A × ℝ × ℝ => p.2.1) p0 :=
    (analyticAt_fst (p := p0.2)).comp analyticAt_snd
  have hτ : AnalyticAt ℝ (fun p : A × ℝ × ℝ => p.2.2) p0 :=
    (analyticAt_snd (p := p0.2)).comp analyticAt_snd
  have hw : AnalyticAt ℝ (fun p : A × ℝ × ℝ => wEl c p.2.1) p0 := by unfold wEl; fun_prop
  have hP : AnalyticAt ℝ (fun p : A × ℝ × ℝ => PEl c p.2.1 p.2.2) p0 := by
    unfold PEl; fun_prop
  have hPi : AnalyticAt ℝ (fun p : A × ℝ × ℝ => Ring.inverse (PEl c p.2.1 p.2.2)) p0 := by
    refine analyticAt_ringInv hP (iotaUnit hc0 * iotaUnit hc0) ?_
    have : PEl c 0 0 = iota c * iota c := by simp [PEl, wEl]
    simp only [hp0]; rw [this]; simp [iotaUnit]
  have hf : AnalyticAt ℝ (fun p : A × ℝ × ℝ => fEl p.1) p0 := by unfold fEl; fun_prop
  have hH : AnalyticAt ℝ (fun p : A × ℝ × ℝ => HEl c p.1 p.2.1 p.2.2) p0 := by
    unfold HEl; exact hf.fun_mul hPi
  have hY : AnalyticAt ℝ (fun p : A × ℝ × ℝ => YEl c L p.1 p.2.1 p.2.2) p0 := by
    unfold YEl; fun_prop
  have hbs : AnalyticAt ℝ (binomialSeries A (1 / 2 : ℝ)).sum (YEl c L (F0 c L) 0 0) :=
    analyticAt_sum_of_norm radius_binom (Y0_norm hc hL hcL)
  have hS : AnalyticAt ℝ (fun p : A × ℝ × ℝ => SEl c L p.1 p.2.1 p.2.2) p0 := by
    unfold SEl; exact (hbs.comp_of_eq hY rfl).fun_const_smul
  have hWs : AnalyticAt ℝ (FormalMultilinearSeries.ofScalars A cOm).sum ((1 / 4 : ℝ) • fEl (F0 c L)) :=
    analyticAt_sum_of_norm radius_Om (fEl_norm hc hL hcL)
  have hW : AnalyticAt ℝ (fun p : A × ℝ × ℝ => WEl p.1) p0 := by
    unfold WEl; exact hWs.comp_of_eq hf.fun_const_smul rfl
  have hD : AnalyticAt ℝ (fun p : A × ℝ × ℝ => DEl c L p.1 p.2.1 p.2.2) p0 := by
    unfold DEl; exact (hS.fun_mul hW).fun_const_smul
  have hwi : AnalyticAt ℝ (fun p : A × ℝ × ℝ => Ring.inverse (wEl c p.2.1)) p0 := by
    refine analyticAt_ringInv hw (iotaUnit hc0) ?_
    simp [hp0, wEl, iotaUnit]
  have hx : AnalyticAt ℝ (fun p : A × ℝ × ℝ => p.2.2 • (Ring.inverse (wEl c p.2.1) * Ring.inverse (wEl c p.2.1))) p0 :=
    hτ.fun_smul (hwi.fun_mul hwi)
  have hMs : AnalyticAt ℝ (FormalMultilinearSeries.ofScalars A cM).sum
      ((0 : ℝ) • (Ring.inverse (wEl c 0) * Ring.inverse (wEl c 0))) :=
    analyticAt_sum_of_norm radius_M (by simp)
  have hK : AnalyticAt ℝ (fun p : A × ℝ × ℝ => KEl c p.2.1 p.2.2) p0 := by
    unfold KEl; exact hwi.fun_mul (hMs.comp_of_eq hx (by simp [hp0]))
  have hI : AnalyticAt ℝ (fun p : A × ℝ × ℝ => iota c * DEl c L p.1 p.2.1 p.2.2 * KEl c p.2.1 p.2.2) p0 :=
    (analyticAt_const.fun_mul hD).fun_mul hK
  unfold Phi
  exact analyticAt_const.fun_mul ((intCLM.analyticAt _).comp hI)

end main

end QuantumNLS.Local007AlgB
#print axioms QuantumNLS.Local007AlgB.analyticAt_Phi
#print axioms QuantumNLS.Local007AlgB.radius_M
