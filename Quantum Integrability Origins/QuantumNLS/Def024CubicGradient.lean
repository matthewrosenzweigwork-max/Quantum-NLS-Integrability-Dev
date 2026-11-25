import QuantumNLS.Def024Gradient

/-!
# DEF-024, stage C1: the order-2 Hamiltonian `Re I_3` (cubic NLS energy) and its DEF-015 gradient

Source: `DEFINITIONS_LEDGER.md` DEF-024 (`chapters/definitions.tex:145-149`: "the joint classical
flow is the composition of the Hamiltonian flows of `I_{r+1}^{(κ)}`"); DEF-022 (`I_3 = ∫(|∂ₓu|² +
κ|u|⁴)`, proved as `ClassicalCharges.charge_three`); DEF-023 (`iu_t = −u_xx + 2κ|u|²u`, the same
coupling convention `2κ`); the gradient convention `HierarchyFlow.IsSmoothGradient`
(`dF(u)[h] = 2 Re⟨g, h⟩`, `⟨f, g⟩ = ∫_0^L \bar f g`).

Index convention (checked against `HierarchyFlow.hamiltonian`): `hamiltonian L κ r = Re I_{r+1}`,
so the order-`r = 2` Hamiltonian is `Re I_3`.

What is proved (smooth periodic data only; no positivity of `L` needed):
* `cub_hamiltonian`: `Re I_3(u) = ∫₀^L (|∂ₓu|² + κ|u|⁴)` on smooth periodic `u`;
* `cubicGrad κ u = −∂ₓ²u + 2κ|u|²u` is smooth and periodic (`cub_smoothPeriodic_grad`);
* `cub_gradient`: `IsSmoothGradient L (hamiltonian L κ 2) u (cubicGrad κ u)` for smooth periodic `u`;
* `cub_ode_coeff`: for `g = cubicGrad κ u`, `i · (−i g) = g`, so the frozen Hamiltonian equation
  `∂_s Φ = −i ∇F(Φ)` reads `i ∂_s Φ = −∂ₓ²Φ + 2κ|Φ|²Φ`, the DEF-023 equation.

Not proved here: existence, smoothness in time, or uniqueness of any order-2 flow (see
`Def024CubicClassical`, which isolates exactly what is missing).
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate ContDiff
open MeasureTheory

namespace QuantumNLS.Def024CubicGradient

open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow QuantumNLS.Def024Gradient

variable {L : ℝ}

/-- The candidate DEF-015 gradient of `Re I_3` (cubic NLS): `g = −∂ₓ²u + 2κ|u|²u`. -/
def cubicGrad (κ : ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -(deriv (deriv u) x) + (2 * κ : ℂ) * ((‖u x‖ ^ 2 : ℝ) : ℂ) * u x

/-- The derivative of a smooth periodic profile is smooth periodic. -/
theorem cub_smoothPeriodic_deriv {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    SmoothPeriodic L (deriv u) :=
  ⟨(contDiff_infty_iff_deriv.mp hu.smooth).2, WeakDerivatives.periodic_deriv hu.periodic⟩

/-- **Energy**: `Re I_3(u) = ∫₀^L (|∂ₓu|² + κ|u|⁴)` on smooth periodic data. -/
theorem cub_hamiltonian (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    hamiltonian L κ 2 u = ∫ x in (0 : ℝ)..L, (‖deriv u x‖ ^ 2 + κ * ‖u x‖ ^ 4) := by
  unfold hamiltonian
  rw [show (2 + 1 : ℕ) = 3 from rfl, charge_three L κ hu, Complex.ofReal_re]

/-- The cubic gradient is smooth and periodic on smooth periodic data. -/
theorem cub_smoothPeriodic_grad (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    SmoothPeriodic L (cubicGrad κ u) := by
  have hd1 := cub_smoothPeriodic_deriv hu
  have hd2 := cub_smoothPeriodic_deriv hd1
  have hP : ContDiff ℝ ∞ (fun x => ((‖u x‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (ContDiff.norm_sq ℝ hu.smooth)
  refine ⟨?_, fun x => ?_⟩
  · unfold cubicGrad
    exact hd2.smooth.neg.add ((contDiff_const.mul hP).mul hu.smooth)
  · simp only [cubicGrad, hd2.periodic x, hu.periodic x]

/-! ### Pointwise expansion along `u + εh` (real `ε`) -/

/-- `|z + εw|² = |z|² + ε·2Re(z̄w) + ε²|w|²`. -/
theorem cub_sq_add (z w : ℂ) (ε : ℝ) :
    ‖z + (ε : ℂ) * w‖ ^ 2 = ‖z‖ ^ 2 + ε * (2 * (conj z * w).re) + ε ^ 2 * ‖w‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- `|z + εw|⁴` as a polynomial in `ε` of degree four. -/
theorem cub_quartic_add (z w : ℂ) (ε : ℝ) :
    ‖z + (ε : ℂ) * w‖ ^ 4 = (‖z‖ ^ 2) ^ 2 + ε * (2 * ‖z‖ ^ 2 * (2 * (conj z * w).re))
      + ε ^ 2 * ((2 * (conj z * w).re) ^ 2 + 2 * ‖z‖ ^ 2 * ‖w‖ ^ 2)
      + ε ^ 3 * (2 * (2 * (conj z * w).re) * ‖w‖ ^ 2) + ε ^ 4 * (‖w‖ ^ 2) ^ 2 := by
  have h := cub_sq_add z w ε
  have h4 : ‖z + (ε : ℂ) * w‖ ^ 4 = (‖z + (ε : ℂ) * w‖ ^ 2) ^ 2 := by ring
  rw [h4, h]
  ring

/-- Coefficient of `ε⁰` in the energy integrand along `u + εh`. -/
def cubA (κ : ℝ) (u : ℝ → ℂ) (x : ℝ) : ℝ := ‖deriv u x‖ ^ 2 + κ * ‖u x‖ ^ 4

/-- Coefficient of `ε¹`. -/
def cubB (κ : ℝ) (u h : ℝ → ℂ) (x : ℝ) : ℝ :=
  2 * (conj (deriv u x) * deriv h x).re + κ * (2 * ‖u x‖ ^ 2 * (2 * (conj (u x) * h x).re))

/-- Coefficient of `ε²`. -/
def cubC (κ : ℝ) (u h : ℝ → ℂ) (x : ℝ) : ℝ :=
  ‖deriv h x‖ ^ 2 + κ * ((2 * (conj (u x) * h x).re) ^ 2 + 2 * ‖u x‖ ^ 2 * ‖h x‖ ^ 2)

/-- Coefficient of `ε³`. -/
def cubD (κ : ℝ) (u h : ℝ → ℂ) (x : ℝ) : ℝ :=
  κ * (2 * (2 * (conj (u x) * h x).re) * ‖h x‖ ^ 2)

/-- Coefficient of `ε⁴`. -/
def cubE (κ : ℝ) (h : ℝ → ℂ) (x : ℝ) : ℝ := κ * (‖h x‖ ^ 2) ^ 2

/-- The energy integrand along `u + εh` is the degree-four polynomial with coefficients above. -/
theorem cub_integrand (κ ε : ℝ) {u h : ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h)
    (x : ℝ) :
    ‖deriv (fun y => u y + (ε : ℂ) * h y) x‖ ^ 2 + κ * ‖u x + (ε : ℂ) * h x‖ ^ 4 =
      cubA κ u x + ε * cubB κ u h x + ε ^ 2 * cubC κ u h x + ε ^ 3 * cubD κ u h x
        + ε ^ 4 * cubE κ h x := by
  have hu1 : DifferentiableAt ℝ u x := ((contDiff_infty_iff_deriv.mp hu).1) x
  have hh1 : DifferentiableAt ℝ h x := ((contDiff_infty_iff_deriv.mp hh).1) x
  have hd : deriv (fun y => u y + (ε : ℂ) * h y) x = deriv u x + (ε : ℂ) * deriv h x :=
    (hu1.hasDerivAt.add (hh1.hasDerivAt.const_mul (ε : ℂ))).deriv
  rw [hd, cub_sq_add, cub_quartic_add]
  unfold cubA cubB cubC cubD cubE
  ring

/-- **Polynomial differentiation under the integral**: the `ε`-derivative at `0` of a degree-four
polynomial with continuous coefficients is the integral of the linear coefficient. -/
theorem cub_hasDerivAt_quartic {a b c d e : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) (hd : Continuous d) (he : Continuous e) :
    HasDerivAt (fun ε : ℝ => ∫ x in (0 : ℝ)..L,
        (a x + ε * b x + ε ^ 2 * c x + ε ^ 3 * d x + ε ^ 4 * e x))
      (∫ x in (0 : ℝ)..L, b x) 0 := by
  have hfun : (fun ε : ℝ => ∫ x in (0 : ℝ)..L,
      (a x + ε * b x + ε ^ 2 * c x + ε ^ 3 * d x + ε ^ 4 * e x))
      = fun ε : ℝ => (∫ x in (0 : ℝ)..L, a x) + ε * (∫ x in (0 : ℝ)..L, b x)
          + ε ^ 2 * (∫ x in (0 : ℝ)..L, c x) + ε ^ 3 * (∫ x in (0 : ℝ)..L, d x)
          + ε ^ 4 * (∫ x in (0 : ℝ)..L, e x) := by
    funext ε
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_add]
    all_goals first
      | (simp only [intervalIntegral.integral_const_mul])
      | (apply Continuous.intervalIntegrable; fun_prop)
  rw [hfun]
  have h1 := ((((hasDerivAt_const (0 : ℝ) (∫ x in (0 : ℝ)..L, a x)).add
    ((hasDerivAt_id' (0 : ℝ)).mul_const (∫ x in (0 : ℝ)..L, b x))).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (∫ x in (0 : ℝ)..L, c x))).add
    ((hasDerivAt_pow 3 (0 : ℝ)).mul_const (∫ x in (0 : ℝ)..L, d x))).add
    ((hasDerivAt_pow 4 (0 : ℝ)).mul_const (∫ x in (0 : ℝ)..L, e x))
  convert h1 using 1
  simp

/-- The smooth periodic profile `u + εh`. -/
theorem cub_smoothPeriodic_add_smul {u h : ℝ → ℂ} (hu : SmoothPeriodic L u)
    (hh : SmoothPeriodic L h) (ε : ℝ) : SmoothPeriodic L (fun x => u x + (ε : ℂ) * h x) :=
  ⟨hu.smooth.add (contDiff_const.mul hh.smooth), fun x => by
    simp only [hu.periodic x, hh.periodic x]⟩

/-- Integration by parts for the linear term: `∫ 2Re(∂ₓū ∂ₓh) = −∫ 2Re(∂ₓ²ū h)`. -/
theorem cub_ibp_re {u h : ℝ → ℂ} (hu : SmoothPeriodic L u) (hh : SmoothPeriodic L h)
    (hcu : Continuous (deriv u)) (hch : Continuous (deriv h))
    (hcdd : Continuous (deriv (deriv u))) (hch0 : Continuous h) :
    ∫ x in (0 : ℝ)..L, 2 * (conj (deriv u x) * deriv h x).re
      = -∫ x in (0 : ℝ)..L, 2 * (conj (deriv (deriv u) x) * h x).re := by
  have ibp := integral_conj_mul_deriv (cub_smoothPeriodic_deriv hu) hh
  have hre := congrArg Complex.re ibp
  have c1 : Continuous (fun x => conj (deriv u x) * deriv h x) :=
    (Complex.continuous_conj.comp hcu).mul hch
  have c2 : Continuous (fun x => conj (deriv (deriv u) x) * h x) :=
    (Complex.continuous_conj.comp hcdd).mul hch0
  rw [Complex.neg_re, re_integral c1, re_integral c2] at hre
  simp only [intervalIntegral.integral_const_mul]
  rw [hre]
  ring

/-- **The order-2 DEF-015 gradient**: on smooth periodic `u`, `−∂ₓ²u + 2κ|u|²u` is a gradient of
`Re I_3` in the frozen `IsSmoothGradient` sense. -/
theorem cub_gradient (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    IsSmoothGradient L (hamiltonian L κ 2) u (cubicGrad κ u) := by
  refine ⟨cub_smoothPeriodic_grad κ hu, fun h hh => ?_⟩
  have hcu : Continuous u := hu.smooth.continuous
  have hch0 : Continuous h := hh.smooth.continuous
  have hcdu : Continuous (deriv u) := (contDiff_infty_iff_deriv.mp hu.smooth).2.continuous
  have hcdh : Continuous (deriv h) := (contDiff_infty_iff_deriv.mp hh.smooth).2.continuous
  have hcddu : Continuous (deriv (deriv u)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hu.smooth).2).2.continuous
  have hval : (fun ε : ℝ => hamiltonian L κ 2 (fun x => u x + (ε : ℂ) * h x)) =
      fun ε : ℝ => ∫ x in (0 : ℝ)..L, (cubA κ u x + ε * cubB κ u h x + ε ^ 2 * cubC κ u h x
        + ε ^ 3 * cubD κ u h x + ε ^ 4 * cubE κ h x) := by
    funext ε
    rw [cub_hamiltonian κ (cub_smoothPeriodic_add_smul hu hh ε)]
    exact intervalIntegral.integral_congr (fun x _ => cub_integrand κ ε hu.smooth hh.smooth x)
  have hcA : Continuous (cubA κ u) := by unfold cubA; fun_prop
  have hcB : Continuous (cubB κ u h) := by unfold cubB; fun_prop
  have hcC : Continuous (cubC κ u h) := by unfold cubC; fun_prop
  have hcD : Continuous (cubD κ u h) := by unfold cubD; fun_prop
  have hcE : Continuous (cubE κ h) := by unfold cubE; fun_prop
  rw [hval]
  convert cub_hasDerivAt_quartic (L := L) hcA hcB hcC hcD hcE using 1
  -- the linear coefficient is `2 Re⟨g, h⟩`
  have hcontG : Continuous (fun x => conj (cubicGrad κ u x) * h x) :=
    (Complex.continuous_conj.comp (cub_smoothPeriodic_grad κ hu).smooth.continuous).mul hch0
  have hpt : ∀ x, 2 * (conj (cubicGrad κ u x) * h x).re
      = -(2 * (conj (deriv (deriv u) x) * h x).re)
        + κ * (2 * ‖u x‖ ^ 2 * (2 * (conj (u x) * h x).re)) := by
    intro x
    have hc : (2 * κ : ℂ) * ((‖u x‖ ^ 2 : ℝ) : ℂ) = (((2 * κ * ‖u x‖ ^ 2 : ℝ)) : ℂ) := by
      push_cast; ring
    simp only [cubicGrad]
    rw [hc]
    simp only [map_add, map_neg, map_mul, Complex.conj_ofReal, add_mul, neg_mul, mul_assoc,
      Complex.add_re, Complex.neg_re, Complex.re_ofReal_mul]
    ring
  have hN : Continuous (fun x => 2 * (conj (deriv (deriv u) x) * h x).re) := by
    have : Continuous (fun x => conj (deriv (deriv u) x) * h x) :=
      (Complex.continuous_conj.comp hcddu).mul hch0
    fun_prop
  have hK : Continuous (fun x => 2 * (conj (deriv u x) * deriv h x).re) := by
    have : Continuous (fun x => conj (deriv u x) * deriv h x) :=
      (Complex.continuous_conj.comp hcdu).mul hcdh
    fun_prop
  have hX : Continuous (fun x => κ * (2 * ‖u x‖ ^ 2 * (2 * (conj (u x) * h x).re))) := by
    have : Continuous (fun x => conj (u x) * h x) := (Complex.continuous_conj.comp hcu).mul hch0
    fun_prop
  have hibp := cub_ibp_re hu hh hcdu hcdh hcddu hch0
  have hKi : IntervalIntegrable (fun x => 2 * (conj (deriv u x) * deriv h x).re)
      MeasureTheory.volume 0 L := hK.intervalIntegrable _ _
  have hXi : IntervalIntegrable (fun x => κ * (2 * ‖u x‖ ^ 2 * (2 * (conj (u x) * h x).re)))
      MeasureTheory.volume 0 L := hX.intervalIntegrable _ _
  have hNn : Continuous (fun x => -(2 * (conj (deriv (deriv u) x) * h x).re)) := hN.neg
  have hNni : IntervalIntegrable (fun x => -(2 * (conj (deriv (deriv u) x) * h x).re))
      MeasureTheory.volume 0 L := hNn.intervalIntegrable _ _
  have hsplitB : (∫ x in (0 : ℝ)..L, cubB κ u h x) =
      (∫ x in (0 : ℝ)..L, 2 * (conj (deriv u x) * deriv h x).re)
        + (∫ x in (0 : ℝ)..L, κ * (2 * ‖u x‖ ^ 2 * (2 * (conj (u x) * h x).re))) := by
    unfold cubB
    exact intervalIntegral.integral_add hKi hXi
  have hA : 2 * (pair L (cubicGrad κ u) h).re
      = ∫ x in (0 : ℝ)..L, 2 * (conj (cubicGrad κ u x) * h x).re := by
    unfold pair
    rw [re_integral hcontG, intervalIntegral.integral_const_mul]
  rw [hA]
  calc (∫ x in (0 : ℝ)..L, 2 * (conj (cubicGrad κ u x) * h x).re)
      = ∫ x in (0 : ℝ)..L, (-(2 * (conj (deriv (deriv u) x) * h x).re)
          + κ * (2 * ‖u x‖ ^ 2 * (2 * (conj (u x) * h x).re))) :=
        intervalIntegral.integral_congr (fun x _ => hpt x)
    _ = (∫ x in (0 : ℝ)..L, -(2 * (conj (deriv (deriv u) x) * h x).re))
          + (∫ x in (0 : ℝ)..L, κ * (2 * ‖u x‖ ^ 2 * (2 * (conj (u x) * h x).re))) := by
        rw [intervalIntegral.integral_add hNni hXi]
    _ = -(∫ x in (0 : ℝ)..L, 2 * (conj (deriv (deriv u) x) * h x).re)
          + (∫ x in (0 : ℝ)..L, κ * (2 * ‖u x‖ ^ 2 * (2 * (conj (u x) * h x).re))) := by
        rw [intervalIntegral.integral_neg]
    _ = (∫ x in (0 : ℝ)..L, 2 * (conj (deriv u x) * deriv h x).re)
          + (∫ x in (0 : ℝ)..L, κ * (2 * ‖u x‖ ^ 2 * (2 * (conj (u x) * h x).re))) := by
        rw [hibp]
    _ = ∫ x in (0 : ℝ)..L, cubB κ u h x := hsplitB.symm

/-- **Frozen equation**: for `g = cubicGrad κ u`, `i · (−i g) = g`; so `∂_s Φ = −i ∇F(Φ)` is
`i ∂_s Φ = −∂ₓ²Φ + 2κ|Φ|²Φ`, the DEF-023 equation with the same coefficient `2κ`. -/
theorem cub_ode_coeff (κ : ℝ) (u : ℝ → ℂ) (x : ℝ) :
    Complex.I * (-Complex.I * cubicGrad κ u x) = cubicGrad κ u x := by
  linear_combination (-(cubicGrad κ u x)) * Complex.I_mul_I

#print axioms cub_hamiltonian
#print axioms cub_smoothPeriodic_grad
#print axioms cub_gradient
#print axioms cub_ode_coeff

end QuantumNLS.Def024CubicGradient
