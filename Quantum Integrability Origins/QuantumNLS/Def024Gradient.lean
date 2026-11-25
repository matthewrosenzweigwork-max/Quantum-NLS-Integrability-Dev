import QuantumNLS.HierarchyFlow

/-!
# DEF-024, stage D1: the DEF-015 gradients of the order-0 and order-1 Hamiltonians

Source: `DEFINITIONS_LEDGER.md` DEF-024 (`chapters/definitions.tex:145-149`), DEF-022
(`I_1 = ‖u‖₂²`, `I_2 = ∫ ū (−i ∂ₓ u)`), DEF-015 gradient convention as frozen in
`HierarchyFlow.IsSmoothGradient`: `dF(u)[h] = 2 Re⟨g, h⟩`, `⟨f, g⟩ = ∫_0^L \bar f g`.

The source theorem `thm:hierarchy` (R-7B122087) covers orders `r ≥ 2`; DEF-024 uses every
nonnegative order, so the orders `r = 0` (Hamiltonian `Re I_1`) and `r = 1` (Hamiltonian
`Re I_2`) are supplied here directly from the frozen definitions.

What is proved (no hypothesis beyond smoothness/periodicity; `L > 0` only for uniqueness):
* `gradient_unique`: a smooth periodic DEF-015 gradient is unique;
* `gradient_zero`: `∇ (Re I_1)(u) = u`;
* `gradient_one`: `∇ (Re I_2)(u) = −i ∂ₓ u`;
* `integral_conj_mul_deriv`: integration by parts on the circle.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate ContDiff
open MeasureTheory

namespace QuantumNLS.Def024Gradient

open QuantumNLS.ClassicalCharges QuantumNLS.HierarchyFlow

variable {L : ℝ}

/-- A real quadratic polynomial in `ε` under the integral has derivative `∫ b` at `0`. -/
theorem hasDerivAt_integral_quadratic {a b c : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) :
    HasDerivAt (fun ε : ℝ => ∫ x in (0 : ℝ)..L, (a x + ε * b x + ε ^ 2 * c x))
      (∫ x in (0 : ℝ)..L, b x) 0 := by
  have hfun : (fun ε : ℝ => ∫ x in (0 : ℝ)..L, (a x + ε * b x + ε ^ 2 * c x)) =
      fun ε => (∫ x in (0 : ℝ)..L, a x) + ε * (∫ x in (0 : ℝ)..L, b x) +
        ε ^ 2 * (∫ x in (0 : ℝ)..L, c x) := by
    funext ε
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    all_goals (apply Continuous.intervalIntegrable; fun_prop)
  rw [hfun]
  have h1 : HasDerivAt (fun ε : ℝ => ε * (∫ x in (0 : ℝ)..L, b x))
      (1 * ∫ x in (0 : ℝ)..L, b x) 0 := (hasDerivAt_id (0 : ℝ)).mul_const _
  have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 * (∫ x in (0 : ℝ)..L, c x))
      (((2 : ℕ) : ℝ) * (0 : ℝ) ^ (2 - 1) * ∫ x in (0 : ℝ)..L, c x) 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).mul_const _
  convert ((hasDerivAt_const (0 : ℝ) (∫ x in (0 : ℝ)..L, a x)).add h1).add h2 using 1
  simp

/-- Integration by parts on the circle: `∫₀^L ū ∂ₓh = −∫₀^L conj(∂ₓu) h`. -/
theorem integral_conj_mul_deriv {u h : ℝ → ℂ} (hu : SmoothPeriodic L u)
    (hh : SmoothPeriodic L h) :
    ∫ x in (0 : ℝ)..L, conj (u x) * deriv h x = -∫ x in (0 : ℝ)..L, conj (deriv u x) * h x := by
  have h1 : ∀ x, HasDerivAt u (deriv u x) x := fun x =>
    ((contDiff_infty_iff_deriv.mp hu.smooth).1 x).hasDerivAt
  have h2 : ∀ x, HasDerivAt h (deriv h x) x := fun x =>
    ((contDiff_infty_iff_deriv.mp hh.smooth).1 x).hasDerivAt
  have hc1 : Continuous (deriv u) := (contDiff_infty_iff_deriv.mp hu.smooth).2.continuous
  have hc2 : Continuous (deriv h) := (contDiff_infty_iff_deriv.mp hh.smooth).2.continuous
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (u := fun x => conj (u x)) (u' := fun x => conj (deriv u x)) (v := h) (v' := deriv h)
    (fun x _ => (h1 x).star) (fun x _ => h2 x)
    ((Complex.continuous_conj.comp hc1).intervalIntegrable _ _) (hc2.intervalIntegrable _ _)
  have hb : conj (u L) * h L - conj (u 0) * h 0 = 0 := by
    have e1 : u L = u 0 := by simpa using hu.periodic 0
    have e2 : h L = h 0 := by simpa using hh.periodic 0
    rw [e1, e2]; ring
  rw [key, hb]
  ring

/-- `−i ∂ₓu` is smooth and periodic. -/
theorem smoothPeriodic_negI_deriv {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    SmoothPeriodic L (fun x => -Complex.I * deriv u x) :=
  ⟨contDiff_const.mul (contDiff_infty_iff_deriv.mp hu.smooth).2, fun x => by
    simp only [WeakDerivatives.periodic_deriv hu.periodic x]⟩

/-- A continuous periodic function with `∫₀^L |d|² = 0` vanishes (`L > 0`). -/
theorem eq_zero_of_integral_norm_sq {d : ℝ → ℂ} (hL : 0 < L) (hd : Continuous d)
    (hp : Function.Periodic d L) (h0 : ∫ x in (0 : ℝ)..L, ‖d x‖ ^ 2 = 0) : d = 0 := by
  have hc : Continuous (fun x => ‖d x‖ ^ 2) := by fun_prop
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hL.le
      (Filter.Eventually.of_forall (fun x => by simp only [Pi.zero_apply]; positivity))
      (hc.intervalIntegrable _ _)).mp h0
  have hae' : (fun x => ‖d x‖ ^ 2) =ᵐ[volume.restrict (Set.Ioo 0 L)] 0 :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Ioc_self hae
  have hEq : Set.EqOn (fun x => ‖d x‖ ^ 2) 0 (Set.Ioo 0 L) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hc.continuousOn continuousOn_const
  have hEq' : Set.EqOn (fun x => ‖d x‖ ^ 2) 0 (Set.Icc 0 L) :=
    hEq.of_subset_closure hc.continuousOn continuousOn_const Set.Ioo_subset_Icc_self
      (le_of_eq (closure_Ioo hL.ne).symm)
  funext x
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ hL x
  have := hEq' (Set.Ico_subset_Icc_self hy)
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    norm_eq_zero] at this
  show d x = 0
  rw [hxy]; exact this

/-- **Uniqueness of the DEF-015 gradient** on the smooth periodic class. -/
theorem gradient_unique (hL : 0 < L) {F : (ℝ → ℂ) → ℝ} {u g g' : ℝ → ℂ}
    (hg : IsSmoothGradient L F u g) (hg' : IsSmoothGradient L F u g') : g = g' := by
  set d : ℝ → ℂ := fun x => g x - g' x with hd
  have hdS : SmoothPeriodic L d :=
    ⟨hg.1.smooth.sub hg'.1.smooth, fun x => by simp [d, hg.1.periodic x, hg'.1.periodic x]⟩
  have e := (hg.2 d hdS).unique (hg'.2 d hdS)
  have i1 : IntervalIntegrable (fun x => conj (g x) * d x) volume 0 L :=
    ((Complex.continuous_conj.comp hg.1.smooth.continuous).mul hdS.smooth.continuous).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => conj (g' x) * d x) volume 0 L :=
    ((Complex.continuous_conj.comp hg'.1.smooth.continuous).mul hdS.smooth.continuous).intervalIntegrable _ _
  have hpair : pair L g d - pair L g' d = ((∫ x in (0 : ℝ)..L, ‖d x‖ ^ 2 : ℝ) : ℂ) := by
    unfold pair
    rw [← intervalIntegral.integral_sub i1 i2, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [d]
    rw [← sub_mul, ← map_sub, Complex.conj_mul']
    push_cast
    rfl
  have hre : (∫ x in (0 : ℝ)..L, ‖d x‖ ^ 2) = 0 := by
    have := congrArg Complex.re hpair
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  have hz := eq_zero_of_integral_norm_sq hL hdS.smooth.continuous hdS.periodic hre
  funext x
  have := congrFun hz x
  simp only [d, Pi.zero_apply] at this
  exact sub_eq_zero.mp this

/-- `Re ∫ f = ∫ Re f` for continuous `f`. -/
theorem re_integral {f : ℝ → ℂ} (hf : Continuous f) :
    (∫ x in (0 : ℝ)..L, f x).re = ∫ x in (0 : ℝ)..L, (f x).re := by
  have := Complex.reCLM.intervalIntegral_comp_comm (μ := volume) (a := 0) (b := L)
    (hf.intervalIntegrable 0 L)
  simpa using this.symm

/-- `Re I_1 = ∫ |u|²`. -/
theorem hamiltonian_zero (κ : ℝ) (u : ℝ → ℂ) :
    hamiltonian L κ 0 u = ∫ x in (0 : ℝ)..L, ‖u x‖ ^ 2 := by
  simp only [hamiltonian, zero_add, charge_one, Complex.ofReal_re]

/-- **Order 0**: the DEF-015 gradient of `Re I_1 = ‖u‖₂²` at a smooth periodic `u` is `u`. -/
theorem gradient_zero (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    IsSmoothGradient L (hamiltonian L κ 0) u u := by
  refine ⟨hu, fun h hh => ?_⟩
  have hcu := hu.smooth.continuous
  have hch := hh.smooth.continuous
  have hval : (fun ε : ℝ => hamiltonian L κ 0 (fun x => u x + (ε : ℂ) * h x)) =
      fun ε : ℝ => ∫ x in (0 : ℝ)..L, (‖u x‖ ^ 2 + ε * (2 * (conj (u x) * h x).re) +
        ε ^ 2 * ‖h x‖ ^ 2) := by
    funext ε
    rw [hamiltonian_zero]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    ring
  rw [hval]
  have hb : Continuous (fun x => 2 * (conj (u x) * h x).re) := by fun_prop
  convert hasDerivAt_integral_quadratic (L := L) (a := fun x => ‖u x‖ ^ 2)
    (c := fun x => ‖h x‖ ^ 2) (by fun_prop) hb (by fun_prop) using 1
  show 2 * (pair L u h).re = ∫ x in (0 : ℝ)..L, 2 * (conj (u x) * h x).re
  rw [intervalIntegral.integral_const_mul, pair,
    re_integral (f := fun x => conj (u x) * h x) ((Complex.continuous_conj.comp hcu).mul hch)]

/-- **Order 1**: the DEF-015 gradient of `Re I_2 = Re ∫ ū(−i∂ₓu)` at a smooth periodic `u` is
`−i ∂ₓ u`. -/
theorem gradient_one (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    IsSmoothGradient L (hamiltonian L κ 1) u (fun x => -Complex.I * deriv u x) := by
  refine ⟨smoothPeriodic_negI_deriv hu, fun h hh => ?_⟩
  have hcu := hu.smooth.continuous
  have hch := hh.smooth.continuous
  have hdu := (contDiff_infty_iff_deriv.mp hu.smooth).1
  have hdh := (contDiff_infty_iff_deriv.mp hh.smooth).1
  have hcu' : Continuous (deriv u) := (contDiff_infty_iff_deriv.mp hu.smooth).2.continuous
  have hch' : Continuous (deriv h) := (contDiff_infty_iff_deriv.mp hh.smooth).2.continuous
  have hval : (fun ε : ℝ => hamiltonian L κ 1 (fun x => u x + (ε : ℂ) * h x)) =
      fun ε : ℝ => ∫ x in (0 : ℝ)..L,
        ((conj (u x) * (-Complex.I * deriv u x)).re +
          ε * ((conj (u x) * (-Complex.I * deriv h x)).re +
            (conj (h x) * (-Complex.I * deriv u x)).re) +
          ε ^ 2 * (conj (h x) * (-Complex.I * deriv h x)).re) := by
    funext ε
    have hd : ∀ y, deriv (fun x => u x + (ε : ℂ) * h x) y = deriv u y + (ε : ℂ) * deriv h y :=
      fun y => by
        exact (((hdu y).hasDerivAt).add (((hdh y).hasDerivAt).const_mul (ε : ℂ))).deriv
    have hcont : Continuous (fun x => conj (u x + (ε : ℂ) * h x) *
        (-Complex.I * deriv (fun x => u x + (ε : ℂ) * h x) x)) := by
      simp_rw [hd]; fun_prop
    simp only [hamiltonian]
    rw [show (1 + 1 : ℕ) = 2 from rfl, charge_two, re_integral hcont]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [hd]
    have hid : conj (u x + (ε : ℂ) * h x) * (-Complex.I * (deriv u x + (ε : ℂ) * deriv h x)) =
        conj (u x) * (-Complex.I * deriv u x) +
          (ε : ℂ) * (conj (u x) * (-Complex.I * deriv h x) +
            conj (h x) * (-Complex.I * deriv u x)) +
          ((ε ^ 2 : ℝ) : ℂ) * (conj (h x) * (-Complex.I * deriv h x)) := by
      rw [map_add, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [hid]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
  rw [hval]
  convert hasDerivAt_integral_quadratic (L := L)
    (a := fun x => (conj (u x) * (-Complex.I * deriv u x)).re)
    (b := fun x => (conj (u x) * (-Complex.I * deriv h x)).re +
      (conj (h x) * (-Complex.I * deriv u x)).re)
    (c := fun x => (conj (h x) * (-Complex.I * deriv h x)).re)
    (by fun_prop) (by fun_prop) (by fun_prop) using 1
  show 2 * (pair L (fun x => -Complex.I * deriv u x) h).re = ∫ x in (0 : ℝ)..L,
    ((conj (u x) * (-Complex.I * deriv h x)).re + (conj (h x) * (-Complex.I * deriv u x)).re)
  -- the linear coefficient is `2 Re ⟨−i∂ₓu, h⟩`
  have hsym : ∀ x, (conj (h x) * (-Complex.I * deriv u x)).re =
      (conj (-Complex.I * deriv u x) * h x).re := fun x => by
    rw [← Complex.conj_re (conj (h x) * (-Complex.I * deriv u x)), map_mul, Complex.conj_conj,
      mul_comm]
  simp only [hsym]
  set J := ∫ x in (0 : ℝ)..L, conj (deriv u x) * h x with hJ
  have e1 : ∫ x in (0 : ℝ)..L, conj (u x) * (-Complex.I * deriv h x) = Complex.I * J := by
    have : (fun x => conj (u x) * (-Complex.I * deriv h x)) =
        fun x => -Complex.I * (conj (u x) * deriv h x) := by funext x; ring
    rw [this, intervalIntegral.integral_const_mul, integral_conj_mul_deriv hu hh]
    ring
  have e2 : ∫ x in (0 : ℝ)..L, conj (-Complex.I * deriv u x) * h x = Complex.I * J := by
    have : (fun x => conj (-Complex.I * deriv u x) * h x) =
        fun x => Complex.I * (conj (deriv u x) * h x) := by
      funext x; rw [map_mul, map_neg, Complex.conj_I]; ring
    rw [this, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [← re_integral (f := fun x => conj (u x) * (-Complex.I * deriv h x)) (by fun_prop),
    ← re_integral (f := fun x => conj (-Complex.I * deriv u x) * h x) (by fun_prop), e1, e2, pair,
    e2]
  ring

/-! Kernel axiom audit. -/
#print axioms hasDerivAt_integral_quadratic
#print axioms integral_conj_mul_deriv
#print axioms smoothPeriodic_negI_deriv
#print axioms eq_zero_of_integral_norm_sq
#print axioms gradient_unique
#print axioms re_integral
#print axioms hamiltonian_zero
#print axioms gradient_zero
#print axioms gradient_one

end QuantumNLS.Def024Gradient
