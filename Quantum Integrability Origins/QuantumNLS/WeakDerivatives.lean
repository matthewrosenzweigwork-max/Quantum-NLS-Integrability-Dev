/-
QuantumNLS.WeakDerivatives — weak (distributional) derivatives on the torus `𝕋_L` and their Fourier
identification (owner: opus_tensor).

Source: DEF-001 (definitions.tex:7) mass-`L` torus, `⟨f,g⟩ = ∫₀^L conj f g`,
`e_n(x) = L^{-1/2} e^{2πinx/L}`, `û(n) = ⟨e_n,u⟩`; DEF-002 (:13) `H^s`, `h^s` with weight
`(1+|2πn/L|)^{2s}`; DEF-005/031 kinetic expressions `‖∂ψ‖²`, `A_k = 1 − Σ∂²`.

What is identified (no equivalence assumed):
* `HasWeakDeriv f g`: for EVERY smooth `L`-periodic test function `φ : ℝ → ℂ`,
  `∫₀^L f φ' = −∫₀^L g φ` (distributional derivative on `𝕋_L`, lifted to `[0,L]`).
* (A) weak derivative ⇒ `ĝ(n) = (2πin/L) f̂(n)` for all `n` (test functions `e^{−2πinx/L}`).
* (B) `ĝ(n) = (2πin/L) f̂(n)` for all `n` ⇒ weak derivative, for every C¹ periodic test function
  (Parseval with the report coefficients, integration by parts on `[0,L]`).
* (C) `f` has a weak derivative in `L²` ⇔ `Σ (2πn/L)² |f̂(n)|² < ∞` ⇔ `f ∈ H¹` (DEF-002, `s = 1`).

Frozen import, read-only: Fourier (the formalization) sha256 f0c07d6f…ea0 (`coeff`, `mode`, `fourierL2`,
`freq`).  No contact-form or Bethe file is touched.
-/
import QuantumNLS.EnergyMultiplier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff
open MeasureTheory QuantumNLS.Fourier

noncomputable section

namespace QuantumNLS.WeakDerivatives

variable {L : ℝ} [Fact (0 < L)]

/-! ## Test functions and weak derivatives on `𝕋_L` -/

/-- Smooth `L`-periodic test functions `φ : ℝ → ℂ`. -/
structure IsPeriodicTest (L : ℝ) (φ : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : Function.Periodic φ L

/-- **Weak derivative on `𝕋_L`.**  `g` is the distributional derivative of `f` iff
`∫₀^L f φ' = −∫₀^L g φ` for every smooth `L`-periodic `φ`. -/
def HasWeakDeriv (f g : Lp ℂ 2 (volume : Measure (AddCircle L))) : Prop :=
  ∀ φ : ℝ → ℂ, IsPeriodicTest L φ →
    ∫ x in (0 : ℝ)..L, (f : AddCircle L → ℂ) x * deriv φ x =
      -∫ x in (0 : ℝ)..L, (g : AddCircle L → ℂ) x * φ x

/-- `(2πin/L)`. -/
def ikn (L : ℝ) (n : ℤ) : ℂ := Complex.I * (freq L n : ℂ)

/-! ## (A) Weak derivative ⇒ Fourier relation -/

/-- The test function `χ_n(x) = e^{−2πinx/L}`. -/
def chi (L : ℝ) (n : ℤ) (x : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * n / L) * x)

omit [Fact (0 < L)] in
theorem hasDerivAt_chi (n : ℤ) (x : ℝ) :
    HasDerivAt (chi L n) (-(ikn L n) * chi L n x) x := by
  have h1 : HasDerivAt (fun x : ℝ => -(2 * Real.pi * Complex.I * n / L) * (x : ℂ))
      (-(2 * Real.pi * Complex.I * n / L) * 1) x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (-(2 * Real.pi * Complex.I * n / L))
  have h2 := h1.cexp
  refine h2.congr_deriv ?_
  show Complex.exp (-(2 * Real.pi * Complex.I * n / L) * (x : ℂ)) *
      (-(2 * Real.pi * Complex.I * n / L) * 1) =
    -(Complex.I * ((2 * Real.pi * (n : ℝ) / L : ℝ) : ℂ)) *
      Complex.exp (-(2 * Real.pi * Complex.I * n / L) * (x : ℂ))
  push_cast
  ring

omit [Fact (0 < L)] in
theorem deriv_chi (n : ℤ) : deriv (chi L n) = fun x => -(ikn L n) * chi L n x :=
  funext fun x => (hasDerivAt_chi n x).deriv

theorem chi_isTest (n : ℤ) : IsPeriodicTest L (chi L n) where
  smooth := by
    unfold chi
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  periodic := by
    intro x
    have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < L).ne'
    unfold chi
    have : -(2 * Real.pi * Complex.I * n / L) * ((x + L : ℝ) : ℂ) =
        -(2 * Real.pi * Complex.I * n / L) * (x : ℂ) + (-n : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

omit [Fact (0 < L)] in
/-- `conj(e_n(x)) = L^{-1/2} χ_n(x)` at real lifts. -/
theorem conj_mode_coe (n : ℤ) (x : ℝ) :
    conj (mode L n (x : AddCircle L)) = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * chi L n x := by
  rw [mode_coe, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  ring

/-- `û(n) = L^{-1/2} ∫₀^L χ_n u`. -/
theorem coeff_eq_interval (u : AddCircle L → ℂ) (n : ℤ) :
    coeff L u n = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * ∫ x in (0 : ℝ)..L, chi L n x * u x := by
  unfold coeff
  rw [← AddCircle.intervalIntegral_preimage L 0, zero_add, ← intervalIntegral.integral_const_mul]
  congr 1; funext x
  rw [conj_mode_coe]; ring

/-- **(A)** A weak derivative has Fourier coefficients `ĝ(n) = (2πin/L) f̂(n)`. -/
theorem coeff_of_hasWeakDeriv {f g : Lp ℂ 2 (volume : Measure (AddCircle L))}
    (h : HasWeakDeriv f g) (n : ℤ) :
    coeff L (g : AddCircle L → ℂ) n = ikn L n * coeff L (f : AddCircle L → ℂ) n := by
  have hw := h (chi L n) (chi_isTest n)
  rw [deriv_chi] at hw
  have e1 : ∫ x in (0 : ℝ)..L, (f : AddCircle L → ℂ) x * (-(ikn L n) * chi L n x) =
      -(ikn L n) * ∫ x in (0 : ℝ)..L, chi L n x * (f : AddCircle L → ℂ) x := by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext x; ring
  have e2 : ∫ x in (0 : ℝ)..L, (g : AddCircle L → ℂ) x * chi L n x =
      ∫ x in (0 : ℝ)..L, chi L n x * (g : AddCircle L → ℂ) x := by
    congr 1; funext x; ring
  rw [e1, e2] at hw
  rw [coeff_eq_interval, coeff_eq_interval]
  have hg : ∫ x in (0 : ℝ)..L, chi L n x * (g : AddCircle L → ℂ) x =
      ikn L n * ∫ x in (0 : ℝ)..L, chi L n x * (f : AddCircle L → ℂ) x := by
    linear_combination hw
  rw [hg]; ring

/-- Weak derivatives are unique (as `L²` classes). -/
theorem hasWeakDeriv_unique {f g₁ g₂ : Lp ℂ 2 (volume : Measure (AddCircle L))}
    (h₁ : HasWeakDeriv f g₁) (h₂ : HasWeakDeriv f g₂) : g₁ = g₂ := by
  apply (fourierL2 L).injective
  ext n
  rw [fourierL2_apply, fourierL2_apply, coeff_of_hasWeakDeriv h₁, coeff_of_hasWeakDeriv h₂]

/-! ## (B) Fourier relation ⇒ weak derivative -/

omit [Fact (0 < L)] in
/-- The derivative of an `L`-periodic function is `L`-periodic. -/
theorem periodic_deriv {φ : ℝ → ℂ} (hp : Function.Periodic φ L) :
    Function.Periodic (deriv φ) L := by
  intro x
  have e : (fun y => φ (y + L)) = φ := funext hp
  rw [← deriv_comp_add_const, e]

/-- The continuous lift of a continuous `L`-periodic function to `𝕋_L`. -/
def liftC {ψ : ℝ → ℂ} (hc : Continuous ψ) (hp : Function.Periodic ψ L) : C(AddCircle L, ℂ) :=
  ⟨hp.lift, (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr hc⟩

omit [Fact (0 < L)] in
theorem liftC_coe {ψ : ℝ → ℂ} (hc : Continuous ψ) (hp : Function.Periodic ψ L) (x : ℝ) :
    liftC hc hp (x : AddCircle L) = ψ x := hp.lift_coe x

/-- `D_n(ψ) = ∫_{𝕋_L} e_n ψ` (mass-`L` measure). -/
def pairCoeff (ψ : AddCircle L → ℂ) (n : ℤ) : ℂ :=
  ∫ y, mode L n y * ψ y ∂(volume : Measure (AddCircle L))

/-- **Parseval pairing.**  `∫_{𝕋_L} f ψ = Σₙ D_n(ψ) f̂(n)` for `f ∈ L²` and continuous `ψ`. -/
theorem integral_mul_eq_tsum (f : Lp ℂ 2 (volume : Measure (AddCircle L))) (ψ : C(AddCircle L, ℂ)) :
    ∫ y, (f : AddCircle L → ℂ) y * ψ y ∂(volume : Measure (AddCircle L)) =
      ∑' n, pairCoeff ψ n * coeff L (f : AddCircle L → ℂ) n := by
  let ψc : C(AddCircle L, ℂ) := ⟨fun y => conj (ψ y), Complex.continuous_conj.comp ψ.continuous⟩
  let Ψ : Lp ℂ 2 (volume : Measure (AddCircle L)) := ContinuousMap.toLp (E := ℂ) 2 volume ℂ ψc
  have hΨ : (Ψ : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))] ψc :=
    ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) (volume : Measure (AddCircle L)) ψc
  have h1 : ⟪Ψ, f⟫_ℂ = ∫ y, (f : AddCircle L → ℂ) y * ψ y ∂(volume : Measure (AddCircle L)) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hΨ] with y hy
    rw [RCLike.inner_apply', hy]
    simp [ψc, mul_comm]
  have h2 : ⟪Ψ, f⟫_ℂ = ∑' n, pairCoeff ψ n * coeff L (f : AddCircle L → ℂ) n := by
    rw [← (fourierL2 L).inner_map_map, lp.inner_eq_tsum]
    congr 1; funext n
    rw [RCLike.inner_apply', fourierL2_apply, fourierL2_apply, coeff_congr_ae L hΨ]
    congr 1
    unfold coeff pairCoeff
    rw [← integral_conj]
    congr 1; funext y
    simp [ψc]
  rw [← h1, h2]

/-- `e_n` at real lifts. -/
def emode (L : ℝ) (n : ℤ) (x : ℝ) : ℂ := mode L n (x : AddCircle L)

omit [Fact (0 < L)] in
theorem hasDerivAt_emode (n : ℤ) (x : ℝ) :
    HasDerivAt (emode L n) (ikn L n * emode L n x) x := by
  have e : emode L n = fun x : ℝ =>
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * n * x / L) :=
    funext fun x => mode_coe L n x
  have h1 : HasDerivAt (fun x : ℝ => 2 * Real.pi * Complex.I * n * (x : ℂ) / L)
      (2 * Real.pi * Complex.I * n * 1 / L) x := by
    simpa using (((hasDerivAt_id x).ofReal_comp).const_mul
      (2 * Real.pi * Complex.I * n)).div_const (L : ℂ)
  rw [e]
  refine (h1.cexp.const_mul _).congr_deriv ?_
  beta_reduce
  simp only [ikn, freq]
  push_cast
  ring

omit [Fact (0 < L)] in
theorem continuous_emode (n : ℤ) : Continuous (emode L n) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_emode n x).continuousAt

omit [Fact (0 < L)] in
/-- **Integration by parts on `[0,L]`** (boundary terms cancel by periodicity):
`∫₀^L e_n φ' = −(2πin/L) ∫₀^L e_n φ`. -/
theorem integral_emode_mul_deriv {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hp : Function.Periodic φ L)
    (n : ℤ) :
    ∫ x in (0 : ℝ)..L, emode L n x * deriv φ x =
      -(ikn L n) * ∫ x in (0 : ℝ)..L, emode L n x * φ x := by
  have hd : ∀ x, HasDerivAt φ (deriv φ x) x := fun x =>
    ((hφ.differentiable one_ne_zero) x).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ => hasDerivAt_emode n x)
    (fun x _ => hd x) ((continuous_const.mul (continuous_emode n)).intervalIntegrable _ _)
    ((hφ.continuous_deriv le_rfl).intervalIntegrable _ _)]
  have hb1 : emode L n L = emode L n 0 := by
    simp only [emode]
    rw [AddCircle.coe_period, ← QuotientAddGroup.mk_zero]
  have hb2 : φ L = φ 0 := by simpa using hp 0
  rw [hb1, hb2, sub_self, zero_sub, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_neg]
  congr 1; funext x; ring

/-- **(B)** If `ĝ(n) = (2πin/L) f̂(n)` for all `n`, then `∫₀^L f φ' = −∫₀^L g φ` for every
C¹ `L`-periodic `φ`. -/
theorem weakDeriv_of_coeff {f g : Lp ℂ 2 (volume : Measure (AddCircle L))}
    (h : ∀ n, coeff L (g : AddCircle L → ℂ) n = ikn L n * coeff L (f : AddCircle L → ℂ) n)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hp : Function.Periodic φ L) :
    ∫ x in (0 : ℝ)..L, (f : AddCircle L → ℂ) x * deriv φ x =
      -∫ x in (0 : ℝ)..L, (g : AddCircle L → ℂ) x * φ x := by
  have hc1 : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hp1 : Function.Periodic (deriv φ) L := periodic_deriv hp
  set ψ1 := liftC hc1 hp1
  set ψ0 := liftC hφ.continuous hp
  have e1 : ∫ x in (0 : ℝ)..L, (f : AddCircle L → ℂ) x * deriv φ x =
      ∫ y, (f : AddCircle L → ℂ) y * ψ1 y ∂(volume : Measure (AddCircle L)) := by
    rw [← AddCircle.intervalIntegral_preimage L 0, zero_add]
    congr 1
  have e0 : ∫ x in (0 : ℝ)..L, (g : AddCircle L → ℂ) x * φ x =
      ∫ y, (g : AddCircle L → ℂ) y * ψ0 y ∂(volume : Measure (AddCircle L)) := by
    rw [← AddCircle.intervalIntegral_preimage L 0, zero_add]
    congr 1
  have hD : ∀ n, pairCoeff ψ1 n = -(ikn L n) * pairCoeff ψ0 n := by
    intro n
    have a1 : pairCoeff ψ1 n = ∫ x in (0 : ℝ)..L, emode L n x * deriv φ x := by
      unfold pairCoeff
      rw [← AddCircle.intervalIntegral_preimage L 0, zero_add]
      congr 1
    have a0 : pairCoeff ψ0 n = ∫ x in (0 : ℝ)..L, emode L n x * φ x := by
      unfold pairCoeff
      rw [← AddCircle.intervalIntegral_preimage L 0, zero_add]
      congr 1
    rw [a1, a0, integral_emode_mul_deriv hφ hp]
  rw [e1, e0, integral_mul_eq_tsum, integral_mul_eq_tsum, ← tsum_neg]
  congr 1; funext n
  rw [hD, h]; ring

/-- (B), packaged: the Fourier relation gives the weak derivative (smooth tests). -/
theorem hasWeakDeriv_of_coeff {f g : Lp ℂ 2 (volume : Measure (AddCircle L))}
    (h : ∀ n, coeff L (g : AddCircle L → ℂ) n = ikn L n * coeff L (f : AddCircle L → ℂ) n) :
    HasWeakDeriv f g := fun φ hφ =>
  weakDeriv_of_coeff h (hφ.smooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)))
    hφ.periodic

/-- **Identification (1D).**  `g` is the weak derivative of `f` iff `ĝ(n) = (2πin/L) f̂(n)`. -/
theorem hasWeakDeriv_iff_coeff (f g : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    HasWeakDeriv f g ↔
      ∀ n, coeff L (g : AddCircle L → ℂ) n = ikn L n * coeff L (f : AddCircle L → ℂ) n :=
  ⟨coeff_of_hasWeakDeriv, hasWeakDeriv_of_coeff⟩

/-! ## (C) Existence of an `L²` weak derivative ⇔ Fourier `H¹` -/

omit [Fact (0 < L)] in
theorem norm_ikn_mul_sq (n : ℤ) (c : ℂ) : ‖ikn L n * c‖ ^ 2 = freq L n ^ 2 * ‖c‖ ^ 2 := by
  rw [ikn, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]

/-- **`f` has a weak derivative in `L²` iff `Σ (2πn/L)² |f̂(n)|² < ∞`.** -/
theorem exists_hasWeakDeriv_iff (f : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    (∃ g, HasWeakDeriv f g) ↔
      Summable fun n : ℤ => freq L n ^ 2 * ‖coeff L (f : AddCircle L → ℂ) n‖ ^ 2 := by
  constructor
  · rintro ⟨g, hg⟩
    have hs := (hasSum_sq_coeff L (Lp.memLp g)).summable
    refine hs.congr fun n => ?_
    rw [coeff_of_hasWeakDeriv hg, norm_ikn_mul_sq]
  · intro hs
    have hmem : Memℓp (fun n : ℤ => ikn L n * coeff L (f : AddCircle L → ℂ) n) 2 := by
      rw [QuantumNLS.Energy.memL2_iff]
      exact hs.congr fun n => (norm_ikn_mul_sq n _).symm
    let a : lp (fun _ : ℤ => ℂ) 2 := ⟨_, hmem⟩
    refine ⟨(fourierL2 L).symm a, hasWeakDeriv_of_coeff fun n => ?_⟩
    rw [fourierL2_symm_apply_coeff]

/-- **Weak `H¹` = Fourier `H¹` (DEF-002, `s = 1`).**  `f` has a weak derivative in `L²` iff its
report coefficients lie in `h¹`, i.e. `Σ (1 + |2πn/L|)² |f̂(n)|² < ∞`. -/
theorem exists_hasWeakDeriv_iff_memHs (f : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    (∃ g, HasWeakDeriv f g) ↔ MemHs L 1 (coeff L (f : AddCircle L → ℂ)) := by
  rw [exists_hasWeakDeriv_iff]
  have h0 := (hasSum_sq_coeff L (Lp.memLp f)).summable
  have hw : ∀ n : ℤ, sobolevWeight L 1 n = (1 + |freq L n|) ^ 2 := by
    intro n
    rw [sobolevWeight, mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rfl
  unfold MemHs
  simp_rw [hw]
  constructor
  · intro hs
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((h0.mul_left 2).add (hs.mul_left 2))
    have ht : (1 + |freq L n|) ^ 2 ≤ 2 + 2 * freq L n ^ 2 := by
      nlinarith [sq_abs (freq L n), sq_nonneg (|freq L n| - 1), abs_nonneg (freq L n)]
    have hc := sq_nonneg ‖coeff L (f : AddCircle L → ℂ) n‖
    nlinarith
  · intro hs
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
    have ht : freq L n ^ 2 ≤ (1 + |freq L n|) ^ 2 := by
      nlinarith [sq_abs (freq L n), abs_nonneg (freq L n)]
    exact mul_le_mul_of_nonneg_right ht (sq_nonneg _)

end QuantumNLS.WeakDerivatives

#print axioms QuantumNLS.WeakDerivatives.coeff_of_hasWeakDeriv
#print axioms QuantumNLS.WeakDerivatives.hasWeakDeriv_unique
#print axioms QuantumNLS.WeakDerivatives.integral_mul_eq_tsum
#print axioms QuantumNLS.WeakDerivatives.weakDeriv_of_coeff
#print axioms QuantumNLS.WeakDerivatives.hasWeakDeriv_iff_coeff
#print axioms QuantumNLS.WeakDerivatives.exists_hasWeakDeriv_iff
#print axioms QuantumNLS.WeakDerivatives.exists_hasWeakDeriv_iff_memHs
