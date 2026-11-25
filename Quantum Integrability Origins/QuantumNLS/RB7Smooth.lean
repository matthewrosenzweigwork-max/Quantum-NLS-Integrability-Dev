import Mathlib
import QuantumNLS.SmoothScalarMomentsPhysical
import QuantumNLS.ChargeEnergy
import QuantumNLS.SobolevSpaces

/-!
# R-7B122087 `thm:hierarchy`: `H^∞ = C^∞` identification (own TODO A7, first half)

Printed use: "`u(t) = (Z^new)^{-1} z(t)` is smooth in space and time", "the charges are invariant ... for rapidly decreasing coordinates", i.e. the identification of
`L²` classes lying in every `H^s` with smooth periodic functions and conversely.  Proved here (no analytic input, only `Fourier`, `WeakDerivatives`,
`ChargeEnergy.coeff_deriv`, `SobolevSpaces`):

* `memHs_of_smooth`: for smooth periodic `f`, `smoothL2 hf ∈ H^s` for every real `s` (`MemHsLp L s`), via `û^{(k)}(n) = (2πin/L)^k û(n)` and Parseval;
* `smooth_of_memHs`: an `L²` class lying in `H^s` for every `s` equals `smoothL2 hf` for a smooth periodic `f` (the Fourier series is `C^∞` by termwise
  differentiation, `contDiff_tsum`, since `Σ |û(n)| |2πn/L|^k < ∞` for all `k`; its `L²` class is `u` by `ae_eq_seriesRep`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate ContDiff
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Fourier QuantumNLS.WeakDerivatives QuantumNLS.ClassicalCharges QuantumNLS.ChargeEnergy
open QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.PhysicalTensor

variable {L : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

/-- The (report) Fourier coefficients of a smooth periodic function. -/
def cof (hf : SmoothPeriodic L f) (n : ℤ) : ℂ :=
  coeff L (liftC hf.smooth.continuous hf.periodic : AddCircle L → ℂ) n

theorem fourierL2_smoothL2 (hf : SmoothPeriodic L f) (n : ℤ) :
    fourierL2 L (smoothL2 hf) n = cof hf n := by
  rw [fourierL2_apply]
  exact coeff_congr_ae L (ContinuousMap.coeFn_toLp _ _) n

theorem smooth_deriv (hf : SmoothPeriodic L f) : SmoothPeriodic L (deriv f) :=
  ⟨(contDiff_infty_iff_deriv.mp hf.smooth).2, periodic_deriv hf.periodic⟩

theorem cof_iter (hf : SmoothPeriodic L f) (k : ℕ) :
    ∃ (g : ℝ → ℂ) (hg : SmoothPeriodic L g), ∀ n, cof hg n = (ikn L n) ^ k * cof hf n := by
  induction k with
  | zero => exact ⟨f, hf, fun n => by simp⟩
  | succ k ih =>
    obtain ⟨g, hg, h⟩ := ih
    refine ⟨deriv g, smooth_deriv hg, fun n => ?_⟩
    have := coeff_deriv hg n
    have e : cof (smooth_deriv hg) n = ikn L n * cof hg n := this
    rw [e, h n]; ring

theorem summable_freq_pow (hf : SmoothPeriodic L f) (k : ℕ) :
    Summable fun n : ℤ => freq L n ^ (2 * k) * ‖cof hf n‖ ^ 2 := by
  obtain ⟨g, hg, h⟩ := cof_iter hf k
  have hs := (hasSum_sq_coeff (L := L) (memLp_of_continuous (liftC hg.smooth.continuous hg.periodic).continuous)).summable
  refine hs.congr (fun n => ?_)
  show ‖cof hg n‖ ^ 2 = _
  rw [h n, norm_mul, norm_pow, mul_pow]
  have : ‖ikn L n‖ = |freq L n| := by
    simp [ikn]
  rw [this, ← pow_mul, pow_mul', sq_abs]
  ring

theorem memHs_of_smooth (hf : SmoothPeriodic L f) (s : ℝ) : MemHsLp L s (smoothL2 hf) := by
  obtain ⟨K, hK⟩ := exists_nat_ge s
  unfold MemHsLp MemHs
  have h0 := summable_freq_pow hf 0
  have hK' := summable_freq_pow hf K
  simp only [mul_zero, pow_zero, one_mul] at h0
  have hs : Summable fun n : ℤ => (2 : ℝ) ^ (2 * K - 1) * (‖cof hf n‖ ^ 2 + freq L n ^ (2 * K) * ‖cof hf n‖ ^ 2) :=
    (h0.add hK').mul_left _
  refine Summable.of_nonneg_of_le (fun n => by unfold sobolevWeight; positivity) (fun n => ?_) hs
  simp only [fourierL2_smoothL2]
  have hx : 1 ≤ 1 + |freq L n| := by linarith [abs_nonneg (freq L n)]
  have h1 : sobolevWeight L s n ≤ (1 + |freq L n|) ^ (2 * K) := by
    unfold sobolevWeight
    have : (1 + |2 * Real.pi * (n : ℝ) / L|) = 1 + |freq L n| := rfl
    rw [this]
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx (by push_cast; linarith)
  have h2 : (1 + |freq L n|) ^ (2 * K) ≤ 2 ^ (2 * K - 1) * (1 + freq L n ^ (2 * K)) := by
    have := add_pow_le (zero_le_one' ℝ) (abs_nonneg (freq L n)) (2 * K)
    have e : |freq L n| ^ (2 * K) = freq L n ^ (2 * K) := by
      rw [pow_mul, pow_mul, sq_abs]
    rw [e] at this
    simpa using this
  calc sobolevWeight L s n * ‖cof hf n‖ ^ 2 ≤ ((1 + |freq L n|) ^ (2 * K)) * ‖cof hf n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ ≤ (2 ^ (2 * K - 1) * (1 + freq L n ^ (2 * K))) * ‖cof hf n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = _ := by ring


/-! ## Converse: `H^∞ ⊆ C^∞` -/

theorem iteratedDeriv_expterm (A B : ℂ) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => A * Complex.exp (B * (x : ℂ))) =
      fun x : ℝ => A * B ^ k * Complex.exp (B * (x : ℂ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h : HasDerivAt (fun x : ℝ => A * B ^ k * Complex.exp (B * (x : ℂ)))
        (A * B ^ k * (Complex.exp (B * (x : ℂ)) * B)) x := by
      have h1 : HasDerivAt (fun x : ℝ => B * (x : ℂ)) B x := by
        simpa using ((hasDerivAt_id (x : ℝ)).ofReal_comp).const_mul B
      exact (h1.cexp).const_mul (A * B ^ k)
    rw [h.deriv]; ring

theorem mem04_of_memHs (u : L2T L) (hu : ∀ s : ℝ, MemHsLp L s u) (k : ℕ) :
    Mem04 L 1 (fun n => (freq L n : ℂ) ^ k * fourierL2 L u n) := by
  have h := hu ((k : ℝ) + 1)
  unfold MemHsLp MemHs at h
  unfold Mem04
  refine Summable.of_nonneg_of_le (fun n => by unfold f04Weight; positivity) (fun n => ?_) h
  have hx : 1 ≤ 1 + |freq L n| := by linarith [abs_nonneg (freq L n)]
  have e1 : sobolevWeight L ((k : ℝ) + 1) n = (1 + |freq L n|) ^ (2 * k + 2) := by
    unfold sobolevWeight
    have : (1 + |2 * Real.pi * (n : ℝ) / L|) = 1 + |freq L n| := rfl
    rw [this, ← Real.rpow_natCast]
    congr 1
    push_cast; ring
  have e2 : f04Weight L 1 n = 1 + freq L n ^ 2 := by
    unfold f04Weight; rw [Real.rpow_one]
  rw [e1, e2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have h3 : (1 + freq L n ^ 2) * ((|freq L n| ^ k * ‖fourierL2 L u n‖) ^ 2) ≤
      (1 + |freq L n|) ^ (2 * k + 2) * ‖fourierL2 L u n‖ ^ 2 := by
    have h4 : 1 + freq L n ^ 2 ≤ (1 + |freq L n|) ^ 2 := by
      nlinarith [abs_nonneg (freq L n), sq_abs (freq L n)]
    have h5 : |freq L n| ^ (2 * k) ≤ (1 + |freq L n|) ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (freq L n)]) _
    calc (1 + freq L n ^ 2) * ((|freq L n| ^ k * ‖fourierL2 L u n‖) ^ 2)
        = (1 + freq L n ^ 2) * (|freq L n| ^ (2 * k)) * ‖fourierL2 L u n‖ ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm k 2]; ring
      _ ≤ (1 + |freq L n|) ^ 2 * (1 + |freq L n|) ^ (2 * k) * ‖fourierL2 L u n‖ ^ 2 := by
          gcongr
      _ = _ := by rw [← pow_add]; ring_nf
  exact h3

theorem summable_cof_pow (u : L2T L) (hu : ∀ s : ℝ, MemHsLp L s u) (k : ℕ) :
    Summable fun n : ℤ => ‖fourierL2 L u n‖ * |freq L n| ^ k := by
  have hL : 0 < L := Fact.out
  have := (tsum_norm_le_cL hL (mem04_of_memHs u hu k)).1
  refine this.congr (fun n => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_comm]

/-- **`H^∞ ⊆ C^∞`**: an `L²` class lying in `H^s` for every `s` is the class of a smooth periodic function. -/
theorem smooth_of_memHs (u : L2T L) (hu : ∀ s : ℝ, MemHsLp L s u) :
    ∃ (f : ℝ → ℂ) (hf : SmoothPeriodic L f), smoothL2 hf = u := by
  have hL : 0 < L := Fact.out
  set c : ℤ → ℂ := fun n => fourierL2 L u n with hc
  set g : ℝ → ℂ := fun x => seriesRep L c (x : AddCircle L) with hg
  have hterm : ∀ x : ℝ, g x = ∑' n : ℤ, (c n * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)) *
      Complex.exp ((Complex.I * (freq L n : ℂ)) * (x : ℂ)) := by
    intro x
    simp only [hg, seriesRep, mode_coe]
    refine tsum_congr (fun n => ?_)
    have : (2 * Real.pi * Complex.I * n * x / L : ℂ) = (Complex.I * (freq L n : ℂ)) * (x : ℂ) := by
      simp only [freq]; push_cast; ring
    rw [this]; ring
  have hsm : ContDiff ℝ ∞ g := by
    have : g = fun x : ℝ => ∑' n : ℤ, (c n * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)) *
        Complex.exp ((Complex.I * (freq L n : ℂ)) * (x : ℂ)) := funext hterm
    rw [this]
    refine contDiff_tsum (v := fun k n => ‖c n‖ * |freq L n| ^ k * (Real.sqrt L)⁻¹) ?_ ?_ ?_
    · intro n
      exact contDiff_const.mul (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))
    · intro k _
      exact (summable_cof_pow u hu k).mul_right _
    · intro k n x _
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expterm]
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_inv, Complex.norm_I, one_mul]
      have hE : ‖Complex.exp ((Complex.I * (freq L n : ℂ)) * (x : ℂ))‖ = 1 := by
        have : (Complex.I * (freq L n : ℂ)) * (x : ℂ) = ((freq L n * x : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      rw [hE, abs_of_pos (Real.sqrt_pos.2 hL)]
      apply le_of_eq
      ring
  have hper : Function.Periodic g L := by
    intro x
    simp only [hg]
    rw [show ((x + L : ℝ) : AddCircle L) = (x : AddCircle L) from AddCircle.coe_add_period L x]
  have hf : SmoothPeriodic L g := ⟨hsm, hper⟩
  refine ⟨g, hf, ?_⟩
  -- the class
  have hcont : Continuous (seriesRep L c) := continuous_seriesRep (by simpa using summable_cof_pow u hu 0)
  have hlift : (liftC hf.smooth.continuous hf.periodic : AddCircle L → ℂ) = seriesRep L c := by
    funext y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact liftC_coe _ _ x
  have h04 : Mem04 L 1 (coeff L (u : AddCircle L → ℂ)) := by
    have := mem04_of_memHs u hu 0
    simp only [pow_zero, one_mul] at this
    have e : coeff L (u : AddCircle L → ℂ) = fun n => fourierL2 L u n := funext fun n => (fourierL2_apply L u n).symm
    rw [e]; exact this
  have hae := ae_eq_seriesRep (Lp.memLp u) h04
  have e : coeff L (u : AddCircle L → ℂ) = c := funext fun n => (fourierL2_apply L u n).symm
  rw [e] at hae
  unfold smoothL2
  refine Lp.ext ?_
  refine (ContinuousMap.coeFn_toLp _ _).trans ?_
  rw [hlift]
  exact hae.symm

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.memHs_of_smooth
#print axioms QuantumNLS.RB7.smooth_of_memHs
