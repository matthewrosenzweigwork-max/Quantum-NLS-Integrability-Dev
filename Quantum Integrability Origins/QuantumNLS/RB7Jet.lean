import Mathlib
import QuantumNLS.RB7Smooth

/-!
# R-7B122087 `thm:hierarchy`: derivative jets of `H^q` fields as continuous functions (own TODO A2, step 1)

Printed use: "The differential-polynomial recursion makes `I_{r+1}` a smooth real functional on `H^q`."  The recursion of DEF-022 involves `a`-fold derivatives of `u` and `ū`
(`a ≤ r`).  This module supplies the analytic building blocks, with no analytic input beyond `Fourier`, `SobolevSpaces` (F04 `eq:l1` embedding) and `RB7Smooth`:

* `jet h : H^q →L[ℂ] C(𝕋_L, ℂ)` (`(a : ℝ) + 1 ≤ q`): `u ↦ Σ_n (2πin/L)^a û(n) e_n`, the continuous function `∂^a u` (absolutely summable by the F04 bound), with
  operator norm `≤ c_L` (`norm_jetFun_le`);
* `jet_smooth`: for smooth periodic `f`, `jet h (smoothL2 f) (x) = f^{(a)}(x)`;
* `cconj : C(𝕋_L, ℂ) →L[ℝ] C(𝕋_L, ℂ)`: pointwise complex conjugation;
* `integralCLM : C(𝕋_L, ℂ) →L[ℂ] ℂ`: the integral `∫_{𝕋_L}` (mass `L`), with `integralCLM (liftC ψ) = ∫_0^L ψ` for periodic continuous `ψ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate ContDiff
open MeasureTheory

namespace QuantumNLS.RB7

open QuantumNLS.Fourier QuantumNLS.WeakDerivatives QuantumNLS.ClassicalCharges QuantumNLS.ChargeEnergy
open QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.PhysicalTensor QuantumNLS.Sobolev

variable {L : ℝ} [Fact (0 < L)]

/-- The Fourier coefficients of the `a`-th derivative of an `H^q` field: `n ↦ (2πin/L)^a û(n)`. -/
def dcoef (a : ℕ) {q : ℝ} (u : H02 L q) : ℤ → ℂ := fun n => ikn L n ^ a * fourierL2 L u.val n

theorem weight_le {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) (n : ℤ) :
    f04Weight L 1 n * ‖ikn L n ^ a‖ ^ 2 ≤ sobolevWeight L q n := by
  have hn : ‖ikn L n‖ = |freq L n| := by simp [ikn]
  set t := |freq L n| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hx : 1 ≤ 1 + t := by linarith
  have e : ‖ikn L n ^ a‖ ^ 2 = t ^ (2 * a) := by
    rw [norm_pow, hn, ← pow_mul, mul_comm]
  have e2 : freq L n ^ 2 = t ^ 2 := by rw [ht, sq_abs]
  rw [f04Weight_one, e, e2]
  have h1 : 1 + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
  have h2 : t ^ (2 * a) ≤ (1 + t) ^ (2 * a) := pow_le_pow_left₀ ht0 (by linarith) _
  have h3 : (1 + t ^ 2) * t ^ (2 * a) ≤ (1 + t) ^ (2 + 2 * a) := by
    rw [pow_add]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 : (1 + t) ^ (2 + 2 * a) = (1 + t) ^ (((2 + 2 * a : ℕ) : ℝ)) := by
    rw [Real.rpow_natCast]
  have h5 : (1 + t) ^ (((2 + 2 * a : ℕ) : ℝ)) ≤ (1 + t) ^ (2 * q) :=
    Real.rpow_le_rpow_of_exponent_le hx (by push_cast; linarith)
  have h6 : sobolevWeight L q n = (1 + t) ^ (2 * q) := rfl
  rw [h6]
  exact h3.trans (h4.le.trans h5)

theorem mem04_dcoef {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) (u : H02 L q) :
    Mem04 L 1 (dcoef a u) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) u.summable
  · exact mul_nonneg (f04Weight_pos L 1 n).le (sq_nonneg _)
  · show f04Weight L 1 n * ‖ikn L n ^ a * fourierL2 L u.val n‖ ^ 2 ≤ sobolevWeight L q n * ‖fourierL2 L u.val n‖ ^ 2
    rw [norm_mul, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (weight_le h n) (sq_nonneg _)

theorem f04NormSq_dcoef_le {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) (u : H02 L q) :
    f04NormSq L 1 (dcoef a u) ≤ ‖u‖ ^ 2 := by
  rw [WField.norm_sq_eq_tsum]
  refine Summable.tsum_le_tsum (fun n => ?_) (mem04_dcoef h u) u.summable
  show f04Weight L 1 n * ‖ikn L n ^ a * fourierL2 L u.val n‖ ^ 2 ≤ sobolevWeight L q n * ‖fourierL2 L u.val n‖ ^ 2
  rw [norm_mul, mul_pow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (weight_le h n) (sq_nonneg _)

theorem summable_dcoef {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) (u : H02 L q) :
    Summable fun n => ‖dcoef a u n‖ :=
  (tsum_norm_le_cL (Fact.out : 0 < L) (mem04_dcoef h u)).1

/-- The continuous function `∂^a u` of an `H^q` field, `a + 1 ≤ q`. -/
def jetFun {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) (u : H02 L q) : C(AddCircle L, ℂ) :=
  ⟨seriesRep L (dcoef a u), continuous_seriesRep (summable_dcoef h u)⟩

theorem norm_jetFun_le {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) (u : H02 L q) :
    ‖jetFun h u‖ ≤ cL L * ‖u‖ := by
  have hL : 0 < L := Fact.out
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  refine (ContinuousMap.norm_le _ (mul_nonneg (cL_nonneg L) (norm_nonneg u))).2 (fun x => ?_)
  obtain ⟨hS, hle⟩ := tsum_norm_le_cL hL (mem04_dcoef h u)
  have hnorm : Real.sqrt (f04NormSq L 1 (dcoef a u)) ≤ ‖u‖ := by
    rw [← Real.sqrt_sq (norm_nonneg u)]
    exact Real.sqrt_le_sqrt (f04NormSq_dcoef_le h u)
  show ‖seriesRep L (dcoef a u) x‖ ≤ _
  calc ‖seriesRep L (dcoef a u) x‖ ≤ (Real.sqrt L)⁻¹ * ∑' n, ‖dcoef a u n‖ := norm_seriesRep_le hS x
    _ ≤ (Real.sqrt L)⁻¹ * (Real.sqrt L * cL L * Real.sqrt (f04NormSq L 1 (dcoef a u))) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hs.le)
    _ ≤ (Real.sqrt L)⁻¹ * (Real.sqrt L * cL L * ‖u‖) := by
        gcongr
        exact mul_nonneg hs.le (cL_nonneg L)
    _ = cL L * ‖u‖ := by field_simp

/-- `jetFun` as a `ℂ`-linear map. -/
def jetₗ {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) : H02 L q →ₗ[ℂ] C(AddCircle L, ℂ) where
  toFun := jetFun h
  map_add' u v := by
    ext x
    have e : dcoef a (u + v) = fun n => dcoef a u n + dcoef a v n := by
      funext n
      simp only [dcoef, WField.val_add, map_add, lp.coeFn_add, Pi.add_apply, mul_add]
    show seriesRep L (dcoef a (u + v)) x = seriesRep L (dcoef a u) x + seriesRep L (dcoef a v) x
    rw [e, seriesRep_add' (summable_dcoef h u) (summable_dcoef h v)]
  map_smul' c u := by
    ext x
    have e : dcoef a (c • u) = fun n => c * dcoef a u n := by
      funext n
      simp only [dcoef, WField.val_smul, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    show seriesRep L (dcoef a (c • u)) x = c * seriesRep L (dcoef a u) x
    rw [e, seriesRep_smul']

theorem jetₗ_apply {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) (u : H02 L q) : jetₗ h u = jetFun h u := rfl

/-- **The jet map** `u ↦ ∂^a u ∈ C(𝕋_L, ℂ)`, continuous linear on `H^q` for `a + 1 ≤ q`. -/
def jet {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) : H02 L q →L[ℂ] C(AddCircle L, ℂ) :=
  (jetₗ h).mkContinuous (cL L) (fun u => by rw [jetₗ_apply]; exact norm_jetFun_le h u)

theorem jet_apply {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) (u : H02 L q) (x : AddCircle L) :
    jet h u x = seriesRep L (dcoef a u) x := rfl

/-! ### Smooth periodic profiles -/

theorem smooth_iter {f : ℝ → ℂ} (hf : SmoothPeriodic L f) (a : ℕ) :
    SmoothPeriodic L (iteratedDeriv a f) := by
  induction a with
  | zero => simpa using hf
  | succ a ih => rw [iteratedDeriv_succ]; exact smooth_deriv ih

theorem cof_congr {f g : ℝ → ℂ} (h : f = g) (hf : SmoothPeriodic L f) (hg : SmoothPeriodic L g) (n : ℤ) :
    cof hg n = cof hf n := by
  subst h; rfl

theorem cof_iterated {f : ℝ → ℂ} (hf : SmoothPeriodic L f) (a : ℕ) (n : ℤ) :
    cof (smooth_iter hf a) n = ikn L n ^ a * cof hf n := by
  induction a with
  | zero =>
    rw [cof_congr (iteratedDeriv_zero).symm hf (smooth_iter hf 0) n]
    simp
  | succ a ih =>
    rw [cof_congr (iteratedDeriv_succ).symm (smooth_deriv (smooth_iter hf a)) (smooth_iter hf (a + 1)) n]
    have e : cof (smooth_deriv (smooth_iter hf a)) n = ikn L n * cof (smooth_iter hf a) n :=
      coeff_deriv (smooth_iter hf a) n
    rw [e, ih, pow_succ]; ring

theorem jet_smooth {q : ℝ} {a : ℕ} (h : (a : ℝ) + 1 ≤ q) {f : ℝ → ℂ} (hf : SmoothPeriodic L f)
    (hm : MemHsLp L q (smoothL2 hf)) (x : ℝ) :
    jet h (⟨smoothL2 hf, hm⟩ : H02 L q) (x : AddCircle L) = iteratedDeriv a f x := by
  set u : H02 L q := ⟨smoothL2 hf, hm⟩ with hu
  set g : C(AddCircle L, ℂ) := liftC (smooth_iter hf a).smooth.continuous (smooth_iter hf a).periodic with hg
  have hco : coeff L (g : AddCircle L → ℂ) = dcoef a u := by
    funext n
    have e1 : coeff L (g : AddCircle L → ℂ) n = cof (smooth_iter hf a) n := rfl
    rw [e1, cof_iterated]
    show _ = ikn L n ^ a * fourierL2 L (smoothL2 hf) n
    rw [fourierL2_smoothL2]
  have h1 : Mem04 L 1 (coeff L (g : AddCircle L → ℂ)) := by rw [hco]; exact mem04_dcoef h u
  have hae := ae_eq_seriesRep (memLp_of_continuous g.continuous) h1
  rw [hco] at hae
  have heq : (g : AddCircle L → ℂ) = seriesRep L (dcoef a u) :=
    (Continuous.ae_eq_iff_eq volume g.continuous
      (continuous_seriesRep (summable_dcoef h u))).1 hae
  rw [jet_apply, ← heq, hg]
  exact liftC_coe _ _ x

/-! ### Conjugation and integration on `C(𝕋_L, ℂ)` -/

/-- Pointwise complex conjugation, `ℝ`-linear and continuous. -/
def cconj : C(AddCircle L, ℂ) →L[ℝ] C(AddCircle L, ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℝ (AddCircle L) Complex.conjCLE.toContinuousLinearMap

theorem cconj_apply (g : C(AddCircle L, ℂ)) (x : AddCircle L) : cconj g x = conj (g x) := rfl

/-- The integral over `𝕋_L` (mass-`L` measure) as a continuous linear functional on `C(𝕋_L, ℂ)`. -/
def integralCLM : C(AddCircle L, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ x, g x ∂(volume : Measure (AddCircle L))
      map_add' := fun f g => by
        have hf : Integrable f (volume : Measure (AddCircle L)) :=
          f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        have hg : Integrable g (volume : Measure (AddCircle L)) :=
          g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        exact integral_add hf hg
      map_smul' := fun c g => by
        simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
    ((volume : Measure (AddCircle L)).real Set.univ)
    (fun g => by
      have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (AddCircle L))) (f := fun x => g x)
        (C := ‖g‖) (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
      rw [mul_comm]; exact this)

theorem integralCLM_apply (g : C(AddCircle L, ℂ)) :
    integralCLM g = ∫ x, g x ∂(volume : Measure (AddCircle L)) := rfl

theorem integralCLM_liftC {ψ : ℝ → ℂ} (hc : Continuous ψ) (hp : Function.Periodic ψ L) :
    integralCLM (liftC hc hp) = ∫ x in (0 : ℝ)..L, ψ x := by
  rw [integralCLM_apply, ← AddCircle.intervalIntegral_preimage L 0, zero_add]
  congr 1

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.jet
#print axioms QuantumNLS.RB7.jet_smooth
#print axioms QuantumNLS.RB7.cconj
#print axioms QuantumNLS.RB7.integralCLM_liftC
