import Mathlib
import QuantumNLS.CorrelationConstrainedSumGen
import QuantumNLS.CorrelationFourierBridge

/-!
# REG-006 stage (c1): derivatives of the translated correlation (`CC:G04:correlation`)

Source: `source/chapters/regularity/integer_moments.tex`, lines 159--205. Stage (c1) of the split REG-006
work: termwise differentiation of the Fourier series of `C(h) = ∫ ∏_j f_j(x + h_j)`, the statement
`C ∈ C^{2k}(ℝ^q)`, the identification of the iterated derivatives with the differentiated series, and the
uniform bound on partial derivatives of total order `≤ 2k`. Stage (c2), the Taylor remainders, is NOT here.

Imports read-only: `QuantumNLS.CorrelationConstrainedSumGen` (constrained sum, general `q`) and
`QuantumNLS.CorrelationFourierBridge` (Fourier series `Cfun_eq_fourier`, `coefH`, `summable_norm_coefH`).

Route. Each Fourier term is a single character of the frequency form `h ↦ Σ_j a_{n,j} h_j`, with
`a_{n,j} = 2π n_j / L`:
`∏_j fourier(n_j)(h_j) = exp(i ⟨a_n, h⟩)`. Its `d`-th derivative in direction `v_1,…,v_d` is
`∏_i (i ⟨a_n, v_i⟩) · exp(i⟨a_n,h⟩)`, of norm at most `(Σ_j |a_{n,j}|)^d`. The bound
`(Σ_j |a_j|)^d ≤ q^d Σ_j |a_j|^d` and `constrained_bound` with weight `d · e_j` give a summable
uniform majorant for `d ≤ 2k`, so `contDiff_tsum` applies.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open AddCircle MeasureTheory

namespace QuantumNLS.CorrelationDerivatives

open QuantumNLS.CorrelationLatticeBound QuantumNLS.CorrelationConstrainedSum
open QuantumNLS.CorrelationConstrainedSumGen QuantumNLS.CorrelationFourierBridge
open QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

/-- The frequency `a_{n,j} = 2π n_j / L`. -/
def freq (L : ℝ) {q : ℕ} (n : Fin q → ℤ) (j : Fin q) : ℝ := 2 * Real.pi * (n j : ℝ) / L

/-- The linear form `h ↦ Σ_j a_{n,j} h_j` on `ℝ^q`. -/
def lin (L : ℝ) {q : ℕ} (n : Fin q → ℤ) : (Fin q → ℝ) →L[ℝ] ℝ :=
  ∑ j, freq L n j • ContinuousLinearMap.proj j

theorem lin_apply {q : ℕ} (n : Fin q → ℤ) (h : Fin q → ℝ) :
    lin L n h = ∑ j, freq L n j * h j := by
  simp [lin, ContinuousLinearMap.sum_apply]

theorem lin_single {q : ℕ} (n : Fin q → ℤ) (j : Fin q) :
    lin L n (Pi.single j 1) = freq L n j := by
  rw [lin_apply]
  simp [Pi.single_apply]

theorem norm_lin_le {q : ℕ} (n : Fin q → ℤ) : ‖lin L n‖ ≤ ∑ j, |freq L n j| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => abs_nonneg _)
    (fun h => ?_)
  rw [lin_apply, Real.norm_eq_abs]
  calc |∑ j, freq L n j * h j| ≤ ∑ j, |freq L n j * h j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |freq L n j| * ‖h‖ := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm h j)
          (abs_nonneg _)
    _ = (∑ j, |freq L n j|) * ‖h‖ := by rw [Finset.sum_mul]

/-- The Fourier product is one exponential of the frequency form. -/
theorem prod_fourier_eq {q : ℕ} (n : Fin q → ℤ) (h : Fin q → ℝ) :
    ∏ j, fourier (n j) ((h j : ℝ) : AddCircle L) =
      Complex.exp (Complex.I * ((lin L n h : ℝ) : ℂ)) := by
  have hterm : ∀ j, fourier (n j) ((h j : ℝ) : AddCircle L) =
      Complex.exp (Complex.I * ((freq L n j * h j : ℝ) : ℂ)) := by
    intro j
    rw [fourier_coe_apply]
    congr 1
    unfold freq
    push_cast
    ring
  rw [Finset.prod_congr rfl (fun j _ => hterm j), ← Complex.exp_sum]
  congr 1
  simp [lin_apply, Finset.mul_sum, Complex.ofReal_sum]

/-- Smoothness of `s ↦ exp(c s)` on `ℝ`. -/
theorem contDiff_cexp_real (c : ℂ) (N : WithTop ℕ∞) :
    ContDiff ℝ N (fun s : ℝ => Complex.exp (c * (s : ℂ))) := by
  have h1 : ContDiff ℝ N (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
  exact (contDiff_const.mul h1).cexp

/-- Smoothness of `y ↦ exp(c · ℓ(y))` for a continuous linear form `ℓ`. -/
theorem contDiff_cexp_lin {q : ℕ} (c : ℂ) (ℓ : (Fin q → ℝ) →L[ℝ] ℝ) (N : WithTop ℕ∞) :
    ContDiff ℝ N (fun y => Complex.exp (c * ((ℓ y : ℝ) : ℂ))) := by
  have h1 : ContDiff ℝ N (fun y => ((ℓ y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp ℓ.contDiff
  exact (contDiff_const.mul h1).cexp

/-- The `d`-th derivative of `s ↦ exp(c s)` on `ℝ` with complex `c`. -/
theorem iteratedDeriv_cexp_real (c : ℂ) (d : ℕ) :
    iteratedDeriv d (fun s : ℝ => Complex.exp (c * (s : ℂ))) =
      fun s : ℝ => c ^ d * Complex.exp (c * (s : ℂ)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
      simpa using (hasDerivAt_id s).ofReal_comp
    have h1 := ((h0.const_mul c).cexp).const_mul (c ^ d)
    rw [h1.deriv]
    ring

/-- Directional derivatives of `y ↦ exp(c · ℓ(y))` for a continuous linear form `ℓ`. -/
theorem iteratedFDeriv_cexp_lin {q : ℕ} (c : ℂ) (ℓ : (Fin q → ℝ) →L[ℝ] ℝ) (d : ℕ)
    (x : Fin q → ℝ) (v : Fin d → (Fin q → ℝ)) :
    iteratedFDeriv ℝ d (fun y => Complex.exp (c * ((ℓ y : ℝ) : ℂ))) x v =
      (∏ i, c * ((ℓ (v i) : ℝ) : ℂ)) * Complex.exp (c * ((ℓ x : ℝ) : ℂ)) := by
  have hf := contDiff_cexp_real c (d : WithTop ℕ∞)
  have key := ContinuousLinearMap.iteratedFDeriv_comp_right ℓ hf x (i := d) (le_refl _)
  rw [show (fun y => Complex.exp (c * ((ℓ y : ℝ) : ℂ))) =
      (fun s : ℝ => Complex.exp (c * (s : ℂ))) ∘ ℓ from rfl, key,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_cexp_real, Complex.real_smul]
  push_cast
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- A single Fourier term `c · exp(i ⟨a_n, h⟩)` and its `d`-th derivative in directions `v`. -/
theorem iteratedFDeriv_term {q : ℕ} (c : ℂ) (n : Fin q → ℤ) (d : ℕ) (x : Fin q → ℝ)
    (v : Fin d → (Fin q → ℝ)) :
    iteratedFDeriv ℝ d (fun y => c * Complex.exp (Complex.I * ((lin L n y : ℝ) : ℂ))) x v =
      c * ((∏ i, Complex.I * ((lin L n (v i) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((lin L n x : ℝ) : ℂ))) := by
  have hexp := contDiff_cexp_lin Complex.I (lin L n) (d : WithTop ℕ∞)
  rw [show (fun y => c * Complex.exp (Complex.I * ((lin L n y : ℝ) : ℂ))) =
      c • (fun y : Fin q → ℝ => Complex.exp (Complex.I * ((lin L n y : ℝ) : ℂ))) from rfl,
    iteratedFDeriv_const_smul_apply hexp.contDiffAt, ContinuousMultilinearMap.smul_apply,
    iteratedFDeriv_cexp_lin Complex.I (lin L n) d x v, smul_eq_mul]

/-- Norm bound: `‖∂^d (c e^{i⟨a_n,·⟩})(x)‖ ≤ ‖c‖ (Σ_j |a_{n,j}|)^d`, uniformly in `x`. -/
theorem norm_iteratedFDeriv_term_le {q : ℕ} (c : ℂ) (n : Fin q → ℤ) (d : ℕ) (x : Fin q → ℝ) :
    ‖iteratedFDeriv ℝ d (fun y => c * Complex.exp (Complex.I * ((lin L n y : ℝ) : ℂ))) x‖ ≤
      ‖c‖ * (∑ j, |freq L n j|) ^ d := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [iteratedFDeriv_term, norm_mul, norm_mul, norm_prod, Complex.norm_exp_I_mul_ofReal, mul_one]
  have hprod : ∏ i, ‖Complex.I * ((lin L n (m i) : ℝ) : ℂ)‖ ≤
      (∑ j, |freq L n j|) ^ d * ∏ i, ‖m i‖ := by
    have hA : ∀ i, ‖Complex.I * ((lin L n (m i) : ℝ) : ℂ)‖ ≤
        (∑ j, |freq L n j|) * ‖m i‖ := by
      intro i
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm (lin L n) (m i)).trans
        (mul_le_mul_of_nonneg_right (norm_lin_le n) (norm_nonneg _)) |>.trans_eq' (by
          rw [Real.norm_eq_abs])
    calc ∏ i, ‖Complex.I * ((lin L n (m i) : ℝ) : ℂ)‖
        ≤ ∏ i, ((∑ j, |freq L n j|) * ‖m i‖) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hA i)
      _ = (∑ j, |freq L n j|) ^ d * ∏ i, ‖m i‖ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hprod (norm_nonneg _)

/-- Summable-friendly power mean: `(Σ x_j)^d ≤ q^d Σ x_j^d` for nonnegative `x_j`. -/
theorem sum_pow_le_card_mul_sum_pow {q : ℕ} (hq : 1 ≤ q) (x : Fin q → ℝ) (hx : ∀ j, 0 ≤ x j)
    (d : ℕ) : (∑ j, x j) ^ d ≤ (q : ℝ) ^ d * ∑ j, x j ^ d := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hw : ∑ _j : Fin q, (1 : ℝ) / q = 1 := by
    simp [Finset.sum_const, Finset.card_univ]
    field_simp
  have h1 := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ) (fun _ : Fin q => (1 : ℝ) / q) x
    (fun i _ => by positivity) hw (fun i _ => hx i) d
  have hT : 0 ≤ ∑ j, x j ^ d := Finset.sum_nonneg fun j _ => pow_nonneg (hx j) d
  have hS : (∑ j, x j) ^ d = (q : ℝ) ^ d * ((1 / q) * ∑ j, x j) ^ d := by
    rw [mul_pow, ← mul_assoc, ← mul_pow, mul_one_div_cancel hqpos.ne', one_pow, one_mul]
  have hM : (1 / (q : ℝ)) * ∑ j, x j ^ d ≤ ∑ j, x j ^ d :=
    mul_le_of_le_one_left hT (by rw [div_le_one hqpos]; exact_mod_cast hq)
  rw [hS]
  calc (q : ℝ) ^ d * ((1 / q) * ∑ j, x j) ^ d
      ≤ (q : ℝ) ^ d * ∑ j, (1 / (q : ℝ)) * x j ^ d := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [Finset.mul_sum] using h1
    _ = (q : ℝ) ^ d * ((1 / q) * ∑ j, x j ^ d) := by simp only [Finset.mul_sum]
    _ ≤ (q : ℝ) ^ d * ∑ j, x j ^ d := mul_le_mul_of_nonneg_left hM (by positivity)


/-! ## Summation layer and the `C^{2k}` statement -/

/-- The constraint set `{n : Fin (m+2) → ℤ | Σ_j n_j = 0}`, the index set of the Fourier series. -/
abbrev Cset (m : ℕ) : Type := {n : Fin (m + 2) → ℤ // ∑ j, n j = 0}

/-- The coefficient `c_n = L^{1−(m+2)/2} ∏_j coefH(f_j)(n_j)` of the Fourier series of `Cfun`. -/
def cc {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) (n : Fin (m + 2) → ℤ) : ℂ :=
  (((L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ) * ∏ j, coefH hk (f j) (n j)

theorem norm_cc {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) (n : Fin (m + 2) → ℤ) :
    ‖cc hk f n‖ = (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) * ∏ j, ‖coefH hk (f j) (n j)‖ := by
  unfold cc
  rw [norm_mul, norm_prod, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (Fact.out : (0 : ℝ) < L).le _)]

/-- The series of `Cfun` in the form used for differentiation. -/
theorem Cfun_eq_series {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) (h : Fin (m + 2) → ℝ) :
    Cfun f h = ∑' n : Cset m,
      cc hk f n.1 * Complex.exp (Complex.I * ((lin L n.1 h : ℝ) : ℂ)) := by
  rw [Cfun_eq_fourier (by omega) hk f h]
  refine tsum_congr fun n => ?_
  rw [prod_fourier_eq, cc]
  ring

theorem abs_freq {q : ℕ} (n : Fin q → ℤ) (j : Fin q) :
    |freq L n j| = (2 * Real.pi / L) * |(n j : ℝ)| := by
  have hL : (0 : ℝ) < L := Fact.out
  unfold freq
  rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hL]
  ring

theorem prod_pow_single {q : ℕ} (x : Fin q → ℝ) (j : Fin q) (d : ℕ) :
    ∏ i, x i ^ (Pi.single j d : Fin q → ℕ) i = x j ^ d := by
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem prod_comp_fiber {d q : ℕ} (js : Fin d → Fin q) (g : Fin q → ℝ) :
    ∏ i, g (js i) = ∏ j, g j ^ (Finset.univ.filter (fun i => js i = j)).card := by
  rw [← Finset.prod_fiberwise Finset.univ js (fun i => g (js i))]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.prod_const]

theorem sum_card_fiber {d q : ℕ} (js : Fin d → Fin q) :
    ∑ j, (Finset.univ.filter (fun i => js i = j)).card = d := by
  rw [← Finset.card_eq_sum_card_fiberwise (f := js) (s := Finset.univ) (t := Finset.univ)
    (fun i _ => Finset.mem_univ _)]
  simp

/-- Each single-coordinate weighted family is summable over the constraint set, for `d ≤ 2k`. -/
theorem summable_norm_cc_freq {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) {d : ℕ}
    (hd : d ≤ 2 * k) (j : Fin (m + 2)) :
    Summable (fun n : Cset m => ‖cc hk f n.1‖ * |freq L n.1 j| ^ d) := by
  have hL : (0 : ℝ) < L := Fact.out
  have hα : ∑ i, (Pi.single j d : Fin (m + 2) → ℕ) i ≤ 2 * k := by
    simp [Pi.single_apply]
    omega
  have hcon := constrained_bound (m := m) (k := k) hk (Pi.single j d) hα
    (fun i => coefH hk (f i)) (fun i => (coef_weighted_bound hk (f i)).1)
  refine Summable.congr (hcon.1.mul_left ((L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) *
    (2 * Real.pi / L) ^ d)) (fun n => ?_)
  have hp := prod_pow_single (fun i => |((n.1 i : ℤ) : ℝ)|) j d
  rw [norm_cc, abs_freq, mul_pow, hp]
  ring

/-- Summable uniform majorant `‖c_n‖ (Σ_j |a_{n,j}|)^d` over the constraint set, for `d ≤ 2k`. -/
theorem summable_norm_cc_sum {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) {d : ℕ}
    (hd : d ≤ 2 * k) :
    Summable (fun n : Cset m => ‖cc hk f n.1‖ * (∑ j, |freq L n.1 j|) ^ d) := by
  have hq : 1 ≤ m + 2 := by omega
  have hsum2 : Summable (fun n : Cset m =>
      ∑ j, ((m + 2 : ℕ) : ℝ) ^ d * (‖cc hk f n.1‖ * |freq L n.1 j| ^ d)) :=
    summable_sum fun j _ => (summable_norm_cc_freq hk f hd j).mul_left (((m + 2 : ℕ) : ℝ) ^ d)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) _))
    (fun n => ?_) hsum2
  calc ‖cc hk f n.1‖ * (∑ j, |freq L n.1 j|) ^ d
      ≤ ‖cc hk f n.1‖ * (((m + 2 : ℕ) : ℝ) ^ d * ∑ j, |freq L n.1 j| ^ d) :=
        mul_le_mul_of_nonneg_left
          (sum_pow_le_card_mul_sum_pow hq _ (fun j => abs_nonneg _) d) (norm_nonneg _)
    _ = ∑ j, ((m + 2 : ℕ) : ℝ) ^ d * (‖cc hk f n.1‖ * |freq L n.1 j| ^ d) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- The series of `Cfun` is `C^{2k}`: the termwise Fourier terms are smooth, with the uniform summable
majorant of `summable_norm_cc_sum`. -/
theorem contDiff_Cfun {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) :
    ContDiff ℝ ((2 * k : ℕ) : WithTop ℕ∞) (fun h => Cfun f h) := by
  have hfun : (fun h => Cfun f h) = fun h =>
      ∑' n : Cset m, cc hk f n.1 * Complex.exp (Complex.I * ((lin L n.1 h : ℝ) : ℂ)) :=
    funext (Cfun_eq_series hk f)
  rw [hfun]
  refine contDiff_tsum (f := fun (n : Cset m) (y : Fin (m + 2) → ℝ) =>
      cc hk f n.1 * Complex.exp (Complex.I * ((lin L n.1 y : ℝ) : ℂ)))
    (v := fun d n => ‖cc hk f n.1‖ * (∑ j, |freq L n.1 j|) ^ d)
    (fun n => contDiff_const.mul (contDiff_cexp_lin Complex.I (lin L n.1)
      ((2 * k : ℕ) : WithTop ℕ∞))) ?_ ?_
  · intro d hd
    exact summable_norm_cc_sum hk f (by exact_mod_cast hd)
  · intro d n x _
    exact norm_iteratedFDeriv_term_le _ _ _ _

/-- Evaluation of a convergent `tsum` of continuous multilinear maps at a direction tuple. -/
theorem tsum_cmlm_apply {ι : Type*} {d q : ℕ}
    (M : ι → ContinuousMultilinearMap ℝ (fun _ : Fin d => Fin q → ℝ) ℂ)
    (hM : Summable M) (v : Fin d → (Fin q → ℝ)) :
    (∑' i, M i) v = ∑' i, M i v := by
  have := (ContinuousMultilinearMap.apply (𝕜 := ℝ) (E := fun _ : Fin d => Fin q → ℝ) (F := ℂ) v).map_tsum hM
  simpa using this

/-- The `d`-th derivative of `C` at `h` is the convergent series of the termwise derivatives (as
continuous multilinear maps). -/
theorem iteratedFDeriv_Cfun_eq_tsum {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) {d : ℕ}
    (hd : d ≤ 2 * k) (h : Fin (m + 2) → ℝ) :
    iteratedFDeriv ℝ d (fun y => Cfun f y) h =
      ∑' n : Cset m, iteratedFDeriv ℝ d
        (fun y => cc hk f n.1 * Complex.exp (Complex.I * ((lin L n.1 y : ℝ) : ℂ))) h := by
  have hfun : (fun y => Cfun f y) = fun y =>
      ∑' n : Cset m, cc hk f n.1 * Complex.exp (Complex.I * ((lin L n.1 y : ℝ) : ℂ)) :=
    funext (Cfun_eq_series hk f)
  have hN : (d : ℕ∞) ≤ ((2 * k : ℕ) : ℕ∞) := by exact_mod_cast hd
  rw [hfun]
  exact iteratedFDeriv_tsum_apply (N := ((2 * k : ℕ) : ℕ∞))
    (f := fun (n : Cset m) (y : Fin (m + 2) → ℝ) =>
      cc hk f n.1 * Complex.exp (Complex.I * ((lin L n.1 y : ℝ) : ℂ)))
    (fun n => contDiff_const.mul (contDiff_cexp_lin Complex.I (lin L n.1)
      ((2 * k : ℕ) : WithTop ℕ∞)))
    (v := fun d n => ‖cc hk f n.1‖ * (∑ j, |freq L n.1 j|) ^ d)
    (fun d' hd' => summable_norm_cc_sum hk f (by exact_mod_cast hd'))
    (fun d' n x _ => norm_iteratedFDeriv_term_le _ _ _ _) hN h

/-- Termwise identity: the `d`-th derivative of `C` in directions `v` is the series of the termwise
derivatives. -/
theorem iteratedFDeriv_Cfun_apply {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) {d : ℕ}
    (hd : d ≤ 2 * k) (h : Fin (m + 2) → ℝ) (v : Fin d → (Fin (m + 2) → ℝ)) :
    iteratedFDeriv ℝ d (fun y => Cfun f y) h v =
      ∑' n : Cset m, cc hk f n.1 *
        ((∏ i, Complex.I * ((lin L n.1 (v i) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((lin L n.1 h : ℝ) : ℂ))) := by
  have hS : Summable (fun n : Cset m => iteratedFDeriv ℝ d
      (fun y => cc hk f n.1 * Complex.exp (Complex.I * ((lin L n.1 y : ℝ) : ℂ))) h) :=
    Summable.of_norm_bounded (summable_norm_cc_sum hk f hd)
      (fun n => norm_iteratedFDeriv_term_le _ _ _ _)
  rw [iteratedFDeriv_Cfun_eq_tsum hk f hd h, tsum_cmlm_apply _ hS v]
  refine tsum_congr fun n => ?_
  rw [iteratedFDeriv_term]

/-- The norm of a single term evaluated at a direction tuple of basis vectors. -/
theorem norm_term_basis {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) {d : ℕ}
    (js : Fin d → Fin (m + 2)) (h : Fin (m + 2) → ℝ) (n : Cset m) :
    ‖cc hk f n.1 * ((∏ i, Complex.I * ((lin L n.1 (Pi.single (js i) (1 : ℝ)) : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((lin L n.1 h : ℝ) : ℂ)))‖ =
      ‖cc hk f n.1‖ * ∏ i, |freq L n.1 (js i)| := by
  rw [norm_mul, norm_mul, norm_prod, Complex.norm_exp_I_mul_ofReal, mul_one]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, lin_single]

/-- **Partial derivative bound.** For `d ≤ 2k`, `q = m + 2 ≥ 2`, `k ≥ 1`, and any multi-index
`(j_1, …, j_d)` (the partial derivative `∂_{j_1} ⋯ ∂_{j_d} C`), uniformly in `h ∈ ℝ^{m+2}`:
`|∂_{j_1} ⋯ ∂_{j_d} C(h)| ≤ max(1, 2π/L)^{2k} · L^{1−(m+2)/2} · (2^k)^m (m+2)(m+1) C_k^{m+2}
· min(1, 2π/L)^{−k(m+2)} · ∏_j ‖f_j‖_{H^k}`, with `C_k = (Σ_x W(x)^{−2k})^{1/2}`. -/
theorem partial_derivative_bound {m k : ℕ} (hk : 1 ≤ k) (f : Fin (m + 2) → Hk L k) {d : ℕ}
    (hd : d ≤ 2 * k) (js : Fin d → Fin (m + 2)) (h : Fin (m + 2) → ℝ) :
    ‖iteratedFDeriv ℝ d (fun y => Cfun f y) h (fun i => Pi.single (js i) (1 : ℝ))‖ ≤
      (max 1 (2 * Real.pi / L)) ^ (2 * k) * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) *
        (((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (Ckc k) ^ (m + 2)) *
        ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ ^ (m + 2) * ∏ j, ‖f j‖ := by
  have hL : (0 : ℝ) < L := Fact.out
  have hmin : 0 < min 1 (2 * Real.pi / L) := lt_min one_pos (div_pos (by positivity) hL)
  have hPnn : 0 ≤ (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) := Real.rpow_nonneg hL.le _
  set α : Fin (m + 2) → ℕ := fun j => (Finset.univ.filter (fun i => js i = j)).card with hαdef
  have hαsum : ∑ j, α j ≤ 2 * k := by
    rw [hαdef, sum_card_fiber]
    exact hd
  have hcon := constrained_bound (m := m) (k := k) hk α hαsum
    (fun i => coefH hk (f i)) (fun i => (coef_weighted_bound hk (f i)).1)
  -- each term is a coefficient times the basis-direction product of frequencies
  have hfam : ∀ n : Cset m, ‖cc hk f n.1‖ * ∏ i, |freq L n.1 (js i)| =
      ((2 * Real.pi / L) ^ d * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2)) *
        ((∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖coefH hk (f j) (n.1 j)‖) := by
    intro n
    have hp : ∏ i, |freq L n.1 (js i)| = (2 * Real.pi / L) ^ d * ∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j := by
      simp only [abs_freq]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        prod_comp_fiber js (fun j => |((n.1 j : ℤ) : ℝ)|)]
    rw [norm_cc, hp]
    ring
  have hsumC : Summable (fun n : Cset m => ‖cc hk f n.1‖ * ∏ i, |freq L n.1 (js i)|) :=
    (hcon.1.mul_left ((2 * Real.pi / L) ^ d * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2))).congr
      (fun n => (hfam n).symm)
  have hterm := fun n : Cset m => norm_term_basis hk f js h n
  have hsumT : Summable (fun n : Cset m => ‖cc hk f n.1 * ((∏ i, Complex.I *
      ((lin L n.1 (Pi.single (js i) (1 : ℝ)) : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((lin L n.1 h : ℝ) : ℂ)))‖) :=
    hsumC.congr (fun n => (hterm n).symm)
  -- norm of the series ≤ series of norms
  have hN : ∀ j, Nc (fun j => coefH hk (f j)) k j ≤ ‖f j‖ * ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ := by
    intro j
    have h1 := (coef_weighted_bound hk (f j)).2
    have hpos : 0 < (min 1 (2 * Real.pi / L)) ^ k := pow_pos hmin k
    have hN' : Nc (fun j => coefH hk (f j)) k j =
        Real.sqrt (∑' x : ℤ, Wt x ^ (2 * k) * ‖coefH hk (f j) x‖ ^ 2) := rfl
    rw [hN']
    calc Real.sqrt (∑' x : ℤ, Wt x ^ (2 * k) * ‖coefH hk (f j) x‖ ^ 2)
        = ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ *
            ((min 1 (2 * Real.pi / L)) ^ k * Real.sqrt (∑' x : ℤ, Wt x ^ (2 * k) * ‖coefH hk (f j) x‖ ^ 2)) := by
          field_simp
      _ ≤ ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ * ‖f j‖ :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hpos.le)
      _ = ‖f j‖ * ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ := mul_comm _ _
  have hprodN : ∏ j, Nc (fun j => coefH hk (f j)) k j ≤
      ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ ^ (m + 2) * ∏ j, ‖f j‖ := by
    calc ∏ j, Nc (fun j => coefH hk (f j)) k j
        ≤ ∏ j, (‖f j‖ * ((min 1 (2 * Real.pi / L)) ^ k)⁻¹) :=
          Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) (fun j _ => hN j)
      _ = ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ ^ (m + 2) * ∏ j, ‖f j‖ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            mul_comm]
  have hX : (2 * Real.pi / L) ^ d ≤ (max 1 (2 * Real.pi / L)) ^ (2 * k) :=
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) d).trans
      (pow_le_pow_right₀ (le_max_left _ _) hd)
  have hK : 0 ≤ ((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (Ckc k) ^ (m + 2) := by
    have : 0 ≤ Ckc k := Real.sqrt_nonneg _
    positivity
  have hprodNnn : 0 ≤ ∏ j, Nc (fun j => coefH hk (f j)) k j :=
    Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
  calc ‖iteratedFDeriv ℝ d (fun y => Cfun f y) h (fun i => Pi.single (js i) (1 : ℝ))‖
      = ‖∑' n : Cset m, cc hk f n.1 * ((∏ i, Complex.I *
          ((lin L n.1 (Pi.single (js i) (1 : ℝ)) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((lin L n.1 h : ℝ) : ℂ)))‖ := by
        rw [iteratedFDeriv_Cfun_apply hk f hd h]
    _ ≤ ∑' n : Cset m, ‖cc hk f n.1 * ((∏ i, Complex.I *
          ((lin L n.1 (Pi.single (js i) (1 : ℝ)) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((lin L n.1 h : ℝ) : ℂ)))‖ :=
        norm_tsum_le_tsum_norm hsumT
    _ = ∑' n : Cset m, ‖cc hk f n.1‖ * ∏ i, |freq L n.1 (js i)| := tsum_congr hterm
    _ = ((2 * Real.pi / L) ^ d * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2)) *
          ∑' n : Cset m, ((∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖coefH hk (f j) (n.1 j)‖) := by
        rw [← tsum_mul_left]
        exact tsum_congr hfam
    _ ≤ ((2 * Real.pi / L) ^ d * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2)) *
          ((((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (Ckc k) ^ (m + 2)) *
            ∏ j, Nc (fun j => coefH hk (f j)) k j) :=
        mul_le_mul_of_nonneg_left hcon.2 (mul_nonneg (by positivity) hPnn)
    _ ≤ (max 1 (2 * Real.pi / L)) ^ (2 * k) * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) *
          (((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (Ckc k) ^ (m + 2)) *
          ((min 1 (2 * Real.pi / L)) ^ k)⁻¹ ^ (m + 2) * ∏ j, ‖f j‖ := by
        have hmax : 0 ≤ (max 1 (2 * Real.pi / L)) ^ (2 * k) :=
          pow_nonneg (le_max_of_le_left zero_le_one) _
        calc ((2 * Real.pi / L) ^ d * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2)) *
              ((((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (Ckc k) ^ (m + 2)) *
                ∏ j, Nc (fun j => coefH hk (f j)) k j)
            ≤ (max 1 (2 * Real.pi / L)) ^ (2 * k) * (L : ℝ) ^ (1 - ((m + 2 : ℕ) : ℝ) / 2) *
              ((((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (Ckc k) ^ (m + 2)) *
                (((min 1 (2 * Real.pi / L)) ^ k)⁻¹ ^ (m + 2) * ∏ j, ‖f j‖)) :=
              mul_le_mul (mul_le_mul_of_nonneg_right hX hPnn) (mul_le_mul_of_nonneg_left hprodN hK)
                (mul_nonneg hK hprodNnn) (mul_nonneg hmax hPnn)
          _ = _ := by ring

end QuantumNLS.CorrelationDerivatives

/-! Axiom audit (chunk 1). -/
#print axioms QuantumNLS.CorrelationDerivatives.prod_fourier_eq
#print axioms QuantumNLS.CorrelationDerivatives.iteratedDeriv_cexp_real
#print axioms QuantumNLS.CorrelationDerivatives.iteratedFDeriv_cexp_lin
#print axioms QuantumNLS.CorrelationDerivatives.iteratedFDeriv_term
#print axioms QuantumNLS.CorrelationDerivatives.norm_iteratedFDeriv_term_le
#print axioms QuantumNLS.CorrelationDerivatives.sum_pow_le_card_mul_sum_pow
#print axioms QuantumNLS.CorrelationDerivatives.summable_norm_cc_sum
#print axioms QuantumNLS.CorrelationDerivatives.contDiff_Cfun
#print axioms QuantumNLS.CorrelationDerivatives.iteratedFDeriv_Cfun_eq_tsum
#print axioms QuantumNLS.CorrelationDerivatives.iteratedFDeriv_Cfun_apply
#print axioms QuantumNLS.CorrelationDerivatives.partial_derivative_bound
#print axioms QuantumNLS.CorrelationDerivatives.lin_apply
#print axioms QuantumNLS.CorrelationDerivatives.lin_single
#print axioms QuantumNLS.CorrelationDerivatives.norm_lin_le
#print axioms QuantumNLS.CorrelationDerivatives.contDiff_cexp_real
#print axioms QuantumNLS.CorrelationDerivatives.contDiff_cexp_lin
#print axioms QuantumNLS.CorrelationDerivatives.norm_cc
#print axioms QuantumNLS.CorrelationDerivatives.Cfun_eq_series
#print axioms QuantumNLS.CorrelationDerivatives.abs_freq
#print axioms QuantumNLS.CorrelationDerivatives.prod_pow_single
#print axioms QuantumNLS.CorrelationDerivatives.prod_comp_fiber
#print axioms QuantumNLS.CorrelationDerivatives.sum_card_fiber
#print axioms QuantumNLS.CorrelationDerivatives.summable_norm_cc_freq
#print axioms QuantumNLS.CorrelationDerivatives.tsum_cmlm_apply
#print axioms QuantumNLS.CorrelationDerivatives.norm_term_basis
