import Mathlib
import QuantumNLS.RB7Smooth
import QuantumNLS.SobolevSpaces

/-!
# R-7B122087 `thm:hierarchy`, sub-obligation A7b(a): joint `(t,x)`-smoothness (RB7H, haiku_inventory)

Printed use: "`u(t)=(Z^new)^{-1} z(t)` is smooth in space and time" (termwise Fourier smoothness in two variables).

Input (explicit, no chart, no REG-015): a curve `u : ℝ → L²(𝕋_L)` which lies in every `H^q`, `q ≥ 0`, as a `C^∞` curve
(`hlift`).  Output: a jointly `C^∞` function `G : ℝ × ℝ → ℂ` which for each `τ` is a smooth periodic representative of `u τ`
(as an `L²` class), with the explicit Fourier formula `G (τ,x) = Σ_n (√L)^{-1} e^{i 2πn x/L} û_n(τ)`.

Method (no time-uniform bounds needed): for `s > 1` the coefficient functionals `ℓ_n : H^s → ℂ`, `ℓ_n v = û_n(v)`, satisfy
`‖ℓ_n‖ ≤ (1+|2πn/L|)^{-s}` (from the `H^s` norm).  The map `x ↦ Φ_s(x) := Σ_n c_n(x) ℓ_n ∈ (H^s →L ℂ)`, `c_n(x) = (√L)^{-1} e^{i ω_n x}`,
is `C^k` on `ℝ` for `s = k+2` (`contDiff_tsum` in the Banach space `H^s →L ℂ`, derivative bounds `|ω_n|^j(1+|ω_n|)^{-s}` summable).
Then `G (τ,x) = Φ_s(x)(v(τ))` with `v` the `C^∞` lift into `H^s`, a composition of `C^k` maps through the bilinear evaluation (`ContDiff.clm_apply`).

Module imports only the verified RB7Smooth (`iteratedDeriv_expterm`, `summable_cof_pow`, `mem04_of_memHs`) and SobolevSpaces.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set

namespace QuantumNLS.RB7H

open QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.PhysicalTensor QuantumNLS.ClassicalCharges
open QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.RB7 QuantumNLS.WeakDerivatives

variable {L : ℝ} [Fact (0 < L)]

/-- The base `1 + |2πn/L|` of the DEF-002 weights. -/
theorem one_le_base (n : ℤ) : 1 ≤ 1 + |2 * Real.pi * (n : ℝ) / L| := by
  linarith [abs_nonneg (2 * Real.pi * (n : ℝ) / L)]

/-- Decay of the DEF-002 base: `Σ_n (1+|2πn/L|)^{-p} < ∞` for `p > 1`. -/
theorem summable_base_rpow {p : ℝ} (hp : 1 < p) :
    Summable fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-p) := by
  have hL : 0 < L := Fact.out
  set c : ℝ := min 1 (2 * Real.pi / L) with hc
  have hcpos : 0 < c := lt_min one_pos (div_pos (by positivity) hL)
  have h1 : Summable fun n : ℤ => c ^ (-p) * |(n : ℝ)| ^ (-p) :=
    (Real.summable_abs_int_rpow hp).mul_left _
  refine Summable.of_norm_bounded_eventually h1 ?_
  have hev : ∀ᶠ n : ℤ in cofinite, n ≠ 0 := Filter.eventually_cofinite_ne 0
  filter_upwards [hev] with n hn
  have hn' : (0 : ℝ) < |(n : ℝ)| := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    exact abs_pos.2 this
  have hωge : c * |(n : ℝ)| ≤ |2 * Real.pi * (n : ℝ) / L| := by
    have e : |2 * Real.pi * (n : ℝ) / L| = (2 * Real.pi / L) * |(n : ℝ)| := by
      rw [show 2 * Real.pi * (n : ℝ) / L = (2 * Real.pi / L) * (n : ℝ) by ring, abs_mul,
        abs_of_pos (div_pos (by positivity) hL)]
    rw [e]
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
  have hpos : 0 < c * |(n : ℝ)| := mul_pos hcpos hn'
  have hbase : c * |(n : ℝ)| ≤ 1 + |2 * Real.pi * (n : ℝ) / L| := by
    have : 0 ≤ |2 * Real.pi * (n : ℝ) / L| := abs_nonneg _
    linarith
  have hnn : 0 ≤ (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-p) := by
    apply Real.rpow_nonneg; linarith [abs_nonneg (2 * Real.pi * (n : ℝ) / L)]
  rw [Real.norm_of_nonneg hnn, ← Real.mul_rpow hcpos.le (abs_nonneg _)]
  exact Real.rpow_le_rpow_of_nonpos hpos hbase (by linarith)

/-! ## Coefficient functionals on `H^s` -/

/-- The Fourier coefficient functional `v ↦ û_n` on the physical Sobolev space `H^s`. -/
def coefLin (s : ℝ) (n : ℤ) : H02 L s →ₗ[ℂ] ℂ where
  toFun v := fourierL2 L v.val n
  map_add' v w := by
    simp [WField.val_add]
  map_smul' c v := by
    simp [WField.val_smul]

/-- `|û_n(v)| ≤ (1+|2πn/L|)^{-s} ‖v‖_{H^s}`. -/
theorem norm_coefLin_le {s : ℝ} (hs : 0 ≤ s) (n : ℤ) (v : H02 L s) :
    ‖coefLin (L := L) s n v‖ ≤ (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-s) * ‖v‖ := by
  set w : ℝ := 1 + |2 * Real.pi * (n : ℝ) / L| with hw
  have hw1 : 1 ≤ w := one_le_base n
  have hw0 : 0 < w := by linarith
  have hsum := WField.norm_sq_eq_tsum (L := L) v
  have hle : (def002 L s).w n * ‖fourierL2 L v.val n‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hsum]
    exact (WField.summable (L := L) v).le_tsum n (fun j _ => mul_nonneg ((def002 L s).pos j).le (sq_nonneg _))
  have hwn : (def002 L s).w n = w ^ (2 * s) := rfl
  have hA : w ^ (2 * s) = (w ^ s) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0.le]
    congr 1; push_cast; ring
  have hApos : 0 < w ^ s := Real.rpow_pos_of_pos hw0 s
  have h2 : ((w ^ s) * ‖fourierL2 L v.val n‖) ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [mul_pow, ← hA, ← hwn]; exact hle
  have h3 : (w ^ s) * ‖fourierL2 L v.val n‖ ≤ ‖v‖ :=
    (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h2
  have e : ‖coefLin (L := L) s n v‖ = ‖fourierL2 L v.val n‖ := rfl
  rw [e, Real.rpow_neg hw0.le]
  rw [← div_eq_inv_mul, le_div_iff₀ hApos]
  linarith [mul_comm (‖fourierL2 L v.val n‖) (w ^ s)]

/-- The coefficient functional as a continuous linear map on `H^s`. -/
def coefCLM (s : ℝ) (hs : 0 ≤ s) (n : ℤ) : H02 L s →L[ℂ] ℂ :=
  LinearMap.mkContinuous (coefLin (L := L) s n) ((1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-s))
    (fun v => norm_coefLin_le hs n v)

theorem norm_coefCLM_le {s : ℝ} (hs : 0 ≤ s) (n : ℤ) :
    ‖coefCLM (L := L) s hs n‖ ≤ (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-s) :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg (by linarith [abs_nonneg (2 * Real.pi * (n : ℝ) / L)]) _) _

/-- The unit-normalized exponential `c_n(x) = (√L)^{-1} e^{i 2πn x/L}` (as in `seriesRep`). -/
def cfun (L : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp ((Complex.I * (freq L n : ℂ)) * (x : ℂ))

theorem contDiff_cfun (n : ℤ) : ContDiff ℝ ∞ (cfun L n) := by
  unfold cfun
  exact contDiff_const.mul (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))

theorem norm_cfun (n : ℤ) (x : ℝ) : ‖cfun L n x‖ = (Real.sqrt L)⁻¹ := by
  have hL : 0 < L := Fact.out
  have hE : ‖Complex.exp ((Complex.I * (freq L n : ℂ)) * (x : ℂ))‖ = 1 := by
    have : (Complex.I * (freq L n : ℂ)) * (x : ℂ) = ((freq L n * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  unfold cfun
  rw [norm_mul, hE, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hL))]

/-- The `(H^s →L ℂ)`-valued Fourier series `Φ_s(x) = Σ_n c_n(x) ℓ_n` (for `s > 1`). -/
def Phi (s : ℝ) (hs : 0 ≤ s) (x : ℝ) : H02 L s →L[ℂ] ℂ :=
  ∑' n : ℤ, cfun L n x • coefCLM (L := L) s hs n

/-! ## Joint smoothness of `G(τ,x) = Φ_s(x)(v(τ))` -/

/-- Derivative bound for one term: `‖∂^j (c_n • ℓ_n)‖ ≤ (1+|ω_n|)^{-s} (√L)^{-1} |ω_n|^j`. -/
theorem norm_iteratedFDeriv_term (s : ℝ) (hs : 0 ≤ s) (n : ℤ) (j : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : ℝ => cfun L n y • coefCLM (L := L) s hs n) x‖ ≤
      (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-s) * ((Real.sqrt L)⁻¹ * |freq L n| ^ j) := by
  have hL : 0 < L := Fact.out
  set M : ℂ →L[ℝ] (H02 L s →L[ℂ] ℂ) :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (coefCLM (L := L) s hs n)).restrictScalars ℝ with hM
  have hfun : (fun y : ℝ => cfun L n y • coefCLM (L := L) s hs n) = fun y => M (cfun L n y) := by
    funext y; simp [hM]
  rw [hfun]
  have hcd : ContDiffAt ℝ ∞ (cfun L n) x := (contDiff_cfun n).contDiffAt
  have h1 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left M hcd (n := j) (by simp)
  have hMn : ‖M‖ ≤ (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-s) := by
    have : ‖M‖ ≤ ‖coefCLM (L := L) s hs n‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun z => by
        rw [hM]; simp [norm_smul, mul_comm])
    exact this.trans (norm_coefCLM_le hs n)
  have hit : ‖iteratedFDeriv ℝ j (cfun L n) x‖ = (Real.sqrt L)⁻¹ * |freq L n| ^ j := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hd : iteratedDeriv j (cfun L n) = fun y : ℝ =>
        (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (Complex.I * (freq L n : ℂ)) ^ j *
          Complex.exp ((Complex.I * (freq L n : ℂ)) * (y : ℂ)) :=
      iteratedDeriv_expterm _ _ j
    rw [hd]
    have hE : ‖Complex.exp ((Complex.I * (freq L n : ℂ)) * (x : ℂ))‖ = 1 := by
      have : (Complex.I * (freq L n : ℂ)) * (x : ℂ) = ((freq L n * x : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have hI : ‖(Complex.I * (freq L n : ℂ))‖ = |freq L n| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, norm_pow, hE, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 hL)), hI]
  calc ‖iteratedFDeriv ℝ j (fun y => M (cfun L n y)) x‖
      ≤ ‖M‖ * ‖iteratedFDeriv ℝ j (cfun L n) x‖ := h1
    _ ≤ (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-s) * ((Real.sqrt L)⁻¹ * |freq L n| ^ j) := by
      rw [hit]
      exact mul_le_mul_of_nonneg_right hMn (by positivity)

/-- The weight `|ω_n|^j (1+|ω_n|)^{-(k+2)}` is summable for `j ≤ k`. -/
theorem summable_term_bound (k j : ℕ) (hj : j ≤ k) :
    Summable fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-((k : ℝ) + 2)) * |freq L n| ^ j := by
  have hL : 0 < L := Fact.out
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_base_rpow (L := L) (p := 2) one_lt_two)
  set b : ℝ := 1 + |2 * Real.pi * (n : ℝ) / L| with hb
  have hb1 : 1 ≤ b := one_le_base n
  have hfr : |freq L n| ≤ b := by
    have : freq L n = 2 * Real.pi * (n : ℝ) / L := rfl
    rw [this]; linarith [abs_nonneg (2 * Real.pi * (n : ℝ) / L)]
  have hpow : |freq L n| ^ j ≤ b ^ (k : ℕ) := by
    calc |freq L n| ^ j ≤ b ^ j := pow_le_pow_left₀ (abs_nonneg _) hfr j
      _ ≤ b ^ k := pow_le_pow_right₀ hb1 hj
  have hsplit : b ^ (k : ℕ) * b ^ (-((k : ℝ) + 2)) = b ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]
    congr 1; push_cast; ring
  calc b ^ (-((k : ℝ) + 2)) * |freq L n| ^ j
      ≤ b ^ (-((k : ℝ) + 2)) * b ^ (k : ℕ) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by linarith) _)
    _ = b ^ (-(2 : ℝ)) := by rw [mul_comm]; exact hsplit
    _ = (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-(2 : ℝ)) := rfl


/-! ## Evaluation pairing and the series `Φ_s` -/

/-- The evaluation `(φ, v) ↦ φ v` on `(H^s →L[ℂ] ℂ) × H^s` is a bounded bilinear map over `ℝ`. -/
theorem isBoundedBilinear_eval (s : ℝ) :
    IsBoundedBilinearMap ℝ (fun p : (H02 L s →L[ℂ] ℂ) × H02 L s => p.1 p.2) where
  add_left x₁ x₂ y := by simp
  smul_left c x y := by
    simp [Complex.real_smul]
  add_right x y₁ y₂ := by simp
  smul_right c x y := by
    rw [← Complex.coe_smul c y, map_smul, Complex.coe_smul c (x y)]
  bound := ⟨1, one_pos, fun x y => by
    simpa using ContinuousLinearMap.le_opNorm x y⟩

/-! ## The series `Φ_s` and the joint function `G` -/

theorem summable_Phi_terms {s : ℝ} (hs : 1 < s) (hs0 : 0 ≤ s) (x : ℝ) :
    Summable fun n : ℤ => cfun L n x • coefCLM (L := L) s hs0 n := by
  have hL : 0 < L := Fact.out
  refine Summable.of_norm_bounded ((summable_base_rpow (L := L) (p := s) hs).mul_left ((Real.sqrt L)⁻¹)) ?_
  intro n
  rw [norm_smul, norm_cfun]
  exact mul_le_mul_of_nonneg_left (norm_coefCLM_le hs0 n) (by positivity)

theorem Phi_apply {s : ℝ} (hs : 1 < s) (hs0 : 0 ≤ s) (x : ℝ) (v : H02 L s) :
    Phi (L := L) s hs0 x v = ∑' n : ℤ, cfun L n x * coefLin (L := L) s n v := by
  unfold Phi
  rw [tsum_apply (summable_Phi_terms hs hs0 x)]
  refine tsum_congr (fun n => ?_)
  rfl

/-- **Derivatives in `x`**: `x ↦ Φ_{k+2}(x)` is `C^k` as an `(H^{k+2} →L ℂ)`-valued map. -/
theorem phi_contDiff (k : ℕ) :
    ContDiff ℝ (k : ℕ∞) (fun x : ℝ => Phi (L := L) ((k : ℝ) + 2) (by positivity) x) := by
  have hL : 0 < L := Fact.out
  set s : ℝ := (k : ℝ) + 2 with hs_def
  have hs0 : 0 ≤ s := by positivity
  have hkey : ∀ j : ℕ, j ≤ k → Summable fun n : ℤ => (Real.sqrt L)⁻¹ *
      ((1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-s) * |freq L n| ^ j) := by
    intro j hj
    exact (summable_term_bound (L := L) k j hj).mul_left _ |>.congr (fun n => by rw [hs_def])
  refine contDiff_tsum (f := fun n x => cfun L n x • coefCLM (L := L) s hs0 n)
    (v := fun j n => (Real.sqrt L)⁻¹ * ((1 + |2 * Real.pi * (n : ℝ) / L|) ^ (-s) * |freq L n| ^ j))
    ?_ ?_ ?_
  · intro n
    exact (contDiff_cfun n).smul contDiff_const |>.of_le (by exact_mod_cast le_top)
  · intro j hj
    have hj' : j ≤ k := by exact_mod_cast hj
    exact hkey j hj'
  · intro j n x hj
    have hj' : j ≤ k := by exact_mod_cast hj
    have h := norm_iteratedFDeriv_term (L := L) s hs0 n j x
    refine h.trans (le_of_eq ?_)
    ring

/-- The joint function `G(τ,x) = Σ_n c_n(x) û_n(u τ)` (`c_n(x) = (√L)^{-1} e^{i 2πn x/L}`). -/
def Gfun (u : ℝ → L2T L) (p : ℝ × ℝ) : ℂ :=
  ∑' n : ℤ, cfun L n p.2 * fourierL2 L (u p.1) n

theorem cfun_add_period (n : ℤ) (x : ℝ) : cfun L n (x + L) = cfun L n x := by
  have hL0 : L ≠ 0 := ne_of_gt (Fact.out : 0 < L)
  have hfr : freq L n * L = 2 * Real.pi * n := by
    unfold freq; field_simp
  have hfrC : (freq L n : ℂ) * (L : ℂ) = (n : ℂ) * (2 * Real.pi) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hfr
    push_cast at this ⊢
    linear_combination this
  have e : (Complex.I * (freq L n : ℂ)) * ((x + L : ℝ) : ℂ) =
      (Complex.I * (freq L n : ℂ)) * (x : ℂ) + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    linear_combination Complex.I * hfrC
  unfold cfun
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem Gfun_periodic (u : ℝ → L2T L) (τ x : ℝ) : Gfun u (τ, x + L) = Gfun u (τ, x) := by
  simp only [Gfun]
  exact tsum_congr (fun n => by rw [cfun_add_period])

theorem Gfun_eq_seriesRep (u : ℝ → L2T L) (τ x : ℝ) :
    Gfun u (τ, x) = seriesRep L (fun n => fourierL2 L (u τ) n) (x : AddCircle L) := by
  simp only [Gfun, seriesRep]
  refine tsum_congr (fun n => ?_)
  have hexp : (2 * Real.pi * Complex.I * n * x / L : ℂ) = (Complex.I * (freq L n : ℂ)) * (x : ℂ) := by
    simp only [freq]; push_cast; ring
  rw [mode_coe, hexp]
  unfold cfun
  ring

theorem memHs_of_le {s t : ℝ} (hst : s ≤ t) (x : ℤ → ℂ) (h : MemHs L t x) : MemHs L s x := by
  unfold MemHs at h ⊢
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · unfold sobolevWeight; positivity
  · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    unfold sobolevWeight
    exact Real.rpow_le_rpow_of_exponent_le (one_le_base n) (by linarith)

/-- A `C^∞` lift into every `H^q`, `q ≥ 0`, gives membership of `u τ` in every `H^s`, `s ∈ ℝ`. -/
theorem memHs_all_of_lift {u : ℝ → L2T L}
    (hlift : ∀ q : ℝ, 0 < q → ∃ V : ℝ → H02 L q, ContDiff ℝ ∞ V ∧ ∀ τ, (V τ).val = u τ)
    (τ : ℝ) (s : ℝ) : MemHsLp L s (u τ) := by
  obtain ⟨V, -, hVu⟩ := hlift (max s 1) (lt_of_lt_of_le one_pos (le_max_right _ _))
  have h1 : MemHs L (max s 1) (fun n => fourierL2 L (u τ) n) := by
    have hv := WField.summable (L := L) (V τ)
    rw [hVu τ] at hv
    exact hv
  exact memHs_of_le (le_max_left s 1) _ h1

/-- **A7b(a), joint smoothness.** A curve `u : ℝ → L²(𝕋_L)` which lies in every `H^q` as a `C^∞` curve
(`hlift`) has a jointly `C^∞` Fourier representative `G(τ,x)`, each slice a smooth periodic representative of `u τ`. -/
theorem joint_smooth (u : ℝ → L2T L)
    (hlift : ∀ q : ℝ, 0 < q → ∃ V : ℝ → H02 L q, ContDiff ℝ ∞ V ∧ ∀ τ, (V τ).val = u τ) :
    ContDiff ℝ ∞ (Gfun u) ∧
      (∀ τ x, Gfun u (τ, x) = seriesRep L (fun n => fourierL2 L (u τ) n) (x : AddCircle L)) ∧
      ∀ τ : ℝ, ∃ hf : SmoothPeriodic L (fun x => Gfun u (τ, x)), smoothL2 hf = u τ := by
  have hk : ∀ k : ℕ, ContDiff ℝ (k : ℕ∞) (Gfun u) := by
    intro k
    obtain ⟨V, hV, hVu⟩ := hlift ((k : ℝ) + 2) (by positivity)
    have hs1 : 1 < (k : ℝ) + 2 := by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
    have hfun : Gfun u = fun p : ℝ × ℝ => Phi (L := L) ((k : ℝ) + 2) (by positivity) p.2 (V p.1) := by
      funext p
      rw [Phi_apply hs1 (by positivity) p.2 (V p.1)]
      simp only [Gfun]
      refine tsum_congr (fun n => ?_)
      simp only [coefLin, LinearMap.coe_mk, AddHom.coe_mk, hVu]
    rw [hfun]
    have hVk : ContDiff ℝ (k : ℕ∞) V := hV.of_le (by exact_mod_cast le_top)
    have hPk : ContDiff ℝ (k : ℕ∞) (fun p : ℝ × ℝ => Phi (L := L) ((k : ℝ) + 2) (by positivity) p.2) :=
      (phi_contDiff k).comp contDiff_snd
    have hpair : ContDiff ℝ (k : ℕ∞)
        (fun p : ℝ × ℝ => (Phi (L := L) ((k : ℝ) + 2) (by positivity) p.2, V p.1)) :=
      hPk.prodMk (hVk.comp contDiff_fst)
    exact (isBoundedBilinear_eval (L := L) ((k : ℝ) + 2)).contDiff.comp hpair
  have hGs : ContDiff ℝ ∞ (Gfun u) := contDiff_infty.2 hk
  refine ⟨hGs, fun τ x => Gfun_eq_seriesRep u τ x, fun τ => ?_⟩
  have hsm : ContDiff ℝ ∞ (fun x => Gfun u (τ, x)) := hGs.comp (contDiff_const.prodMk contDiff_id)
  have hper : Function.Periodic (fun x => Gfun u (τ, x)) L := fun x => Gfun_periodic u τ x
  refine ⟨⟨hsm, hper⟩, ?_⟩
  have hu : ∀ s : ℝ, MemHsLp L s (u τ) := memHs_all_of_lift hlift τ
  have hcont : Continuous (seriesRep L (fun n => fourierL2 L (u τ) n)) :=
    continuous_seriesRep (by simpa using summable_cof_pow (u τ) hu 0)
  have hlift_eq : (liftC hsm.continuous hper : AddCircle L → ℂ) =
      seriesRep L (fun n => fourierL2 L (u τ) n) := by
    funext y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [liftC_coe, Gfun_eq_seriesRep]
  have h04 : Mem04 L 1 (coeff L ((u τ) : AddCircle L → ℂ)) := by
    have := mem04_of_memHs (u τ) hu 0
    simp only [pow_zero, one_mul] at this
    have e : coeff L ((u τ) : AddCircle L → ℂ) = fun n => fourierL2 L (u τ) n :=
      funext fun n => (fourierL2_apply L (u τ) n).symm
    rw [e]; exact this
  have hae := ae_eq_seriesRep (Lp.memLp (u τ)) h04
  have e : coeff L ((u τ) : AddCircle L → ℂ) = fun n => fourierL2 L (u τ) n :=
    funext fun n => (fourierL2_apply L (u τ) n).symm
  rw [e] at hae
  unfold smoothL2
  refine Lp.ext ?_
  refine (ContinuousMap.coeFn_toLp _ _).trans ?_
  rw [hlift_eq]
  exact hae.symm

end QuantumNLS.RB7H

#print axioms QuantumNLS.RB7H.joint_smooth
#print axioms QuantumNLS.RB7H.Gfun_eq_seriesRep
#print axioms QuantumNLS.RB7H.phi_contDiff
