import Mathlib
import QuantumNLS.SymplecticBracket
import QuantumNLS.FourierBracket

/-!
# R-8DD5AE6E `norm:rephasing`: the rephasing flow on `ℓ²(ℤ)`

Source: `source-text/chapters/global/scaling_and_phase_freedom.tex` (Proposition `norm:rephasing`, around
line 52), with DEF-015 (`definitions.tex:93`), DEF-016 (`:99`) and DEF-017 (`:105`).

Owner: sonnet_fourier.  Built on the frozen `SymplecticBracket 056a23e2` (DEF-015 realization: `omega`,
`gradient`, `hamField`) and `FourierBracket 5f75abbe` (`gradient_eq_of_hasFDerivAt`), both read-only.

Strategy (no assumed conclusions):

* the phase multiplier is the exponential of an `ℓ^∞` element in the Banach algebra `ℓ^∞(ℤ)`,
  `U_a(z) = mulB (exp (wB a z)) z`; real analyticity (`AnalyticAt ℝ`) follows from Mathlib's analyticity
  of `exp` in a Banach algebra and of bounded bilinear maps; DEF-017's literal series form is extracted
  from `HasFPowerSeriesOnBall`;
* `F_κ = cκ(‖z‖⁴ − ‖SC(z,z)‖²)` with `SC(x,y)_n = Re(conj x_n y_n)`; Fréchet derivative by the chain rule,
  and `∇F_κ` identified through `FourierBracket.gradient_eq_of_hasFDerivAt`;
* Hamilton's equation by `hasDerivAt_exp_smul_const`; uniqueness by conservation of `‖z‖²`, `|z_n|²`
  and a scalar ODE per coordinate;
* strong symplecticity: explicit coordinate formula for `DU(z)h` (derivative read off coordinatewise),
  phases cancel in `⟨DU h, DU k⟩`, the remaining cross terms cancel after summing; invertible derivative
  from `U_{-t} ∘ U_t = id`.
-/

open scoped ComplexConjugate ENNReal
open InnerProductSpace

namespace QuantumNLS.RephasingFlow

noncomputable section

abbrev E := lp (fun _ : ℤ => ℂ) 2

lemma summable_sq (z : E) : Summable fun n => ‖z n‖ ^ 2 := by
  have := (lp.memℓp z : Memℓp z 2).summable (by norm_num)
  simpa using this

lemma tsum_sq (z : E) : ‖z‖ ^ 2 = ∑' n, ‖z n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) z
  simpa using h

lemma norm_apply_le (z : E) (n : ℤ) : ‖z n‖ ≤ ‖z‖ := lp.norm_apply_le_norm (by norm_num) z n

lemma sq_le_tsum (z : E) (n : ℤ) : ‖z n‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  rw [tsum_sq]
  exact (summable_sq z).le_tsum n (fun m _ => sq_nonneg _)

/-- bounded multiplier -/
lemma memℓp_mul (w : ℤ → ℂ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C) (z : E) :
    Memℓp (fun n => w n * z n) 2 := by
  apply memℓp_gen
  have h1 : Summable fun n => C ^ 2 * ‖z n‖ ^ 2 := (summable_sq z).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h1
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul]
  rw [mul_pow]
  have : ‖w n‖ ^ 2 ≤ C ^ 2 := by
    have := hw n
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

def mulFun (w : ℤ → ℂ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C) (z : E) : E :=
  ⟨fun n => w n * z n, memℓp_mul w C hw z⟩

lemma mulFun_apply (w : ℤ → ℂ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C) (z : E) (n : ℤ) :
    mulFun w C hw z n = w n * z n := rfl

lemma norm_mulFun_le (w : ℤ → ℂ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C) (z : E) :
    ‖mulFun w C hw z‖ ≤ |C| * ‖z‖ := by
  have hC : 0 ≤ |C| * ‖z‖ := by positivity
  apply lp.norm_le_of_tsum_le (by norm_num) hC
  have : ∀ n, ‖mulFun w C hw z n‖ ^ (2:ℝ≥0∞).toReal ≤ |C| ^ 2 * ‖z n‖ ^ 2 := by
    intro n
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, mulFun_apply, norm_mul]
    rw [mul_pow]
    have : ‖w n‖ ^ 2 ≤ |C| ^ 2 := by
      have := (hw n).trans (le_abs_self C)
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  calc ∑' n, ‖mulFun w C hw z n‖ ^ (2:ℝ≥0∞).toReal ≤ ∑' n, |C| ^ 2 * ‖z n‖ ^ 2 :=
        Summable.tsum_le_tsum this ((memℓp_mul w C hw z).summable (by norm_num) |>.congr (by intro n; rfl)) ((summable_sq z).mul_left _)
    _ = |C| ^ 2 * ‖z‖ ^ 2 := by rw [tsum_mul_left, tsum_sq]
    _ = (|C| * ‖z‖) ^ (2:ℝ≥0∞).toReal := by simp [mul_pow]


abbrev B := lp (fun _ : ℤ => ℂ) ∞

lemma norm_B_apply_le (m : B) (n : ℤ) : ‖m n‖ ≤ ‖m‖ := lp.norm_apply_le_norm (by simp) m n

def mulInf (m : B) (z : E) : E := mulFun (fun n => m n) ‖m‖ (norm_B_apply_le m) z

lemma mulInf_apply (m : B) (z : E) (n : ℤ) : mulInf m z n = m n * z n := rfl

lemma norm_mulInf_le (m : B) (z : E) : ‖mulInf m z‖ ≤ ‖m‖ * ‖z‖ := by
  have := norm_mulFun_le (fun n => m n) ‖m‖ (norm_B_apply_le m) z
  simpa [mulInf, abs_of_nonneg (norm_nonneg m)] using this

def mulInfBil : B →ₗ[ℝ] E →ₗ[ℝ] E :=
  LinearMap.mk₂ ℝ mulInf
    (by intro m₁ m₂ z; ext n; simp [mulInf_apply, add_mul])
    (by intro c m z; ext n; simp [mulInf_apply, mul_assoc])
    (by intro m z₁ z₂; ext n; simp [mulInf_apply, mul_add])
    (by intro c m z; ext n; simp [mulInf_apply]; ring)


def mulB : B →L[ℝ] E →L[ℝ] E :=
  LinearMap.mkContinuous₂ mulInfBil 1 (by
    intro m z
    simpa [mulInfBil] using norm_mulInf_le m z)

lemma mulB_apply (m : B) (z : E) : mulB m z = mulInf m z := rfl

/-- `S x y = (conj x_n * y_n)_n` as an element of `ℓ^∞`. -/
lemma memInf_conjmul (x y : E) : Memℓp (fun n => conj (x n) * y n) ∞ := by
  apply memℓp_infty
  refine ⟨‖x‖ * ‖y‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  simp only [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (norm_apply_le x n) (norm_apply_le y n) (norm_nonneg _) (norm_nonneg _)

def Sfun (x y : E) : B := ⟨fun n => conj (x n) * y n, memInf_conjmul x y⟩

lemma Sfun_apply (x y : E) (n : ℤ) : Sfun x y n = conj (x n) * y n := rfl

lemma norm_Sfun_le (x y : E) : ‖Sfun x y‖ ≤ ‖x‖ * ‖y‖ := by
  apply lp.norm_le_of_forall_le (by positivity)
  intro n
  simp only [Sfun_apply, norm_mul, RCLike.norm_conj]
  exact mul_le_mul (norm_apply_le x n) (norm_apply_le y n) (norm_nonneg _) (norm_nonneg _)

def SBil : E →ₗ[ℝ] E →ₗ[ℝ] B :=
  LinearMap.mk₂ ℝ Sfun
    (by intro x₁ x₂ y; ext n; simp [Sfun_apply, add_mul])
    (by intro c x y; ext n; simp [Sfun_apply]; ring)
    (by intro x y₁ y₂; ext n; simp [Sfun_apply, mul_add])
    (by intro c x y; ext n; simp [Sfun_apply]; ring)

def SB : E →L[ℝ] E →L[ℝ] B :=
  LinearMap.mkContinuous₂ SBil 1 (by
    intro x y
    simpa [SBil] using norm_Sfun_le x y)

lemma SB_apply (x y : E) : SB x y = Sfun x y := rfl


def evalRH (n : ℤ) : B →+* ℂ where
  toFun f := f n
  map_one' := rfl
  map_mul' f g := by simp [lp.infty_coeFn_mul]
  map_zero' := rfl
  map_add' f g := rfl

lemma evalRH_cont (n : ℤ) : Continuous (evalRH n) :=
  (lp.lipschitzWith_one_eval (E := fun _ : ℤ => ℂ) ∞ n).continuous

def wB (a : ℝ) (z : E) : B := (-(a:ℂ) * Complex.I) • ((‖z‖ ^ 2 : ℝ) • (1 : B) - SB z z)

lemma wB_apply (a : ℝ) (z : E) (n : ℤ) :
    wB a z n = (-(a:ℂ) * Complex.I) * (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ)) := by
  unfold wB
  rw [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.infty_coeFn_one, Pi.one_apply, SB_apply, Sfun_apply]
  simp [Complex.conj_mul']

def mB (a : ℝ) (z : E) : B := NormedSpace.exp (wB a z)

lemma mB_apply (a : ℝ) (z : E) (n : ℤ) : mB a z n = Complex.exp (wB a z n) := by
  have := NormedSpace.map_exp (evalRH n) (evalRH_cont n) (wB a z)
  rw [Complex.exp_eq_exp_ℂ]
  exact this


/-- The phase multiplier of the flow, `U_a z = (exp(-i a (‖z‖²-|z_n|²)) z_n)_n`, with `a = 2cκt`. -/
def Ufun (a : ℝ) (z : E) : E := mulB (mB a z) z

lemma Ufun_apply (a : ℝ) (z : E) (n : ℤ) :
    Ufun a z n = Complex.exp (-(a:ℂ) * Complex.I * (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ))) * z n := by
  unfold Ufun
  rw [mulB_apply, mulInf_apply, mB_apply, wB_apply]

lemma analyticAt_normsq (z₀ : E) : AnalyticAt ℝ (fun z : E => ‖z‖ ^ 2) z₀ := by
  have h : (fun z : E => ‖z‖ ^ 2) = fun z => (innerSL ℝ z) z := by
    ext z; simp
  rw [h]
  exact ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).analyticAt_bilinear (z₀, z₀)).comp₂
    (analyticAt_id (𝕜 := ℝ)) (analyticAt_id (𝕜 := ℝ))

lemma analyticAt_SB (z₀ : E) : AnalyticAt ℝ (fun z : E => SB z z) z₀ :=
  (SB.analyticAt_bilinear (z₀, z₀)).comp₂ (analyticAt_id (𝕜 := ℝ)) (analyticAt_id (𝕜 := ℝ))

lemma analyticAt_wB (a : ℝ) (z₀ : E) : AnalyticAt ℝ (wB a) z₀ := by
  have h1 : AnalyticAt ℝ (fun z : E => (‖z‖ ^ 2 : ℝ) • (1 : B) - SB z z) z₀ :=
    ((analyticAt_normsq z₀).smul analyticAt_const).sub (analyticAt_SB z₀)
  have h2 : ∀ x : B, AnalyticAt ℝ (fun x : B => (-(a:ℂ) * Complex.I) • x) x := fun x =>
    show AnalyticAt ℝ (⇑(((-(a:ℂ) * Complex.I) • ContinuousLinearMap.id ℂ B).restrictScalars ℝ)) x from
      ContinuousLinearMap.analyticAt _ x
  exact (h2 _).comp h1

lemma analyticAt_Ufun (a : ℝ) (z₀ : E) : AnalyticAt ℝ (Ufun a) z₀ := by
  have h1 : AnalyticAt ℝ (fun z : E => mB a z) z₀ :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (wB a z₀)).comp (analyticAt_wB a z₀)
  exact (mulB.analyticAt_bilinear (mB a z₀, z₀)).comp₂ h1 (analyticAt_id (𝕜 := ℝ))


/-! ### The functional `F` -/

/-- `ρ_n(x,y) = Re(conj x_n y_n)`. -/
lemma memℓp_re_conjmul (x y : E) : Memℓp (fun n => (((conj (x n) * y n).re : ℝ) : ℂ)) 2 := by
  apply memℓp_gen
  have h1 : Summable fun n => ‖x‖ ^ 2 * ‖y n‖ ^ 2 := (summable_sq y).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h1
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real, Real.norm_eq_abs]
  rw [← mul_pow]
  apply pow_le_pow_left₀ (abs_nonneg _)
  calc |(conj (x n) * y n).re| ≤ ‖conj (x n) * y n‖ := Complex.abs_re_le_norm _
    _ = ‖x n‖ * ‖y n‖ := by simp
    _ ≤ ‖x‖ * ‖y n‖ := mul_le_mul_of_nonneg_right (norm_apply_le x n) (norm_nonneg _)

def SCfun (x y : E) : E := ⟨_, memℓp_re_conjmul x y⟩

lemma SCfun_apply (x y : E) (n : ℤ) : SCfun x y n = (((conj (x n) * y n).re : ℝ) : ℂ) := rfl

lemma norm_SCfun_le (x y : E) : ‖SCfun x y‖ ≤ ‖x‖ * ‖y‖ := by
  have hC : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  apply lp.norm_le_of_tsum_le (by norm_num) hC
  have hle : ∀ n, ‖SCfun x y n‖ ^ (2:ℝ≥0∞).toReal ≤ ‖x‖ ^ 2 * ‖y n‖ ^ 2 := by
    intro n
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, SCfun_apply, Complex.norm_real, Real.norm_eq_abs]
    rw [← mul_pow]
    apply pow_le_pow_left₀ (abs_nonneg _)
    calc |(conj (x n) * y n).re| ≤ ‖conj (x n) * y n‖ := Complex.abs_re_le_norm _
      _ = ‖x n‖ * ‖y n‖ := by simp
      _ ≤ ‖x‖ * ‖y n‖ := mul_le_mul_of_nonneg_right (norm_apply_le x n) (norm_nonneg _)
  calc ∑' n, ‖SCfun x y n‖ ^ (2:ℝ≥0∞).toReal ≤ ∑' n, ‖x‖ ^ 2 * ‖y n‖ ^ 2 :=
        Summable.tsum_le_tsum hle
          (((SCfun x y).2.summable (by norm_num)))
          ((summable_sq y).mul_left _)
    _ = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by rw [tsum_mul_left, ← tsum_sq y]
    _ = (‖x‖ * ‖y‖) ^ (2:ℝ≥0∞).toReal := by simp [mul_pow]

def SCbil : E →ₗ[ℝ] E →ₗ[ℝ] E :=
  LinearMap.mk₂ ℝ SCfun
    (by intro x₁ x₂ y; ext n; simp [SCfun_apply, add_mul, Complex.add_re])
    (by intro c x y; ext n; simp [SCfun_apply]; ring)
    (by intro x y₁ y₂; ext n; simp [SCfun_apply, mul_add])
    (by intro c x y; ext n; simp [SCfun_apply]; ring)

def SC : E →L[ℝ] E →L[ℝ] E :=
  LinearMap.mkContinuous₂ SCbil 1 (by
    intro x y
    simpa [SCbil] using norm_SCfun_le x y)

lemma SC_apply (x y : E) : SC x y = SCfun x y := rfl

lemma SC_comm (x y : E) : SC x y = SC y x := by
  rw [SC_apply, SC_apply]
  apply lp.ext
  funext n
  show SCfun x y n = SCfun y x n
  simp only [SCfun_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  congr 1
  ring_nf


def F (c κ : ℝ) (z : E) : ℝ := c * κ * ((∑' n, ‖z n‖ ^ 2) ^ 2 - ∑' n, ‖z n‖ ^ 4)

lemma norm_SC_self_apply (z : E) (n : ℤ) : ‖SC z z n‖ = ‖z n‖ ^ 2 := by
  rw [SC_apply, SCfun_apply, Complex.norm_real, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re, Real.norm_of_nonneg (sq_nonneg _)]

lemma F_eq (c κ : ℝ) (z : E) : F c κ z = c * κ * ((‖z‖ ^ 2) ^ 2 - ‖SC z z‖ ^ 2) := by
  unfold F
  rw [tsum_sq (SC z z), tsum_sq z]
  congr 3
  funext n
  rw [norm_SC_self_apply]
  ring

lemma hasFDerivAt_SCdiag (z : E) : HasFDerivAt (fun z : E => SC z z) (SC z + SC.flip z) z := by
  have := (SC.hasFDerivAt (x := z)).clm_apply (hasFDerivAt_id z)
  simpa using this

/-- Fréchet derivative of `F`, as an explicit continuous real-linear functional. -/
def dF (c κ : ℝ) (z : E) : E →L[ℝ] ℝ :=
  (c * κ) • (((2 * ‖z‖ ^ 2 : ℝ)) • ((2 : ℕ) • innerSL ℝ z) -
    (2 : ℕ) • ((innerSL ℝ (SC z z)).comp (SC z + SC.flip z)))

lemma dF_apply (c κ : ℝ) (z h : E) :
    dF c κ z h = c * κ * (2 * ‖z‖ ^ 2 * (2 * inner ℝ z h) -
      2 * inner ℝ (SC z z) (SC z h + SC h z)) := by
  simp [dF, inner_add_right]
  left; ring

lemma hasFDerivAt_F (c κ : ℝ) (z : E) : HasFDerivAt (F c κ) (dF c κ z) z := by
  have h1 : HasFDerivAt (fun z : E => ‖z‖ ^ 2) ((2 : ℕ) • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h1' := h1.pow 2
  have h2 : HasFDerivAt (fun z : E => ‖SC z z‖ ^ 2)
      ((2 : ℕ) • (innerSL ℝ (SC z z)).comp (SC z + SC.flip z)) z :=
    (hasFDerivAt_SCdiag z).norm_sq
  have h3 := (h1'.sub h2).const_mul (c * κ)
  have hF : F c κ = fun z => c * κ * ((‖z‖ ^ 2) ^ 2 - ‖SC z z‖ ^ 2) := funext (F_eq c κ)
  rw [hF]
  convert h3 using 1
  ext h
  simp [dF]


/-- The candidate gradient `g(z)_n = 2cκ(‖z‖² − |z_n|²) z_n`. -/
def gvec (c κ : ℝ) (z : E) : E :=
  mulFun (fun n => ((2 * c * κ * (‖z‖ ^ 2 - ‖z n‖ ^ 2) : ℝ) : ℂ)) (2 * |c| * |κ| * ‖z‖ ^ 2) (by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_two]
    have h0 : 0 ≤ ‖z‖ ^ 2 - ‖z n‖ ^ 2 := sub_nonneg.2 (pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le z n) 2)
    have h1 : ‖z‖ ^ 2 - ‖z n‖ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z n‖]
    rw [abs_of_nonneg h0]
    have : 0 ≤ 2 * |c| * |κ| := by positivity
    calc 2 * |c| * |κ| * (‖z‖ ^ 2 - ‖z n‖ ^ 2) ≤ 2 * |c| * |κ| * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_left h1 this
      ) z

lemma gvec_apply (c κ : ℝ) (z : E) (n : ℤ) :
    gvec c κ z n = ((2 * c * κ * (‖z‖ ^ 2 - ‖z n‖ ^ 2) : ℝ) : ℂ) * z n := rfl

lemma inner_real_coord (a b : ℂ) : inner ℝ a b = (conj a * b).re := by rw [Complex.inner, mul_comm]

lemma re_inner_gvec (c κ : ℝ) (z h : E) (i : ℤ) :
    (inner ℂ (gvec c κ z i) (h i)).re =
      2 * c * κ * (‖z‖ ^ 2 - ‖z i‖ ^ 2) * (conj (z i) * h i).re := by
  rw [gvec_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  have : h i * (((2 * c * κ * (‖z‖ ^ 2 - ‖z i‖ ^ 2) : ℝ) : ℂ) * conj (z i)) =
      ((2 * c * κ * (‖z‖ ^ 2 - ‖z i‖ ^ 2) : ℝ) : ℂ) * (conj (z i) * h i) := by ring
  rw [this, Complex.re_ofReal_mul]

lemma dF_eq_inner (c κ : ℝ) (z h : E) : dF c κ z h = 2 * (inner ℂ (gvec c κ z) h).re := by
  have hs1 : HasSum (fun i => (conj (z i) * h i).re) (inner ℝ z h) := by
    have := lp.hasSum_inner (𝕜 := ℝ) (G := fun _ : ℤ => ℂ) z h
    have e : (fun i => inner ℝ (z i) (h i)) = fun i => (conj (z i) * h i).re :=
      funext fun i => inner_real_coord _ _
    rwa [e] at this
  have hs2 : HasSum (fun i => ‖z i‖ ^ 2 * (conj (z i) * h i).re) (inner ℝ (SC z z) (SC z h)) := by
    have := lp.hasSum_inner (𝕜 := ℝ) (G := fun _ : ℤ => ℂ) (SC z z) (SC z h)
    have e : (fun i => inner ℝ ((SC z z) i) ((SC z h) i)) =
        fun i => ‖z i‖ ^ 2 * (conj (z i) * h i).re := by
      funext i
      rw [inner_real_coord, SC_apply, SC_apply, SCfun_apply, SCfun_apply, Complex.conj_ofReal,
        ← Complex.ofReal_mul, Complex.ofReal_re, Complex.conj_mul', ← Complex.ofReal_pow,
        Complex.ofReal_re]
    rwa [e] at this
  have hs3 : HasSum (fun i => (inner ℂ (gvec c κ z i) (h i)).re) (inner ℂ (gvec c κ z) h).re :=
    ((lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : ℤ => ℂ) (gvec c κ z) h).mapL Complex.reCLM)
  have hs4 : HasSum (fun i => (inner ℂ (gvec c κ z i) (h i)).re)
      (2 * c * κ * (‖z‖ ^ 2 * inner ℝ z h - inner ℝ (SC z z) (SC z h))) := by
    have := ((hs1.mul_left (‖z‖ ^ 2)).sub hs2).mul_left (2 * c * κ)
    convert this using 1
    funext i
    rw [re_inner_gvec]
    ring
  have := hs3.unique hs4
  rw [dF_apply, this, SC_comm h z, inner_add_right]
  ring


/-! ### The flow map -/

lemma Ufun_zero (z : E) : Ufun 0 z = z := by
  apply lp.ext; funext n
  rw [Ufun_apply]; simp

lemma norm_Ufun_apply (a : ℝ) (z : E) (n : ℤ) : ‖Ufun a z n‖ = ‖z n‖ := by
  rw [Ufun_apply, norm_mul, Complex.norm_exp]
  have : (-(a:ℂ) * Complex.I * (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ))).re = 0 := by
    rw [← Complex.ofReal_sub]
    generalize ‖z‖ ^ 2 - ‖z n‖ ^ 2 = r
    simp [Complex.mul_re]
  rw [this]; simp

lemma norm_Ufun (a : ℝ) (z : E) : ‖Ufun a z‖ = ‖z‖ := by
  have h : ‖Ufun a z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [tsum_sq, tsum_sq z]
    congr 1; funext n; rw [norm_Ufun_apply]
  have h1 := norm_nonneg (Ufun a z)
  have h2 := norm_nonneg z
  nlinarith [sq_nonneg (‖Ufun a z‖ - ‖z‖), sq_nonneg (‖Ufun a z‖ + ‖z‖)]

lemma Ufun_add (a b : ℝ) (z : E) : Ufun a (Ufun b z) = Ufun (a + b) z := by
  apply lp.ext; funext n
  rw [Ufun_apply a (Ufun b z) n, norm_Ufun, norm_Ufun_apply, Ufun_apply b z n,
    Ufun_apply (a + b) z n, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma wB_smul (a t : ℝ) (z : E) : wB (a * t) z = t • wB a z := by
  apply lp.ext; funext n
  rw [lp.coeFn_smul, Pi.smul_apply, wB_apply, wB_apply, Complex.real_smul]
  push_cast
  ring

lemma mB_mul (a t : ℝ) (z : E) : mB (a * t) z = NormedSpace.exp (t • wB a z) := by
  unfold mB; rw [wB_smul]

lemma hasDerivAt_Ufun_time (a : ℝ) (z : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Ufun (a * t) z) (mulB (mB (a * t) z * wB a z) z) t := by
  have hm : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • wB a z))
      (NormedSpace.exp (t • wB a z) * wB a z) t := hasDerivAt_exp_smul_const (wB a z) t
  have := (mulB.flip z).hasFDerivAt.comp_hasDerivAt t hm
  have e : (fun t : ℝ => Ufun (a * t) z) = (mulB.flip z) ∘ (fun t : ℝ => NormedSpace.exp (t • wB a z)) := by
    funext t; simp [Ufun, mB_mul]
  rw [e]
  simpa [mB_mul] using this


lemma deriv_vec_eq (c κ t : ℝ) (z : E) :
    mulB (mB (2 * c * κ * t) z * wB (2 * c * κ) z) z =
      (-Complex.I) • gvec c κ (Ufun (2 * c * κ * t) z) := by
  apply lp.ext; funext n
  rw [lp.coeFn_smul, Pi.smul_apply, gvec_apply, norm_Ufun, norm_Ufun_apply, Ufun_apply,
    mulB_apply, mulInf_apply, lp.infty_coeFn_mul, Pi.mul_apply, mB_apply, wB_apply, wB_apply,
    smul_eq_mul]
  push_cast
  ring_nf


/-! ### Derivative of the flow map -/

/-- coordinate evaluation as a real-linear continuous map -/
def pr (n : ℤ) : E →L[ℝ] ℂ := (lp.evalCLM (E := fun _ : ℤ => ℂ) ℂ 2 n).restrictScalars ℝ

lemma pr_apply (n : ℤ) (z : E) : pr n z = z n := rfl

lemma hasFDerivAt_coord (a : ℝ) (z : E) (n : ℤ) :
    HasFDerivAt (fun z : E => Ufun a z n)
      (Complex.exp (-(a:ℂ) * Complex.I * (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ))) •
        (pr n + ((z n) • ((-(a:ℂ) * Complex.I) •
          (Complex.ofRealCLM.comp ((2 : ℕ) • innerSL ℝ z - (2 : ℕ) • (innerSL ℝ (z n)).comp (pr n)))))))
      z := by
  have h1 : HasFDerivAt (fun z : E => ‖z‖ ^ 2) ((2 : ℕ) • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 : HasFDerivAt (fun z : E => ‖z n‖ ^ 2) ((2 : ℕ) • (innerSL ℝ (z n)).comp (pr n)) z := by
    have := ((hasStrictFDerivAt_norm_sq (z n)).hasFDerivAt).comp z (pr n).hasFDerivAt
    exact this
  have h3 := h1.sub h2
  have h4 := Complex.ofRealCLM.hasFDerivAt.comp z h3
  have h5 := h4.const_smul (-(a:ℂ) * Complex.I)
  have h6 := (Complex.hasDerivAt_exp _).comp_hasFDerivAt z h5
  have h7 := h6.mul (pr n).hasFDerivAt
  convert h7 using 1
  · funext z
    simp [Ufun_apply, Function.comp, pr_apply]
  · ext h
    simp [pr_apply]
    ring


lemma coord_identity (p z hn kn : ℂ) (hp : ‖p‖ = 1) (a sh sk : ℝ) :
    (conj (p * (hn + (-(a:ℂ) * Complex.I) * (sh : ℂ) * z)) * (p * (kn + (-(a:ℂ) * Complex.I) * (sk : ℂ) * z))).im
      = (conj hn * kn).im + a * (sh * (conj z * kn).re - sk * (conj z * hn).re) := by
  have h1 : conj p * p = 1 := by
    rw [Complex.conj_mul', hp]; simp
  have : conj (p * (hn + (-(a:ℂ) * Complex.I) * (sh : ℂ) * z)) * (p * (kn + (-(a:ℂ) * Complex.I) * (sk : ℂ) * z))
      = (conj p * p) * (conj (hn + (-(a:ℂ) * Complex.I) * (sh : ℂ) * z) * (kn + (-(a:ℂ) * Complex.I) * (sk : ℂ) * z)) := by
    rw [map_mul]; ring
  rw [this, h1, one_mul]
  simp [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring


/-- the real Gateaux/Fréchet derivative of `Ufun a` read off coordinatewise -/
lemma fderiv_Ufun_apply (a : ℝ) (z h : E) (n : ℤ) :
    (fderiv ℝ (Ufun a) z h) n =
      Complex.exp (-(a:ℂ) * Complex.I * (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ))) *
        (h n + (-(a:ℂ) * Complex.I) * ((2 * inner ℝ z h - 2 * (conj (z n) * h n).re : ℝ) : ℂ) * z n) := by
  have hd : HasFDerivAt (Ufun a) (fderiv ℝ (Ufun a) z) z :=
    ((analyticAt_Ufun a z).differentiableAt).hasFDerivAt
  have h1 := (pr n).hasFDerivAt.comp z hd
  have h2 := hasFDerivAt_coord a z n
  have e : (pr n) ∘ (Ufun a) = fun z => Ufun a z n := rfl
  rw [e] at h1
  have h3 := h1.unique h2
  have h4 := congrArg (fun L => L h) h3
  simp only [ContinuousLinearMap.comp_apply] at h4
  have h5 : (pr n) (fderiv ℝ (Ufun a) z h) = (fderiv ℝ (Ufun a) z h) n := rfl
  rw [← h5, h4]
  simp [pr_apply]
  ring


lemma inner_c (x y : ℂ) : inner ℂ x y = conj x * y := by
  rw [RCLike.inner_apply, mul_comm]

lemma hasSum_rho (z h : E) : HasSum (fun i => (conj (z i) * h i).re) (inner ℝ z h) := by
  have := lp.hasSum_inner (𝕜 := ℝ) (G := fun _ : ℤ => ℂ) z h
  have e : (fun i => inner ℝ (z i) (h i)) = fun i => (conj (z i) * h i).re :=
    funext fun i => inner_real_coord _ _
  rwa [e] at this

lemma norm_phase (a : ℝ) (z : E) (n : ℤ) :
    ‖Complex.exp (-(a:ℂ) * Complex.I * (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have : (-(a:ℂ) * Complex.I * (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ))).re = 0 := by
    rw [← Complex.ofReal_sub]
    generalize ‖z‖ ^ 2 - ‖z n‖ ^ 2 = r
    simp [Complex.mul_re]
  rw [this]; simp

lemma symplectic_Ufun (a : ℝ) (z h k : E) :
    (inner ℂ (fderiv ℝ (Ufun a) z h) (fderiv ℝ (Ufun a) z k)).im = (inner ℂ h k).im := by
  have hL : HasSum (fun n => (inner ℂ (fderiv ℝ (Ufun a) z h n) (fderiv ℝ (Ufun a) z k n)).im)
      (inner ℂ (fderiv ℝ (Ufun a) z h) (fderiv ℝ (Ufun a) z k)).im :=
    ((lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : ℤ => ℂ)
    (fderiv ℝ (Ufun a) z h) (fderiv ℝ (Ufun a) z k)).mapL Complex.imCLM)
  have hH : HasSum (fun n => (inner ℂ (h n) (k n)).im) (inner ℂ h k).im :=
    ((lp.hasSum_inner (𝕜 := ℂ) (G := fun _ : ℤ => ℂ) h k).mapL Complex.imCLM)
  have hρk := hasSum_rho z k
  have hρh := hasSum_rho z h
  have hT : HasSum (fun n => (inner ℂ (h n) (k n)).im +
      a * (2 * inner ℝ z h * (conj (z n) * k n).re - 2 * inner ℝ z k * (conj (z n) * h n).re))
      ((inner ℂ h k).im + a * (2 * inner ℝ z h * inner ℝ z k - 2 * inner ℝ z k * inner ℝ z h)) := by
    refine hH.add ?_
    refine HasSum.mul_left a ?_
    exact (hρk.mul_left (2 * inner ℝ z h)).sub (hρh.mul_left (2 * inner ℝ z k))
  have hterm : (fun n => (inner ℂ (fderiv ℝ (Ufun a) z h n) (fderiv ℝ (Ufun a) z k n)).im) =
      (fun n => (inner ℂ (h n) (k n)).im +
      a * (2 * inner ℝ z h * (conj (z n) * k n).re - 2 * inner ℝ z k * (conj (z n) * h n).re)) := by
    funext n
    rw [inner_c, fderiv_Ufun_apply, fderiv_Ufun_apply, coord_identity _ _ _ _ (norm_phase a z n), inner_c]
    ring
  rw [hterm] at hL
  have := hL.unique hT
  rw [this]; ring


lemma norm_eq_of_norm_apply_eq {x y : E} (h : ∀ n, ‖x n‖ = ‖y n‖) : ‖x‖ = ‖y‖ := by
  have h2 : ‖x‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [tsum_sq, tsum_sq y]
    congr 1; funext n; rw [h]
  have h1 := norm_nonneg x
  have h3 := norm_nonneg y
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ + ‖y‖)]

/-! ### Invertible derivative -/

lemma Ufun_neg_left (a : ℝ) (z : E) : Ufun (-a) (Ufun a z) = z := by
  rw [Ufun_add, neg_add_cancel, Ufun_zero]

lemma Ufun_neg_right (a : ℝ) (z : E) : Ufun a (Ufun (-a) z) = z := by
  rw [Ufun_add, add_neg_cancel, Ufun_zero]

lemma hasFDerivAt_Ufun (a : ℝ) (z : E) : HasFDerivAt (Ufun a) (fderiv ℝ (Ufun a) z) z :=
  (analyticAt_Ufun a z).differentiableAt.hasFDerivAt

lemma fderiv_comp_inverse (a : ℝ) (z : E) :
    (fderiv ℝ (Ufun (-a)) (Ufun a z)).comp (fderiv ℝ (Ufun a) z) = ContinuousLinearMap.id ℝ E := by
  have h1 := (hasFDerivAt_Ufun (-a) (Ufun a z)).comp z (hasFDerivAt_Ufun a z)
  have e : (Ufun (-a)) ∘ (Ufun a) = id := funext (Ufun_neg_left a)
  rw [e] at h1
  exact (hasFDerivAt_id z).unique h1 |>.symm

theorem exists_fderiv_equiv (a : ℝ) (z : E) :
    ∃ e : E ≃L[ℝ] E, (e : E → E) = fderiv ℝ (Ufun a) z := by
  have h1 := fderiv_comp_inverse a z
  have h2 := fderiv_comp_inverse (-a) (Ufun a z)
  rw [neg_neg, Ufun_neg_left] at h2
  refine ⟨ContinuousLinearEquiv.equivOfInverse (fderiv ℝ (Ufun a) z)
    (fderiv ℝ (Ufun (-a)) (Ufun a z)) ?_ ?_, rfl⟩
  · intro x
    have := congrArg (fun L => L x) h1
    simpa using this
  · intro x
    have := congrArg (fun L => L x) h2
    simpa using this


/-! ### Symmetries -/

/-- independent coordinate rotations `(R_θ z)_n = e^{iθ_n} z_n` -/
def rotE (θ : ℤ → ℝ) (z : E) : E :=
  mulFun (fun n => Complex.exp ((θ n : ℂ) * Complex.I)) 1 (by
    intro n; rw [Complex.norm_exp_ofReal_mul_I]) z

lemma rotE_apply (θ : ℤ → ℝ) (z : E) (n : ℤ) :
    rotE θ z n = Complex.exp ((θ n : ℂ) * Complex.I) * z n := rfl

lemma norm_rotE (θ : ℤ → ℝ) (z : E) : ‖rotE θ z‖ = ‖z‖ :=
  norm_eq_of_norm_apply_eq fun n => by
    rw [rotE_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem Ufun_comm_rotE (a : ℝ) (θ : ℤ → ℝ) (z : E) :
    Ufun a (rotE θ z) = rotE θ (Ufun a z) := by
  apply lp.ext; funext n
  rw [Ufun_apply, rotE_apply, rotE_apply, Ufun_apply, norm_rotE]
  have : ‖Complex.exp ((θ n : ℂ) * Complex.I) * z n‖ = ‖z n‖ := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [this]; ring

lemma memℓp_comp_equiv (σ : ℤ ≃ ℤ) (z : E) : Memℓp (fun n => z (σ n)) 2 := by
  apply memℓp_gen
  have h := σ.summable_iff.2 (summable_sq z)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact h

/-- index permutation `(P_σ z)_n = z_{σ n}` -/
def permE (σ : ℤ ≃ ℤ) (z : E) : E := ⟨fun n => z (σ n), memℓp_comp_equiv σ z⟩

lemma permE_apply (σ : ℤ ≃ ℤ) (z : E) (n : ℤ) : permE σ z n = z (σ n) := rfl

lemma norm_permE (σ : ℤ ≃ ℤ) (z : E) : ‖permE σ z‖ = ‖z‖ := by
  have h2 : ‖permE σ z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [tsum_sq, tsum_sq z]
    exact σ.tsum_eq (fun n => ‖z n‖ ^ 2)
  have h1 := norm_nonneg (permE σ z)
  have h3 := norm_nonneg z
  nlinarith [sq_nonneg (‖permE σ z‖ - ‖z‖), sq_nonneg (‖permE σ z‖ + ‖z‖)]

theorem Ufun_comm_permE (a : ℝ) (σ : ℤ ≃ ℤ) (z : E) :
    Ufun a (permE σ z) = permE σ (Ufun a z) := by
  apply lp.ext; funext n
  rw [Ufun_apply, permE_apply, permE_apply, Ufun_apply, norm_permE]

theorem Ufun_single (a : ℝ) (m : ℤ) (w : ℂ) :
    Ufun a (lp.single (E := fun _ : ℤ => ℂ) 2 m w) = lp.single (E := fun _ : ℤ => ℂ) 2 m w := by
  apply lp.ext; funext n
  rw [Ufun_apply, lp.norm_single (by norm_num)]
  by_cases h : n = m
  · subst h
    simp
  · have h0 : (lp.single (E := fun _ : ℤ => ℂ) 2 m w) n = 0 := lp.single_apply_ne _ _ _ h
    rw [h0]; simp

theorem Ufun_smul (a s : ℝ) (z : E) : Ufun a (s • z) = s • Ufun (a * s ^ 2) z := by
  apply lp.ext; funext n
  rw [Ufun_apply, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply, Ufun_apply,
    norm_smul, norm_smul, Complex.real_smul, Complex.real_smul]
  have e1 : ((‖s‖ * ‖z‖) ^ 2 : ℝ) = s ^ 2 * ‖z‖ ^ 2 := by rw [Real.norm_eq_abs, mul_pow, sq_abs]
  have e2 : ((‖s‖ * ‖z n‖) ^ 2 : ℝ) = s ^ 2 * ‖z n‖ ^ 2 := by rw [Real.norm_eq_abs, mul_pow, sq_abs]
  rw [e1, e2]
  have : (-(a:ℂ) * Complex.I * (((s ^ 2 * ‖z‖ ^ 2 : ℝ) : ℂ) - ((s ^ 2 * ‖z n‖ ^ 2 : ℝ) : ℂ))) =
      (-((a * s ^ 2 : ℝ) : ℂ) * Complex.I * (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ))) := by
    push_cast
    ring
  rw [this]; ring


/-! ### Identity differential at zero and the `C¹` free limit -/

theorem fderiv_Ufun_zero (a : ℝ) : fderiv ℝ (Ufun a) 0 = ContinuousLinearMap.id ℝ E := by
  ext h : 1
  apply lp.ext; funext n
  rw [fderiv_Ufun_apply]
  simp

lemma phase_sub_one_le (a : ℝ) (z : E) (n : ℤ) :
    ‖Complex.exp (-(a:ℂ) * Complex.I * (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ))) - 1‖
      ≤ |a| * ‖z‖ ^ 2 := by
  have e : -(a:ℂ) * Complex.I * (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ)) =
      Complex.I * ((-a * (‖z‖ ^ 2 - ‖z n‖ ^ 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_neg]
  have h0 : 0 ≤ ‖z‖ ^ 2 - ‖z n‖ ^ 2 := sub_nonneg.2 (pow_le_pow_left₀ (norm_nonneg _) (norm_apply_le z n) 2)
  have h1 : ‖z‖ ^ 2 - ‖z n‖ ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg ‖z n‖]
  rw [abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg a)

theorem norm_Ufun_sub_le (a : ℝ) (z : E) : ‖Ufun a z - z‖ ≤ |a| * ‖z‖ ^ 3 := by
  have h : Ufun a z - z = mulFun (fun n => Complex.exp (-(a:ℂ) * Complex.I *
      (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ))) - 1) (|a| * ‖z‖ ^ 2) (phase_sub_one_le a z) z := by
    apply lp.ext; funext n
    rw [lp.coeFn_sub, Pi.sub_apply, Ufun_apply, mulFun_apply]
    ring
  rw [h]
  refine (norm_mulFun_le _ _ _ z).trans ?_
  rw [abs_of_nonneg (by positivity)]
  nlinarith [norm_nonneg z, pow_nonneg (norm_nonneg z) 3]


lemma abs_s_le (z h : E) (n : ℤ) :
    |2 * inner ℝ z h - 2 * (conj (z n) * h n).re| ≤ 4 * ‖z‖ * ‖h‖ := by
  have h1 : |inner ℝ z h| ≤ ‖z‖ * ‖h‖ := abs_real_inner_le_norm z h
  have h2 : |(conj (z n) * h n).re| ≤ ‖z‖ * ‖h‖ := by
    calc |(conj (z n) * h n).re| ≤ ‖conj (z n) * h n‖ := Complex.abs_re_le_norm _
      _ = ‖z n‖ * ‖h n‖ := by simp
      _ ≤ ‖z‖ * ‖h‖ := mul_le_mul (norm_apply_le z n) (norm_apply_le h n) (norm_nonneg _) (norm_nonneg _)
  calc |2 * inner ℝ z h - 2 * (conj (z n) * h n).re|
      ≤ |2 * inner ℝ z h| + |2 * (conj (z n) * h n).re| := abs_sub _ _
    _ = 2 * |inner ℝ z h| + 2 * |(conj (z n) * h n).re| := by simp [abs_mul]
    _ ≤ 4 * ‖z‖ * ‖h‖ := by nlinarith

theorem norm_fderiv_Ufun_sub_id_apply (a : ℝ) (z h : E) :
    ‖fderiv ℝ (Ufun a) z h - h‖ ≤ 5 * |a| * ‖z‖ ^ 2 * ‖h‖ := by
  set P : ℤ → ℂ := fun n => Complex.exp (-(a:ℂ) * Complex.I *
    (((‖z‖ ^ 2 : ℝ) : ℂ) - ((‖z n‖ ^ 2 : ℝ) : ℂ))) with hPdef
  have hP1 : ∀ n, ‖P n‖ ≤ 1 := fun n => (norm_phase a z n).le
  have hPm : ∀ n, ‖P n - 1‖ ≤ |a| * ‖z‖ ^ 2 := fun n => phase_sub_one_le a z n
  have hw : ∀ n, ‖(-(a:ℂ) * Complex.I) * ((2 * inner ℝ z h - 2 * (conj (z n) * h n).re : ℝ) : ℂ)‖
      ≤ |a| * (4 * ‖z‖ * ‖h‖) := by
    intro n
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg, Complex.norm_real,
      Complex.norm_I, mul_one, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_s_le z h n) (abs_nonneg a)
  set T : E := mulFun (fun n => (-(a:ℂ) * Complex.I) *
    ((2 * inner ℝ z h - 2 * (conj (z n) * h n).re : ℝ) : ℂ)) _ hw z with hT
  have hV : fderiv ℝ (Ufun a) z h - h = mulFun (fun n => P n - 1) _ hPm h + mulFun P 1 hP1 T := by
    apply lp.ext; funext n
    rw [lp.coeFn_sub, Pi.sub_apply, fderiv_Ufun_apply, lp.coeFn_add, Pi.add_apply, mulFun_apply,
      mulFun_apply, hT, mulFun_apply]
    simp only [hPdef]
    ring
  rw [hV]
  have b1 : ‖mulFun (fun n => P n - 1) _ hPm h‖ ≤ |a| * ‖z‖ ^ 2 * ‖h‖ := by
    refine (norm_mulFun_le _ _ _ h).trans ?_
    rw [abs_of_nonneg (by positivity)]
  have b2 : ‖mulFun P 1 hP1 T‖ ≤ 4 * |a| * ‖z‖ ^ 2 * ‖h‖ := by
    refine (norm_mulFun_le _ _ _ T).trans ?_
    rw [abs_one, one_mul]
    refine (norm_mulFun_le _ _ _ z).trans ?_
    rw [abs_of_nonneg (by positivity)]
    nlinarith [norm_nonneg z, norm_nonneg h, abs_nonneg a, mul_nonneg (mul_nonneg (norm_nonneg z) (norm_nonneg z)) (norm_nonneg h)]
  calc _ ≤ ‖mulFun (fun n => P n - 1) _ hPm h‖ + ‖mulFun P 1 hP1 T‖ := norm_add_le _ _
    _ ≤ 5 * |a| * ‖z‖ ^ 2 * ‖h‖ := by nlinarith

theorem norm_fderiv_Ufun_sub_id_le (a : ℝ) (z : E) :
    ‖fderiv ℝ (Ufun a) z - ContinuousLinearMap.id ℝ E‖ ≤ 5 * |a| * ‖z‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  simpa using norm_fderiv_Ufun_sub_id_apply a z h


/-! ### Uniqueness of the flow -/

/-- the Hamiltonian vector field `X_F = -i ∇F` with `∇F = gvec` -/
def Xvec (c κ : ℝ) (u : E) : E := (-Complex.I) • gvec c κ u

lemma Xvec_apply (c κ : ℝ) (u : E) (n : ℤ) :
    Xvec c κ u n = (-Complex.I) * (((2 * c * κ * (‖u‖ ^ 2 - ‖u n‖ ^ 2) : ℝ) : ℂ) * u n) := rfl

lemma re_conj_Xvec (c κ : ℝ) (u : E) (n : ℤ) : (conj (u n) * Xvec c κ u n).re = 0 := by
  rw [Xvec_apply]
  have : conj (u n) * ((-Complex.I) * (((2 * c * κ * (‖u‖ ^ 2 - ‖u n‖ ^ 2) : ℝ) : ℂ) * u n))
      = (-Complex.I) * (((2 * c * κ * (‖u‖ ^ 2 - ‖u n‖ ^ 2) * ‖u n‖ ^ 2 : ℝ)) : ℂ) := by
    rw [mul_left_comm, mul_left_comm (conj (u n)), ← mul_assoc, Complex.conj_mul']
    push_cast; ring
  rw [this]
  generalize (2 * c * κ * (‖u‖ ^ 2 - ‖u n‖ ^ 2) * ‖u n‖ ^ 2 : ℝ) = r
  simp

lemma inner_real_Xvec (c κ : ℝ) (u : E) : inner ℝ u (Xvec c κ u) = 0 := by
  have := hasSum_rho u (Xvec c κ u)
  have e : (fun i => (conj (u i) * Xvec c κ u i).re) = fun _ => 0 := funext (re_conj_Xvec c κ u)
  rw [e] at this
  exact this.unique hasSum_zero

theorem flow_unique (c κ : ℝ) (γ : ℝ → E) (hγ : ∀ t, HasDerivAt γ (Xvec c κ (γ t)) t) (t : ℝ) :
    γ t = Ufun (2 * c * κ * t) (γ 0) := by
  have hcoord : ∀ n t, HasDerivAt (fun t => γ t n) (Xvec c κ (γ t) n) t :=
    fun n t => (pr n).hasFDerivAt.comp_hasDerivAt t (hγ t)
  -- conserved total mass
  have hN : ∀ t, ‖γ t‖ ^ 2 = ‖γ 0‖ ^ 2 := by
    intro t
    have hd : ∀ x, HasDerivAt (fun t => ‖γ t‖ ^ 2) 0 x := by
      intro x
      have := (hγ x).norm_sq
      rwa [inner_real_Xvec, mul_zero] at this
    exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
  have hS : ∀ n t, ‖γ t n‖ ^ 2 = ‖γ 0 n‖ ^ 2 := by
    intro n t
    have hd : ∀ x, HasDerivAt (fun t => ‖γ t n‖ ^ 2) 0 x := by
      intro x
      have := (hcoord n x).norm_sq
      rw [inner_real_coord, re_conj_Xvec, mul_zero] at this
      exact this
    exact is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
  apply lp.ext; funext n
  set μ : ℂ := (-Complex.I) * (((2 * c * κ * (‖γ 0‖ ^ 2 - ‖γ 0 n‖ ^ 2) : ℝ) : ℂ)) with hμ
  have hode : ∀ t, HasDerivAt (fun t => γ t n) (μ * γ t n) t := by
    intro t
    have := hcoord n t
    rw [Xvec_apply, hN t, hS n t] at this
    convert this using 1
    rw [hμ]; ring
  have hq : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-μ * (t : ℂ)) * γ t n) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-μ * (t : ℂ))) (Complex.exp (-μ * (t : ℂ)) * (-μ)) t := by
      have := ((hasDerivAt_id (t : ℂ)).const_mul (-μ)).cexp.comp_ofReal
      simpa using this
    have := h1.mul (hode t)
    convert this using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun x => (hq x).differentiableAt) (fun x => (hq x).deriv) t 0
  rw [Ufun_apply]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hc
  have : γ t n = Complex.exp (μ * t) * γ 0 n := by
    have h2 := congrArg (fun w => Complex.exp (μ * t) * w) hc
    beta_reduce at h2
    rw [← mul_assoc, ← Complex.exp_add] at h2
    simpa using h2
  rw [this, hμ]
  congr 2
  push_cast
  ring


/-! ### Conjugation and relative Cartesian products -/

lemma memℓp_conj (z : E) : Memℓp (fun n => conj (z n)) 2 := by
  apply memℓp_gen
  simpa using summable_sq z

/-- componentwise complex conjugation -/
def conjE (z : E) : E := ⟨fun n => conj (z n), memℓp_conj z⟩

lemma conjE_apply (z : E) (n : ℤ) : conjE z n = conj (z n) := rfl

lemma norm_conjE (z : E) : ‖conjE z‖ = ‖z‖ :=
  norm_eq_of_norm_apply_eq fun n => by rw [conjE_apply, RCLike.norm_conj]

theorem conj_Ufun (a : ℝ) (z : E) : conjE (Ufun a z) = Ufun (-a) (conjE z) := by
  apply lp.ext; funext n
  rw [conjE_apply, Ufun_apply, Ufun_apply, norm_conjE, conjE_apply, RCLike.norm_conj, map_mul,
    ← Complex.exp_conj]
  congr 2
  simp [map_sub, Complex.conj_ofReal]

def twoMode (β : ℝ) : E := lp.single (E := fun _ : ℤ => ℂ) 2 0 1 + lp.single (E := fun _ : ℤ => ℂ) 2 1 (β : ℂ)

lemma twoMode_zero (β : ℝ) : twoMode β 0 = 1 := by
  simp [twoMode, lp.single_apply]

lemma twoMode_one (β : ℝ) : twoMode β 1 = β := by
  simp [twoMode, lp.single_apply]

lemma twoMode_other (β : ℝ) (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) : twoMode β n = 0 := by
  simp [twoMode, lp.single_apply, h0, h1]

lemma norm_twoMode_sq (β : ℝ) : ‖twoMode β‖ ^ 2 = 1 + β ^ 2 := by
  rw [tsum_sq, tsum_eq_sum (s := ({0, 1} : Finset ℤ))]
  · rw [Finset.sum_pair (by norm_num), twoMode_zero, twoMode_one]
    simp
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [twoMode_other β n hn.1 hn.2]; simp


lemma Ufun_twoMode_zero (a β : ℝ) :
    Ufun a (twoMode β) 0 = Complex.exp (((-(a * β ^ 2) : ℝ) : ℂ) * Complex.I) := by
  rw [Ufun_apply, twoMode_zero, norm_twoMode_sq]
  simp only [norm_one, mul_one]
  congr 1
  push_cast; ring

lemma Ufun_twoMode_one (a β : ℝ) :
    Ufun a (twoMode β) 1 = Complex.exp (((-a : ℝ) : ℂ) * Complex.I) * (β : ℂ) := by
  rw [Ufun_apply, twoMode_one, norm_twoMode_sq]
  congr 2
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  push_cast; ring

lemma conjE_twoMode (β : ℝ) : conjE (twoMode β) = twoMode β := by
  apply lp.ext; funext n
  rw [conjE_apply]
  by_cases h0 : n = 0
  · subst h0; simp [twoMode_zero]
  by_cases h1 : n = 1
  · subst h1; simp [twoMode_one]
  rw [twoMode_other β n h0 h1]; simp

/-- the witness amplitude: `β² = π/(4|a|)` -/
lemma exists_beta (a : ℝ) (ha : a ≠ 0) :
    ∃ β : ℝ, 0 < β ∧ (a * β ^ 2 = Real.pi / 4 ∨ a * β ^ 2 = -(Real.pi / 4)) := by
  have ha' : 0 < |a| := abs_pos.2 ha
  have hpos : 0 < Real.pi / (4 * |a|) := by positivity
  refine ⟨Real.sqrt (Real.pi / (4 * |a|)), Real.sqrt_pos.2 hpos, ?_⟩
  have hsq : Real.sqrt (Real.pi / (4 * |a|)) ^ 2 = Real.pi / (4 * |a|) := Real.sq_sqrt hpos.le
  rcases lt_or_gt_of_ne ha with h | h
  · right
    rw [hsq, abs_of_neg h]
    field_simp
  · left
    rw [hsq, abs_of_pos h]
    field_simp


theorem not_comm_conjE (a : ℝ) (ha : a ≠ 0) : ∃ z : E, Ufun a (conjE z) ≠ conjE (Ufun a z) := by
  obtain ⟨β, hβ, hθ⟩ := exists_beta a ha
  refine ⟨twoMode β, ?_⟩
  rw [conj_Ufun, conjE_twoMode]
  intro h
  have h0 := congrArg (fun w : E => (w 0).im) h
  simp only [Ufun_twoMode_zero, Complex.exp_ofReal_mul_I_im] at h0
  rw [neg_mul, neg_neg, Real.sin_neg] at h0
  have h1 : Real.sin (a * β ^ 2) = 0 := by linarith
  have h2 : Real.sin (Real.pi / 4) ≠ 0 := by
    rw [Real.sin_pi_div_four]; positivity
  rcases hθ with hθ | hθ
  · rw [hθ] at h1; exact h2 h1
  · rw [hθ, Real.sin_neg] at h1; exact h2 (by linarith)

theorem cartesian_product_changes (a : ℝ) (ha : a ≠ 0) :
    ∃ z : E, (Ufun a z 0).re * (Ufun a z 1).re ≠ (z 0).re * (z 1).re := by
  obtain ⟨β, hβ, hθ⟩ := exists_beta a ha
  refine ⟨twoMode β, ?_⟩
  rw [Ufun_twoMode_zero, Ufun_twoMode_one, twoMode_zero, twoMode_one]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.one_re]
  have hc : Real.cos (-(a * β ^ 2)) = Real.sqrt 2 / 2 := by
    rw [Real.cos_neg]
    rcases hθ with hθ | hθ
    · rw [hθ, Real.cos_pi_div_four]
    · rw [hθ, Real.cos_neg, Real.cos_pi_div_four]
  rw [hc]
  intro h
  have h3 : Real.sqrt 2 / 2 * Real.cos (-a) = 1 := by
    exact mul_right_cancel₀ hβ.ne' (by linarith [h])
  have h4 : |Real.cos (-a)| ≤ 1 := Real.abs_cos_le_one _
  have h5 : Real.sqrt 2 < 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h6 : Real.sqrt 2 / 2 * Real.cos (-a) ≤ Real.sqrt 2 / 2 * |Real.cos (-a)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  nlinarith [Real.sqrt_nonneg 2]


/-! ### DEF-017 -/

/-- DEF-017 (literal, first form): near `x` the map has a norm-convergent series of continuous real
homogeneous polynomials `h ↦ p_k(h,…,h)` (`p_k` a continuous `k`-linear map). -/
def AnalyticAtDEF017 (f : E → E) (x : E) : Prop :=
  ∃ (p : FormalMultilinearSeries ℝ E E) (r : ℝ≥0∞), 0 < r ∧
    ∀ h : E, h ∈ Metric.eball (0 : E) r →
      Summable (fun k => ‖p k (fun _ => h)‖) ∧ HasSum (fun k => p k (fun _ => h)) (f (x + h))

lemma analyticAt_def017 {f : E → E} {x : E} (hf : AnalyticAt ℝ f x) : AnalyticAtDEF017 f x := by
  obtain ⟨p, r, hp⟩ := hf
  refine ⟨p, r, hp.r_pos, fun h hh => ⟨?_, hp.hasSum hh⟩⟩
  exact p.summable_norm_apply (Metric.eball_subset_eball hp.r_le hh)

lemma diag_homogeneous (p : FormalMultilinearSeries ℝ E E) (k : ℕ) (s : ℝ) (h : E) :
    p k (fun _ => s • h) = s ^ k • p k (fun _ => h) := by
  have := (p k).map_smul_univ (fun _ => s) (fun _ => h)
  simpa using this


/-! ### `F` is a continuous real quartic polynomial -/

lemma fin4_ne : (1 : Fin 4) ≠ 0 ∧ (2 : Fin 4) ≠ 0 ∧ (3 : Fin 4) ≠ 0 ∧ (2 : Fin 4) ≠ 1 ∧
    (3 : Fin 4) ≠ 1 ∧ (3 : Fin 4) ≠ 2 := by
  decide

/-- the (non-symmetrized) real 4-linear form with `F z = Q₄(z,z,z,z)` -/
def quartMulti (c κ : ℝ) : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ where
  toFun m := c * κ * (inner ℝ (m 0) (m 1) * inner ℝ (m 2) (m 3) -
    inner ℝ (SC (m 0) (m 1)) (SC (m 2) (m 3)))
  map_update_add' m i x y := by
    obtain ⟨h10, h20, h30, h21, h31, h32⟩ := fin4_ne
    fin_cases i
    · simp [Function.update_self, Function.update_of_ne, h10, h20, h30, inner_add_left]; ring
    · simp [Function.update_self, Function.update_of_ne, h10.symm, h21, h31, inner_add_left, inner_add_right]; ring
    · simp [Function.update_self, Function.update_of_ne, h20.symm, h21.symm, h32, inner_add_left, inner_add_right]; ring
    · simp [Function.update_self, Function.update_of_ne, h30.symm, h31.symm, h32.symm, inner_add_right]; ring
  map_update_smul' m i r x := by
    obtain ⟨h10, h20, h30, h21, h31, h32⟩ := fin4_ne
    fin_cases i
    · simp [Function.update_self, Function.update_of_ne, h10, h20, h30, inner_smul_left]; ring
    · simp [Function.update_self, Function.update_of_ne, h10.symm, h21, h31, inner_smul_left, inner_smul_right]; ring
    · simp [Function.update_self, Function.update_of_ne, h20.symm, h21.symm, h32, inner_smul_left, inner_smul_right]; ring
    · simp [Function.update_self, Function.update_of_ne, h30.symm, h31.symm, h32.symm, inner_smul_right]; ring


lemma quartMulti_apply (c κ : ℝ) (m : Fin 4 → E) :
    quartMulti c κ m = c * κ * (inner ℝ (m 0) (m 1) * inner ℝ (m 2) (m 3) -
      inner ℝ (SC (m 0) (m 1)) (SC (m 2) (m 3))) := rfl

lemma quartMulti_bound (c κ : ℝ) (m : Fin 4 → E) :
    ‖quartMulti c κ m‖ ≤ (2 * |c * κ|) * ∏ i, ‖m i‖ := by
  rw [quartMulti_apply, Fin.prod_univ_four, Real.norm_eq_abs, abs_mul, ← mul_assoc]
  have hA : |inner ℝ (m 0) (m 1) * inner ℝ (m 2) (m 3)| ≤ ‖m 0‖ * ‖m 1‖ * (‖m 2‖ * ‖m 3‖) := by
    rw [abs_mul]
    exact mul_le_mul (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _) (abs_nonneg _)
      (by positivity)
  have hB : |inner ℝ (SC (m 0) (m 1)) (SC (m 2) (m 3))| ≤ ‖m 0‖ * ‖m 1‖ * (‖m 2‖ * ‖m 3‖) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (norm_SCfun_le _ _) (norm_SCfun_le _ _) (norm_nonneg _) (by positivity)
  have hAB := abs_sub (inner ℝ (m 0) (m 1) * inner ℝ (m 2) (m 3))
    (inner ℝ (SC (m 0) (m 1)) (SC (m 2) (m 3)))
  have h0 : 0 ≤ |c * κ| := abs_nonneg _
  have : |c * κ| * |inner ℝ (m 0) (m 1) * inner ℝ (m 2) (m 3) -
      inner ℝ (SC (m 0) (m 1)) (SC (m 2) (m 3))| ≤ |c * κ| * (2 * (‖m 0‖ * ‖m 1‖ * (‖m 2‖ * ‖m 3‖))) :=
    mul_le_mul_of_nonneg_left (by linarith) h0
  nlinarith [this]

/-- `F` is a continuous real quartic polynomial: `F z = Q₄(z,z,z,z)` with `Q₄` continuous 4-linear. -/
def quartCont (c κ : ℝ) : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ :=
  (quartMulti c κ).mkContinuous (2 * |c * κ|) (quartMulti_bound c κ)

theorem F_eq_quartCont (c κ : ℝ) (z : E) : F c κ z = quartCont c κ (fun _ => z) := by
  rw [F_eq]
  show _ = quartMulti c κ (fun _ => z)
  rw [quartMulti_apply, real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq (SC z z)]
  ring


/-! ## Bridge to DEF-015 (gradient, `X_F`, `Ω`), DEF-016 and DEF-017 -/

/-- DEF-015: the gradient of `F_κ` is `∇F_κ(u)_n = 2cκ(‖u‖² − |u_n|²)u_n`. -/
theorem gradient_F (c κ : ℝ) (u : E) : SymplecticBracket.gradient (F c κ) u = gvec c κ u := by
  have h := FourierBracket.gradient_eq_of_hasFDerivAt (hasFDerivAt_F c κ u)
  have key : ∀ w : E, (inner ℂ (SymplecticBracket.gradient (F c κ) u - gvec c κ u) w).re = 0 := by
    intro w
    have h0 := h w
    rw [real_inner_eq_re_inner ℂ] at h0
    have h1 : dF c κ u w = 2 * (inner ℂ (SymplecticBracket.gradient (F c κ) u) w).re := h0
    rw [dF_eq_inner] at h1
    rw [inner_sub_left, Complex.sub_re]
    linarith
  have h2 := key (SymplecticBracket.gradient (F c κ) u - gvec c κ u)
  rw [SymplecticBracket.inner_self_eq_ofReal] at h2
  simp only [Complex.ofReal_re] at h2
  have h3 : ‖SymplecticBracket.gradient (F c κ) u - gvec c κ u‖ = 0 := by
    have := sq_eq_zero_iff.1 h2
    exact this
  exact sub_eq_zero.1 (norm_eq_zero.1 h3)

theorem gradient_F_apply (c κ : ℝ) (u : E) (n : ℤ) :
    SymplecticBracket.gradient (F c κ) u n = ((2 * c * κ * (‖u‖ ^ 2 - ‖u n‖ ^ 2) : ℝ) : ℂ) * u n := by
  rw [gradient_F]; rfl

theorem hamField_F (c κ : ℝ) : SymplecticBracket.hamField (F c κ) = Xvec c κ := by
  funext u
  unfold SymplecticBracket.hamField Xvec
  rw [gradient_F]

/-- The flow `U_{κ,t}`. -/
def U (c κ t : ℝ) (z : E) : E := Ufun (2 * c * κ * t) z

theorem U_apply (c κ t : ℝ) (z : E) (n : ℤ) :
    U c κ t z n = Complex.exp (-(2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z n‖ ^ 2 : ℝ) : ℂ)) * z n := by
  unfold U
  rw [Ufun_apply]
  congr 2
  push_cast
  ring

theorem U_zero (c κ : ℝ) (z : E) : U c κ 0 z = z := by
  unfold U; rw [mul_zero, Ufun_zero]

theorem U_add (c κ s t : ℝ) (z : E) : U c κ s (U c κ t z) = U c κ (s + t) z := by
  unfold U; rw [Ufun_add]; congr 1; ring

theorem U_neg_left (c κ t : ℝ) (z : E) : U c κ (-t) (U c κ t z) = z := by
  rw [U_add, neg_add_cancel, U_zero]

theorem U_neg_right (c κ t : ℝ) (z : E) : U c κ t (U c κ (-t) z) = z := by
  rw [U_add, add_neg_cancel, U_zero]

theorem norm_U_apply (c κ t : ℝ) (z : E) (n : ℤ) : ‖U c κ t z n‖ = ‖z n‖ := norm_Ufun_apply _ z n

theorem norm_U (c κ t : ℝ) (z : E) : ‖U c κ t z‖ = ‖z‖ := norm_Ufun _ z

/-- every action `|z_n|²` and the functional `F_κ` itself are conserved -/
theorem F_comp_U (c κ t : ℝ) (z : E) : F c κ (U c κ t z) = F c κ z := by
  unfold F
  simp only [norm_U_apply]

/-- **Hamilton's equation** `ż = X_F(z)`, `X_F = −i∇F` (DEF-015), for all real times. -/
theorem U_hasDerivAt (c κ : ℝ) (z : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U c κ s z) (SymplecticBracket.hamField (F c κ) (U c κ t z)) t := by
  have h := hasDerivAt_Ufun_time (2 * c * κ) z t
  rw [hamField_F]
  have e : mulB (mB (2 * c * κ * t) z * wB (2 * c * κ) z) z = Xvec c κ (U c κ t z) := by
    unfold U Xvec
    exact deriv_vec_eq c κ t z
  rw [← e]
  exact h

/-- the flow is the unique solution of Hamilton's equation, for all times -/
theorem U_unique (c κ : ℝ) (γ : ℝ → E)
    (hγ : ∀ t, HasDerivAt γ (SymplecticBracket.hamField (F c κ) (γ t)) t) (t : ℝ) :
    γ t = U c κ t (γ 0) := by
  rw [hamField_F] at hγ
  exact flow_unique c κ γ hγ t

/-! ### DEF-016 and DEF-017 -/

/-- DEF-016 on `ℓ²(ℤ)`: a differentiable diffeomorphism whose derivative is a bounded real-linear
isomorphism at every point and which preserves `Ω(h,k) = 2 Im ⟨h,k⟩` (DEF-015). -/
structure IsStrongSymplecticDiffeo (Φ : E → E) : Prop where
  exists_inverse : ∃ Ψ : E → E, (∀ z, Ψ (Φ z) = z) ∧ (∀ w, Φ (Ψ w) = w) ∧
    (∀ w, DifferentiableAt ℝ Ψ w)
  differentiable : ∀ z, DifferentiableAt ℝ Φ z
  deriv_iso : ∀ z, ∃ e : E ≃L[ℝ] E, (e : E → E) = fderiv ℝ Φ z
  symplectic : ∀ z h k, SymplecticBracket.omega (fderiv ℝ Φ z h) (fderiv ℝ Φ z k) =
    SymplecticBracket.omega h k

/-- DEF-017: real analytic at every input (literal first form). -/
def IsRealAnalyticDEF017 (f : E → E) : Prop := ∀ x : E, AnalyticAtDEF017 f x

theorem U_strongSymplectic (c κ t : ℝ) : IsStrongSymplecticDiffeo (U c κ t) where
  exists_inverse := ⟨U c κ (-t), U_neg_left c κ t, U_neg_right c κ t,
    fun w => (analyticAt_Ufun _ w).differentiableAt⟩
  differentiable := fun z => (analyticAt_Ufun _ z).differentiableAt
  deriv_iso := fun z => exists_fderiv_equiv _ z
  symplectic := fun z h k => by
    unfold SymplecticBracket.omega
    show 2 * (inner ℂ (fderiv ℝ (Ufun (2 * c * κ * t)) z h) (fderiv ℝ (Ufun (2 * c * κ * t)) z k)).im = _
    rw [symplectic_Ufun]

theorem U_realAnalytic (c κ t : ℝ) : IsRealAnalyticDEF017 (U c κ t) :=
  fun x => analyticAt_def017 (analyticAt_Ufun _ x)

theorem U_analyticAt (c κ t : ℝ) (x : E) : AnalyticAt ℝ (U c κ t) x := analyticAt_Ufun _ x

/-- `F_κ` is a continuous real quartic polynomial. -/
theorem F_quartic (c κ : ℝ) :
    ∃ Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ, ∀ z, F c κ z = Q (fun _ => z) :=
  ⟨quartCont c κ, F_eq_quartCont c κ⟩

/-! ### Time one -/

theorem U_one_fderiv_zero (c κ : ℝ) : fderiv ℝ (U c κ 1) 0 = ContinuousLinearMap.id ℝ E :=
  fderiv_Ufun_zero _

theorem U_single (c κ t : ℝ) (m : ℤ) (w : ℂ) :
    U c κ t (lp.single (E := fun _ : ℤ => ℂ) 2 m w) = lp.single (E := fun _ : ℤ => ℂ) 2 m w :=
  Ufun_single _ m w

theorem U_comm_rot (c κ t : ℝ) (θ : ℤ → ℝ) (z : E) : U c κ t (rotE θ z) = rotE θ (U c κ t z) :=
  Ufun_comm_rotE _ θ z

theorem U_comm_perm (c κ t : ℝ) (σ : ℤ ≃ ℤ) (z : E) : U c κ t (permE σ z) = permE σ (U c κ t z) :=
  Ufun_comm_permE _ σ z

/-- common phase `e^{iφ}` -/
theorem U_comm_common_phase (c κ t φ : ℝ) (z : E) :
    U c κ t (rotE (fun _ => φ) z) = rotE (fun _ => φ) (U c κ t z) := U_comm_rot c κ t _ z

/-- Fourier translation `û(n) ↦ e^{i n y} û(n)` -/
theorem U_comm_translation (c κ t y : ℝ) (z : E) :
    U c κ t (rotE (fun n => (n : ℝ) * y) z) = rotE (fun n => (n : ℝ) * y) (U c κ t z) :=
  U_comm_rot c κ t _ z

/-- boost: index shift `n ↦ n + m` -/
theorem U_comm_boost (c κ t : ℝ) (m : ℤ) (z : E) :
    U c κ t (permE (Equiv.addRight m) z) = permE (Equiv.addRight m) (U c κ t z) :=
  U_comm_perm c κ t _ z

/-- reflection `n ↦ −n` -/
theorem U_comm_reflection (c κ t : ℝ) (z : E) :
    U c κ t (permE (Equiv.neg ℤ) z) = permE (Equiv.neg ℤ) (U c κ t z) :=
  U_comm_perm c κ t _ z

/-- coupling scaling `U_{κ,1}(s z) = s U_{κ s²,1}(z)` -/
theorem U_one_smul (c κ s : ℝ) (z : E) : U c κ 1 (s • z) = s • U c (κ * s ^ 2) 1 z := by
  unfold U
  rw [Ufun_smul]
  congr 2
  ring

theorem norm_U_one_sub_le (c κ : ℝ) (z : E) : ‖U c κ 1 z - z‖ ≤ 2 * |c| * |κ| * ‖z‖ ^ 3 := by
  have := norm_Ufun_sub_le (2 * c * κ * 1) z
  unfold U
  calc _ ≤ |2 * c * κ * 1| * ‖z‖ ^ 3 := this
    _ = 2 * |c| * |κ| * ‖z‖ ^ 3 := by
      rw [mul_one, abs_mul, abs_mul, abs_two]

theorem norm_fderiv_U_one_sub_id_le (c κ : ℝ) (z : E) :
    ‖fderiv ℝ (U c κ 1) z - ContinuousLinearMap.id ℝ E‖ ≤ 10 * |c| * |κ| * ‖z‖ ^ 2 := by
  have := norm_fderiv_Ufun_sub_id_le (2 * c * κ * 1) z
  unfold U
  calc _ ≤ 5 * |2 * c * κ * 1| * ‖z‖ ^ 2 := this
    _ = 10 * |c| * |κ| * ‖z‖ ^ 2 := by
      rw [mul_one, abs_mul, abs_mul, abs_two]; ring

/-- bounded-ball `C¹` free limit: `U_{κ,1} → id` in `C¹` uniformly on `‖z‖ ≤ R` as `κ → 0⁺`. -/
theorem U_one_C1_free_limit (c : ℝ) (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ < κ₀ → ∀ z : E, ‖z‖ ≤ R →
      ‖U c κ 1 z - z‖ ≤ ε ∧ ‖fderiv ℝ (U c κ 1) z - ContinuousLinearMap.id ℝ E‖ ≤ ε := by
  set K : ℝ := 10 * |c| * (R ^ 3 + R ^ 2) + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨ε / K, div_pos hε hKpos, fun κ hκ hκ' z hz => ?_⟩
  have hκK : κ * K < ε := by
    have := (lt_div_iff₀ hKpos).1 hκ'
    exact this
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have h2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hz0 hz 2
  have h3 : ‖z‖ ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hz0 hz 3
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hk : |κ| = κ := abs_of_pos hκ
  constructor
  · have h := norm_U_one_sub_le c κ z
    rw [hk] at h
    refine h.trans ?_
    have : 2 * |c| * κ * ‖z‖ ^ 3 ≤ 10 * |c| * (R ^ 3 + R ^ 2) * κ := by
      have hR2 : 0 ≤ R ^ 2 := by positivity
      nlinarith [mul_nonneg hc0 hκ.le, mul_nonneg (mul_nonneg hc0 hκ.le) hR2,
        mul_nonneg (mul_nonneg hc0 hκ.le) (sub_nonneg.2 h3)]
    nlinarith
  · have h := norm_fderiv_U_one_sub_id_le c κ z
    rw [hk] at h
    refine h.trans ?_
    have : 10 * |c| * κ * ‖z‖ ^ 2 ≤ 10 * |c| * (R ^ 3 + R ^ 2) * κ := by
      have hR3 : 0 ≤ R ^ 3 := by positivity
      nlinarith [mul_nonneg hc0 hκ.le, mul_nonneg (mul_nonneg hc0 hκ.le) hR3,
        mul_nonneg (mul_nonneg hc0 hκ.le) (sub_nonneg.2 h2)]
    nlinarith

/-- conjugation reverses the displayed phase: `conj (U_{κ,t} z) = U_{κ,−t} (conj z)` -/
theorem conjE_U (c κ t : ℝ) (z : E) : conjE (U c κ t z) = U c κ (-t) (conjE z) := by
  unfold U
  rw [conj_Ufun]
  congr 1; ring

/-- `U_{κ,t}` does not commute with componentwise conjugation (any `t ≠ 0`, `c ≠ 0`, `κ ≠ 0`). -/
theorem U_not_comm_conjE (c κ t : ℝ) (hc : c ≠ 0) (hκ : κ ≠ 0) (ht : t ≠ 0) :
    ∃ z : E, U c κ t (conjE z) ≠ conjE (U c κ t z) := by
  have ha : 2 * c * κ * t ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc) hκ) ht
  exact not_comm_conjE _ ha

/-- the relative Cartesian product of two coordinates changes -/
theorem U_cartesian_product_changes (c κ t : ℝ) (hc : c ≠ 0) (hκ : κ ≠ 0) (ht : t ≠ 0) :
    ∃ z : E, (U c κ t z 0).re * (U c κ t z 1).re ≠ (z 0).re * (z 1).re := by
  have ha : 2 * c * κ * t ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hc) hκ) ht
  exact cartesian_product_changes _ ha

/-- relative phase identity: `U(z)_n conj U(z)_m = e^{-2icκt(|z_m|²−|z_n|²)} z_n conj z_m` -/
theorem U_relative_phase (c κ t : ℝ) (z : E) (n m : ℤ) :
    U c κ t z n * conj (U c κ t z m) =
      Complex.exp (-(2 * Complex.I * c * κ * t) * ((‖z m‖ ^ 2 - ‖z n‖ ^ 2 : ℝ) : ℂ)) * (z n * conj (z m)) := by
  rw [U_apply, U_apply, map_mul, ← Complex.exp_conj]
  have : conj (-(2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z m‖ ^ 2 : ℝ) : ℂ)) =
      (2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z m‖ ^ 2 : ℝ) : ℂ) := by
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  rw [this]
  have h2 : Complex.exp (-(2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z n‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp ((2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z m‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-(2 * Complex.I * c * κ * t) * ((‖z m‖ ^ 2 - ‖z n‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  calc Complex.exp (-(2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z n‖ ^ 2 : ℝ) : ℂ)) * z n *
        (Complex.exp ((2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z m‖ ^ 2 : ℝ) : ℂ)) * conj (z m))
      = (Complex.exp (-(2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z n‖ ^ 2 : ℝ) : ℂ)) *
        Complex.exp ((2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z m‖ ^ 2 : ℝ) : ℂ))) * (z n * conj (z m)) := by ring
    _ = _ := by rw [h2]

/-! ## The proposition `norm:rephasing` (R-8DD5AE6E) -/

/-- **Proposition `norm:rephasing`.** For real `c ≠ 0` and `κ > 0`, with
`F_κ(z) = cκ[(Σ|z_n|²)² − Σ|z_n|⁴]` on `ℓ²(ℤ)` and
`U_{κ,t}(z)_n = e^{−2icκt(‖z‖₂²−|z_n|²)} z_n`:

1. `F_κ` is a continuous real quartic polynomial and `∇F_κ(u)_n = 2cκ(‖u‖²−|u_n|²)u_n` (DEF-015);
2. `U_{κ,t}` is the complete Hamiltonian flow of `F_κ`: group law, `U_0 = id`, solves `ż = X_F(z)`
   (`X_F = −i∇F`) for all real `t`, and is the unique such solution;
3. for every `t`, `U_{κ,t}` is a strong symplectic diffeomorphism (DEF-016) with inverse `U_{κ,−t}`,
   real analytic (DEF-017, literal series form) with real-analytic inverse, preserving every action;
4. at `t = 1`: identity differential at `0`, fixes every single-mode vector, commutes with
   independent coordinate rotations and every index permutation, coupling scaling, bounded-ball
   `C¹` free limit as `κ → 0⁺`;
5. it does not commute with componentwise conjugation and changes relative Cartesian products. -/
theorem norm_rephasing (c κ : ℝ) (hc : c ≠ 0) (hκ : 0 < κ) :
    -- (1) the functional
    ((∃ Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ, ∀ z, F c κ z = Q (fun _ => z)) ∧
      (∀ u : E, ∀ n : ℤ, SymplecticBracket.gradient (F c κ) u n =
        ((2 * c * κ * (‖u‖ ^ 2 - ‖u n‖ ^ 2) : ℝ) : ℂ) * u n)) ∧
    -- (2) the complete Hamiltonian flow
    ((∀ (t : ℝ) (z : E) (n : ℤ), U c κ t z n =
        Complex.exp (-(2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z n‖ ^ 2 : ℝ) : ℂ)) * z n) ∧
      (∀ z : E, U c κ 0 z = z) ∧
      (∀ (s t : ℝ) (z : E), U c κ s (U c κ t z) = U c κ (s + t) z) ∧
      (∀ (z : E) (t : ℝ), HasDerivAt (fun s : ℝ => U c κ s z)
        (SymplecticBracket.hamField (F c κ) (U c κ t z)) t) ∧
      (∀ γ : ℝ → E, (∀ t, HasDerivAt γ (SymplecticBracket.hamField (F c κ) (γ t)) t) →
        ∀ t, γ t = U c κ t (γ 0))) ∧
    -- (3) for every time
    (∀ t : ℝ, IsStrongSymplecticDiffeo (U c κ t) ∧ IsRealAnalyticDEF017 (U c κ t) ∧
      IsRealAnalyticDEF017 (U c κ (-t)) ∧
      (∀ z : E, ∀ n : ℤ, ‖U c κ t z n‖ ^ 2 = ‖z n‖ ^ 2) ∧
      (∀ z : E, U c κ (-t) (U c κ t z) = z)) ∧
    -- (4) time one
    (fderiv ℝ (U c κ 1) 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ (m : ℤ) (w : ℂ), U c κ 1 (lp.single (E := fun _ : ℤ => ℂ) 2 m w) =
        lp.single (E := fun _ : ℤ => ℂ) 2 m w) ∧
      (∀ (θ : ℤ → ℝ) (z : E), U c κ 1 (rotE θ z) = rotE θ (U c κ 1 z)) ∧
      (∀ (σ : ℤ ≃ ℤ) (z : E), U c κ 1 (permE σ z) = permE σ (U c κ 1 z)) ∧
      (∀ (s : ℝ) (z : E), 0 < s → U c κ 1 (s • z) = s • U c (κ * s ^ 2) 1 z) ∧
      (∀ R ε : ℝ, 0 ≤ R → 0 < ε → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ' : ℝ, 0 < κ' → κ' < κ₀ → ∀ z : E,
        ‖z‖ ≤ R → ‖U c κ' 1 z - z‖ ≤ ε ∧
          ‖fderiv ℝ (U c κ' 1) z - ContinuousLinearMap.id ℝ E‖ ≤ ε)) ∧
    -- (5) general inputs
    ((∃ z : E, U c κ 1 (conjE z) ≠ conjE (U c κ 1 z)) ∧
      (∃ z : E, (U c κ 1 z 0).re * (U c κ 1 z 1).re ≠ (z 0).re * (z 1).re)) :=
  ⟨⟨F_quartic c κ, gradient_F_apply c κ⟩,
   ⟨U_apply c κ, U_zero c κ, U_add c κ, U_hasDerivAt c κ, U_unique c κ⟩,
   fun t => ⟨U_strongSymplectic c κ t, U_realAnalytic c κ t, U_realAnalytic c κ (-t),
     fun z n => by rw [norm_U_apply], U_neg_left c κ t⟩,
   ⟨U_one_fderiv_zero c κ, U_single c κ 1, U_comm_rot c κ 1, U_comm_perm c κ 1,
     fun s z _ => U_one_smul c κ s z, U_one_C1_free_limit c⟩,
   ⟨U_not_comm_conjE c κ 1 hc hκ.ne' one_ne_zero, U_cartesian_product_changes c κ 1 hc hκ.ne' one_ne_zero⟩⟩

end
end QuantumNLS.RephasingFlow
