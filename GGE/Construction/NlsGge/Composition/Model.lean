import NlsGge.Composition.Weight
import NlsGge.Composition.Convolution

/-!
# W03: the space `A_w(X)` of Banach-valued periodic functions and its coefficient model

Source: `paper/v2.tex`, lines 1438-1446.  Period one: functions on `AddCircle (1:ℝ)`, Fourier
coefficients are mathlib's `fourierCoeff` (normalized Haar measure, `fourier n θ = e^{2π i n θ}`).

* `MemAw w f` : `f` is continuous and `∑ (w_n ‖f̂(n)‖)^2 < ∞`;
* `awNorm w f = (∑ (w_n ‖f̂(n)‖)^2)^{1/2}`;
* `Model X` : the Banach space `ℓ²(ℤ; X)` of *weighted* coefficient sequences `g_n = w_n f̂(n)`;
* `synth w g θ = ∑ fourier n θ • (w_n⁻¹ • g_n)` : synthesis, with
  `fourierCoeff (synth w g) n = w_n⁻¹ • g_n` and, for `MemAw w f`, `synth w (toModel f) = f`
  and `‖toModel f‖ = awNorm w f` (explicit isometric identification).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NlsGge.Composition

open MeasureTheory AddCircle

/-- Admissible weights: everything about `w` used in the proof of `D:lem:composition`. -/
structure AdmissibleWeight (w : ℤ → ℝ) : Prop where
  pos : ∀ n, 0 < w n
  even : ∀ n, w (-n) = w n
  inv_sq : Summable fun n => (w n)⁻¹ ^ 2
  ratio : ∃ r, RatioMajorant w r
  exp_decay : ∀ c : ℝ, 0 < c → Summable fun n : ℤ => w n ^ 2 * Real.exp (-c * |(n : ℝ)|)

/-- The source weight `exp(a√|n|) ⟨n⟩^b` (`a > 0`, `b` real) is admissible. -/
theorem srcWeight_admissible {a : ℝ} (ha : 0 < a) (b : ℝ) : AdmissibleWeight (srcWeight a b) where
  pos := srcWeight_pos a b
  even := srcWeight_neg a b
  inv_sq := summable_srcWeight_inv_sq ha b
  ratio := ⟨ratioMajorant a b,
    { w_pos := srcWeight_pos a b
      r_nonneg := ratioMajorant_nonneg a b
      r_sq := summable_ratioMajorant_sq ha b
      ratio := fun k l hkl => srcWeight_ratio ha.le b k l hkl }⟩
  exp_decay := fun _ hc => summable_srcWeight_sq_mul_exp a b hc

/-! ### The coefficient model `ℓ²(ℤ; X)` -/

/-- The model space `ℓ²(ℤ; X)` (a type synonym of `lp`, carrying only the real normed-space
structure, to avoid the `ℝ`/`ℂ` scalar diamond on `lp`). -/
def Model (X : Type*) [NormedAddCommGroup X] : Type _ := lp (fun _ : ℤ => X) 2

section ModelInst

variable {X : Type*} [NormedAddCommGroup X]

instance : NormedAddCommGroup (Model X) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℤ => X) 2))

instance [NormedSpace ℝ X] : NormedSpace ℝ (Model X) :=
  inferInstanceAs (NormedSpace ℝ (lp (fun _ : ℤ => X) 2))

instance [CompleteSpace X] : CompleteSpace (Model X) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : ℤ => X) 2))

/-- Underlying `lp` element. -/
def Model.toLp (g : Model X) : lp (fun _ : ℤ => X) 2 := g

/-- Model element from an `lp` element. -/
def Model.ofLp (g : lp (fun _ : ℤ => X) 2) : Model X := g

instance : CoeFun (Model X) (fun _ => ℤ → X) := ⟨fun g => (g.toLp : ℤ → X)⟩

@[simp] theorem Model.toLp_ofLp (g : lp (fun _ : ℤ => X) 2) : (Model.ofLp g).toLp = g := rfl

@[simp] theorem Model.coe_ofLp (g : lp (fun _ : ℤ => X) 2) (n : ℤ) :
    (Model.ofLp g) n = (g : ℤ → X) n := rfl

@[simp] theorem Model.add_apply (g h : Model X) (n : ℤ) : (g + h) n = g n + h n := rfl

@[simp] theorem Model.sub_apply (g h : Model X) (n : ℤ) : (g - h) n = g n - h n := rfl

@[simp] theorem Model.neg_apply (g : Model X) (n : ℤ) : (-g) n = -g n := rfl

@[simp] theorem Model.zero_apply (n : ℤ) : (0 : Model X) n = 0 := rfl

@[simp] theorem Model.smul_apply [NormedSpace ℝ X] (c : ℝ) (g : Model X) (n : ℤ) :
    (c • g) n = c • g n := rfl

theorem Model.norm_def (g : Model X) : ‖g‖ = ‖g.toLp‖ := rfl

theorem Model.ext {g h : Model X} (H : ∀ n, g n = h n) : g = h := by
  have : g.toLp = h.toLp := lp.ext (funext H)
  exact this

/-- Build a model element from a square-summable sequence. -/
def Model.mk (f : ℤ → X) (hf : Summable fun n => ‖f n‖ ^ 2) : Model X :=
  Model.ofLp ⟨f, by
    refine memℓp_gen ?_
    simpa using hf⟩

@[simp] theorem Model.mk_apply (f : ℤ → X) (hf : Summable fun n => ‖f n‖ ^ 2) (n : ℤ) :
    Model.mk f hf n = f n := rfl

theorem Model.summable_sq (g : Model X) : Summable fun n => ‖g n‖ ^ 2 := by
  have := (lp.memℓp g.toLp).summable (p := 2) (by norm_num)
  simpa using this

theorem Model.norm_sq_eq (g : Model X) : ‖g‖ ^ 2 = ∑' n, ‖g n‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) g.toLp
  rw [Model.norm_def]; simpa using this

theorem Model.norm_eq_sqrt (g : Model X) : ‖g‖ = Real.sqrt (∑' n, ‖g n‖ ^ 2) := by
  rw [← g.norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]

theorem Model.norm_apply_le (g : Model X) (n : ℤ) : ‖g n‖ ≤ ‖g‖ := by
  have := lp.norm_apply_le_norm (p := 2) (by norm_num) g.toLp n
  exact this

/-- Norm of a `Model.mk`. -/
theorem Model.norm_mk (f : ℤ → X) (hf : Summable fun n => ‖f n‖ ^ 2) :
    ‖Model.mk f hf‖ = Real.sqrt (∑' n, ‖f n‖ ^ 2) := by
  rw [Model.norm_eq_sqrt]; rfl

/-- A model element is bounded in norm by any `C ≥ 0` with `∑ ‖g n‖² ≤ C²`. -/
theorem Model.norm_le_of_tsum_le (g : Model X) {C : ℝ} (hC : 0 ≤ C)
    (h : ∑' n, ‖g n‖ ^ 2 ≤ C ^ 2) : ‖g‖ ≤ C := by
  rw [Model.norm_eq_sqrt]
  exact Real.sqrt_le_iff.mpr ⟨hC, h⟩

end ModelInst

/-! ### Absolutely convergent exponential sums -/

section ExpSum

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- `θ ↦ ∑_n e^{2π i n θ} c_n`. -/
def expSum (c : ℤ → X) (θ : AddCircle (1 : ℝ)) : X := ∑' n, fourier n θ • c n

theorem norm_fourier_smul (n : ℤ) (θ : AddCircle (1 : ℝ)) (v : X) :
    ‖fourier n θ • v‖ = ‖v‖ := by
  rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]

theorem summable_expSum_terms {c : ℤ → X} (hc : Summable fun n => ‖c n‖) (θ : AddCircle (1 : ℝ)) :
    Summable fun n => fourier n θ • c n :=
  Summable.of_norm (hc.congr fun n => (norm_fourier_smul n θ (c n)).symm)

theorem norm_expSum_le {c : ℤ → X} (hc : Summable fun n => ‖c n‖) (θ : AddCircle (1 : ℝ)) :
    ‖expSum c θ‖ ≤ ∑' n, ‖c n‖ := by
  unfold expSum
  refine (norm_tsum_le_tsum_norm (hc.congr fun n => (norm_fourier_smul n θ (c n)).symm)).trans_eq ?_
  exact tsum_congr fun n => norm_fourier_smul n θ (c n)

theorem continuous_expSum {c : ℤ → X} (hc : Summable fun n => ‖c n‖) : Continuous (expSum c) :=
  continuous_tsum (fun n => (map_continuous (fourier n)).smul continuous_const) hc
    (fun n θ => (norm_fourier_smul n θ (c n)).le)

theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] {f : AddCircle (1 : ℝ) → E}
    (hf : Continuous f) : Integrable f haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem fourierCoeff_fourier_smul (m n : ℤ) (v : X) :
    fourierCoeff (fun θ : AddCircle (1 : ℝ) => fourier m θ • v) n =
      if m = n then v else 0 := by
  unfold fourierCoeff
  simp_rw [smul_smul]
  rw [integral_smul_const]
  have h := congrFun (fourierCoeff_fourier (T := 1) m) n
  unfold fourierCoeff at h
  simp only [smul_eq_mul] at h
  rw [h]
  by_cases hmn : m = n
  · subst hmn; simp
  · simp [hmn, Ne.symm hmn]

/-- Fourier coefficients of an absolutely convergent exponential sum. -/
theorem fourierCoeff_expSum {c : ℤ → X} (hc : Summable fun n => ‖c n‖) (m : ℤ) :
    fourierCoeff (expSum c) m = c m := by
  have hterm : ∀ n, Integrable (fun θ : AddCircle (1 : ℝ) => fourier (-m) θ • (fourier n θ • c n))
      haarAddCircle := fun n =>
    integrable_of_continuous ((map_continuous (fourier (T := 1) (-m))).smul
      ((map_continuous (fourier (T := 1) n)).smul continuous_const))
  have hsum : Summable fun n => ∫ θ : AddCircle (1 : ℝ),
      ‖fourier (-m) θ • (fourier n θ • c n)‖ ∂haarAddCircle := by
    refine hc.congr fun n => ?_
    simp_rw [norm_fourier_smul]
    simp
  unfold fourierCoeff expSum
  have hpt : ∀ θ : AddCircle (1 : ℝ), fourier (-m) θ • ∑' n, fourier n θ • c n =
      ∑' n, fourier (-m) θ • (fourier n θ • c n) := fun θ =>
    ((summable_expSum_terms hc θ).tsum_const_smul _).symm
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hterm hsum]
  have : ∀ n, ∫ θ : AddCircle (1 : ℝ), fourier (-m) θ • (fourier n θ • c n) ∂haarAddCircle =
      if n = m then c n else 0 := by
    intro n
    have := fourierCoeff_fourier_smul n m (c n)
    unfold fourierCoeff at this
    exact this
  simp_rw [this]
  rw [tsum_ite_eq]

theorem expSum_add {c d : ℤ → X} (hc : Summable fun n => ‖c n‖) (hd : Summable fun n => ‖d n‖)
    (θ : AddCircle (1 : ℝ)) : expSum (c + d) θ = expSum c θ + expSum d θ := by
  unfold expSum
  simp_rw [Pi.add_apply, smul_add]
  exact (summable_expSum_terms hc θ).tsum_add (summable_expSum_terms hd θ)

theorem expSum_smul (r : ℝ) (c : ℤ → X) (θ : AddCircle (1 : ℝ)) :
    expSum (r • c) θ = r • expSum c θ := by
  unfold expSum
  simp_rw [Pi.smul_apply, smul_comm (fourier _ θ) r]
  exact tsum_const_smul'' r

/-- Inversion: a continuous function with absolutely summable Fourier coefficients is the sum of
its Fourier series (Banach-valued, via dual functionals). -/
theorem expSum_fourierCoeff {f : AddCircle (1 : ℝ) → X} (hf : Continuous f)
    (hs : Summable fun n => ‖fourierCoeff f n‖) : expSum (fourierCoeff f) = f := by
  funext θ
  refine (NormedSpace.eq_iff_forall_dual_eq ℂ).mpr fun ℓ => ?_
  -- scalar Fourier series of `ℓ ∘ f`
  set g : C(AddCircle (1 : ℝ), ℂ) := ⟨fun t => ℓ (f t), ℓ.continuous.comp hf⟩ with hg
  have hcoef : ∀ n, fourierCoeff (g : AddCircle (1 : ℝ) → ℂ) n = ℓ (fourierCoeff f n) := by
    intro n
    unfold fourierCoeff
    rw [← ℓ.integral_comp_comm ((integrable_of_continuous hf).fourier_smul _)]
    simp [hg]
  have hgs : Summable (fourierCoeff (g : AddCircle (1 : ℝ) → ℂ)) := by
    refine Summable.of_norm_bounded (hs.mul_left ‖ℓ‖) fun n => ?_
    rw [hcoef]; exact ℓ.le_opNorm _
  have h1 := has_pointwise_sum_fourier_series_of_summable hgs θ
  have h2 : ℓ (expSum (fourierCoeff f) θ) = ∑' n, fourierCoeff (g : AddCircle (1 : ℝ) → ℂ) n *
      fourier n θ := by
    unfold expSum
    rw [ℓ.map_tsum (summable_expSum_terms hs θ)]
    congr 1; ext n
    rw [map_smul, hcoef, smul_eq_mul, mul_comm]
  rw [h2]
  have := h1.tsum_eq
  simp only [smul_eq_mul] at this
  rw [this]
  rfl

end ExpSum

/-! ### Weighted synthesis -/

section Synth

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {w : ℤ → ℝ}

/-- Coefficients `c_n = w_n⁻¹ g_n` of a model element. -/
def coeff (w : ℤ → ℝ) (g : Model X) (n : ℤ) : X := (w n)⁻¹ • g n

/-- `S_w = (∑ w_n^{-2})^{1/2}`, the sup-norm constant of W03.01. -/
def supConst (w : ℤ → ℝ) : ℝ := Real.sqrt (∑' n, (w n)⁻¹ ^ 2)

theorem supConst_nonneg (w : ℤ → ℝ) : 0 ≤ supConst w := Real.sqrt_nonneg _

theorem norm_coeff (hw : AdmissibleWeight w) (g : Model X) (n : ℤ) :
    ‖coeff w g n‖ = (w n)⁻¹ * ‖g n‖ := by
  rw [coeff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hw.pos n))]

/-- W03.01: the coefficients of a model element are absolutely summable, with
`∑ ‖c_n‖ ≤ S_w ‖g‖`. -/
theorem summable_norm_coeff (hw : AdmissibleWeight w) (g : Model X) :
    Summable (fun n => ‖coeff w g n‖) ∧ ∑' n, ‖coeff w g n‖ ≤ supConst w * ‖g‖ := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hf0 : ∀ n, 0 ≤ (w n)⁻¹ := fun n => (inv_pos.mpr (hw.pos n)).le
  have hg0 : ∀ n, 0 ≤ ‖g n‖ := fun n => norm_nonneg _
  have hf2 : Summable fun n => (w n)⁻¹ ^ (2 : ℝ) := by
    simpa [Real.rpow_two] using hw.inv_sq
  have hg2 : Summable fun n => ‖g n‖ ^ (2 : ℝ) := by
    simpa [Real.rpow_two] using g.summable_sq
  have hsum := Real.summable_mul_of_Lp_Lq_of_nonneg hpq hf0 hg0 hf2 hg2
  have hle := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf0 hg0 hf2 hg2
  simp_rw [norm_coeff hw]
  refine ⟨hsum, hle.trans_eq ?_⟩
  simp only [Real.rpow_two]
  rw [supConst, Model.norm_eq_sqrt, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- Weighted synthesis `θ ↦ ∑ e^{2πinθ} w_n⁻¹ g_n`. -/
def synth (w : ℤ → ℝ) (g : Model X) : AddCircle (1 : ℝ) → X := expSum (coeff w g)

theorem continuous_synth (hw : AdmissibleWeight w) (g : Model X) : Continuous (synth w g) :=
  continuous_expSum (summable_norm_coeff hw g).1

/-- Sup bound `‖synth g θ‖ ≤ S_w ‖g‖` (absolute uniform convergence, W03.01). -/
theorem norm_synth_le (hw : AdmissibleWeight w) (g : Model X) (θ : AddCircle (1 : ℝ)) :
    ‖synth w g θ‖ ≤ supConst w * ‖g‖ :=
  (norm_expSum_le (summable_norm_coeff hw g).1 θ).trans (summable_norm_coeff hw g).2

theorem fourierCoeff_synth (hw : AdmissibleWeight w) (g : Model X) (n : ℤ) :
    fourierCoeff (synth w g) n = coeff w g n :=
  fourierCoeff_expSum (summable_norm_coeff hw g).1 n

theorem synth_add (hw : AdmissibleWeight w) (g h : Model X) (θ : AddCircle (1 : ℝ)) :
    synth w (g + h) θ = synth w g θ + synth w h θ := by
  unfold synth
  have : coeff w (g + h) = coeff w g + coeff w h := by
    funext n; simp [coeff, smul_add]
  rw [this, expSum_add (summable_norm_coeff hw g).1 (summable_norm_coeff hw h).1]

theorem synth_smul (r : ℝ) (g : Model X) (θ : AddCircle (1 : ℝ)) :
    synth w (r • g) θ = r • synth w g θ := by
  unfold synth
  have : coeff w (r • g) = r • coeff w g := by
    funext n; simp only [coeff, Model.smul_apply, Pi.smul_apply]; rw [smul_comm]
  rw [this, expSum_smul]

/-- Evaluation of the synthesized function at `θ`, as a continuous `ℝ`-linear map with norm
at most `S_w`. -/
def evalCLM (hw : AdmissibleWeight w) (θ : AddCircle (1 : ℝ)) : Model X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun g => synth w g θ
      map_add' := fun g h => synth_add hw g h θ
      map_smul' := fun r g => synth_smul r g θ }
    (supConst w) (fun g => norm_synth_le hw g θ)

@[simp] theorem evalCLM_apply (hw : AdmissibleWeight w) (θ : AddCircle (1 : ℝ)) (g : Model X) :
    evalCLM hw θ g = synth w g θ := rfl

theorem norm_evalCLM_le (hw : AdmissibleWeight w) (θ : AddCircle (1 : ℝ)) :
    ‖(evalCLM hw θ : Model X →L[ℝ] X)‖ ≤ supConst w :=
  LinearMap.mkContinuous_norm_le _ (supConst_nonneg w) _

/-- Synthesis is injective (coefficients are recovered as Fourier coefficients). -/
theorem synth_injective (hw : AdmissibleWeight w) {g h : Model X}
    (H : synth w g = synth w h) : g = h := by
  refine Model.ext fun n => ?_
  have h1 := fourierCoeff_synth hw g n
  have h2 := fourierCoeff_synth hw h n
  rw [H, h2] at h1
  have hw0 : w n ≠ 0 := (hw.pos n).ne'
  have := congrArg (fun x => w n • x) h1
  simp only [coeff, smul_smul, mul_inv_cancel₀ hw0, one_smul] at this
  exact this.symm

end Synth

/-! ### The function space `A_w(X)` -/

section Aw

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {w : ℤ → ℝ}

/-- `f ∈ A_w(X)`: `f` is continuous and `∑ w_n² ‖f̂(n)‖² < ∞` (source line 1440). -/
def MemAw (w : ℤ → ℝ) (f : AddCircle (1 : ℝ) → X) : Prop :=
  Continuous f ∧ Summable fun n => (w n * ‖fourierCoeff f n‖) ^ 2

/-- `‖f‖_{A_w(X)} = (∑ w_n² ‖f̂(n)‖²)^{1/2}` (source line 1441). -/
def awNorm (w : ℤ → ℝ) (f : AddCircle (1 : ℝ) → X) : ℝ :=
  Real.sqrt (∑' n, (w n * ‖fourierCoeff f n‖) ^ 2)

/-- The model element `(w_n f̂(n))_n` of `f ∈ A_w(X)`. -/
def toModel (hw : AdmissibleWeight w) {f : AddCircle (1 : ℝ) → X} (hf : MemAw w f) : Model X :=
  Model.mk (fun n => w n • fourierCoeff f n) (by
    refine hf.2.congr fun n => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hw.pos n)])

@[simp] theorem toModel_apply (hw : AdmissibleWeight w) {f : AddCircle (1 : ℝ) → X}
    (hf : MemAw w f) (n : ℤ) : toModel hw hf n = w n • fourierCoeff f n := rfl

theorem norm_toModel (hw : AdmissibleWeight w) {f : AddCircle (1 : ℝ) → X} (hf : MemAw w f) :
    ‖toModel hw hf‖ = awNorm w f := by
  rw [toModel, Model.norm_mk, awNorm]
  congr 1
  congr 1; ext n
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hw.pos n)]

theorem coeff_toModel (hw : AdmissibleWeight w) {f : AddCircle (1 : ℝ) → X} (hf : MemAw w f)
    (n : ℤ) : coeff w (toModel hw hf) n = fourierCoeff f n := by
  simp [coeff, smul_smul, inv_mul_cancel₀ (hw.pos n).ne']

/-- Every `f ∈ A_w(X)` is the synthesis of its model element. -/
theorem synth_toModel (hw : AdmissibleWeight w) {f : AddCircle (1 : ℝ) → X} (hf : MemAw w f) :
    synth w (toModel hw hf) = f := by
  unfold synth
  have : coeff w (toModel hw hf) = fourierCoeff f := funext (coeff_toModel hw hf)
  rw [this]
  apply expSum_fourierCoeff hf.1
  have := (summable_norm_coeff hw (toModel hw hf)).1
  simpa [coeff_toModel hw hf] using this

/-- Every synthesized function lies in `A_w(X)`, with norm equal to the model norm. -/
theorem memAw_synth (hw : AdmissibleWeight w) (g : Model X) : MemAw w (synth w g) := by
  refine ⟨continuous_synth hw g, ?_⟩
  refine g.summable_sq.congr fun n => ?_
  rw [fourierCoeff_synth hw, norm_coeff hw, ← mul_assoc, mul_inv_cancel₀ (hw.pos n).ne', one_mul]

theorem toModel_synth (hw : AdmissibleWeight w) (g : Model X) :
    toModel hw (memAw_synth hw g) = g := by
  refine Model.ext fun n => ?_
  rw [toModel_apply, fourierCoeff_synth hw, coeff, smul_smul, mul_inv_cancel₀ (hw.pos n).ne',
    one_smul]

theorem awNorm_synth (hw : AdmissibleWeight w) (g : Model X) : awNorm w (synth w g) = ‖g‖ := by
  rw [← norm_toModel hw (memAw_synth hw g), toModel_synth]

end Aw

end NlsGge.Composition
