import QuantumNLS.Fourier

/-!
# DEF-002 / F04 weighted Hilbert spaces `h^s(ℤ)`, `H^s(T_L)`; completeness; Fourier unitary; inclusions

Source anchors (pinned PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`):
* `source/chapters/definitions.tex:13` (DEF-002): for `s ≥ 0`, `H^s(T_L)` / `h^s(ℤ)` use the squared
  norm `Σ (1+|2πn/L|)^{2s} |û(n)|²`; equivalent weights give the same topology but an estimate in a
  different weight needs its conversion constant.
* `source/chapters/foundations/F04.tex:22–29`: F04 uses the *different* bracket `(1+p_n²)^s`, `p_n = 2πn/L`.
* `fable-reconciled-plan.md` §2 (Norms (exact)).

Three weights are kept **distinct** and never silently identified (all constants explicit, from
`QuantumNLS.Fourier`): DEF-002 `sobolevWeight L s`, F04 `f04Weight L s`, unit-circle `bracketWeight s`.

Construction.  A bundled positive weight `W : PosWeight` gives the genuine sequence space
`WSeq W = {x : ℤ → ℂ | Σ W_n |x_n|² < ∞}` (a submodule of `ℤ → ℂ`), with norm `‖x‖² = Σ W_n |x_n|²`;
its normed / inner product / complete structure is *induced* from `ℓ²(ℤ)` along the linear
bijection `x ↦ (√W_n x_n)_n` (mathlib's own pattern for `H^{s,p}`), so completeness is proved, not
assumed.  The sequence space makes sense for every real `s` (positive weights); the **field**
spaces `H^s(T_L) ⊆ L²(T_L)` are only built for `s ≥ 0` (for `s < 0` elements are distributions, which
are not realized here).

No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory AddCircle
open scoped ENNReal ComplexConjugate
open QuantumNLS.Fourier

namespace QuantumNLS.Sobolev

/-- A positive weight on the frequency lattice `ℤ`. -/
structure PosWeight where
  w : ℤ → ℝ
  pos : ∀ n, 0 < w n

namespace PosWeight

variable (W : PosWeight)

theorem sq_sqrt_mul (w : ℝ) (hw : 0 ≤ w) (z : ℂ) : ‖(Real.sqrt w : ℂ) * z‖ ^ 2 = w * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg w),
    Real.sq_sqrt hw]

/-- The sequences with finite weighted square sum, `Σ W_n |x_n|² < ∞`. -/
def carrier : Submodule ℂ (ℤ → ℂ) where
  carrier := {x | Summable fun n => W.w n * ‖x n‖ ^ 2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (W.pos n).le (sq_nonneg _))
      (fun n => ?_) ((hx.mul_left 2).add (hy.mul_left 2))
    have h1 : ‖x n + y n‖ ^ 2 ≤ 2 * ‖x n‖ ^ 2 + 2 * ‖y n‖ ^ 2 := by
      have h0 : ‖x n + y n‖ ^ 2 ≤ (‖x n‖ + ‖y n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (x n) (y n)) 2
      nlinarith [sq_nonneg (‖x n‖ - ‖y n‖)]
    calc W.w n * ‖(x + y) n‖ ^ 2 ≤ W.w n * (2 * ‖x n‖ ^ 2 + 2 * ‖y n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (W.pos n).le
      _ = 2 * (W.w n * ‖x n‖ ^ 2) + 2 * (W.w n * ‖y n‖ ^ 2) := by ring
  smul_mem' := by
    intro c x hx
    refine (hx.mul_left (‖c‖ ^ 2)).congr fun n => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    ring

/-- The weighted sequence space `{x : ℤ → ℂ | Σ W_n |x_n|² < ∞}`.  It is a `def` (not an `abbrev`) on
purpose: the ambient product topology of `ℤ → ℂ` must not be inherited by instance search, since
the topology of this space is the norm topology below. -/
def WSeq : Type := ↥(carrier W)

instance : AddCommGroup (WSeq W) := inferInstanceAs (AddCommGroup ↥(carrier W))
instance : Module ℂ (WSeq W) := inferInstanceAs (Module ℂ ↥(carrier W))

/-- The underlying sequence. -/
def WSeq.val {W : PosWeight} (x : WSeq W) : ℤ → ℂ := Subtype.val (show ↥(carrier W) from x)

theorem WSeq.summable {W : PosWeight} (x : WSeq W) : Summable fun n => W.w n * ‖x.val n‖ ^ 2 :=
  (show ↥(carrier W) from x).2

/-- Build an element from a sequence with finite weighted sum. -/
def WSeq.mk (x : ℤ → ℂ) (h : Summable fun n => W.w n * ‖x n‖ ^ 2) : WSeq W :=
  (⟨x, h⟩ : ↥(carrier W))

@[simp] theorem WSeq.val_mk (x : ℤ → ℂ) (h : Summable fun n => W.w n * ‖x n‖ ^ 2) :
    (WSeq.mk W x h).val = x := rfl

theorem WSeq.ext {W : PosWeight} {x y : WSeq W} (h : x.val = y.val) : x = y := Subtype.ext h

@[simp] theorem WSeq.val_add (x y : WSeq W) : (x + y).val = x.val + y.val := rfl
@[simp] theorem WSeq.val_smul (c : ℂ) (x : WSeq W) : (c • x).val = c • x.val := rfl
@[simp] theorem WSeq.val_zero : (0 : WSeq W).val = 0 := rfl
@[simp] theorem WSeq.val_neg (x : WSeq W) : (-x).val = -x.val := rfl
@[simp] theorem WSeq.val_sub (x y : WSeq W) : (x - y).val = x.val - y.val := rfl

/-- `x ↦ (√W_n x_n)_n` lands in `ℓ²(ℤ)`. -/
theorem memℓp_sqrt (x : WSeq W) :
    Memℓp (fun n => (Real.sqrt (W.w n) : ℂ) * x.val n) 2 := by
  apply memℓp_gen
  have : ∀ n, ‖(Real.sqrt (W.w n) : ℂ) * x.val n‖ ^ (2 : ℝ≥0∞).toReal =
      W.w n * ‖x.val n‖ ^ 2 := fun n => by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact sq_sqrt_mul _ (W.pos n).le _
  simp_rw [this]
  exact x.summable

theorem summable_sq_of_lp (z : lp (fun _ : ℤ => ℂ) 2) : Summable fun n => ‖(z : ℤ → ℂ) n‖ ^ 2 := by
  have := (lp.memℓp z).summable (by simp)
  simpa [Real.rpow_two] using this

/-- The isometry candidate `x ↦ (√W_n x_n)_n : h_W → ℓ²(ℤ)`. -/
def toL2 : WSeq W →ₗ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  toFun x := ⟨fun n => (Real.sqrt (W.w n) : ℂ) * x.val n, memℓp_sqrt W x⟩
  map_add' x y := by
    apply Subtype.ext; funext n
    exact mul_add _ _ _
  map_smul' c x := by
    apply Subtype.ext; funext n
    show (Real.sqrt (W.w n) : ℂ) * (c * x.val n) = c * ((Real.sqrt (W.w n) : ℂ) * x.val n)
    ring

theorem toL2_apply (x : WSeq W) (n : ℤ) :
    (toL2 W x : ℤ → ℂ) n = (Real.sqrt (W.w n) : ℂ) * x.val n := rfl

theorem sqrt_ne_zero' (n : ℤ) : (Real.sqrt (W.w n) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (W.pos n)).ne'

theorem toL2_injective : Function.Injective (toL2 W) := by
  intro x y h
  apply WSeq.ext; funext n
  have := congrFun (congrArg Subtype.val h) n
  simp only [toL2_apply] at this
  exact mul_left_cancel₀ (sqrt_ne_zero' W n) this

theorem toL2_surjective : Function.Surjective (toL2 W) := by
  intro z
  have hz := summable_sq_of_lp z
  have hs : Summable fun n => W.w n * ‖(z : ℤ → ℂ) n / (Real.sqrt (W.w n) : ℂ)‖ ^ 2 := by
    refine hz.congr fun n => ?_
    have h0 : 0 < Real.sqrt (W.w n) := Real.sqrt_pos.2 (W.pos n)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg h0.le, div_pow, Real.sq_sqrt (W.pos n).le]
    field_simp [(W.pos n).ne']
  refine ⟨WSeq.mk W (fun n => (z : ℤ → ℂ) n / (Real.sqrt (W.w n) : ℂ)) hs, ?_⟩
  apply Subtype.ext; funext n
  show (Real.sqrt (W.w n) : ℂ) * ((z : ℤ → ℂ) n / (Real.sqrt (W.w n) : ℂ)) = (z : ℤ → ℂ) n
  exact mul_div_cancel₀ _ (sqrt_ne_zero' W n)

instance : NormedAddCommGroup (WSeq W) :=
  NormedAddCommGroup.induced (WSeq W) (lp (fun _ : ℤ => ℂ) 2) (toL2 W) (toL2_injective W)

theorem norm_def (x : WSeq W) : ‖x‖ = ‖toL2 W x‖ := rfl

instance : NormedSpace ℂ (WSeq W) where
  norm_smul_le c x := by
    rw [norm_def, norm_def, map_smul, norm_smul]

instance : InnerProductSpace ℂ (WSeq W) where
  inner x y := inner ℂ (toL2 W x) (toL2 W y)
  norm_sq_eq_re_inner x := by exact norm_sq_eq_re_inner (toL2 W x)
  conj_inner_symm x y := by exact inner_conj_symm (toL2 W x) (toL2 W y)
  add_left x y z := by simp
  smul_left x y c := by simp [mul_comm]

theorem inner_def (x y : WSeq W) : inner ℂ x y = inner ℂ (toL2 W x) (toL2 W y) := rfl

/-- The linear isometric equivalence `h_W ≃ ℓ²(ℤ)`, `x ↦ (√W_n x_n)_n`. -/
def toL2ᵢ : WSeq W ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 where
  __ := LinearEquiv.ofBijective (toL2 W) ⟨toL2_injective W, toL2_surjective W⟩
  norm_map' _ := rfl

/-- **Completeness**: the weighted sequence space is a Hilbert space, for every positive weight. -/
instance : CompleteSpace (WSeq W) :=
  (toL2ᵢ W).toIsometryEquiv.completeSpace

/-- **The norm is the DEF-002 / F04 weighted square sum**: `‖x‖² = Σ W_n |x_n|²`. -/
theorem hasSum_norm_sq (x : WSeq W) :
    HasSum (fun n => W.w n * ‖x.val n‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by simp) (toL2 W x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  have e : (fun i => ‖(toL2 W x : ℤ → ℂ) i‖ ^ 2) = fun n => W.w n * ‖x.val n‖ ^ 2 :=
    funext fun n => sq_sqrt_mul _ (W.pos n).le _
  rw [e] at h
  rw [norm_def]
  exact h

theorem norm_sq_eq_tsum (x : WSeq W) : ‖x‖ ^ 2 = ∑' n, W.w n * ‖x.val n‖ ^ 2 :=
  (hasSum_norm_sq W x).tsum_eq.symm

/-! ### Continuous inclusions between weighted spaces (explicit constants) -/

theorem summable_of_le {W₁ W₂ : PosWeight} {C : ℝ} (h : ∀ n, W₁.w n ≤ C * W₂.w n) (x : WSeq W₂) :
    Summable fun n => W₁.w n * ‖x.val n‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (W₁.pos n).le (sq_nonneg _))
    (fun n => by
      calc W₁.w n * ‖x.val n‖ ^ 2 ≤ (C * W₂.w n) * ‖x.val n‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (h n) (sq_nonneg _)
        _ = C * (W₂.w n * ‖x.val n‖ ^ 2) := by ring)
    (x.summable.mul_left C)

/-- The identity on sequences `h_{W₂} → h_{W₁}` when `W₁ ≤ C W₂` (linear). -/
def inclₗ (W₁ W₂ : PosWeight) {C : ℝ} (h : ∀ n, W₁.w n ≤ C * W₂.w n) :
    WSeq W₂ →ₗ[ℂ] WSeq W₁ where
  toFun x := WSeq.mk W₁ x.val (summable_of_le h x)
  map_add' _ _ := WSeq.ext rfl
  map_smul' _ _ := WSeq.ext rfl

@[simp] theorem inclₗ_val (W₁ W₂ : PosWeight) {C : ℝ} (h : ∀ n, W₁.w n ≤ C * W₂.w n)
    (x : WSeq W₂) : (inclₗ W₁ W₂ h x).val = x.val := rfl

theorem norm_inclₗ_le (W₁ W₂ : PosWeight) {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, W₁.w n ≤ C * W₂.w n)
    (x : WSeq W₂) : ‖inclₗ W₁ W₂ h x‖ ≤ Real.sqrt C * ‖x‖ := by
  have h1 : ‖inclₗ W₁ W₂ h x‖ ^ 2 ≤ C * ‖x‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) (WSeq.summable _) (x.summable.mul_left C)
    simp only [inclₗ_val]
    calc W₁.w n * ‖x.val n‖ ^ 2 ≤ (C * W₂.w n) * ‖x.val n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (h n) (sq_nonneg _)
      _ = C * (W₂.w n * ‖x.val n‖ ^ 2) := by ring
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [mul_pow, Real.sq_sqrt hC]
  exact h1

/-- **Continuous inclusion `h_{W₂} ↪ h_{W₁}`** (identity on sequences), norm `≤ √C`,
whenever `W₁ ≤ C · W₂`. -/
def incl (W₁ W₂ : PosWeight) {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, W₁.w n ≤ C * W₂.w n) :
    WSeq W₂ →L[ℂ] WSeq W₁ :=
  (inclₗ W₁ W₂ h).mkContinuous (Real.sqrt C) (norm_inclₗ_le W₁ W₂ hC h)

@[simp] theorem incl_val (W₁ W₂ : PosWeight) {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, W₁.w n ≤ C * W₂.w n)
    (x : WSeq W₂) : (incl W₁ W₂ hC h x).val = x.val := rfl

theorem norm_incl_le (W₁ W₂ : PosWeight) {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, W₁.w n ≤ C * W₂.w n)
    (x : WSeq W₂) : ‖incl W₁ W₂ hC h x‖ ≤ Real.sqrt C * ‖x‖ :=
  norm_inclₗ_le W₁ W₂ hC h x

/-- Weights comparable in both directions give a **continuous linear equivalence**
(same topology), with explicit norm bounds `√C₁` and `√C₂`. -/
def equivOfComparable (W₁ W₂ : PosWeight) {C₁ C₂ : ℝ} (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂)
    (hle : ∀ n, W₁.w n ≤ C₁ * W₂.w n) (hge : ∀ n, W₂.w n ≤ C₂ * W₁.w n) :
    WSeq W₂ ≃L[ℂ] WSeq W₁ :=
  ContinuousLinearEquiv.equivOfInverse (incl W₁ W₂ h₁ hle) (incl W₂ W₁ h₂ hge)
    (fun _ => WSeq.ext rfl) (fun _ => WSeq.ext rfl)

@[simp] theorem equivOfComparable_val (W₁ W₂ : PosWeight) {C₁ C₂ : ℝ} (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂)
    (hle : ∀ n, W₁.w n ≤ C₁ * W₂.w n) (hge : ∀ n, W₂.w n ≤ C₂ * W₁.w n) (x : WSeq W₂) :
    (equivOfComparable W₁ W₂ h₁ h₂ hle hge x).val = x.val := rfl

end PosWeight

/-! ## The three distinct weights (never silently identified) -/

section Instances

open PosWeight

/-- DEF-002 weight `(1+|2πn/L|)^{2s}` (`definitions.tex:13`). -/
def def002 (L s : ℝ) : PosWeight := ⟨sobolevWeight L s, sobolevWeight_pos L s⟩

/-- F04 bracket weight `(1+p_n²)^s`, `p_n = 2πn/L` (`F04.tex:22`). -/
def f04W (L s : ℝ) : PosWeight := ⟨f04Weight L s, f04Weight_pos L s⟩

theorem bracketWeight_pos (s : ℝ) (n : ℤ) : 0 < bracketWeight s n := by
  unfold bracketWeight; exact Real.rpow_pos_of_pos (by positivity) _

/-- The unit-circle bracket `(1+n²)^s` (period-1 GGE convention), a third, different weight. -/
def bracketW (s : ℝ) : PosWeight := ⟨bracketWeight s, bracketWeight_pos s⟩

/-- DEF-002 `h^s(ℤ)` (valid, as a sequence space, for every real `s`; the report uses `s ≥ 0`). -/
abbrev h02 (L s : ℝ) : Type := WSeq (def002 L s)
/-- F04 `h^s(ℤ)` with the bracket weight. -/
abbrev h04 (L s : ℝ) : Type := WSeq (f04W L s)
/-- Unit-circle bracket `h^s(ℤ)`. -/
abbrev hBr (s : ℝ) : Type := WSeq (bracketW s)

/-- The norm of `h^s` *is* DEF-002's sum: `‖x‖² = Σ (1+|2πn/L|)^{2s} |x_n|²` (= `hsNormSq`). -/
theorem h02_norm_sq (L s : ℝ) (x : h02 L s) : ‖x‖ ^ 2 = hsNormSq L s x.val :=
  norm_sq_eq_tsum _ x

theorem h04_norm_sq (L s : ℝ) (x : h04 L s) : ‖x‖ ^ 2 = f04NormSq L s x.val :=
  norm_sq_eq_tsum _ x

theorem hBr_norm_sq (s : ℝ) (x : hBr s) :
    ‖x‖ ^ 2 = ∑' n, bracketWeight s n * ‖x.val n‖ ^ 2 :=
  norm_sq_eq_tsum _ x

/-- Elements of `h^s` are exactly the DEF-002 sequences `MemHs`. -/
theorem h02_mem (L s : ℝ) (x : h02 L s) : MemHs L s x.val := x.summable

def h02.ofMem {L s : ℝ} {x : ℤ → ℂ} (hx : MemHs L s x) : h02 L s := WSeq.mk _ x hx

theorem h04_mem (L s : ℝ) (x : h04 L s) : Mem04 L s x.val := x.summable

def h04.ofMem {L s : ℝ} {x : ℤ → ℂ} (hx : Mem04 L s x) : h04 L s := WSeq.mk _ x hx

theorem sobolevWeight_mono (L : ℝ) {s t : ℝ} (hst : s ≤ t) (n : ℤ) :
    sobolevWeight L s n ≤ sobolevWeight L t n := by
  unfold sobolevWeight
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (2 * Real.pi * (n : ℝ) / L)])
    (by linarith)

theorem def002_le_of_le (L : ℝ) {s t : ℝ} (hst : s ≤ t) (n : ℤ) :
    (def002 L s).w n ≤ 1 * (def002 L t).w n := by
  simpa [def002] using sobolevWeight_mono L hst n

theorem f04W_le_of_le (L : ℝ) {s t : ℝ} (hst : s ≤ t) (n : ℤ) :
    (f04W L s).w n ≤ 1 * (f04W L t).w n := by
  simpa [f04W] using f04Weight_mono L hst n

/-- **Continuous inclusion `h^t ↪ h^s` for `s ≤ t`** (DEF-002 weight), norm `≤ 1`. -/
def h02_mono (L : ℝ) {s t : ℝ} (hst : s ≤ t) : h02 L t →L[ℂ] h02 L s :=
  incl (def002 L s) (def002 L t) (C := 1) zero_le_one (def002_le_of_le L hst)

theorem norm_h02_mono_le (L : ℝ) {s t : ℝ} (hst : s ≤ t) (x : h02 L t) :
    ‖h02_mono L hst x‖ ≤ ‖x‖ := by
  have h := norm_incl_le (def002 L s) (def002 L t) (C := 1) zero_le_one (def002_le_of_le L hst) x
  rw [Real.sqrt_one, one_mul] at h
  exact h

/-- **Continuous inclusion `h^t ↪ h^s` for `s ≤ t`** (F04 weight), norm `≤ 1`. -/
def h04_mono (L : ℝ) {s t : ℝ} (hst : s ≤ t) : h04 L t →L[ℂ] h04 L s :=
  incl (f04W L s) (f04W L t) (C := 1) zero_le_one (f04W_le_of_le L hst)

theorem norm_h04_mono_le (L : ℝ) {s t : ℝ} (hst : s ≤ t) (x : h04 L t) :
    ‖h04_mono L hst x‖ ≤ ‖x‖ := by
  have h := norm_incl_le (f04W L s) (f04W L t) (C := 1) zero_le_one (f04W_le_of_le L hst) x
  rw [Real.sqrt_one, one_mul] at h
  exact h

theorem f04W_le_def002 (L : ℝ) {s : ℝ} (hs : 0 ≤ s) (n : ℤ) :
    (f04W L s).w n ≤ 1 * (def002 L s).w n := by
  simpa [f04W, def002] using (f04Weight_comparison L s hs n).1

theorem def002_le_f04W (L : ℝ) {s : ℝ} (hs : 0 ≤ s) (n : ℤ) :
    (def002 L s).w n ≤ (2 : ℝ) ^ s * (f04W L s).w n :=
  (f04Weight_comparison L s hs n).2

/-- **DEF-002 ↔ F04 conversion** (`s ≥ 0`): continuous linear equivalence `h^s_{DEF-002} ≃ h^s_{F04}`
(identity on sequences) with the explicit constants of `f04Weight_comparison`:
`‖x‖_{F04} ≤ ‖x‖_{DEF-002}` and `‖x‖_{DEF-002} ≤ 2^{s/2} ‖x‖_{F04}`. -/
def h02EquivH04 (L : ℝ) {s : ℝ} (hs : 0 ≤ s) : h02 L s ≃L[ℂ] h04 L s :=
  equivOfComparable (f04W L s) (def002 L s) (C₁ := 1) (C₂ := (2 : ℝ) ^ s) zero_le_one
    (by positivity) (f04W_le_def002 L hs) (def002_le_f04W L hs)

theorem norm_h02EquivH04_le (L : ℝ) {s : ℝ} (hs : 0 ≤ s) (x : h02 L s) :
    ‖h02EquivH04 L hs x‖ ≤ ‖x‖ := by
  have h := norm_incl_le (f04W L s) (def002 L s) (C := 1) zero_le_one (f04W_le_def002 L hs) x
  rw [Real.sqrt_one, one_mul] at h
  exact h

theorem norm_h02EquivH04_symm_le (L : ℝ) {s : ℝ} (hs : 0 ≤ s) (y : h04 L s) :
    ‖(h02EquivH04 L hs).symm y‖ ≤ Real.sqrt ((2 : ℝ) ^ s) * ‖y‖ :=
  norm_incl_le (def002 L s) (f04W L s) (C := (2 : ℝ) ^ s) (by positivity)
    (def002_le_f04W L hs) y

/-- **DEF-002 ↔ unit-circle bracket** (`L > 0`, `s ≥ 0`): continuous linear equivalence with the
explicit L-dependent constants `lowerConst`, `upperConst` of `sobolevWeight_comparison`. -/
def h02EquivHBr {L : ℝ} (hL : 0 < L) {s : ℝ} (hs : 0 ≤ s) : h02 L s ≃L[ℂ] hBr s :=
  equivOfComparable (bracketW s) (def002 L s) (C₁ := (lowerConst L s)⁻¹) (C₂ := upperConst L s)
    (inv_nonneg.2 (lowerConst_pos L s hL).le) (upperConst_pos L s).le
    (fun n => by
      have h := (sobolevWeight_comparison L s hL hs n).1
      exact (le_inv_mul_iff₀ (lowerConst_pos L s hL)).2 h)
    (fun n => (sobolevWeight_comparison L s hL hs n).2)

end Instances

/-! ## Field spaces `H^s(T_L) ⊆ L²(T_L)` and the Fourier unitary restricted to weights

Only for weights `W ≥ 1` (i.e. `s ≥ 0`): then `WSeq W ⊆ ℓ²` and the field space is a genuine `L²`
subspace.  For `s < 0` the elements of `H^s` are distributions, which are **not** realized here (only
the sequence spaces `h^s` above exist for negative `s`). -/

section Field

open PosWeight

variable (L : ℝ) [Fact (0 < L)]

/-- The orthonormal coefficient sequence `(û(n))_n` of an `L²` class, as a plain sequence. -/
def fourierSeq : Lp ℂ 2 (volume : Measure (AddCircle L)) →ₗ[ℂ] (ℤ → ℂ) where
  toFun u := fun n => fourierL2 L u n
  map_add' u v := by funext n; simp
  map_smul' c u := by funext n; simp

theorem fourierSeq_apply (u : Lp ℂ 2 (volume : Measure (AddCircle L))) (n : ℤ) :
    fourierSeq L u n = fourierL2 L u n := rfl

/-- `L²` classes whose coefficient sequence has finite `W`-weighted square sum. -/
def fieldSub (W : PosWeight) : Submodule ℂ (Lp ℂ 2 (volume : Measure (AddCircle L))) :=
  (carrier W).comap (fourierSeq L)

/-- The field space `H_W(T_L)`.  A `def` (not an `abbrev`), so that neither the `L²` norm nor the
subtype topology of the ambient `Lp` is inherited: its norm is the weighted one below. -/
def WField (W : PosWeight) : Type := ↥(fieldSub L W)

variable {L}

instance (W : PosWeight) : AddCommGroup (WField L W) :=
  inferInstanceAs (AddCommGroup ↥(fieldSub L W))
instance (W : PosWeight) : Module ℂ (WField L W) := inferInstanceAs (Module ℂ ↥(fieldSub L W))

/-- The underlying `L²` class. -/
def WField.val {W : PosWeight} (u : WField L W) : Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  Subtype.val (show ↥(fieldSub L W) from u)

theorem WField.summable {W : PosWeight} (u : WField L W) :
    Summable fun n => W.w n * ‖fourierL2 L u.val n‖ ^ 2 :=
  (show ↥(fieldSub L W) from u).2

def WField.mk {W : PosWeight} (u : Lp ℂ 2 (volume : Measure (AddCircle L)))
    (h : Summable fun n => W.w n * ‖fourierL2 L u n‖ ^ 2) : WField L W :=
  (⟨u, h⟩ : ↥(fieldSub L W))

@[simp] theorem WField.val_mk {W : PosWeight} (u : Lp ℂ 2 (volume : Measure (AddCircle L)))
    (h : Summable fun n => W.w n * ‖fourierL2 L u n‖ ^ 2) : (WField.mk (W := W) u h).val = u := rfl

theorem WField.ext {W : PosWeight} {u v : WField L W} (h : u.val = v.val) : u = v := Subtype.ext h

@[simp] theorem WField.val_add {W : PosWeight} (u v : WField L W) : (u + v).val = u.val + v.val := rfl
@[simp] theorem WField.val_smul {W : PosWeight} (c : ℂ) (u : WField L W) :
    (c • u).val = c • u.val := rfl

variable (L)

/-- The coefficient map `u ↦ (û(n))_n` into the weighted sequence space. -/
def toSeq (W : PosWeight) : WField L W →ₗ[ℂ] WSeq W where
  toFun u := WSeq.mk W (fourierSeq L u.val) u.summable
  map_add' u v := WSeq.ext (by
    show fourierSeq L (u + v).val = fourierSeq L u.val + fourierSeq L v.val
    rw [WField.val_add, map_add])
  map_smul' c u := WSeq.ext (by
    show fourierSeq L (c • u).val = c • fourierSeq L u.val
    rw [WField.val_smul, map_smul])

theorem toSeq_val {W : PosWeight} (u : WField L W) (n : ℤ) :
    (toSeq L W u).val n = fourierL2 L u.val n := rfl

theorem toSeq_injective (W : PosWeight) : Function.Injective (toSeq L W) := by
  intro u v h
  apply WField.ext
  apply (fourierL2 L).injective
  apply Subtype.ext; funext n
  have := congrFun (congrArg WSeq.val h) n
  simpa [toSeq_val] using this

instance (W : PosWeight) : NormedAddCommGroup (WField L W) :=
  NormedAddCommGroup.induced (WField L W) (WSeq W) (toSeq L W) (toSeq_injective L W)

theorem WField.norm_def {W : PosWeight} (u : WField L W) : ‖u‖ = ‖toSeq L W u‖ := rfl

instance (W : PosWeight) : NormedSpace ℂ (WField L W) where
  norm_smul_le c u := by
    rw [WField.norm_def, WField.norm_def, map_smul, norm_smul]

instance (W : PosWeight) : InnerProductSpace ℂ (WField L W) where
  inner u v := inner ℂ (toSeq L W u) (toSeq L W v)
  norm_sq_eq_re_inner u := by exact norm_sq_eq_re_inner (toSeq L W u)
  conj_inner_symm u v := by exact inner_conj_symm (toSeq L W u) (toSeq L W v)
  add_left u v w := by simp
  smul_left u v c := by simp [mul_comm]

/-- **The norm of `H_W(T_L)` is the weighted coefficient sum**: `‖u‖² = Σ W_n |û(n)|²`. -/
theorem WField.norm_sq_eq_tsum {W : PosWeight} (u : WField L W) :
    ‖u‖ ^ 2 = ∑' n, W.w n * ‖fourierL2 L u.val n‖ ^ 2 := by
  rw [WField.norm_def, PosWeight.norm_sq_eq_tsum]; rfl

variable {L}

/-- For weights `W ≥ 1` the coefficient map is onto the weighted sequence space. -/
theorem toSeq_surjective {W : PosWeight} (hW : ∀ n, 1 ≤ W.w n) :
    Function.Surjective (toSeq L W) := by
  intro x
  have hsum : Summable fun n => ‖x.val n‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      (fun n => by nlinarith [hW n, sq_nonneg ‖x.val n‖]) x.summable
  let z : lp (fun _ : ℤ => ℂ) 2 := ⟨x.val, by
    apply memℓp_gen
    simpa [Real.rpow_two] using hsum⟩
  have hz : ∀ n, fourierL2 L ((fourierL2 L).symm z) n = x.val n := fun n => by
    rw [LinearIsometryEquiv.apply_symm_apply]
  have hmem : Summable fun n => W.w n * ‖fourierL2 L ((fourierL2 L).symm z) n‖ ^ 2 := by
    simp_rw [hz]; exact x.summable
  refine ⟨WField.mk ((fourierL2 L).symm z) hmem, ?_⟩
  apply WSeq.ext; funext n
  exact hz n

/-- **The Fourier unitary restricted to weights**: `U1 : H_W(T_L) ≃ₗᵢ h_W(ℤ)`, `u ↦ (û(n))_n`
(`W ≥ 1`, i.e. `s ≥ 0`).  Isometric by construction of the norm; surjectivity is the content. -/
def fourierHs {W : PosWeight} (hW : ∀ n, 1 ≤ W.w n) : WField L W ≃ₗᵢ[ℂ] WSeq W where
  __ := LinearEquiv.ofBijective (toSeq L W) ⟨toSeq_injective L W, toSeq_surjective hW⟩
  norm_map' _ := rfl

theorem fourierHs_val {W : PosWeight} (hW : ∀ n, 1 ≤ W.w n) (u : WField L W) (n : ℤ) :
    (fourierHs hW u).val n = fourierL2 L u.val n := rfl

/-- **Completeness**: `H_W(T_L)` is a Hilbert space for every weight `W ≥ 1`. -/
theorem WField.completeSpace {W : PosWeight} (hW : ∀ n, 1 ≤ W.w n) :
    CompleteSpace (WField L W) :=
  (fourierHs (L := L) hW).toIsometryEquiv.completeSpace

end Field

/-! ## Continuous inclusions of the field spaces; instantiation at `s ≥ 0`; links to `Fourier.lean` -/

section FieldIncl

open PosWeight

variable {L : ℝ} [Fact (0 < L)]

theorem lp_norm_sq_tsum (z : lp (fun _ : ℤ => ℂ) 2) : ‖z‖ ^ 2 = ∑' n, ‖(z : ℤ → ℂ) n‖ ^ 2 := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by simp) z
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  exact h.tsum_eq.symm

/-- The `L²` norm is dominated by the `H_W` norm when `W ≥ 1`. -/
theorem WField.norm_val_le {W : PosWeight} (hW : ∀ n, 1 ≤ W.w n) (u : WField L W) :
    ‖u.val‖ ≤ ‖u‖ := by
  have h1 : ‖u.val‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [WField.norm_sq_eq_tsum, ← norm_fourierL2 L u.val, lp_norm_sq_tsum]
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_sq_of_lp _) u.summable
    have := hW n
    nlinarith [sq_nonneg ‖fourierL2 L u.val n‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

/-- For weight `≡ 1` the `H_W` norm is exactly the `L²` norm. -/
theorem WField.norm_val_eq {W : PosWeight} (h1 : ∀ n, W.w n = 1) (u : WField L W) :
    ‖u.val‖ = ‖u‖ := by
  have h : ‖u.val‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [WField.norm_sq_eq_tsum, ← norm_fourierL2 L u.val, lp_norm_sq_tsum]
    exact tsum_congr fun n => by rw [h1 n, one_mul]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The linear map `u ↦ u.val`, `H_W(T_L) → L²(T_L)`. -/
def fieldToL2Lin (W : PosWeight) : WField L W →ₗ[ℂ] Lp ℂ 2 (volume : Measure (AddCircle L)) where
  toFun u := u.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Continuous inclusion `H^s(T_L) ↪ L²(T_L)`** (any weight `W ≥ 1`, i.e. `s ≥ 0`), norm `≤ 1`. -/
def fieldToL2 {W : PosWeight} (hW : ∀ n, 1 ≤ W.w n) :
    WField L W →L[ℂ] Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  (fieldToL2Lin W).mkContinuous 1 (fun u => by
    have h := WField.norm_val_le hW u
    rw [one_mul]
    exact h)

@[simp] theorem fieldToL2_apply {W : PosWeight} (hW : ∀ n, 1 ≤ W.w n) (u : WField L W) :
    fieldToL2 hW u = u.val := rfl

theorem norm_fieldToL2_le {W : PosWeight} (hW : ∀ n, 1 ≤ W.w n) (u : WField L W) :
    ‖fieldToL2 hW u‖ ≤ ‖u‖ := WField.norm_val_le hW u

/-- Monotone inclusion of field spaces, identity on `L²` classes, for `W₁ ≤ C · W₂`;
norm `≤ √C`.  (No lower bound on the weights is needed.) -/
def fieldInclₗ (W₁ W₂ : PosWeight) {C : ℝ} (h : ∀ n, W₁.w n ≤ C * W₂.w n) :
    WField L W₂ →ₗ[ℂ] WField L W₁ where
  toFun u := WField.mk u.val (summable_of_le h (toSeq L W₂ u))
  map_add' _ _ := WField.ext rfl
  map_smul' _ _ := WField.ext rfl

@[simp] theorem fieldInclₗ_val (W₁ W₂ : PosWeight) {C : ℝ} (h : ∀ n, W₁.w n ≤ C * W₂.w n)
    (u : WField L W₂) : (fieldInclₗ W₁ W₂ h u).val = u.val := rfl

theorem norm_fieldInclₗ_le (W₁ W₂ : PosWeight) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, W₁.w n ≤ C * W₂.w n) (u : WField L W₂) :
    ‖fieldInclₗ W₁ W₂ h u‖ ≤ Real.sqrt C * ‖u‖ := by
  have e : toSeq L W₁ (fieldInclₗ W₁ W₂ h u) = incl W₁ W₂ hC h (toSeq L W₂ u) := WSeq.ext rfl
  rw [WField.norm_def, WField.norm_def, e]
  exact norm_incl_le W₁ W₂ hC h _

/-- **Continuous inclusion `H_{W₂}(T_L) ↪ H_{W₁}(T_L)`** when `W₁ ≤ C W₂`, norm `≤ √C`. -/
def fieldIncl (W₁ W₂ : PosWeight) {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, W₁.w n ≤ C * W₂.w n) :
    WField L W₂ →L[ℂ] WField L W₁ :=
  (fieldInclₗ W₁ W₂ h).mkContinuous (Real.sqrt C) (norm_fieldInclₗ_le W₁ W₂ hC h)

@[simp] theorem fieldIncl_val (W₁ W₂ : PosWeight) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, W₁.w n ≤ C * W₂.w n) (u : WField L W₂) : (fieldIncl W₁ W₂ hC h u).val = u.val := rfl

theorem norm_fieldIncl_le (W₁ W₂ : PosWeight) {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, W₁.w n ≤ C * W₂.w n)
    (u : WField L W₂) : ‖fieldIncl W₁ W₂ hC h u‖ ≤ Real.sqrt C * ‖u‖ :=
  norm_fieldInclₗ_le W₁ W₂ hC h u

/-! ### DEF-002 and F04 field spaces for `s ≥ 0` -/

theorem one_le_def002 (L : ℝ) {s : ℝ} (hs : 0 ≤ s) (n : ℤ) : 1 ≤ (def002 L s).w n :=
  one_le_sobolevWeight L s hs n

theorem one_le_f04W (L : ℝ) {s : ℝ} (hs : 0 ≤ s) (n : ℤ) : 1 ≤ (f04W L s).w n := by
  show 1 ≤ (1 + freq L n ^ 2) ^ s
  exact Real.one_le_rpow (by nlinarith [sq_nonneg (freq L n)]) hs

/-- DEF-002 `H^s(T_L)` as a Hilbert subspace of `L²(T_L)` (`s ≥ 0`). -/
abbrev H02 (L s : ℝ) [Fact (0 < L)] : Type := WField L (def002 L s)

/-- F04 `H^s(T_L)` (bracket weight) as a Hilbert subspace of `L²(T_L)` (`s ≥ 0`). -/
abbrev H04sp (L s : ℝ) [Fact (0 < L)] : Type := WField L (f04W L s)

/-- Membership in the DEF-002 `H^s` is exactly the Fourier-module predicate `MemHsLp`. -/
theorem mem_fieldSub_def002 {s : ℝ} (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    u ∈ fieldSub L (def002 L s) ↔ MemHsLp L s u := Iff.rfl

/-- The `H^s` norm of `H02` is the DEF-002 sum of `Fourier.lean`: `‖u‖² = hsLpNormSq`. -/
theorem H02.norm_sq_eq {s : ℝ} (u : H02 L s) : ‖u‖ ^ 2 = hsLpNormSq L s u.val := by
  rw [WField.norm_sq_eq_tsum]; rfl

/-- `H^s ↪ L²` (DEF-002, `s ≥ 0`): `‖u‖_{L²} ≤ ‖u‖_{H^s}`. -/
def H02.toL2 {s : ℝ} (hs : 0 ≤ s) : H02 L s →L[ℂ] Lp ℂ 2 (volume : Measure (AddCircle L)) :=
  fieldToL2 (one_le_def002 L hs)

/-- `H^0 = L²` isometrically (DEF-002 at `s = 0`). -/
theorem H02.norm_zero (u : H02 L 0) : ‖u.val‖ = ‖u‖ :=
  WField.norm_val_eq (fun n => by simp [def002]) u

/-- Every `L²` class is in `H^0`. -/
theorem H02.exists_zero (v : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    ∃ u : H02 L 0, u.val = v := by
  refine ⟨WField.mk v ?_, rfl⟩
  have := summable_sq_of_lp (fourierL2 L v)
  simpa [def002] using this

/-- Continuous inclusion `H^t ↪ H^s`, `0 ≤ s ≤ t`, norm `≤ 1` (DEF-002). -/
def H02.mono {s t : ℝ} (hst : s ≤ t) : H02 L t →L[ℂ] H02 L s :=
  fieldIncl (def002 L s) (def002 L t) (C := 1) zero_le_one (def002_le_of_le L hst)

theorem H02.norm_mono_le {s t : ℝ} (hst : s ≤ t) (u : H02 L t) : ‖H02.mono hst u‖ ≤ ‖u‖ := by
  have h := norm_fieldIncl_le (def002 L s) (def002 L t) (C := 1) zero_le_one
    (def002_le_of_le L hst) u
  rw [Real.sqrt_one, one_mul] at h
  exact h

/-- F04: the same, `H^t ↪ H^s`, `s ≤ t`, norm `≤ 1`. -/
def H04sp.mono {s t : ℝ} (hst : s ≤ t) : H04sp L t →L[ℂ] H04sp L s :=
  fieldIncl (f04W L s) (f04W L t) (C := 1) zero_le_one (f04W_le_of_le L hst)

theorem H04sp.norm_mono_le {s t : ℝ} (hst : s ≤ t) (u : H04sp L t) : ‖H04sp.mono hst u‖ ≤ ‖u‖ := by
  have h := norm_fieldIncl_le (f04W L s) (f04W L t) (C := 1) zero_le_one (f04W_le_of_le L hst) u
  rw [Real.sqrt_one, one_mul] at h
  exact h

/-- DEF-002 ↔ F04 field spaces (`s ≥ 0`): continuous inclusions with the exact constants
`1` and `√(2^s)` (`f04Weight_comparison`). -/
def H02.toH04 {s : ℝ} (hs : 0 ≤ s) : H02 L s →L[ℂ] H04sp L s :=
  fieldIncl (f04W L s) (def002 L s) (C := 1) zero_le_one (f04W_le_def002 L hs)

def H04sp.toH02 {s : ℝ} (hs : 0 ≤ s) : H04sp L s →L[ℂ] H02 L s :=
  fieldIncl (def002 L s) (f04W L s) (C := (2 : ℝ) ^ s) (by positivity) (def002_le_f04W L hs)

theorem H02.norm_toH04_le {s : ℝ} (hs : 0 ≤ s) (u : H02 L s) : ‖H02.toH04 hs u‖ ≤ ‖u‖ := by
  have h := norm_fieldIncl_le (f04W L s) (def002 L s) (C := 1) zero_le_one (f04W_le_def002 L hs) u
  rw [Real.sqrt_one, one_mul] at h
  exact h

theorem H04sp.norm_toH02_le {s : ℝ} (hs : 0 ≤ s) (u : H04sp L s) :
    ‖H04sp.toH02 hs u‖ ≤ Real.sqrt ((2 : ℝ) ^ s) * ‖u‖ :=
  norm_fieldIncl_le (def002 L s) (f04W L s) (C := (2 : ℝ) ^ s) (by positivity)
    (def002_le_f04W L hs) u

/-- The `L²` coefficient of `toLp f` is the report coefficient of `f` (a.e.-invariance). -/
theorem fourierL2_toLp {f : AddCircle L → ℂ} (hf : MemLp f 2 (volume : Measure (AddCircle L)))
    (n : ℤ) : fourierL2 L (hf.toLp f) n = coeff L f n := by
  rw [fourierL2_apply]; exact coeff_congr_ae L hf.coeFn_toLp n

/-- Link to the function-level R-00E786F0 predicate: `H04 L s f` iff the `L²` class of `f` lies in the
F04 field space. -/
theorem H04_iff_mem_fieldSub {s : ℝ} {f : AddCircle L → ℂ}
    (hf : MemLp f 2 (volume : Measure (AddCircle L))) :
    H04 L s f ↔ hf.toLp f ∈ fieldSub L (f04W L s) := by
  have e : ∀ n, coeff L f n = fourierL2 L (hf.toLp f) n := fun n => (fourierL2_toLp hf n).symm
  constructor
  · intro h
    have h2 := h.2
    unfold Mem04 at h2
    simp_rw [e] at h2
    exact h2
  · intro h
    refine ⟨hf, ?_⟩
    unfold Mem04
    simp_rw [e]
    exact h

/-- ... and the F04 norm of the function-level theory is the norm in `H04sp`. -/
theorem h04Norm_eq_norm {s : ℝ} {f : AddCircle L → ℂ}
    (hf : MemLp f 2 (volume : Measure (AddCircle L)))
    (h : hf.toLp f ∈ fieldSub L (f04W L s)) :
    h04Norm L s f = ‖(WField.mk (W := f04W L s) (hf.toLp f) h)‖ := by
  have e : ∀ n, coeff L f n = fourierL2 L (hf.toLp f) n := fun n => (fourierL2_toLp hf n).symm
  have hsq := WField.norm_sq_eq_tsum L (WField.mk (W := f04W L s) (hf.toLp f) h)
  unfold h04Norm f04NormSq
  simp_rw [e]
  rw [← Real.sqrt_sq (norm_nonneg (WField.mk (W := f04W L s) (hf.toLp f) h)), hsq]
  rfl

end FieldIncl

/-! ## `H¹(T_L) ↪ C(T_L)` (F04 `eq:l1`, as a continuous linear embedding) -/

section Embedding

open PosWeight

variable {L : ℝ} [Fact (0 < L)]

omit [Fact (0 < L)] in
theorem seriesRep_add' {a b : ℤ → ℂ} (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (x : AddCircle L) :
    seriesRep L (fun n => a n + b n) x = seriesRep L a x + seriesRep L b x := by
  have h1 : Summable fun n => a n * mode L n x :=
    Summable.of_norm (by simpa [norm_mul, norm_mode] using ha.mul_right (Real.sqrt L)⁻¹)
  have h2 : Summable fun n => b n * mode L n x :=
    Summable.of_norm (by simpa [norm_mul, norm_mode] using hb.mul_right (Real.sqrt L)⁻¹)
  unfold seriesRep
  simp_rw [add_mul]
  exact h1.tsum_add h2

omit [Fact (0 < L)] in
theorem seriesRep_smul' (c : ℂ) (a : ℤ → ℂ) (x : AddCircle L) :
    seriesRep L (fun n => c * a n) x = c * seriesRep L a x := by
  unfold seriesRep
  simp_rw [mul_assoc]
  rw [tsum_mul_left]

/-- Elements of the F04 `H¹` field space have absolutely summable coefficients. -/
theorem WField.summable_norm_f04 (u : WField L (f04W L 1)) :
    Summable fun n => ‖fourierL2 L u.val n‖ :=
  (tsum_norm_le_cL (Fact.out : 0 < L) (x := fun n => fourierL2 L u.val n) u.summable).1

/-- The continuous sum `Σ û(n) e_n` of an `H¹` element, as a continuous function. -/
def sobolevSeries (u : WField L (f04W L 1)) : C(AddCircle L, ℂ) :=
  ⟨seriesRep L (fun n => fourierL2 L u.val n), continuous_seriesRep u.summable_norm_f04⟩

theorem sobolevSeries_apply (u : WField L (f04W L 1)) (x : AddCircle L) :
    sobolevSeries u x = seriesRep L (fun n => fourierL2 L u.val n) x := rfl

/-- **F04 `eq:l1` sup bound, field-space form**: `‖Σ û(n)e_n(x)‖ ≤ c_L ‖u‖_{H¹}` for every `x`. -/
theorem norm_sobolevSeries_apply_le (u : WField L (f04W L 1)) (x : AddCircle L) :
    ‖sobolevSeries u x‖ ≤ cL L * ‖u‖ := by
  have hL : 0 < L := Fact.out
  obtain ⟨hS, hle⟩ := tsum_norm_le_cL hL (x := fun n => fourierL2 L u.val n) u.summable
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hnorm : Real.sqrt (f04NormSq L 1 fun n => fourierL2 L u.val n) = ‖u‖ := by
    have := WField.norm_sq_eq_tsum L u
    rw [← Real.sqrt_sq (norm_nonneg u), this]
    rfl
  rw [hnorm] at hle
  rw [sobolevSeries_apply]
  calc ‖seriesRep L (fun n => fourierL2 L u.val n) x‖
      ≤ (Real.sqrt L)⁻¹ * ∑' n, ‖fourierL2 L u.val n‖ := norm_seriesRep_le hS x
    _ ≤ (Real.sqrt L)⁻¹ * (Real.sqrt L * cL L * ‖u‖) :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hs.le)
    _ = cL L * ‖u‖ := by field_simp

/-- The embedding as a linear map into `C(T_L, ℂ)`. -/
def sobolevEmbeddingₗ : WField L (f04W L 1) →ₗ[ℂ] C(AddCircle L, ℂ) where
  toFun := sobolevSeries
  map_add' u v := by
    ext x
    have e : (fun n => fourierL2 L (u + v).val n) =
        fun n => fourierL2 L u.val n + fourierL2 L v.val n := funext fun n => by simp
    show seriesRep L (fun n => fourierL2 L (u + v).val n) x = _
    rw [e, seriesRep_add' u.summable_norm_f04 v.summable_norm_f04]
    rfl
  map_smul' c u := by
    ext x
    have e : (fun n => fourierL2 L (c • u).val n) = fun n => c * fourierL2 L u.val n :=
      funext fun n => by simp
    show seriesRep L (fun n => fourierL2 L (c • u).val n) x = _
    rw [e, seriesRep_smul']
    rfl

/-- **Continuous embedding `H¹(T_L) ↪ C(T_L)`** (F04 bracket norm): operator norm `≤ c_L`. -/
def sobolevEmbedding : WField L (f04W L 1) →L[ℂ] C(AddCircle L, ℂ) :=
  (sobolevEmbeddingₗ (L := L)).mkContinuous (cL L) (fun u =>
    (ContinuousMap.norm_le _ (mul_nonneg (cL_nonneg L) (norm_nonneg u))).2
      (fun x => norm_sobolevSeries_apply_le u x))

theorem sobolevEmbedding_apply (u : WField L (f04W L 1)) :
    sobolevEmbedding u = sobolevSeries u := rfl

theorem norm_sobolevEmbedding_le (u : WField L (f04W L 1)) :
    ‖sobolevEmbedding u‖ ≤ cL L * ‖u‖ :=
  (ContinuousMap.norm_le _ (mul_nonneg (cL_nonneg L) (norm_nonneg u))).2
    (fun x => norm_sobolevSeries_apply_le u x)

/-- The continuous function is a representative of the `L²` class: `u = Σ û(n)e_n` a.e. -/
theorem sobolevEmbedding_ae (u : WField L (f04W L 1)) :
    (u.val : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))] ⇑(sobolevEmbedding u) := by
  have hco : coeff L (u.val : AddCircle L → ℂ) = fun n => fourierL2 L u.val n :=
    funext fun n => (fourierL2_apply L u.val n).symm
  have h1 : Mem04 L 1 (coeff L (u.val : AddCircle L → ℂ)) := by
    rw [hco]; exact u.summable
  have := ae_eq_seriesRep (Lp.memLp u.val) h1
  rw [hco] at this
  exact this

end Embedding

end QuantumNLS.Sobolev
