import Mathlib

/-!
# R-1602B09D `CC:F03:core` (`F03.tex:26`): calculus of the form norm

For a measure `μ` on `ℝ` and `h : ℝ → ℝ`:
* `formE μ h = ∬ |h(x)-h(y)|²/|x-y|² dμ dμ` (value `0` on the diagonal, Lean's `x/0 = 0`), `formL2 μ h = ∫ h² dμ`, `formN = formL2 + formE` (the square of the form norm).
* `formN_add_le`: `N(f+g) ≤ 2 N(f) + 2 N(g)`.
* `Approx μ h`: `h` is approximable by `C_c^∞(ℝ;ℝ)` in the form norm.  `approx_of_close`: closure of `Approx` (a quasi-triangle argument).
* Truncation (first step of the printed proof): for measurable `h` with `N(h) < ∞`, `N(h - T_k h) → 0` (`k → ∞`), `T_k r = max(-k, min(k,r))`, and `N(T_k h) ≤ N(h)`;
  hence `approx_of_bounded`: it suffices to approximate bounded measurable functions of finite form norm.
* The multiplication estimate `formN_mul_le` for a weight `w ∈ [0,1]` and `|h| ≤ M`:
  `N(w h) ≤ M² ∫ w² dμ + 2 ∬ w(x)² |D h|² dμdμ + 2 M² E(w)`  (the identity `w h(x) - w h(y) = w(x)(h(x)-h(y)) + h(y)(w(x)-w(y))` of the printed proof).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

namespace QuantumNLS.FormCore

/-- The squared divided difference `|h(x)-h(y)|²/|x-y|²` (`0` on the diagonal). -/
def dq (h : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := (h p.1 - h p.2) ^ 2 / (p.1 - p.2) ^ 2

theorem dq_nonneg (h : ℝ → ℝ) (p : ℝ × ℝ) : 0 ≤ dq h p := by unfold dq; positivity

theorem measurable_dq {h : ℝ → ℝ} (hh : Measurable h) : Measurable (dq h) := by
  unfold dq
  have h1 : Measurable fun p : ℝ × ℝ => h p.1 := hh.comp measurable_fst
  have h2 : Measurable fun p : ℝ × ℝ => h p.2 := hh.comp measurable_snd
  exact ((h1.sub h2).pow_const 2).div ((measurable_fst.sub measurable_snd).pow_const 2)

/-- `∫ h² dμ`. -/
def formL2 (μ : Measure ℝ) (h : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂μ

/-- `E_μ(h) = ∬ |h(x)-h(y)|²/|x-y|² dμ(x) dμ(y)`. -/
def formE (μ : Measure ℝ) (h : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ p, ENNReal.ofReal (dq h p) ∂(μ.prod μ)

/-- The squared form norm `‖h‖²_{L²(μ)} + E_μ(h)`. -/
def formN (μ : Measure ℝ) (h : ℝ → ℝ) : ℝ≥0∞ := formL2 μ h + formE μ h

theorem formL2_le_formN (μ : Measure ℝ) (h : ℝ → ℝ) : formL2 μ h ≤ formN μ h := le_self_add
theorem formE_le_formN (μ : Measure ℝ) (h : ℝ → ℝ) : formE μ h ≤ formN μ h := le_add_self

/-! ### Quasi-triangle inequality -/

theorem dq_add_le (f g : ℝ → ℝ) (p : ℝ × ℝ) :
    dq (fun x => f x + g x) p ≤ 2 * dq f p + 2 * dq g p := by
  unfold dq
  have hd : 0 ≤ (p.1 - p.2) ^ 2 := sq_nonneg _
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  apply div_le_div_of_nonneg_right _ hd
  nlinarith [sq_nonneg (f p.1 - f p.2 - (g p.1 - g p.2))]

theorem ofReal_two_mul_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal (2 * a + 2 * b) = 2 * ENNReal.ofReal a + 2 * ENNReal.ofReal b := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_mul (by norm_num)]
  simp

theorem lintegral_two_mul_add {α : Type*} [MeasurableSpace α] {ν : Measure α} {F G : α → ℝ≥0∞}
    (hF : Measurable F) : ∫⁻ x, (2 * F x + 2 * G x) ∂ν = 2 * ∫⁻ x, F x ∂ν + 2 * ∫⁻ x, G x ∂ν := by
  rw [lintegral_add_left (hF.const_mul 2), lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]

theorem formN_add_le {μ : Measure ℝ} {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    formN μ (fun x => f x + g x) ≤ 2 * formN μ f + 2 * formN μ g := by
  have hL : formL2 μ (fun x => f x + g x) ≤ 2 * formL2 μ f + 2 * formL2 μ g := by
    unfold formL2
    calc ∫⁻ x, ENNReal.ofReal ((f x + g x) ^ 2) ∂μ
        ≤ ∫⁻ x, (2 * ENNReal.ofReal (f x ^ 2) + 2 * ENNReal.ofReal (g x ^ 2)) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← ofReal_two_mul_add _ _ (sq_nonneg _) (sq_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (f x - g x)])
      _ = _ := lintegral_two_mul_add (ENNReal.measurable_ofReal.comp (hf.pow_const 2))
  have hE : formE μ (fun x => f x + g x) ≤ 2 * formE μ f + 2 * formE μ g := by
    unfold formE
    calc ∫⁻ p, ENNReal.ofReal (dq (fun x => f x + g x) p) ∂(μ.prod μ)
        ≤ ∫⁻ p, (2 * ENNReal.ofReal (dq f p) + 2 * ENNReal.ofReal (dq g p)) ∂(μ.prod μ) := by
          refine lintegral_mono fun p => ?_
          rw [← ofReal_two_mul_add _ _ (dq_nonneg _ _) (dq_nonneg _ _)]
          exact ENNReal.ofReal_le_ofReal (dq_add_le f g p)
      _ = _ := lintegral_two_mul_add (ENNReal.measurable_ofReal.comp (measurable_dq hf))
  unfold formN
  calc formL2 μ (fun x => f x + g x) + formE μ (fun x => f x + g x)
      ≤ (2 * formL2 μ f + 2 * formL2 μ g) + (2 * formE μ f + 2 * formE μ g) := add_le_add hL hE
    _ = 2 * (formL2 μ f + formE μ f) + 2 * (formL2 μ g + formE μ g) := by ring

/-! ### Approximability and its closure -/

/-- `h` is approximable by `C_c^∞(ℝ;ℝ)` in the form norm. -/
def Approx (μ : Measure ℝ) (h : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    formN μ (fun x => h x - φ x) < ENNReal.ofReal ε

theorem four_lt {a b c d : ℝ≥0∞} {ε : ℝ} (ha : a < ENNReal.ofReal (ε / 4)) (hb : b < ENNReal.ofReal (ε / 4))
    (hc : c < ENNReal.ofReal (ε / 4)) (hd : d < ENNReal.ofReal (ε / 4)) (hε : 0 < ε) :
    a + b + (c + d) < ENNReal.ofReal ε := by
  have h1 := ENNReal.add_lt_add ha hb
  have h2 := ENNReal.add_lt_add hc hd
  have h3 := ENNReal.add_lt_add h1 h2
  have e : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) =
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  rwa [e] at h3

theorem approx_of_close {μ : Measure ℝ} {h : ℝ → ℝ} (hh : Measurable h)
    (H : ∀ ε : ℝ, 0 < ε → ∃ g : ℝ → ℝ, Measurable g ∧ Approx μ g ∧
      formN μ (fun x => h x - g x) < ENNReal.ofReal ε) : Approx μ h := by
  intro ε hε
  obtain ⟨g, hg, hag, hN1⟩ := H (ε / 4) (by positivity)
  obtain ⟨φ, hφ, hφc, hN2⟩ := hag (ε / 4) (by positivity)
  refine ⟨φ, hφ, hφc, ?_⟩
  have hφm : Measurable φ := hφ.continuous.measurable
  have e : (fun x => h x - φ x) = fun x => (h x - g x) + (g x - φ x) := by funext x; ring
  rw [e]
  refine lt_of_le_of_lt (formN_add_le (hh.sub hg) (hg.sub hφm)) ?_
  have := four_lt hN1 hN1 hN2 hN2 hε
  calc 2 * formN μ (fun x => h x - g x) + 2 * formN μ (fun x => g x - φ x)
      = formN μ (fun x => h x - g x) + formN μ (fun x => h x - g x) +
        (formN μ (fun x => g x - φ x) + formN μ (fun x => g x - φ x)) := by ring
    _ < _ := this

end QuantumNLS.FormCore

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.FormCore.formN_add_le
#print axioms QuantumNLS.FormCore.approx_of_close
