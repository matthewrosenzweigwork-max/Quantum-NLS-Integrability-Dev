import Mathlib
import QuantumNLS.GLowerBound

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (G), part 5: the lower bound for `𝒥_N`

Source (F03.tex): "Weak lower semicontinuity of the ordinary square norm, together with `Q_N → Q` strongly, therefore proves `liminf_N 𝒥_N(v_N) ≥ 𝒥(v)`."

Formal statement (`J_lower_conv`), for sequences along which the three pieces converge (the printed proof passes to a subsequence realizing the liminf; boundedness gives convergent subsequences):
`‖v_n‖² → x`, `ℰ_n(v_n) = ofReal(y_n)` with `y_n → y`, `Q_n → Q` strongly in `L²`, `v_n ⇀ v_0` with `‖v_n‖ ≤ M`.
Then `v_0` is in the form domain and `(L/2)‖v_0‖² + (κ/2) ℰ(v_0) − ⟨Q,v_0⟩ ≤ (L/2) x + (κ/2) y − lim ⟨Q_n, v_n⟩` where `lim ⟨Q_n,v_n⟩ = ⟨Q,v_0⟩`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QuantumNLS.JLower

open QuantumNLS.QuantileForm (uI)
open QuantumNLS.BulkResponseForm (L2Unit formEnergy)
open QuantumNLS.GLowerBound (ENint weak_liminf)

section
variable {v : ℕ → L2Unit} {v0 : L2Unit} {M : ℝ}

/-- Strong × weak pairing. -/
theorem inner_tendsto_of_strong {Qe : ℕ → L2Unit} {Q0 : L2Unit}
    (hQ : Tendsto (fun n => ‖Qe n - Q0‖) atTop (𝓝 0)) (hM : ∀ n, ‖v n‖ ≤ M)
    (hw : ∀ φ : L2Unit, Tendsto (fun n => inner ℝ (v n) φ) atTop (𝓝 (inner ℝ v0 φ))) :
    Tendsto (fun n => inner ℝ (Qe n) (v n)) atTop (𝓝 (inner ℝ Q0 v0)) := by
  have herr : Tendsto (fun n => inner ℝ (Qe n - Q0) (v n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _))) (by simpa using hQ.mul_const M)
  have h2 : Tendsto (fun n => inner ℝ Q0 (v n)) atTop (𝓝 (inner ℝ Q0 v0)) := by
    simpa only [real_inner_comm] using hw Q0
  have := herr.add h2
  rw [zero_add] at this
  refine this.congr fun n => ?_
  rw [inner_sub_left]; ring

/-- Weak lower semicontinuity of the squared norm along a convergent sequence of squared norms. -/
theorem norm_sq_lsc {x : ℝ} (hx : Tendsto (fun n => ‖v n‖ ^ 2) atTop (𝓝 x))
    (hw : ∀ φ : L2Unit, Tendsto (fun n => inner ℝ (v n) φ) atTop (𝓝 (inner ℝ v0 φ))) :
    ‖v0‖ ^ 2 ≤ x := by
  have hx0 : 0 ≤ x := ge_of_tendsto' hx fun n => sq_nonneg _
  have h1 : Tendsto (fun n => inner ℝ (v n) v0) atTop (𝓝 (‖v0‖ ^ 2)) := by
    simpa [real_inner_self_eq_norm_sq] using hw v0
  have h2 : Tendsto (fun n => ‖v n‖ * ‖v0‖) atTop (𝓝 (Real.sqrt x * ‖v0‖)) := by
    have := (hx.sqrt).mul_const ‖v0‖
    exact this.congr fun n => by rw [Real.sqrt_sq (norm_nonneg _)]
  have h3 : ‖v0‖ ^ 2 ≤ Real.sqrt x * ‖v0‖ :=
    le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun n => (le_abs_self _).trans (abs_real_inner_le_norm _ _))
  rcases (norm_nonneg v0).eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using hx0
  · have : ‖v0‖ ≤ Real.sqrt x := by nlinarith
    calc ‖v0‖ ^ 2 ≤ (Real.sqrt x) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = x := Real.sq_sqrt hx0

end

section
variable {Q : ℝ → ℝ} {Qn : ℕ → ℝ → ℝ} {cn : ℕ → ℝ}
  {v : ℕ → L2Unit} {v0 : L2Unit} {M : ℝ}

/-- The discrete energies converge to `y` ⇒ `ℰ(v₀) ≤ y`. -/
theorem energy_lsc_conv (hQm : Measurable Q) (hQnm : ∀ n, Measurable (Qn n))
    (hc : Tendsto cn atTop (𝓝 0))
    (hQl : ∀ᵐ t ∂uI, Tendsto (fun n => Qn n t) atTop (𝓝 (Q t)))
    (hM : ∀ n, ‖v n‖ ≤ M)
    (hw : ∀ φ : L2Unit, Tendsto (fun n => inner ℝ (v n) φ) atTop (𝓝 (inner ℝ v0 φ)))
    {y : ℕ → ℝ} {y0 : ℝ} (hy : ∀ n, ENint (cn n) (Qn n) (v n) = ENNReal.ofReal (y n))
    (hyl : Tendsto y atTop (𝓝 y0)) :
    formEnergy Q v0 ≤ ENNReal.ofReal y0 := by
  have h := weak_liminf hQm hQnm hc hQl hM hw
  have h2 : Tendsto (fun n => ENNReal.ofReal (y n)) atTop (𝓝 (ENNReal.ofReal y0)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hyl
  have h3 : liminf (fun n => ENint (cn n) (Qn n) (v n)) atTop = ENNReal.ofReal y0 := by
    simp_rw [hy]; exact h2.liminf_eq
  rwa [h3] at h

/-- **Lower bound for `𝒥_N`** along sequences with convergent pieces: the values
`𝒥_n(v_n) = (L/2)‖v_n‖² + (κ/2) y_n − ⟨Q_n, v_n⟩` converge to `(L/2)x + (κ/2)y₀ − ⟨Q,v₀⟩`, which dominates `𝒥(v₀)`. -/
theorem J_lower_conv (L κ : ℝ) (hL : 0 ≤ L) (hκ : 0 ≤ κ)
    (hQm : Measurable Q) (hQnm : ∀ n, Measurable (Qn n))
    (hc : Tendsto cn atTop (𝓝 0))
    (hQl : ∀ᵐ t ∂uI, Tendsto (fun n => Qn n t) atTop (𝓝 (Q t)))
    (hM : ∀ n, ‖v n‖ ≤ M)
    (hw : ∀ φ : L2Unit, Tendsto (fun n => inner ℝ (v n) φ) atTop (𝓝 (inner ℝ v0 φ)))
    {Qe : ℕ → L2Unit} {Q0 : L2Unit} (hQ : Tendsto (fun n => ‖Qe n - Q0‖) atTop (𝓝 0))
    {x : ℝ} (hx : Tendsto (fun n => ‖v n‖ ^ 2) atTop (𝓝 x))
    {y : ℕ → ℝ} {y0 : ℝ} (hy : ∀ n, ENint (cn n) (Qn n) (v n) = ENNReal.ofReal (y n))
    (hy0 : ∀ n, 0 ≤ y n) (hyl : Tendsto y atTop (𝓝 y0)) :
    ∃ _ : formEnergy Q v0 < ⊤,
      (L / 2) * ‖v0‖ ^ 2 + (κ / 2) * (formEnergy Q v0).toReal - inner ℝ Q0 v0 ≤
        (L / 2) * x + (κ / 2) * y0 - inner ℝ Q0 v0 ∧
      Tendsto (fun n => (L / 2) * ‖v n‖ ^ 2 + (κ / 2) * y n - inner ℝ (Qe n) (v n)) atTop
        (𝓝 ((L / 2) * x + (κ / 2) * y0 - inner ℝ Q0 v0)) := by
  have he := energy_lsc_conv hQm hQnm hc hQl hM hw hy hyl
  have hfin : formEnergy Q v0 < ⊤ := lt_of_le_of_lt he ENNReal.ofReal_lt_top
  have hy00 : 0 ≤ y0 := ge_of_tendsto' hyl hy0
  have h1 : (formEnergy Q v0).toReal ≤ y0 := ENNReal.toReal_le_of_le_ofReal hy00 he
  have h2 : ‖v0‖ ^ 2 ≤ x := norm_sq_lsc hx hw
  refine ⟨hfin, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ L / 2)
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ κ / 2)
    linarith
  · exact ((hx.const_mul (L / 2)).add (hyl.const_mul (κ / 2))).sub
      (inner_tendsto_of_strong hQ hM hw)

end

end QuantumNLS.JLower

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.JLower.inner_tendsto_of_strong
#print axioms QuantumNLS.JLower.norm_sq_lsc
#print axioms QuantumNLS.JLower.J_lower_conv
