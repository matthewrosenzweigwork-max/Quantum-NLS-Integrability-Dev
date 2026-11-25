import Mathlib
import QuantumNLS.SmoothRecovery
import QuantumNLS.StepIntegrals

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (H), part 2: `𝒥_N(h(Q_N)) → 𝒥(h(Q))` and the step-function bridge

Source (F03.tex, `CC:F03:smooth-recovery`): `ℰ_N(h(Q_N)) → ℰ(h(Q))`, `𝒥_N(h(Q_N)) → 𝒥(h(Q))`, using `h(Q_N) → h(Q)` strongly in `L²` (`‖h(Q_N) − h(Q)‖ ≤ Lip(h)‖Q_N − Q‖`).

* `compL2`: the `L²(0,1)` element of `h ∘ f` for bounded measurable `h`;
* `smooth_J_tendsto`: the functional values `(L/2)‖h(Q_n)‖² + (κ/2)ℰ_n(h(Q_n)) − ⟨Q_n, h(Q_n)⟩` converge to those of `h(Q)`;
* `JN_comp`: for the vector `(h(q_i))_i` the finite energy `FiniteResponse.JN` is the functional of the function `h(Q_N)` (`Q_N` the step function of `q`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace QuantumNLS.SmoothJ

open QuantumNLS.BulkResponseRiesz (mu2 ae_fst ae_snd inner_eq_integral)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.BulkResponseForm (L2Unit formEnergy quot)
open QuantumNLS.GLowerBound (ENint)
open QuantumNLS.StepIntegrals (idx stepF stepL2 stepL2_ae measurable_stepF JN_step)
open QuantumNLS.FiniteResponse (JN)
open QuantumNLS.SmoothRecovery (pt_bound smooth_energy_tendsto)

theorem ENint_congr_ae {c : ℝ} {Qn : ℝ → ℝ} {w w' : ℝ → ℝ} (h : w =ᵐ[uI] w') :
    ENint c Qn w = ENint c Qn w' := by
  unfold ENint
  refine lintegral_congr_ae ?_
  filter_upwards [ae_fst h, ae_snd h] with p h1 h2
  rw [h1, h2]

/-- The `L²(0,1)` element of `h ∘ f` for bounded measurable `h`, `f`. -/
def compL2 {h : ℝ → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) {f : ℝ → ℝ}
    (hf : Measurable f) : L2Unit :=
  (MemLp.of_bound (hm.comp hf).aestronglyMeasurable B
    (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hB (f t)) : MemLp (fun t => h (f t)) 2 uI).toLp _

theorem compL2_ae {h : ℝ → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) {f : ℝ → ℝ}
    (hf : Measurable f) : (compL2 hm hB hf : ℝ → ℝ) =ᵐ[uI] fun t => h (f t) :=
  MemLp.coeFn_toLp _

theorem norm_compL2_sub_le {K : ℝ≥0} {h : ℝ → ℝ} (hh : LipschitzWith K h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) {F G : L2Unit}
    (hF : (F : ℝ → ℝ) =ᵐ[uI] f) (hG : (G : ℝ → ℝ) =ᵐ[uI] g) :
    ‖compL2 hh.continuous.measurable hB hf - compL2 hh.continuous.measurable hB hg‖ ≤ (K : ℝ) * ‖F - G‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [Lp.coeFn_sub (compL2 hh.continuous.measurable hB hf) (compL2 hh.continuous.measurable hB hg),
    Lp.coeFn_sub F G, compL2_ae hh.continuous.measurable hB hf, compL2_ae hh.continuous.measurable hB hg,
    hF, hG] with t h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, h6, Real.norm_eq_abs, Real.norm_eq_abs]
  have := hh.dist_le_mul (f t) (g t)
  simpa [Real.dist_eq] using this

section
variable {Q : ℝ → ℝ} {Qn : ℕ → ℝ → ℝ} {cn : ℕ → ℝ} {Qe : ℕ → L2Unit} {Q0 : L2Unit}

theorem formEnergy_comp_ne_top {K : ℝ≥0} {h : ℝ → ℝ} (hh : LipschitzWith K h) (Q : ℝ → ℝ) :
    formEnergy Q (fun t => h (Q t)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := (K : ℝ) ^ 2)) ?_
  unfold formEnergy
  calc ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((quot Q (fun t => h (Q t)) p.1 p.2) ^ 2) ∂mu2
      ≤ ∫⁻ _ : ℝ × ℝ, ENNReal.ofReal ((K : ℝ) ^ 2) ∂mu2 := by
        refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal ?_
        have := pt_bound hh 0 (Q p.1) (Q p.2)
        simp only [quot, div_pow]
        simpa using this
    _ = ENNReal.ofReal ((K : ℝ) ^ 2) := by simp

theorem smooth_J_tendsto {K : ℝ≥0} {h : ℝ → ℝ} (hh : LipschitzWith K h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B)
    (hQm : Measurable Q) (hQnm : ∀ n, Measurable (Qn n)) (hc : Tendsto cn atTop (𝓝 0))
    (hna : ∀ᵐ p ∂mu2, Q p.1 ≠ Q p.2)
    (hQ : Tendsto (fun n => ‖Qe n - Q0‖) atTop (𝓝 0))
    (hQe : ∀ n, (Qe n : ℝ → ℝ) =ᵐ[uI] Qn n) (hQ0 : (Q0 : ℝ → ℝ) =ᵐ[uI] Q) (L κ : ℝ) :
    Tendsto (fun n => (L / 2) * ‖compL2 hh.continuous.measurable hB (hQnm n)‖ ^ 2 +
        (κ / 2) * (ENint (cn n) (Qn n) (fun t => h (Qn n t))).toReal -
        inner ℝ (Qe n) (compL2 hh.continuous.measurable hB (hQnm n))) atTop
      (𝓝 ((L / 2) * ‖compL2 hh.continuous.measurable hB hQm‖ ^ 2 +
        (κ / 2) * (formEnergy Q (fun t => h (Q t))).toReal -
        inner ℝ Q0 (compL2 hh.continuous.measurable hB hQm))) := by
  have hconv : Tendsto (fun n => compL2 hh.continuous.measurable hB (hQnm n)) atTop
      (𝓝 (compL2 hh.continuous.measurable hB hQm)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => norm_compL2_sub_le hh hB (hQnm n) hQm (hQe n) hQ0) ?_
    simpa using hQ.const_mul (K : ℝ)
  have hQs : Tendsto Qe atTop (𝓝 Q0) := tendsto_iff_norm_sub_tendsto_zero.2 hQ
  have hE := (ENNReal.tendsto_toReal (formEnergy_comp_ne_top hh Q)).comp
    (smooth_energy_tendsto hh hQm hQnm hc hna hQ hQe hQ0)
  exact (((hconv.norm.pow 2).const_mul (L / 2)).add (hE.const_mul (κ / 2))).sub (hQs.inner hconv)

end

/-! ### The step-function bridge -/

theorem stepL2_comp {N : ℕ} (hN : 0 < N) {h : ℝ → ℝ} (hm : Measurable h) {B : ℝ}
    (hB : ∀ x, |h x| ≤ B) (q : Fin N → ℝ) :
    stepL2 (fun i => h (q i)) = compL2 hm hB (measurable_stepF q) := by
  apply Lp.ext
  filter_upwards [stepL2_ae (fun i => h (q i)), compL2_ae hm hB (measurable_stepF q),
    ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : idx N t < N := by
    unfold idx
    exact (Nat.floor_lt (by nlinarith [h3.1])).2 (by nlinarith [h3.2])
  rw [h1, h2]
  simp [stepF, QuantumNLS.StepIntegrals.ext, hlt]

theorem JN_comp {N : ℕ} (hN : 0 < N) {h : ℝ → ℝ} (hm : Measurable h) {B : ℝ} (hB : ∀ x, |h x| ≤ B)
    (L κ : ℝ) (q : Fin N → ℝ) :
    JN L κ N q (fun i => h (q i)) =
      (L / 2) * ‖compL2 hm hB (measurable_stepF q)‖ ^ 2 +
        (κ / 2) * (ENint (κ / N) (stepF N q) (fun t => h (stepF N q t))).toReal -
        inner ℝ (stepL2 q) (compL2 hm hB (measurable_stepF q)) := by
  rw [JN_step hN, stepL2_comp hN hm hB q]
  have : ENint (κ / N) (stepF N q) (stepF N (fun i => h (q i))) =
      ENint (κ / N) (stepF N q) (fun t => h (stepF N q t)) := by
    refine ENint_congr_ae ?_
    have h2 := stepL2_comp hN hm hB q
    filter_upwards [stepL2_ae (fun i => h (q i)), compL2_ae hm hB (measurable_stepF q)] with t h1 h3
    rw [← h1, h2, h3]
  rw [this]

end QuantumNLS.SmoothJ

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.SmoothJ.smooth_J_tendsto
#print axioms QuantumNLS.SmoothJ.JN_comp
