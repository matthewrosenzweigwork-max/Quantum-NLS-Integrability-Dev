import Mathlib
import QuantumNLS.BulkResponseRiesz

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (G), part 2: bounded coefficients against weakly convergent functions

Source (F03.tex, weak lower bound): for a fixed `ψ ∈ L²((0,1)²)` the adjoint `(A*_{m,N} ψ)(t) = ∫ a_{m,N}(t,s)(ψ(t,s) - ψ(s,t)) ds`
converges strongly in `L²(0,1)` ("Cauchy-Schwarz in `s` and dominated convergence"), hence `A_{m,N} v_N ⇀ A_m v`.

Formalized here in the form actually used: for measurable `K_n → K_0` a.e., `|K_n| ≤ C`, `‖v_n‖ ≤ M`, `v_n ⇀ v_0` weakly in `L²(0,1)` and measurable `ψ ∈ L²((0,1)²)`:
`∬ K_n(t,s) v_n(t) ψ(t,s) → ∬ K_0(t,s) v_0(t) ψ(t,s)`.
The `s`-integral `G_n(t) = ∫ K_n(t,s) ψ(t,s) ds` converges to `G_0` in `L²(0,1)` (`tendsto_GK_L2`); the pairing then converges as weak × strong.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QuantumNLS.GLowerWeak

open QuantumNLS.BulkResponseRiesz (mu2 inner_eq_integral)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.BulkResponseForm (L2Unit)

/-- Jensen on a probability space: `(∫ f)² ≤ ∫ f²`. -/
theorem sq_integral_le {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {f : α → ℝ} (hf : Integrable f ν) (hf2 : Integrable (fun x => f x ^ 2) ν) :
    (∫ x, f x ∂ν) ^ 2 ≤ ∫ x, f x ^ 2 ∂ν :=
  ConvexOn.map_integral_le (Even.convexOn_pow even_two) (continuous_pow 2).continuousOn
    isClosed_univ (Eventually.of_forall fun _ => mem_univ _) hf hf2

/-- `G_K(t) = ∫ K(t,s) ψ(t,s) ds`. -/
def GK (K ψ : ℝ × ℝ → ℝ) (t : ℝ) : ℝ := ∫ s, K (t, s) * ψ (t, s) ∂uI

/-- `Ψ(t) = ∫ ψ(t,s)² ds`. -/
def Psi (ψ : ℝ × ℝ → ℝ) (t : ℝ) : ℝ := ∫ s, ψ (t, s) ^ 2 ∂uI

section
variable {ψ : ℝ × ℝ → ℝ} (hψm : Measurable ψ) (hψ2 : MemLp ψ 2 mu2)
include hψm hψ2

theorem integrable_psi : Integrable (Psi ψ) uI := hψ2.integrable_sq.integral_prod_left

theorem GK_sq_le {K : ℝ × ℝ → ℝ} (hKm : Measurable K) {C : ℝ} (hKb : ∀ p, |K p| ≤ C) :
    ∀ᵐ t ∂uI, (GK K ψ t) ^ 2 ≤ C ^ 2 * Psi ψ t := by
  have hψ1 : Integrable ψ mu2 := hψ2.integrable (by norm_num)
  have hae1 : ∀ᵐ t ∂uI, Integrable (fun s => ψ (t, s)) uI := hψ1.prod_right_ae
  have hae2 : ∀ᵐ t ∂uI, Integrable (fun s => ψ (t, s) ^ 2) uI := hψ2.integrable_sq.prod_right_ae
  filter_upwards [hae1, hae2] with t h1 h2
  have hfm : Measurable fun s => K (t, s) * ψ (t, s) :=
    (hKm.comp measurable_prodMk_left).mul (hψm.comp measurable_prodMk_left)
  have hfi : Integrable (fun s => K (t, s) * ψ (t, s)) uI := by
    refine Integrable.mono' (h1.norm.const_mul C) hfm.aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hKb _) (norm_nonneg _)
  have hpt : ∀ s, (K (t, s) * ψ (t, s)) ^ 2 ≤ C ^ 2 * ψ (t, s) ^ 2 := fun s => by
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have := pow_le_pow_left₀ (abs_nonneg _) (hKb (t, s)) 2
    rwa [sq_abs] at this
  have hfi2 : Integrable (fun s => (K (t, s) * ψ (t, s)) ^ 2) uI := by
    refine Integrable.mono' (h2.const_mul (C ^ 2)) (hfm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt s
  calc (GK K ψ t) ^ 2 ≤ ∫ s, (K (t, s) * ψ (t, s)) ^ 2 ∂uI := sq_integral_le hfi hfi2
    _ ≤ ∫ s, C ^ 2 * ψ (t, s) ^ 2 ∂uI := integral_mono hfi2 (h2.const_mul _) hpt
    _ = C ^ 2 * Psi ψ t := by rw [integral_const_mul]; rfl

theorem stronglyMeasurable_GK {K : ℝ × ℝ → ℝ} (hKm : Measurable K) :
    StronglyMeasurable (GK K ψ) :=
  (hKm.mul hψm).stronglyMeasurable.integral_prod_right'

theorem memLp_GK {K : ℝ × ℝ → ℝ} (hKm : Measurable K) {C : ℝ} (hKb : ∀ p, |K p| ≤ C) :
    MemLp (GK K ψ) 2 uI := by
  have hm : AEStronglyMeasurable (GK K ψ) uI := (stronglyMeasurable_GK hψm hψ2 hKm).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  refine Integrable.mono' ((integrable_psi hψm hψ2).const_mul (C ^ 2)) (hm.pow 2) ?_
  filter_upwards [GK_sq_le hψm hψ2 hKm hKb] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact ht

theorem tendsto_GK_ae {K : ℕ → ℝ × ℝ → ℝ} {K0 : ℝ × ℝ → ℝ} {C : ℝ}
    (hKm : ∀ n, Measurable (K n)) (hKb : ∀ n p, |K n p| ≤ C)
    (hKl : ∀ᵐ p ∂mu2, Tendsto (fun n => K n p) atTop (𝓝 (K0 p))) :
    ∀ᵐ t ∂uI, Tendsto (fun n => GK (K n) ψ t) atTop (𝓝 (GK K0 ψ t)) := by
  have hψ1 : Integrable ψ mu2 := hψ2.integrable (by norm_num)
  have hae1 : ∀ᵐ t ∂uI, Integrable (fun s => ψ (t, s)) uI := hψ1.prod_right_ae
  filter_upwards [hae1, Measure.ae_ae_of_ae_prod hKl] with t h1 hl
  refine tendsto_integral_of_dominated_convergence (fun s => C * ‖ψ (t, s)‖) (fun n => ?_)
    (h1.norm.const_mul C) (fun n => Eventually.of_forall fun s => ?_) ?_
  · exact ((hKm n).comp measurable_prodMk_left |>.mul (hψm.comp measurable_prodMk_left)).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hKb n _) (norm_nonneg _)
  · filter_upwards [hl] with s hs
    exact hs.mul_const _

/-- `G_n → G_0` strongly in `L²(0,1)`: `∫ (G_n - G_0)² → 0`. -/
theorem tendsto_GK_L2 {K : ℕ → ℝ × ℝ → ℝ} {K0 : ℝ × ℝ → ℝ} {C : ℝ}
    (hKm : ∀ n, Measurable (K n)) (hK0m : Measurable K0)
    (hKb : ∀ n p, |K n p| ≤ C) (hK0b : ∀ p, |K0 p| ≤ C)
    (hKl : ∀ᵐ p ∂mu2, Tendsto (fun n => K n p) atTop (𝓝 (K0 p))) :
    Tendsto (fun n => ∫ t, (GK (K n) ψ t - GK K0 ψ t) ^ 2 ∂uI) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (μ := uI)
    (F := fun n t => (GK (K n) ψ t - GK K0 ψ t) ^ 2) (f := fun _ => (0 : ℝ))
    (fun t => 4 * C ^ 2 * Psi ψ t) (fun n => ?_)
    (((integrable_psi hψm hψ2).const_mul (4 * C ^ 2))) (fun n => ?_) ?_
  · simpa using h
  · exact (((stronglyMeasurable_GK hψm hψ2 (hKm n)).aestronglyMeasurable).sub
      ((stronglyMeasurable_GK hψm hψ2 hK0m).aestronglyMeasurable)).pow 2
  · filter_upwards [GK_sq_le hψm hψ2 (hKm n) (hKb n), GK_sq_le hψm hψ2 hK0m hK0b] with t h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (GK (K n) ψ t + GK K0 ψ t)]
  · filter_upwards [tendsto_GK_ae hψm hψ2 hKm hKb hKl] with t ht
    have := (ht.sub_const (GK K0 ψ t)).pow 2
    simpa using this

theorem pair_eq {K : ℝ × ℝ → ℝ} (hKm : Measurable K) {C : ℝ} (hKb : ∀ p, |K p| ≤ C) (f : L2Unit) :
    ∫ p, K p * (f : ℝ → ℝ) p.1 * ψ p ∂mu2 = ∫ t, (f : ℝ → ℝ) t * GK K ψ t ∂uI := by
  have h1 : MemLp (fun p : ℝ × ℝ => (f : ℝ → ℝ) p.1) 2 mu2 := (Lp.memLp f).comp_fst uI
  have h2 := h1.integrable_mul hψ2
  have hint : Integrable (fun p => K p * (f : ℝ → ℝ) p.1 * ψ p) mu2 := by
    refine Integrable.mono' (h2.norm.const_mul C)
      ((hKm.aestronglyMeasurable.mul h1.aestronglyMeasurable).mul hψm.aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [mul_assoc, norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa using hKb p) (norm_nonneg _)
  rw [integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show ∫ s, K (t, s) * (f : ℝ → ℝ) t * ψ (t, s) ∂uI = (f : ℝ → ℝ) t * GK K ψ t
  unfold GK
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun s => by ring)

/-- Bounded coefficients against weakly convergent functions. -/
theorem weak_pair_tendsto {K : ℕ → ℝ × ℝ → ℝ} {K0 : ℝ × ℝ → ℝ} {C : ℝ}
    (hKm : ∀ n, Measurable (K n)) (hK0m : Measurable K0)
    (hKb : ∀ n p, |K n p| ≤ C) (hK0b : ∀ p, |K0 p| ≤ C)
    (hKl : ∀ᵐ p ∂mu2, Tendsto (fun n => K n p) atTop (𝓝 (K0 p)))
    {v : ℕ → L2Unit} {v0 : L2Unit} {M : ℝ} (hM : ∀ n, ‖v n‖ ≤ M)
    (hw : ∀ φ : L2Unit, Tendsto (fun n => inner ℝ (v n) φ) atTop (𝓝 (inner ℝ v0 φ))) :
    Tendsto (fun n => ∫ p, K n p * (v n : ℝ → ℝ) p.1 * ψ p ∂mu2) atTop
      (𝓝 (∫ p, K0 p * (v0 : ℝ → ℝ) p.1 * ψ p ∂mu2)) := by
  have hGm : ∀ n, MemLp (GK (K n) ψ) 2 uI := fun n => memLp_GK hψm hψ2 (hKm n) (hKb n)
  have hG0m : MemLp (GK K0 ψ) 2 uI := memLp_GK hψm hψ2 hK0m hK0b
  let Gn : ℕ → L2Unit := fun n => (hGm n).toLp _
  let G0 : L2Unit := hG0m.toLp _
  have hsq : ∀ n, ‖Gn n - G0‖ ^ 2 = ∫ t, (GK (K n) ψ t - GK K0 ψ t) ^ 2 ∂uI := fun n => by
    rw [← real_inner_self_eq_norm_sq, inner_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (Gn n) G0, (hGm n).coeFn_toLp, hG0m.coeFn_toLp] with t a b c
    rw [a, Pi.sub_apply]
    have b' : (Gn n : ℝ → ℝ) t = GK (K n) ψ t := b
    have c' : (G0 : ℝ → ℝ) t = GK K0 ψ t := c
    rw [b', c']; ring
  have h0 : Tendsto (fun n => ‖Gn n - G0‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using tendsto_GK_L2 hψm hψ2 hKm hK0m hKb hK0b hKl
  have hL2 : Tendsto (fun n => ‖Gn n - G0‖) atTop (𝓝 0) := by
    have := h0.sqrt
    rw [Real.sqrt_zero] at this
    exact this.congr fun n => Real.sqrt_sq (norm_nonneg _)
  have herr : Tendsto (fun n => inner ℝ (v n) (Gn n - G0)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _))) (by simpa using hL2.const_mul M)
  have hinner : Tendsto (fun n => inner ℝ (v n) (Gn n)) atTop (𝓝 (inner ℝ v0 G0)) := by
    have := (hw G0).add herr
    rw [add_zero] at this
    refine this.congr fun n => ?_
    rw [← inner_add_right]; congr 1; abel
  have e1 : ∀ n, ∫ p, K n p * (v n : ℝ → ℝ) p.1 * ψ p ∂mu2 = inner ℝ (v n) (Gn n) := fun n => by
    rw [pair_eq hψm hψ2 (hKm n) (hKb n), inner_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [(hGm n).coeFn_toLp] with t h
    have h' : (Gn n : ℝ → ℝ) t = GK (K n) ψ t := h
    rw [h']
  have e2 : ∫ p, K0 p * (v0 : ℝ → ℝ) p.1 * ψ p ∂mu2 = inner ℝ v0 G0 := by
    rw [pair_eq hψm hψ2 hK0m hK0b, inner_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hG0m.coeFn_toLp] with t h
    have h' : (G0 : ℝ → ℝ) t = GK K0 ψ t := h
    rw [h']
  simp only [e1, e2]
  exact hinner

end

end QuantumNLS.GLowerWeak

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.GLowerWeak.tendsto_GK_L2
#print axioms QuantumNLS.GLowerWeak.weak_pair_tendsto
