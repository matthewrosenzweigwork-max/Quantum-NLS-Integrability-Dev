import Mathlib

/-! # Trunk C prep (generic), K1 zero-face division: the two generic halves

Author: Claude Opus 5.5 (trunk C preparation, coordinator K1 instruction 2026-11-12).
Not self-reviewed, not accepted.  Namespace `NlsGge.ALLS.TransCPrep` (preparatory, `prep_` names).

K1 route (coordinator): the flow derivative is the evaluation at `t` of the derivative of the
`C¹` map `F : E → C(Icc (-T) T, G)` of `l2Flow_contDiff` (no `C(K)`-valued composition is
needed), and `A_n(t, x) = ∫₀¹ D g_t(x − x_n e_n + s ‖x_n‖ e_n)[e_n] ds` is jointly continuous.

English interpretation of the declarations.
* `prep_flowSection_deriv (T) (F : E → C(Icc (-T) T, G)) (hF : ContDiff ℝ 1 F)`: for real normed
  `E, G` and a real-`C¹` map `F` into the continuous maps on `[-T, T]`: (i) for every `t ∈ [-T, T]`
  and every `x`, the time-`t` section `y ↦ F y t` has Fréchet derivative
  `evalCLM t ∘ fderiv F x` at `x`; (ii) `(t, x, v) ↦ (fderiv F x v)(t)` is jointly continuous on
  `[-T, T] × E × E`.
* `prep_zeroFace_integral (D g e β ρ hD hβ hρ hderiv)`: for a topological parameter space `P`,
  real normed `V`, complete real normed `W`, maps `g : P → V → W`, `D : P → V → W`, a direction
  `e : V`, continuous `β : P → V`, `ρ : P → ℝ`, with `(q, y) ↦ D q y` jointly continuous and
  `D q y` the derivative of `r ↦ g q (y + r • e)` at every `r` (`hderiv`): the map
  `A q = ∫₀¹ D q (β q + (s ρ q) • e) ds` is continuous on `P`, and
  `ρ q • A q = g q (β q + ρ q • e) − g q (β q)` for every `q`.
  (For K1: `P = [0,1] × ℓ²`, `β x = x − x_n e_n`, `ρ x = ‖x_n‖`; the vanishing of `g_t` on the
  zero face `x_n = 0`, needed to read this as `A · x_n = g_t(x)`, is NOT part of this lemma.)
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.ALLS.TransCPrep

open Filter Topology

/-- **K1a**: time sections of a `C¹` map into `C([-T,T], G)` and joint continuity of the
evaluated derivative. -/
theorem prep_flowSection_deriv (T : ℝ) {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (F : E → C(Set.Icc (-T) T, G)) (hF : ContDiff ℝ 1 F) :
    (∀ (t : Set.Icc (-T) T) (x : E), HasFDerivAt (fun y => F y t)
        ((ContinuousMap.evalCLM ℝ t).comp (fderiv ℝ F x)) x) ∧
      Continuous (fun q : Set.Icc (-T) T × E × E => fderiv ℝ F q.2.1 q.2.2 q.1) := by
  refine ⟨fun t x => ?_, ?_⟩
  · exact (ContinuousMap.evalCLM ℝ t).hasFDerivAt.comp x
      ((hF.differentiable one_ne_zero x).hasFDerivAt)
  · have h1 : Continuous (fun q : Set.Icc (-T) T × E × E => fderiv ℝ F q.2.1 q.2.2) :=
      ((hF.continuous_fderiv one_ne_zero).comp (continuous_fst.comp continuous_snd)).clm_apply
        (continuous_snd.comp continuous_snd)
    exact continuous_eval.comp (h1.prodMk continuous_fst)

/-- **K1b**: the zero-face integral quotient is continuous and satisfies the FTC identity. -/
theorem prep_zeroFace_integral {P V W : Type*} [TopologicalSpace P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W]
    (g D : P → V → W) (e : V) (β : P → V) (ρ : P → ℝ)
    (hD : Continuous fun q : P × V => D q.1 q.2) (hβ : Continuous β) (hρ : Continuous ρ)
    (hderiv : ∀ (q : P) (y : V) (r : ℝ),
      HasDerivAt (fun r' : ℝ => g q (y + r' • e)) (D q (y + r • e)) r) :
    Continuous (fun q => ∫ s in (0 : ℝ)..1, D q (β q + (s * ρ q) • e)) ∧
      ∀ q : P, ρ q • (∫ s in (0 : ℝ)..1, D q (β q + (s * ρ q) • e)) =
        g q (β q + ρ q • e) - g q (β q) := by
  constructor
  · apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have : Continuous (fun p : P × ℝ => (p.1, β p.1 + (p.2 * ρ p.1) • e)) :=
      continuous_fst.prodMk ((hβ.comp continuous_fst).add
        ((continuous_snd.mul (hρ.comp continuous_fst)).smul continuous_const))
    exact hD.comp this
  · intro q
    have hcont : Continuous (fun u : ℝ => D q (β q + u • e)) :=
      hD.comp (continuous_const.prodMk (continuous_const.add (continuous_id.smul continuous_const)))
    have hftc : ∫ u in (0 : ℝ)..ρ q, D q (β q + u • e) = g q (β q + ρ q • e) - g q (β q) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun r' : ℝ => g q (β q + r' • e)) (fun u _ => hderiv q (β q) u)
        (hcont.intervalIntegrable _ _)]
      simp
    by_cases h0 : ρ q = 0
    · rw [h0, zero_smul, zero_smul, add_zero, sub_self]
    · have hcv := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
        (fun u : ℝ => D q (β q + u • e)) h0
      simp only [mul_zero, mul_one] at hcv
      have hrw : (fun s : ℝ => D q (β q + (s * ρ q) • e)) =
          fun s : ℝ => D q (β q + (ρ q * s) • e) := by
        funext s; rw [mul_comm]
      rw [hrw, hcv, smul_smul, mul_inv_cancel₀ h0, one_smul, hftc]

end NlsGge.ALLS.TransCPrep
