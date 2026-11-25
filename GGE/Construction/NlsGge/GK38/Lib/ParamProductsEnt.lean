import NlsGge.GK38.Lib.ParamProductsCore
import NlsGge.GK38.Lib.EntireProductsParamc

/-!
# L4c, part 2a (regression): `analyticOnNhd_entProd_joint` from the generic lemma

Book Lemma C.1 (jointly analytic form) re-derived from `analyticOnNhd_symm_tprod` (the generic
parametric-product lemma): the factors `F m (z, s) = (σ_m - z)/π_m`, `σ = σ° + s`, on
`E = ℂ × ℓ²`, `U = univ`.  The two hypotheses are exactly those of L4c part 1:
the pointwise `pairMaj` bound (`pairTerm_le_maj`), the linewise majorant `2|s₀|² + 2|h̃|²` of
`Q = |s|²`, and its uniform total mass on balls (`l2Q_hline`, `l2Q_hmass`; also used by the probes).  This is a regression test of the generic statement against the landed
`analyticOnNhd_entProd_joint`; the landed theorem is *not* replaced.
-/

set_option autoImplicit false

open Filter Topology SummationFilter Metric

namespace NlsGge.GK38.Lib

noncomputable section

/-- The `m`-th factor on `ℂ × ℓ²`. -/
def entFactorJ (m : ℤ) (p : ℂ × L2Seq) : ℂ := prodFactor (sigmaOf p.2) p.1 m

theorem analyticOnNhd_entFactorJ (m : ℤ) : AnalyticOnNhd ℂ (entFactorJ m) Set.univ := by
  intro p _
  have h3 : AnalyticAt ℂ (fun p : ℂ × L2Seq => p.2 m) p :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).analyticAt _ |>.comp analyticAt_snd
  have e : entFactorJ m = fun p : ℂ × L2Seq =>
      (1 / (piN m : ℂ)) * ((m : ℂ) * (Real.pi : ℂ) + p.2 m - p.1) := by
    funext q
    simp only [entFactorJ, prodFactor, sigmaOf]
    field_simp [(Complex.ofReal_ne_zero.mpr (piN_ne_zero m))]
  rw [e]
  exact analyticAt_const.mul ((analyticAt_const.add h3).sub analyticAt_fst)

theorem pairDev_entFactorJ (y : ℂ × L2Seq) (m : ℕ) :
    pairDev (fun n => entFactorJ n y) m = pairTerm (sigmaOf y.2) y.1 m := rfl

/-! ### The `ℓ²`-density `Q (z, s) n = ‖s n‖²` (shared with the probes) -/

/-- Linewise majorant of `‖s n‖²` along `x + ζ h`, `‖ζ‖ < 1`. -/
theorem l2Q_hline (x h : ℂ × L2Seq) :
    ∃ ρ > 0, ∃ q : ℤ → ℝ, Summable q ∧ ∀ ζ : ℂ, ‖ζ‖ < ρ → ∀ n : ℤ,
      ‖(x + ζ • h).2 n‖ ^ 2 ≤ q n := by
  refine ⟨1, one_pos, fun n => 2 * ‖x.2 n‖ ^ 2 + 2 * ‖h.2 n‖ ^ 2,
    ((hasSum_sq_l2 x.2).summable.mul_left 2).add ((hasSum_sq_l2 h.2).summable.mul_left 2),
    fun ζ hζ n => ?_⟩
  simp only [Prod.snd_add, Prod.smul_snd, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  have h1 : ‖x.2 n + ζ * h.2 n‖ ≤ ‖x.2 n‖ + ‖h.2 n‖ := by
    calc ‖x.2 n + ζ * h.2 n‖ ≤ ‖x.2 n‖ + ‖ζ * h.2 n‖ := norm_add_le _ _
      _ ≤ ‖x.2 n‖ + ‖h.2 n‖ := by
        rw [norm_mul]
        have := mul_le_mul_of_nonneg_right hζ.le (norm_nonneg (h.2 n))
        linarith
  have h2 : ‖x.2 n + ζ * h.2 n‖ ^ 2 ≤ (‖x.2 n‖ + ‖h.2 n‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖x.2 n‖ - ‖h.2 n‖)]

/-- Uniform total mass of `‖s n‖²` on the unit ball around `x`. -/
theorem l2Q_hmass (x : ℂ × L2Seq) :
    ∃ r > 0, ∃ B : ℝ, ∀ y ∈ ball x r,
      Summable (fun n : ℤ => ‖y.2 n‖ ^ 2) ∧ ∑' n : ℤ, ‖y.2 n‖ ^ 2 ≤ B := by
  refine ⟨1, one_pos, (‖x‖ + 1) ^ 2, fun y hy => ⟨(hasSum_sq_l2 y.2).summable, ?_⟩⟩
  rw [(hasSum_sq_l2 y.2).tsum_eq]
  have hy' : ‖y‖ ≤ ‖x‖ + 1 := by
    have := mem_ball_iff_norm.mp hy
    calc ‖y‖ = ‖(y - x) + x‖ := by simp
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + 1 := by linarith
  have : ‖y.2‖ ≤ ‖x‖ + 1 := (norm_snd_le y).trans hy'
  gcongr

theorem norm_fst_le_of_mem_ball {x y : ℂ × L2Seq} (hy : y ∈ ball x 1) : ‖y.1‖ ≤ ‖x‖ + 1 := by
  have := mem_ball_iff_norm.mp hy
  calc ‖y.1‖ ≤ ‖y‖ := norm_fst_le y
    _ = ‖(y - x) + x‖ := by simp
    _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
    _ ≤ ‖x‖ + 1 := by linarith

/-- **Regression: book Lemma C.1 from the generic lemma** (`analyticOnNhd_symm_tprod_of_mass`,
`Q (z, s) n = ‖s n‖²`, `c = 1`, `R = ‖x‖ + 1`). -/
theorem analyticOnNhd_entProd_joint_of_generic :
    AnalyticOnNhd ℂ (fun p : ℂ × L2Seq => ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf p.2) p.1 m)
      Set.univ := by
  refine analyticOnNhd_symm_tprod_of_mass (F := entFactorJ) (Q := fun y n => ‖y.2 n‖ ^ 2)
    isOpen_univ analyticOnNhd_entFactorJ (fun y n => by positivity) ?_
    (fun x _ h => by
      obtain ⟨ρ, hρ, q, hq, h⟩ := l2Q_hline x h
      exact ⟨ρ, hρ, q, hq, fun ζ hζ _ n => h ζ hζ n⟩)
    (fun x _ => by
      obtain ⟨r, hr, B, h⟩ := l2Q_hmass x
      exact ⟨r, hr, B, fun y hy _ => h y hy⟩)
  intro x _
  refine ⟨1, one_pos, 1, ‖x‖ + 1, zero_le_one, fun y hy _ m => ?_⟩
  rw [pairDev_entFactorJ]
  have hz := norm_fst_le_of_mem_ball hy
  have hd : ∀ n, ‖prodDev (sigmaOf y.2) n‖ ^ 2 ≤ ‖y.2 n‖ ^ 2 := fun n => by rw [dev_sigmaOf]
  have := pairTerm_le_maj hz hd m
  simpa only [one_mul] using this

end

end NlsGge.GK38.Lib
