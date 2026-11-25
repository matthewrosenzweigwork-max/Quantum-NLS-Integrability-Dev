import QuantumNLS.Ext025A5RealForms

/-! Analytic inverse in coordinates on specified invariant real forms.
The power-series hypothesis is explicit. This does not discharge the missing
arbitrary Banach-domain theorem deriving that hypothesis from holomorphy. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.Ext025A5
variable {E F ER FR : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup ER] [NormedSpace ℝ ER]
  [NormedAddCommGroup FR] [NormedSpace ℝ FR]

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F] in
/-- The canonical strictly differentiable inverse is analytic when the
original map has a convergent multilinear power series. -/
theorem analytic_canonical_inverse {f : E → F} {a : E} (i : E ≃L[ℂ] F)
    (ha : AnalyticAt ℂ f a) (hs : HasStrictFDerivAt f i.toContinuousLinearMap a) :
    AnalyticAt ℂ (hs.localInverse f i a) (f a) := by
  obtain ⟨g, hg, _, hl, _⟩ := QuantumNLS.Ext025A.gp03_analytic_inverse i ha hs.hasFDerivAt
  exact hg.congr (hs.localInverse_unique hl)

/-- Real coordinates are supplied by continuous real linear inclusion and
retraction maps. Fixed vectors are precisely the vectors represented by the
chosen real form. Analyticity, the equation, and local uniqueness of the
restricted inverse are proved on one smaller real neighbourhood. -/
theorem analytic_real_form_inverse {f : E → F} {a : E} {b : FR}
    (i : E ≃L[ℂ] F) (ha : AnalyticAt ℂ f a)
    (hd : HasFDerivAt f i.toContinuousLinearMap a)
    (σ : E → E) (τ : F → F) (hσ : ContinuousAt σ a) (hσa : σ a = a)
    (he : ∀ᶠ x in 𝓝 a, f (σ x) = τ (f x))
    (jE : ER →L[ℝ] E) (pE : E →L[ℝ] ER) (jF : FR →L[ℝ] F)
    (hb : jF b = f a) (hjF : ∀ y, τ (jF y) = jF y)
    (hform : ∀ x, σ x = x → jE (pE x) = x) :
    ∃ (gR : FR → ER) (r s : ℝ), 0 < r ∧ 0 < s ∧
      AnalyticAt ℝ gR b ∧ gR b = pE a ∧
      ∀ y ∈ ball b s, jE (gR y) ∈ ball a r ∧ f (jE (gR y)) = jF y ∧
        ∀ x ∈ ball a r, f x = jF y ↔ x = jE (gR y) := by
  have ha0 := ha
  obtain ⟨q, hq⟩ := ha
  have hs : HasStrictFDerivAt f i.toContinuousLinearMap a := by
    have h := hq.hasFDerivAt.unique hd
    exact h ▸ hq.hasStrictFDerivAt
  obtain ⟨g, r, s, hr, hspos, hgeq, _, _, hball⟩ :=
    inverse_fixed_balls i hs σ τ hσ hσa he
  have hga : AnalyticAt ℂ g (f a) := by
    rw [hgeq]
    exact analytic_canonical_inverse i ha0 hs
  let gR : FR → ER := fun y => pE (g (jF y))
  have harg : AnalyticAt ℝ g (jF b) := by
    rw [hb]
    exact hga.restrictScalars
  have hcomp : AnalyticAt ℝ (fun y : FR => g (jF y)) b :=
    harg.comp (f := jF) (jF.analyticAt b)
  have hR : AnalyticAt ℝ gR b :=
    (pE.analyticAt (g (jF b))).comp (f := fun y : FR => g (jF y)) hcomp
  have hbase : gR b = pE a := by
    simp only [gR, hb, hgeq, HasStrictFDerivAt.localInverse_apply_image]
  have hm : ∀ᶠ y in 𝓝 b, jF y ∈ ball (f a) s := by
    have h := jF.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds (jF b) hspos)
    rw [hb] at h
    exact h
  obtain ⟨t, ht, htm⟩ := Metric.eventually_nhds_iff.mp hm
  refine ⟨gR, r, t, hr, ht, hR, hbase, ?_⟩
  intro y hy
  obtain ⟨hmy, hfy, hfix, huniq⟩ := hball (jF y) (htm (mem_ball.mp hy))
  have hj : jE (gR y) = g (jF y) := hform _ (hfix (hjF y))
  rw [hj]
  refine ⟨hmy, hfy, ?_⟩
  intro x hx
  exact ⟨huniq x hx, fun h => h ▸ hfy⟩
end QuantumNLS.Ext025A5

#print axioms QuantumNLS.Ext025A5.analytic_canonical_inverse
#print axioms QuantumNLS.Ext025A5.analytic_real_form_inverse
