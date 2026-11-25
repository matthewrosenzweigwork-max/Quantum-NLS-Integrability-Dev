import QuantumNLS.Ext025AAnalysis

/-! GP-03 inverse invariance on chosen real forms. The conjugations below
are actual continuous maps fixing the base points. Their local compatibility
with the original map is an explicit hypothesis; compatibility of the inverse
is proved by local uniqueness. No analyticity is inferred from holomorphy. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.Ext025A5
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Uniqueness forces the local inverse to intertwine conjugations. -/
theorem inverse_equivariant {f : E → F} {a : E} (i : E ≃L[𝕜] F)
    (hf : HasStrictFDerivAt f i.toContinuousLinearMap a)
    (σ : E → E) (τ : F → F) (hσ : ContinuousAt σ a) (hσa : σ a = a)
    (he : ∀ᶠ x in 𝓝 a, f (σ x) = τ (f x)) :
    ∀ᶠ y in 𝓝 (f a),
      σ (hf.localInverse f i a y) = hf.localInverse f i a (τ y) := by
  let g := hf.localInverse f i a
  have hg : Tendsto g (𝓝 (f a)) (𝓝 a) := hf.localInverse_tendsto
  have hs : Tendsto (fun y => σ (g y)) (𝓝 (f a)) (𝓝 a) := by
    have h := hσ.tendsto.comp hg
    rw [hσa] at h
    exact h
  filter_upwards [hs.eventually hf.eventually_left_inverse,
    hg.eventually he, hf.eventually_right_inverse] with y hl heq hr
  change g (f (σ (g y))) = σ (g y) at hl
  rw [heq, hr] at hl
  exact hl.symm

/-- One smaller pair of balls works for existence, uniqueness, and real-form
invariance at once. A fixed target point has a unique fixed source preimage
in the selected source ball. The radii are chosen, not postulated. -/
theorem inverse_fixed_balls {f : E → F} {a : E} (i : E ≃L[𝕜] F)
    (hf : HasStrictFDerivAt f i.toContinuousLinearMap a)
    (σ : E → E) (τ : F → F) (hσ : ContinuousAt σ a) (hσa : σ a = a)
    (he : ∀ᶠ x in 𝓝 a, f (σ x) = τ (f x)) :
    ∃ (g : F → E) (r s : ℝ), 0 < r ∧ 0 < s ∧
      g = hf.localInverse f i a ∧
      HasStrictFDerivAt g i.symm.toContinuousLinearMap (f a) ∧
      (∀ x ∈ ball a r, g (f x) = x) ∧
      (∀ y ∈ ball (f a) s, g y ∈ ball a r ∧ f (g y) = y ∧
        (τ y = y → σ (g y) = g y) ∧
        ∀ x ∈ ball a r, f x = y → x = g y) := by
  let g := hf.localInverse f i a
  obtain ⟨r, hr, hl⟩ := Metric.eventually_nhds_iff.mp hf.eventually_left_inverse
  have hm : ∀ᶠ y in 𝓝 (f a), g y ∈ ball a r :=
    hf.localInverse_tendsto.eventually (ball_mem_nhds a hr)
  have heq := inverse_equivariant i hf σ τ hσ hσa he
  have hall : ∀ᶠ y in 𝓝 (f a), g y ∈ ball a r ∧ f (g y) = y ∧
      (τ y = y → σ (g y) = g y) := by
    filter_upwards [hm, hf.eventually_right_inverse, heq] with y hmy hry hey
    exact ⟨hmy, hry, fun hy => by simpa [hy] using hey⟩
  obtain ⟨s, hs, hall⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨g, r, s, hr, hs, rfl, hf.to_localInverse, ?_, ?_⟩
  · intro x hx
    exact hl (mem_ball.mp hx)
  · intro y hy
    obtain ⟨hmy, hry, hey⟩ := hall (mem_ball.mp hy)
    refine ⟨hmy, hry, hey, ?_⟩
    intro x hx hxy
    have hxg := hl (mem_ball.mp hx)
    change g (f x) = x at hxg
    simpa [hxy] using hxg.symm
end QuantumNLS.Ext025A5

#print axioms QuantumNLS.Ext025A5.inverse_equivariant
#print axioms QuantumNLS.Ext025A5.inverse_fixed_balls
