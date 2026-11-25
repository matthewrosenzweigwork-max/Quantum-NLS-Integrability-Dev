import QuantumNLS.Ext025ADecay

/-!
# EXT-025 layer A: contract theorem for FIN-EXT025-ROOT-02

Exact source text (FINAL_EXTERNAL_THEOREM_INSTANCES.json, sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782, instance
`FIN-EXT025-ROOT-02`, "Riemann-Lebesgue with uniformity on compact L1 families"):

* Hypotheses: "An integrable scalar density on the real line, extended by zero if
  originally compactly supported. For uniformity, the family of densities is compact in
  the L1 norm."
* Conclusion: "Its oscillatory integral tends to zero at large real frequency. The
  convergence is uniform on a compact L1 family."
* Normalization: "This gives real-frequency decay, uniform only on the exhibited compact
  profile/image class. It does not give uniform decay on an arbitrary bounded L1 ball."

Lean reading.  The density is an integrable `f : ℝ → ℂ` (for `ℂ`-valued scalar density), and
the oscillatory integral is `ω ↦ ∫ exp(-i c ω x) f(x) dx` for any fixed real `c ≠ 0`
(`c = 1` is the unnormalized integral of the report, `c = -1` the opposite sign, `c = 1/(2π)`
etc.), with the frequency tending to `±∞` (the filter `cocompact ℝ`).  "Extended by zero"
is `Set.indicator`: for a measurable set `s` and `f` integrable on `s` the integral over `s`
also tends to zero.  Uniformity: for every `L¹`-compact set `K` of classes in
`Lp ℂ 1 volume`, the convergence is uniform over `K` (`TendstoUniformly` along
`cocompact ℝ`).  The uniform clause is for a family compact in the `L¹` norm and nothing
larger (a bounded set would be false, as the normalization sentence says).
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology

namespace QuantumNLS.Ext025L

open QuantumNLS.Ext025A in
/-- FIN-EXT025-ROOT-02 as a Lean theorem. -/
theorem contract_ROOT02 :
    -- pointwise decay for one integrable density, every nonzero frequency scaling
    (∀ (f : ℝ → ℂ), Integrable f (volume : Measure ℝ) → ∀ c : ℝ, c ≠ 0 →
      Tendsto (fun ω : ℝ => ∫ x : ℝ, Complex.exp (-Complex.I * ((c * ω * x : ℝ) : ℂ)) * f x)
        (cocompact ℝ) (𝓝 0)) ∧
    -- extension by zero: integrable on a measurable set, integral over the set
    (∀ (s : Set ℝ) (_hs : MeasurableSet s) (f : ℝ → ℂ), IntegrableOn f s (volume : Measure ℝ) →
      ∀ c : ℝ, c ≠ 0 →
      Tendsto (fun ω : ℝ => ∫ x in s, Complex.exp (-Complex.I * ((c * ω * x : ℝ) : ℂ)) * f x)
        (cocompact ℝ) (𝓝 0)) ∧
    -- uniform decay on every L¹-compact family
    (∀ K : Set (Lp ℂ 1 (volume : Measure ℝ)), IsCompact K → ∀ c : ℝ, c ≠ 0 →
      TendstoUniformly
        (fun ω : ℝ => fun f : K => ∫ x : ℝ,
          Complex.exp (-Complex.I * ((c * ω * x : ℝ) : ℂ)) * (f.1 : ℝ → ℂ) x)
        (fun _ => 0) (cocompact ℝ)) := by
  have hscale : ∀ c : ℝ, c ≠ 0 → Tendsto (fun ω : ℝ => c * ω) (cocompact ℝ) (cocompact ℝ) :=
    fun c hc => Filter.tendsto_cocompact_mul_left₀ hc
  have key : ∀ (f : Lp ℂ 1 (volume : Measure ℝ)) (c ω : ℝ),
      (∫ x : ℝ, Complex.exp (-Complex.I * ((c * ω * x : ℝ) : ℂ)) * (f : ℝ → ℂ) x) =
        oscillatoryIntegral f (c * ω) := by
    intro f c ω
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro f hf c hc
    have h := («FIN-EXT025-ROOT-02».1 (hf.toL1 f)).comp (hscale c hc)
    refine h.congr' (Eventually.of_forall fun ω => ?_)
    simp only [Function.comp_apply, oscillatoryIntegral]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toL1] with x hx
    rw [hx]
  · intro s hs f hf c hc
    have hi : Integrable (s.indicator f) (volume : Measure ℝ) :=
      (integrable_indicator_iff hs).mpr hf
    have h := («FIN-EXT025-ROOT-02».1 (hi.toL1 (s.indicator f))).comp (hscale c hc)
    refine h.congr' (Eventually.of_forall fun ω => ?_)
    simp only [Function.comp_apply, oscillatoryIntegral]
    rw [← integral_indicator hs]
    refine integral_congr_ae ?_
    filter_upwards [hi.coeFn_toL1] with x hx
    rw [hx]
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]
    · simp only [Set.indicator_of_notMem hxs, mul_zero]
  · intro K hK c hc u hu
    have hu' := («FIN-EXT025-ROOT-02».2 K hK) u hu
    exact (hscale c hc).eventually hu' |>.mono fun ω hω f => by
      have := hω f
      simpa only [Function.comp_apply, oscillatoryIntegral] using this

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_ROOT02
