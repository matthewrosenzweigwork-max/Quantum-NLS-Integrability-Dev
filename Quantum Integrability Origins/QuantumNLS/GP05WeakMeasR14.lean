import QuantumNLS.HolomorphicCauchyC1

/-! Fixed-direction scalar measurability of all covector Taylor coefficients.
It is derived by countable difference quotients of the original scalar slices.
No normed-dual or operator-space measurability is used. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.GP05WeakMeasR14
variable {X E G : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

/-- Weak measurability of the original family propagates to every fixed finite
list of derivatives, locally in its Banach domain. -/
theorem iterated_measurable {F : X → E → G} {U : Set E}
    (L : G →L[ℂ] ℂ) (hU : IsOpen U) (hf : ∀ x, AnalyticOnNhd ℂ (F x) U)
    (hm : ∀ z ∈ U, Measurable (fun x => L (F x z)))
    (n : ℕ) (a : E) (ha : a ∈ U) (v : Fin n → E) :
    Measurable (fun x => L (iteratedFDeriv ℂ n (F x) a v)) := by
  classical
  induction n generalizing a with
  | zero => simpa using hm a ha
  | succ n ih =>
    let t : ℕ → ℂ := fun k => 1/((k : ℂ)+1)
    have ht0 : Tendsto t atTop (𝓝 (0 : ℂ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have htne : ∀ k, t k ≠ 0 := by
      intro k
      dsimp [t]
      apply one_div_ne_zero
      exact_mod_cast (by positivity : (0 : ℝ) < (k : ℝ)+1).ne'
    have ht : Tendsto t atTop (𝓝[≠] (0 : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨ht0, .of_forall htne⟩
    have hloc : ∀ᶠ k in atTop, a+t k • v 0 ∈ U := by
      have hl := (tendsto_const_nhds (x := a)).add (ht0.smul_const (v 0))
      have hl' : Tendsto (fun k => a+t k • v 0) atTop (𝓝 a) := by simpa using hl
      exact hl'.eventually (hU.mem_nhds ha)
    let q : ℕ → X → ℂ := fun k x =>
      if a+t k • v 0 ∈ U then
        (t k)⁻¹ * (L (iteratedFDeriv ℂ n (F x) (a+t k • v 0) (Fin.tail v)) -
          L (iteratedFDeriv ℂ n (F x) a (Fin.tail v)))
      else 0
    have hq : ∀ k, Measurable (q k) := by
      intro k
      dsimp [q]
      split_ifs with hmem
      · exact measurable_const.mul
          ((ih _ hmem (Fin.tail v)).sub (ih a ha (Fin.tail v)))
      · exact measurable_const
    apply measurable_of_tendsto_metrizable hq
    apply tendsto_pi_nhds.mpr
    intro x
    have hdn : DifferentiableAt ℂ (iteratedFDeriv ℂ n (F x)) a :=
      ((hf x).iteratedFDeriv n a ha).differentiableAt
    have hd := hdn.hasFDerivAt.continuousMultilinear_apply_const (Fin.tail v)
    have hde := L.hasFDerivAt.comp a hd
    have hline := QuantumNLS.HolomorphicCauchyC1.hasDerivAt_line hde.differentiableAt (v 0)
    have hline' : HasDerivAt
        (fun s : ℂ => L (iteratedFDeriv ℂ n (F x) (a+s • v 0) (Fin.tail v)))
        (L (iteratedFDeriv ℂ (n+1) (F x) a v)) 0 := by
      convert hline using 1 <;> try rfl
      rw [hde.fderiv]
      rfl
    have hlim := hline'.tendsto_slope_zero.comp ht
    have hlim' : Tendsto (fun k => (t k)⁻¹ *
        (L (iteratedFDeriv ℂ n (F x) (a+t k • v 0) (Fin.tail v)) -
          L (iteratedFDeriv ℂ n (F x) a (Fin.tail v))))
        atTop (𝓝 (L (iteratedFDeriv ℂ (n+1) (F x) a v))) := by
      simpa only [Function.comp_def, zero_add, zero_smul, add_zero, smul_eq_mul] using hlim
    apply hlim'.congr'
    filter_upwards [hloc] with k hk
    simp [q, hk]

end QuantumNLS.GP05WeakMeasR14
