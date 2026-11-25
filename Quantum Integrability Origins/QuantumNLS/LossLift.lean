import Mathlib

/-!
# R-8C922B25 `lem:loss` (`DYNAMICS_LEMMAS.tex:13`), part 2: lifting differentiability through an injective embedding

`lift_hasFDerivAt`: let `ι : E →L F` be a continuous injective linear map of real normed spaces, `E` complete.  If `g : X → E`, `A : X → (X →L E)` is
continuous on the open set `U`, and `ι ∘ g` has Fréchet derivative `ι ∘ A(x)` at every `x ∈ U`, then `g` has Fréchet derivative `A(x)` at every `x ∈ U`.
This is the printed step "the fundamental theorem of calculus in `Y^0` gives `f(x+h) − f(x) = ∫₀¹ Df(x+th)[h] dt`; the integrand is continuous in
`Y^q`, so its integral belongs to `Y^q` and agrees with that difference by injectivity of the embedding".  Mathlib calculus only; no EXT-025 contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
open Filter Topology Set Metric MeasureTheory
noncomputable section
namespace QuantumNLS.Loss

theorem lift_hasFDerivAt {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ι : E →L[ℝ] F) (hι : Function.Injective ι) {U : Set X} (hU : IsOpen U)
    (g : X → E) (A : X → X →L[ℝ] E) (hA : ContinuousOn A U)
    (hG : ∀ x ∈ U, HasFDerivAt (fun y => ι (g y)) (ι.comp (A x)) x) :
    ∀ x ∈ U, HasFDerivAt g (A x) x := by
  intro x hx
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hAx : ContinuousAt A x := hA.continuousAt (hU.mem_nhds hx)
  obtain ⟨η, hη, hηA⟩ := Metric.continuousAt_iff.1 hAx ε hε
  have hev : ∀ᶠ h in 𝓝 (0 : X), ‖h‖ < min (δ / 2) η := by
    have : Metric.ball (0 : X) (min (δ / 2) η) ∈ 𝓝 (0 : X) := Metric.ball_mem_nhds _ (lt_min (by linarith) hη)
    filter_upwards [this] with h hh
    simpa using hh
  filter_upwards [hev] with h hh
  have hh1 : ‖h‖ < δ / 2 := lt_of_lt_of_le hh (min_le_left _ _)
  have hh2 : ‖h‖ < η := lt_of_lt_of_le hh (min_le_right _ _)
  have hseg : ∀ t : ℝ, |t| < 2 → x + t • h ∈ U := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖h‖ ≤ |t| * (δ / 2) := mul_le_mul_of_nonneg_left hh1.le (abs_nonneg _)
      _ < 2 * (δ / 2) := by
        have : 0 < δ / 2 := by linarith
        nlinarith
      _ = δ := by ring
  set a : ℝ → E := fun t => A (x + t • h) h with ha
  have hcont : ContinuousOn a (Ioo (-2 : ℝ) 2) := by
    have h1 : ContinuousOn (fun t : ℝ => x + t • h) (Ioo (-2 : ℝ) 2) := by fun_prop
    have h2 : ContinuousOn (fun t : ℝ => A (x + t • h)) (Ioo (-2 : ℝ) 2) :=
      hA.comp h1 (fun t ht => hseg t (by rw [abs_lt]; exact ⟨ht.1, ht.2⟩))
    exact h2.clm_apply continuousOn_const
  set c : ℝ → E := fun t => ∫ s in (0 : ℝ)..t, a s with hc
  have hcder : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt c (a t) t := by
    intro t ht
    have hsub : uIcc 0 t ⊆ Ioo (-2 : ℝ) 2 := by
      intro s hs
      rw [mem_uIcc] at hs
      rcases hs with hs | hs
      · exact ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
      · exact ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
    exact intervalIntegral.integral_hasDerivAt_right ((hcont.mono hsub).intervalIntegrable)
      ((hcont.stronglyMeasurableAtFilter isOpen_Ioo) t ht)
      ((hcont.continuousAt (isOpen_Ioo.mem_nhds ht)))
  set u : ℝ → E := fun t => g (x + t • h) with hu
  have hluder : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt (fun t => ι (u t)) (ι (a t)) t := by
    intro t ht
    have hUt := hseg t (by rw [abs_lt]; exact ⟨ht.1, ht.2⟩)
    have h1 := hG _ hUt
    have h2 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have := h1.comp_hasDerivAt t h2
    refine HasDerivAt.congr_deriv this ?_
    simp [ha]
  have hlcder : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt (fun t => ι (c t)) (ι (a t)) t := by
    intro t ht
    exact ι.hasFDerivAt.comp_hasDerivAt t (hcder t ht)
  set d : ℝ → F := fun t => ι (u t) - ι (c t) with hd
  have hdder : ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt d 0 t := by
    intro t ht
    have h := (hluder t ht).sub (hlcder t ht)
    rw [sub_self] at h
    exact h
  have hconst := constant_of_derivWithin_zero (f := d) (a := 0) (b := 1)
    (fun t ht => (hdder t ⟨by linarith [ht.1], by linarith [ht.2]⟩).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      have := (hdder t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivWithinAt (s := Icc (0 : ℝ) 1)
      exact this.derivWithin (uniqueDiffOn_Icc zero_lt_one t ⟨ht.1, ht.2.le⟩)) 1 ⟨zero_le_one, le_rfl⟩
  have hc0 : c 0 = 0 := by simp [hc]
  have hdiff : g (x + h) - g x = ∫ s in (0 : ℝ)..1, a s := by
    have h1 : ι (u 1 - c 1) = ι (u 0) := by
      have := hconst
      simp only [hd, hc0, map_zero, sub_zero] at this
      rw [map_sub]
      exact this
    have h2 := hι h1
    have e1 : u 1 = g (x + h) := by simp [hu]
    have e0 : u 0 = g x := by simp [hu]
    rw [e1, e0] at h2
    have : c 1 = ∫ s in (0 : ℝ)..1, a s := rfl
    rw [← this, ← h2]
    abel
  have hsub1 : uIcc (0 : ℝ) 1 ⊆ Ioo (-2 : ℝ) 2 := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hint : IntervalIntegrable a volume 0 1 := (hcont.mono hsub1).intervalIntegrable
  have hb : ‖∫ s in (0 : ℝ)..1, (a s - A x h)‖ ≤ ε * ‖h‖ * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
    rw [uIoc_of_le zero_le_one] at hs
    have hdist : dist (x + s • h) x < η := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1.le]
      calc s * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ < η := by simpa using hh2
    have := hηA hdist
    rw [dist_eq_norm] at this
    calc ‖a s - A x h‖ = ‖(A (x + s • h) - A x) h‖ := by simp [ha]
      _ ≤ ‖A (x + s • h) - A x‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right this.le (norm_nonneg _)
  rw [intervalIntegral.integral_sub hint (by simp)] at hb
  simp at hb
  rw [hdiff]
  simpa using hb

end QuantumNLS.Loss

#print axioms QuantumNLS.Loss.lift_hasFDerivAt
