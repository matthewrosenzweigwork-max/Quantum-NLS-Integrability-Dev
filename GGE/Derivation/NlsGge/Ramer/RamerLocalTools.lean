import NlsGge.Ramer.LinearJacobi
import NlsGge.Ramer.RamerStep8c
import NlsGge.Ramer.RamerJacobianLimits
import NlsGge.Ramer.DivergenceIdentificationGlobal

/-!
# R10-P1: local tools for the Ramer assembly

(a) GL transfer, (b) eventual uniform invertibility of `I + P_k D_H K(x)`, (c) positivity of
`ramerJac` where `I + D_H K(x)` is invertible, (d) locality of `ramerJac`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

section GLTransfer

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- (a) GL transfer: if `I + A ∘ i` is invertible on `H`, then `I + i ∘ A` is a continuous
linear equivalence of `E` with inverse `I + i ∘ B`, `B = -(I + A i)⁻¹ ∘ A`. -/
theorem gl_transfer (i : H →L[ℝ] E) (A : E →L[ℝ] H)
    (hU : IsUnit (1 + A.comp i)) :
    ∃ (Tt : E ≃L[ℝ] E) (B : E →L[ℝ] H),
      (∀ x, Tt x = x + i (A x)) ∧ (∀ y, Tt.symm y = y + i (B y)) ∧
      (∀ u, A u + B (u + i (A u)) = 0) ∧
      (∀ y, B y = -(↑hU.unit⁻¹ : H →L[ℝ] H) (A y)) := by
  set N : H →L[ℝ] H := A.comp i with hN
  set Q : H →L[ℝ] H := ↑hU.unit⁻¹ with hQ
  have hu : (hU.unit : H →L[ℝ] H) = 1 + N := hU.unit_spec
  have hQ1 : Q * (1 + N) = 1 := by
    have h := hU.unit.inv_mul
    rw [hu] at h; exact h
  have hQ2 : (1 + N) * Q = 1 := by
    have h := hU.unit.mul_inv
    rw [hu] at h; exact h
  have hQ1' : ∀ h, Q h + Q (N h) = h := fun h => by
    have := congrArg (fun F : H →L[ℝ] H => F h) hQ1
    simpa using this
  have hQ2' : ∀ h, Q h + N (Q h) = h := fun h => by
    have := congrArg (fun F : H →L[ℝ] H => F h) hQ2
    simpa using this
  set Sinv : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - i.comp (Q.comp A) with hSinv
  set S0 : E →L[ℝ] E := ContinuousLinearMap.id ℝ E + i.comp A with hS0
  have hSi : ∀ x, S0 (Sinv x) = x := by
    intro x
    simp only [hSinv, hS0, sub_apply, add_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_sub]
    have h := hQ2' (A x)
    have : i (A x) - i (Q (A x)) - i (A (i (Q (A x)))) = 0 := by
      rw [← map_sub, ← map_sub]
      have : A (i (Q (A x))) = N (Q (A x)) := rfl
      rw [this]
      have h' : A x - Q (A x) - N (Q (A x)) = 0 := by
        rw [sub_sub]; exact sub_eq_zero.2 h.symm
      rw [h', map_zero]
    linear_combination (norm := abel) this
  have hSi' : ∀ x, Sinv (S0 x) = x := by
    intro x
    simp only [hSinv, hS0, sub_apply, add_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, map_add]
    have h := hQ1' (A x)
    have : i (A x) - i (Q (A x)) - i (Q (A (i (A x)))) = 0 := by
      rw [← map_sub, ← map_sub]
      have : A (i (A x)) = N (A x) := rfl
      rw [this]
      have h' : A x - Q (A x) - Q (N (A x)) = 0 := by
        rw [sub_sub]; exact sub_eq_zero.2 h.symm
      rw [h', map_zero]
    linear_combination (norm := abel) this
  have hBdef : ∀ y, (-(Q.comp A)) y = -(Q (A y)) := fun y => rfl
  refine ⟨ContinuousLinearEquiv.equivOfInverse S0 Sinv hSi' hSi, -(Q.comp A), ?_, ?_, ?_, ?_⟩
  · intro x; simp [hS0]
  · intro x
    show Sinv x = x + i (-(Q.comp A) x)
    simp only [hSinv, sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_neg]
    abel
  · intro u
    rw [hBdef]
    have h := hQ1' (A u)
    have e : A (u + i (A u)) = A u + N (A u) := by rw [map_add]; rfl
    rw [e, map_add, h]; abel
  · intro y; rfl

end GLTransfer

/-- Units are open: a small perturbation of an invertible operator is invertible. -/
theorem exists_isUnit_near {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H) (hU : IsUnit T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ D : H →L[ℝ] H, ‖D‖ < δ → IsUnit (T + D) := by
  obtain ⟨u, rfl⟩ := hU
  rcases subsingleton_or_nontrivial H with hH | hH
  · exact ⟨1, one_pos, fun D _ => isUnit_of_subsingleton _⟩
  refine ⟨‖(↑u⁻¹ : H →L[ℝ] H)‖⁻¹, inv_pos.2 (Units.norm_pos u⁻¹), fun D hD => ?_⟩
  exact (u.add D hD).isUnit

/-- Composition with a pointwise contraction does not increase the operator norm. -/
theorem opNorm_comp_le_of_contraction {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (P : H →L[ℝ] H) (hP : ∀ y, ‖P y‖ ≤ ‖y‖) (D : H →L[ℝ] H) : ‖P.comp D‖ ≤ ‖D‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun y =>
    (hP _).trans (D.le_opNorm y))

/-- Abstract perturbation step for (b). -/
theorem isUnit_one_add_proj_of_near {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] (P : H →L[ℝ] H) (hP : ∀ y, ‖P y‖ ≤ ‖y‖) (D D₀ : H →L[ℝ] H)
    {δ : ℝ}
    (hball : ∀ X : H →L[ℝ] H, ‖X‖ < δ → IsUnit (1 + D₀ + X))
    (h1 : ‖D - D₀‖ < δ / 2) (h2 : ‖P.comp D₀ - D₀‖ < δ / 2) : IsUnit (1 + P.comp D) := by
  have e : 1 + P.comp D = (1 + D₀) + (P.comp (D - D₀) + (P.comp D₀ - D₀)) := by
    ext h; simp
  rw [e]
  have h3 := opNorm_comp_le_of_contraction P hP (D - D₀)
  refine hball _ ?_
  calc ‖P.comp (D - D₀) + (P.comp D₀ - D₀)‖ ≤ ‖P.comp (D - D₀)‖ + ‖P.comp D₀ - D₀‖ :=
        norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

section Concrete

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- (a), concrete form: the data and the vanishing identity `hv` of `ramer_step4_core`, with
`A = fderiv K x₀` and the invertibility hypothesis on `I + D_H K(x₀)`. -/
theorem gl_transfer_hsDerivH (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (x₀ : FullWeightedHilbert c s)
    (hU : IsUnit (1 + (hsDerivH c s hs K x₀).toCLM)) :
    ∃ (Tt : FullWeightedHilbert c s ≃L[ℝ] FullWeightedHilbert c s)
      (B : FullWeightedHilbert c s →L[ℝ] ActualCM c),
      (∀ x, Tt x = x + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
          (fderiv ℝ K x₀ x)) ∧
      (∀ y, Tt.symm y = y + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
          (B y)) ∧
      (∀ u, fderiv ℝ K x₀ u + B (u + cmToFullWeightedHilbert c s
          (le_of_lt (by linarith : 0 < s)) (fderiv ℝ K x₀ u)) = 0) := by
  rw [hsDerivH_toCLM] at hU
  obtain ⟨Tt, B, h1, h2, h3, -⟩ := gl_transfer
    (cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))) (fderiv ℝ K x₀) hU
  exact ⟨Tt, B, h1, h2, h3⟩

/-- `toCLM` of `hsDerivH` of a head-projected field. -/
theorem toCLM_hsDerivH_projField (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : Differentiable ℝ K) (k : ℕ)
    (x : FullWeightedHilbert c s) :
    (hsDerivH c s hs (projField k K) x).toCLM = (headProj c k).comp (hsDerivH c s hs K x).toCLM := by
  rw [hsDerivH_toCLM, hsDerivH_toCLM]
  have hDP : fderiv ℝ (projField k K) x = (headProj c k).comp (fderiv ℝ K x) :=
    ((headProj c k).hasFDerivAt.comp x (hK x).hasFDerivAt).fderiv
  rw [hDP]
  exact ContinuousLinearMap.comp_assoc _ _ _

/-- (b) Eventual uniform invertibility of `I + P_k D_H K(x)` (and of `I + D_H K(x)`) near `x₀`. -/
theorem eventually_uniform_isUnit (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 1 K)
    (x₀ : FullWeightedHilbert c s)
    (hU : IsUnit (1 + (hsDerivH c s hs K x₀).toCLM)) :
    ∃ r : ℝ, 0 < r ∧ ∃ k₀ : ℕ, ∀ x ∈ ball x₀ r,
      IsUnit (1 + (hsDerivH c s hs K x).toCLM) ∧
      ∀ k ≥ k₀, IsUnit (1 + (hsDerivH c s hs (projField k K) x).toCLM) := by
  have hKd : Differentiable ℝ K := hK.differentiable (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := exists_isUnit_near _ hU
  -- HS-norm smallness
  have hc := continuous_hsDerivH c s hs K hK
  have ev1 : ∀ᶠ x in 𝓝 x₀, ‖hsDerivH c s hs K x - hsDerivH c s hs K x₀‖ < δ / 2 := by
    have h := ((hc.tendsto x₀).sub_const (hsDerivH c s hs K x₀)).norm
    simp only [sub_self, norm_zero] at h
    exact h.eventually (gt_mem_nhds (half_pos hδ))
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.1 ev1
  have ev2 : ∀ᶠ k : ℕ in atTop,
      ‖hsDerivH c s hs (projField k K) x₀ - hsDerivH c s hs K x₀‖ < δ / 2 := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1
      (tendsto_hsDerivH_projField (c := c) (s := s) hs K hKd x₀))
    exact this.eventually (gt_mem_nhds (half_pos hδ))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ev2
  refine ⟨r, hr, k₀, fun x hx => ?_⟩
  have hx1 := hr' (by simpa using hx)
  have hopNorm : ∀ D : HilbertSchmidt (ActualCM c) (ActualCM c), ‖D.toCLM‖ ≤ ‖D‖ :=
    fun D => HilbertSchmidt.opNorm_le D
  have hd1 : ‖(hsDerivH c s hs K x).toCLM - (hsDerivH c s hs K x₀).toCLM‖ < δ / 2 := by
    rw [← HilbertSchmidt.toCLM_sub]; exact lt_of_le_of_lt (hopNorm _) hx1
  refine ⟨?_, fun k hk => ?_⟩
  · have : 1 + (hsDerivH c s hs K x).toCLM = (1 + (hsDerivH c s hs K x₀).toCLM) +
        ((hsDerivH c s hs K x).toCLM - (hsDerivH c s hs K x₀).toCLM) := by abel
    rw [this]; exact hball _ (by linarith)
  · have h2 := lt_of_le_of_lt (hopNorm _) (hk₀ k hk)
    rw [HilbertSchmidt.toCLM_sub, toCLM_hsDerivH_projField c s hs K hKd k x₀] at h2
    rw [toCLM_hsDerivH_projField c s hs K hKd k x]
    exact isUnit_one_add_proj_of_near (headProj c k) (fun y => norm_cmTrunc_le c k y) _ _
      (fun D' hD' => hball D' hD') hd1 h2

/-- (c) Positivity of `ramerJac` wherever `I + D_H K(x)` is invertible. -/
theorem ramerJac_pos_of_isUnit (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (x : FullWeightedHilbert c s)
    (hU : IsUnit (1 + (hsDerivH c s hs K x).toCLM)) : 0 < ramerJac c s hs K x := by
  rw [ramerJac_eq]
  exact mul_pos (abs_pos.2 (det2_ne_zero_of_isUnit _ hU)) (Real.exp_pos _)

/-- Countable-cover principle: local a.e. statements on `R ⁻¹' V` globalize. -/
theorem ae_realization_mem_of_local (V : Set (FullWeightedHilbert c s))
    (P : (ℤ → ℂ) → Prop)
    (hloc : ∀ y ∈ V, ∃ t > 0, ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball y t → P z) :
    ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ V → P z := by
  set R := NlsGge.Measure.fullWeightedSequenceRealization c s with hR
  choose t ht hae using hloc
  obtain ⟨T, hT, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : V => ball (y : FullWeightedHilbert c s) (t y y.2))
    (fun _ => isOpen_ball)
  have hall : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val), ∀ i ∈ T,
      R z ∈ ball (i : FullWeightedHilbert c s) (t i i.2) → P z :=
    (ae_ball_iff hT).2 (fun i _ => hae i i.2)
  filter_upwards [hall] with z hz hzV
  have hmem : R z ∈ ⋃ i : V, ball (i : FullWeightedHilbert c s) (t i i.2) :=
    Set.mem_iUnion.2 ⟨⟨R z, hzV⟩, mem_ball_self (ht _ hzV)⟩
  rw [← hTeq] at hmem
  obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 hmem
  exact hz i hi hzi

/-- `ramerDiv` is local (sequence side). -/
theorem ramerDiv_ae_eq_of_eqOn (hs : (1 : ℝ) / 2 < s) {V : Set (FullWeightedHilbert c s)}
    (hV : IsOpen V) {K K' : FullWeightedHilbert c s → ActualCM c}
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K') (hEq : EqOn K K' V) :
    ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ V →
        ramerDiv c s hs K z = ramerDiv c s hs K' z := by
  apply ae_realization_mem_of_local
  intro y hy
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hV y hy
  obtain ⟨r1, hr1, G, η, hGK, hC, -, -⟩ := exists_local_closedDiv c s hs K hK y
  obtain ⟨r2, hr2, G', η', hGK', hC', -, -⟩ := exists_local_closedDiv c s hs K' hK' y
  have h3 := (Classical.choose_spec (divergence_identification c s hs K hK)).2.2.1
  have h3' := (Classical.choose_spec (divergence_identification c s hs K' hK')).2.2.1
  have e1 : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball y r1 →
        ramerDiv c s hs K z = η z := by
    unfold ramerDiv; rw [dite_cond_eq_true (eq_true hK)]; exact h3 y r1 G η hGK hC
  have e2 : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball y r2 →
        ramerDiv c s hs K' z = η' z := by
    unfold ramerDiv; rw [dite_cond_eq_true (eq_true hK')]; exact h3' y r2 G' η' hGK' hC'
  set t := min ρ (min r1 r2) with ht
  have ht0 : 0 < t := lt_min hρ (lt_min hr1 hr2)
  have hGG : EqOn G G' (ball y t) := by
    intro x hx
    have hx1 : x ∈ ball y r1 := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx
    have hx2 : x ∈ ball y r2 := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hx
    have hxV : x ∈ V := hρV (ball_subset_ball (min_le_left _ _) hx)
    rw [hGK hx1, hGK' hx2, hEq hxV]
  have e3 := IsClosedDiv.ae_eq_of_eqOn hs isOpen_ball hGG hC hC'
  refine ⟨t, ht0, ?_⟩
  filter_upwards [e1, e2, e3] with z h1 h2 h3z hz
  have hz1 : NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball y r1 :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hz
  have hz2 : NlsGge.Measure.fullWeightedSequenceRealization c s z ∈ ball y r2 :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hz
  rw [h1 hz1, h2 hz2, h3z hz]

/-- (d) Locality of `ramerJac`: if `K = K'` on an open `V` then `ramerJac K = ramerJac K'`
a.e. on `V`. -/
theorem ramerJac_ae_eq_of_eqOn (hs : (1 : ℝ) / 2 < s) {V : Set (FullWeightedHilbert c s)}
    (hV : IsOpen V) {K K' : FullWeightedHilbert c s → ActualCM c}
    (hK : ContDiff ℝ 2 K) (hK' : ContDiff ℝ 2 K') (hEq : EqOn K K' V) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
      x ∈ V → ramerJac c s hs K x = ramerJac c s hs K' x := by
  have h := ae_of_ae_coordE c s hs (ramerDiv_ae_eq_of_eqOn c s hs hV hK hK' hEq)
  filter_upwards [h] with x hx hxV
  have hx' := hx (by rw [realization_coordE]; exact hxV)
  rw [ramerJac_eq, ramerJac_eq, hx', hEq hxV]
  have : hsDerivH c s hs K x = hsDerivH c s hs K' x := by
    unfold hsDerivH
    have hf : fderiv ℝ K x = fderiv ℝ K' x :=
      (show K =ᶠ[𝓝 x] K' from Filter.mem_of_superset (hV.mem_nhds hxV) hEq).fderiv_eq
    exact congrArg (cmFactorHS c s hs) hf
  rw [this]

end Concrete

end NlsGge.Ramer
