import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.LinearJacobi
import NlsGge.Ramer.LinearDecomposition
import NlsGge.Ramer.LinearSmallJacobiLocal

                                                                                                           
                                                                                                                   
                                                 
                                                                                                                
                                                                                                                    
                                                                                                                      
                                                                               
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- R-041 helper (generic, real): a two-sided inverse of `1 + N` on a complete real inner-product space
when `‖N‖ < 1`, obtained from `Units.oneSub` (the Neumann inverse). -/
theorem r041_neumann_Q {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (N : H →L[ℝ] H) (hN : ‖N‖ < 1) :
    ∃ Q : H ≃L[ℝ] H, (∀ h : H, Q h + N (Q h) = h) ∧ (∀ h : H, Q (h + N h) = h) := by
  have hn : ‖-N‖ < 1 := by rw [norm_neg]; exact hN
  set u := Units.oneSub (-N) hn with hu
  set Qc : H →L[ℝ] H := ↑u⁻¹ with hQc
  have h2 : (u : H →L[ℝ] H) = 1 + N := by simp [hu, Units.val_oneSub]
  have hQ1 : Qc * (1 + N) = 1 := by
    have h := u.inv_mul
    rw [h2] at h; exact h
  have hQ2 : (1 + N) * Qc = 1 := by
    have h := u.mul_inv
    rw [h2] at h; exact h
  have hQ1' : ∀ h : H, Qc ((1 + N) h) = h := fun h => by
    have := congrArg (fun T : H →L[ℝ] H => T h) hQ1
    simpa using this
  have hQ2' : ∀ h : H, (1 + N) (Qc h) = h := fun h => by
    have := congrArg (fun T : H →L[ℝ] H => T h) hQ2
    simpa using this
  refine ⟨ContinuousLinearEquiv.equivOfInverse Qc (1 + N) hQ2' hQ1', fun h => ?_, fun h => ?_⟩
  · show Qc h + N (Qc h) = h
    simpa using hQ2' h
  · show Qc (h + N h) = h
    simpa using hQ1' h

/-- R-041 algebra (generic, real, pointwise). For a uniform `r < 1/3` with `‖A (i h)‖ ≤ r ‖h‖`, the map
`S x = x + i (A x)` is a continuous linear equivalence whose inverse is `y ↦ y + i (C y)` with
`C x = -(Q (A x))`, `Q` the two-sided inverse of `1 + A ∘ i` on `H`, and `‖C (i h)‖ ≤ r/(1-r) ‖h‖`. -/
theorem r041_alg {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (i : H →L[ℝ] E) (A : E →L[ℝ] H) (r : ℝ) (hr0 : 0 ≤ r) (hr3 : r < 1 / 3)
    (hr : ∀ h : H, ‖A (i h)‖ ≤ r * ‖h‖) :
    ∃ (S : E ≃L[ℝ] E) (Q : H ≃L[ℝ] H) (C : E →L[ℝ] H),
      (∀ x : E, S x = x + i (A x)) ∧
      (∀ h : H, Q h + A (i (Q h)) = h) ∧
      (∀ h : H, Q (h + A (i h)) = h) ∧
      (∀ x : E, C x = -(Q (A x))) ∧
      (∀ y : E, S.symm y = y + i (C y)) ∧
      r / (1 - r) < (1 / 2 : ℝ) ∧
      (∀ h : H, ‖C (i h)‖ ≤ (r / (1 - r)) * ‖h‖) := by
  have hN : ‖A.comp i‖ ≤ r :=
    ContinuousLinearMap.opNorm_le_bound _ hr0 (fun h => by simpa [ContinuousLinearMap.comp_apply] using hr h)
  have hr1 : r < 1 := by linarith
  obtain ⟨S, M, hS, hSs, hM, hMn⟩ := NlsGge.Ramer.exists_neumann_equiv i A r hN hr1
  obtain ⟨Q, hQ1, hQ2⟩ := r041_neumann_Q (A.comp i) (lt_of_le_of_lt hN hr1)
  have hMx : ∀ x : E, M x = -(Q (A x)) := by
    intro x
    have e1 : M x = -(A (S.symm x)) := hM x
    rw [hSs x, map_add] at e1
    have e3 : -(M x) = A x + A (i (M x)) := by
      have := congrArg (fun z => -z) e1
      simpa using this
    have hu : -(M x) + A (i (-(M x))) = A x := by
      rw [map_neg i, map_neg A, e3]; abel
    have hq : Q (-(M x) + A (i (-(M x)))) = -(M x) := hQ2 (-(M x))
    rw [hu] at hq
    rw [hq, neg_neg]
  refine ⟨S, Q, M, hS, hQ1, hQ2, hMx, fun y => hSs y, ?_, ?_⟩
  · rw [div_lt_iff₀ (by linarith)]; linarith
  · intro h
    exact ((M.comp i).le_opNorm h).trans (mul_le_mul_of_nonneg_right hMn (norm_nonneg _))

/-- R-041 measure step (generic). Two Jacobi identities `γ.map S⁻¹ = J_B γ` and `γ.map S = J_C γ` give
`J_C(S x) J_B(x) = 1` almost everywhere, by uniqueness of densities; no null-set premise is assumed beyond
these identities (which carry the quasi-measure preservation of `S`). -/
theorem r041_density {X : Type*} [MeasurableSpace X] (γ : Measure X) [IsProbabilityMeasure γ]
    (S Sinv : X → X) (hS : Measurable S) (hSi : Measurable Sinv)
    (hSS : ∀ x, Sinv (S x) = x) (hSS' : ∀ y, S (Sinv y) = y)
    (JB JC : X → ℝ)
    (hJB : AEMeasurable (fun x => ENNReal.ofReal (JB x)) γ)
    (hJC : AEMeasurable (fun x => ENNReal.ofReal (JC x)) γ)
    (hJCnn : ∀ x, 0 ≤ JC x)
    (hBmap : γ.map Sinv = γ.withDensity (fun x => ENNReal.ofReal (JB x)))
    (hCmap : γ.map S = γ.withDensity (fun x => ENNReal.ofReal (JC x))) :
    ∀ᵐ x ∂γ, JC (S x) * JB x = 1 := by
  have hQMP : Measure.QuasiMeasurePreserving S γ γ :=
    ⟨hS, by rw [hCmap]; exact withDensity_absolutelyContinuous _ _⟩
  have hJCS : AEMeasurable (fun x => ENNReal.ofReal (JC (S x))) γ :=
    hJC.comp_quasiMeasurePreserving hQMP
  have hSia : AEMeasurable Sinv γ := hSi.aemeasurable
  have hX : ∀ G : X → ℝ≥0∞, Measurable G →
      ∫⁻ x, G (S x) ∂γ = ∫⁻ y, ENNReal.ofReal (JC y) * G y ∂γ := by
    intro G hG
    have hGae : AEMeasurable G γ := hG.aemeasurable
    rw [← lintegral_map hG hS, hCmap, lintegral_withDensity_eq_lintegral_mul₀ hJC hGae]
    rfl
  have hY : ∀ H : X → ℝ≥0∞, AEMeasurable H γ →
      ∫⁻ y, H (Sinv y) ∂γ = ∫⁻ x, ENNReal.ofReal (JB x) * H x ∂γ := by
    intro H hH
    have hHmap : AEMeasurable H (γ.map Sinv) := by
      rw [hBmap]; exact hH.mono_ac (withDensity_absolutelyContinuous _ _)
    rw [← lintegral_map' hHmap hSia, hBmap, lintegral_withDensity_eq_lintegral_mul₀ hJB hH]
    rfl
  have hint : ∀ A : Set X, MeasurableSet A →
      ∫⁻ x in A, ENNReal.ofReal (JC (S x)) * ENNReal.ofReal (JB x) ∂γ
        = ∫⁻ x in A, (1 : ℝ≥0∞) ∂γ := by
    intro A hA
    have hind : Measurable (A.indicator (fun _ : X => (1 : ℝ≥0∞))) :=
      measurable_const.indicator hA
    have hind' : AEMeasurable (A.indicator (fun _ : X => (1 : ℝ≥0∞))) γ := hind.aemeasurable
    have h1 := hX (fun y => A.indicator (fun _ : X => (1 : ℝ≥0∞)) (Sinv y)) (hind.comp hSi)
    simp only [hSS] at h1
    have hH : AEMeasurable
        (fun x => A.indicator (fun _ : X => (1 : ℝ≥0∞)) x * ENNReal.ofReal (JC (S x))) γ :=
      hind'.mul hJCS
    have h2 := hY _ hH
    simp only [hSS'] at h2
    have h3 : ∫⁻ x, A.indicator (fun _ : X => (1 : ℝ≥0∞)) x ∂γ =
        ∫⁻ x, A.indicator (fun _ : X => (1 : ℝ≥0∞)) x *
          (ENNReal.ofReal (JC (S x)) * ENNReal.ofReal (JB x)) ∂γ := by
      calc ∫⁻ x, A.indicator (fun _ : X => (1 : ℝ≥0∞)) x ∂γ
          = ∫⁻ y, ENNReal.ofReal (JC y) * A.indicator (fun _ : X => (1 : ℝ≥0∞)) (Sinv y) ∂γ := h1
        _ = ∫⁻ y, A.indicator (fun _ : X => (1 : ℝ≥0∞)) (Sinv y) * ENNReal.ofReal (JC y) ∂γ :=
          lintegral_congr fun y => mul_comm _ _
        _ = ∫⁻ x, ENNReal.ofReal (JB x) *
            (A.indicator (fun _ : X => (1 : ℝ≥0∞)) x * ENNReal.ofReal (JC (S x))) ∂γ := h2
        _ = ∫⁻ x, A.indicator (fun _ : X => (1 : ℝ≥0∞)) x *
            (ENNReal.ofReal (JC (S x)) * ENNReal.ofReal (JB x)) ∂γ :=
          lintegral_congr fun x => by ring
    have e1 : ∫⁻ x, A.indicator (fun x : X => ENNReal.ofReal (JC (S x)) * ENNReal.ofReal (JB x)) x ∂γ
        = ∫⁻ x in A, ENNReal.ofReal (JC (S x)) * ENNReal.ofReal (JB x) ∂γ :=
      lintegral_indicator hA _
    have e2 : ∫⁻ x, A.indicator (fun _ : X => (1 : ℝ≥0∞)) x ∂γ = ∫⁻ x in A, (1 : ℝ≥0∞) ∂γ :=
      lintegral_indicator hA _
    rw [← e1, ← e2]
    calc ∫⁻ x, A.indicator (fun x : X => ENNReal.ofReal (JC (S x)) * ENNReal.ofReal (JB x)) x ∂γ
        = ∫⁻ x, A.indicator (fun _ : X => (1 : ℝ≥0∞)) x *
            (ENNReal.ofReal (JC (S x)) * ENNReal.ofReal (JB x)) ∂γ :=
          lintegral_congr fun x => by by_cases hx : x ∈ A <;> simp [Set.indicator, hx]
      _ = ∫⁻ x, A.indicator (fun _ : X => (1 : ℝ≥0∞)) x ∂γ := h3.symm
  have hDm : AEMeasurable (fun x => ENNReal.ofReal (JC (S x)) * ENNReal.ofReal (JB x)) γ :=
    hJCS.mul hJB
  have hDae : (fun x => ENNReal.ofReal (JC (S x)) * ENNReal.ofReal (JB x)) =ᵐ[γ]
      (fun _ => (1 : ℝ≥0∞)) :=
    ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hDm aemeasurable_const (fun s hs _ => hint s hs)
  filter_upwards [hDae] with x hx
  have h1 : ENNReal.ofReal (JC (S x) * JB x) = 1 := by
    rw [ENNReal.ofReal_mul (hJCnn (S x))]; exact hx
  exact ENNReal.ofReal_eq_one.1 h1

theorem linear_small_jacobian_inverse
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (B : RamerE c s →L[ℝ] RamerH c)
    (hB : ∃ r : ℝ, 0 ≤ r ∧ r < (1 / 3 : ℝ) ∧
      ∀ h : RamerH c,
        ‖B (cmEmbedding c s hs h)‖ ≤ r * ‖h‖) :
    ∃ (r : ℝ)
        (S : RamerE c s ≃L[ℝ] RamerE c s)
        (Q : RamerH c ≃L[ℝ] RamerH c)
        (C : RamerE c s →L[ℝ] RamerH c),
      0 ≤ r ∧ r < (1 / 3 : ℝ) ∧
      (∀ h : RamerH c,
        ‖B (cmEmbedding c s hs h)‖ ≤ r * ‖h‖) ∧
      (∀ h : RamerH c,
        Q h + B (cmEmbedding c s hs (Q h)) = h) ∧
      (∀ h : RamerH c,
        Q (h + B (cmEmbedding c s hs h)) = h) ∧
      (∀ x : RamerE c s,
        S x = x + cmEmbedding c s hs (B x)) ∧
      (∀ x : RamerE c s, C x = -(Q (B x))) ∧
      (∀ y : RamerE c s,
        S.symm y = y + cmEmbedding c s hs (C y)) ∧
      (r / (1 - r) < (1 / 2 : ℝ)) ∧
      (∀ h : RamerH c,
        ‖C (cmEmbedding c s hs h)‖ ≤ (r / (1 - r)) * ‖h‖) ∧
      ∀ᵐ x ∂(ramerGaussian c s),
        ramerJac c s hs (fun y : RamerE c s => C y) (S x) *
          ramerJac c s hs (fun y : RamerE c s => B y) x = 1
:= by
  obtain ⟨r, hr0, hr3, hBr⟩ := hB
  obtain ⟨S, Q, C, hS, hQ1, hQ2, hC, hSi, hsmall, hCb⟩ :=
    r041_alg (cmEmbedding c s hs) B r hr0 hr3 hBr
  refine ⟨r, S, Q, C, hr0, hr3, hBr, hQ1, hQ2, hS, hC, hSi, hsmall, hCb, ?_⟩
  show ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), _
  have hJ : ∀ (M : RamerE c s → RamerH c) (x : RamerE c s),
      ramerJac c s hs M x = NlsGge.Ramer.ramerJac c s hs M x :=
    fun M x => (NlsGge.Ramer.ramerJac_eq c s hs M x).symm
  have hBmap := NlsGge.Ramer.linear_map_symm c s hs B S (fun x => hS x)
  have hCmap : (NlsGge.Measure.fullWeightedSequenceGaussian c s).map ⇑S =
      (NlsGge.Measure.fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (NlsGge.Ramer.ramerJac c s hs (fun y => C y) x)) :=
    NlsGge.Ramer.linear_map_symm c s hs C S.symm (fun y => hSi y)
  have key := r041_density (NlsGge.Measure.fullWeightedSequenceGaussian c s) (⇑S) (⇑S.symm)
    S.continuous.measurable S.symm.continuous.measurable
    (fun x => S.symm_apply_apply x) (fun y => S.apply_symm_apply y)
    (fun x => NlsGge.Ramer.ramerJac c s hs (fun y => B y) x)
    (fun x => NlsGge.Ramer.ramerJac c s hs (fun y => C y) x)
    (NlsGge.Ramer.aemeasurable_ofReal_ramerJac c s hs (fun y => B y) B.contDiff)
    (NlsGge.Ramer.aemeasurable_ofReal_ramerJac c s hs (fun y => C y) C.contDiff)
    (fun x => NlsGge.Ramer.ramerJac_nonneg c s hs (fun y => C y) x)
    hBmap hCmap
  filter_upwards [key] with x hx
  rw [hJ, hJ]
  exact hx

end

end NlsGge.ThirdConsultation.R
