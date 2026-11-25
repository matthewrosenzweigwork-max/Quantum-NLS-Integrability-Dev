import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.RamerStep7
import NlsGge.Ramer.LinearDecomposition
import NlsGge.Ramer.TruncatedFieldConvergence
import NlsGge.Sobolev.PhysicalProjection

                                                                                                           
                                                                                                             
                                                                                                                  
                                                                             
                                                                                                                      
                                                                                                                   
                                                                                                                        
                                                                                                                    
                                                                                                                    
                                                                     
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section R045Aux
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- R-045 helper: the fibre derivative of an arbitrary small inverse `F`. -/
theorem r045_hasFDerivAt_fibre (i : H →L[ℝ] E) (L : E → H) (ε : ℝ)
    (hy : NlsGge.Ramer.Step7Hyp i L ε) (F : E → E)
    (hFc : ContinuousOn F (ball (0 : E) (ε / 2)))
    (hFs : ∀ z ∈ ball (0 : E) (ε / 2),
      F z ∈ closedBall (0 : E) ε ∧ F z + i (L (F z)) = z)
    {z : E} (hz : z ∈ ball (0 : E) (ε / 2)) :
    ∃ e : H ≃L[ℝ] H, (∀ u : H, e u = u + fderiv ℝ L (F z) (i u)) ∧
      HasFDerivAt (fun v : H => F (z + i v))
        (i.comp (Ring.inverse (1 + HDeriv i L (F z)))) 0 ∧
      HasFDerivAt (fun v : H => F (z + i v)) (i.comp (e.symm : H →L[ℝ] H)) 0 := by
  have hv : z + i (0 : H) ∈ ball (0 : E) (ε / 2) := by simpa using hz
  have hF0 : F (z + i (0 : H)) = F z := by simp
  set ψ : H → H := fun v => v - L (F (z + i v)) with hψ
  have hfib : ∀ v, z + i v ∈ ball (0 : E) (ε / 2) → F (z + i v) = z + i (ψ v) := by
    intro v hv'
    have h := (hFs _ hv').2
    simp only [hψ, map_sub]
    generalize F (z + i v) = x at h ⊢
    calc x = (z + i v) - i (L x) := eq_sub_of_add_eq h
      _ = z + (i v - i (L x)) := by abel
  have hcont : ContinuousAt (fun v : H => z + i v) 0 := by fun_prop
  have hSc : ContinuousAt (fun v : H => F (z + i v)) 0 :=
    ContinuousAt.comp (f := fun v : H => z + i v) (g := F)
      (hFc.continuousAt (isOpen_ball.mem_nhds hv)) hcont
  have hxm := (hFs _ hv).1
  have hLc : ContinuousAt (fun v : H => L (F (z + i v))) 0 :=
    ContinuousAt.comp (f := fun v : H => F (z + i v)) (g := L)
      (hy.diff _ hxm).continuousAt hSc
  have hψc : ContinuousAt ψ 0 := continuousAt_id.sub hLc
  have hev : ∀ᶠ v in 𝓝 (0 : H), z + i v ∈ ball (0 : E) (ε / 2) :=
    hcont.eventually (isOpen_ball.mem_nhds hv)
  set φ : H → H := fun w => w + L (z + i w) with hφ
  have hxeq : z + i (ψ 0) = F z := by rw [← hF0]; exact (hfib 0 hv).symm
  have hxmz : F z ∈ closedBall (0 : E) ε := (hFs z hz).1
  have hdiffL : HasFDerivAt L (fderiv ℝ L (z + i (ψ 0))) (z + i (ψ 0)) := by
    rw [hxeq]; exact (hy.diff _ hxmz).hasFDerivAt
  have hφd : HasFDerivAt φ (1 + (fderiv ℝ L (z + i (ψ 0))).comp i) (ψ 0) := by
    have h1 : HasFDerivAt (fun w : H => z + i w) i (ψ 0) := by
      simpa using i.hasFDerivAt.const_add z
    exact (hasFDerivAt_id _).add (hdiffL.comp (ψ 0) h1)
  obtain ⟨e, he⟩ := NlsGge.Ramer.exists_equiv_one_add ((fderiv ℝ L (z + i (ψ 0))).comp i)
    (by rw [hxeq]; exact hy.contr _ hxmz)
  have hφd' : HasFDerivAt φ (e : H →L[ℝ] H) (ψ 0) := by rw [he]; exact hφd
  have hlin : ∀ᶠ v in 𝓝 (0 : H), φ (ψ v) = v := by
    filter_upwards [hev] with v hv'
    show ψ v + L (z + i (ψ v)) = v
    rw [← hfib v hv', hψ]; simp
  have hψd : HasFDerivAt ψ (e.symm : H →L[ℝ] H) 0 :=
    HasFDerivAt.of_local_left_inverse hψc hφd' hlin
  have h2 : HasFDerivAt (fun v : H => F (z + i v)) (i.comp (e.symm : H →L[ℝ] H)) 0 := by
    have h3 : HasFDerivAt (fun v : H => z + i (ψ v)) (i.comp (e.symm : H →L[ℝ] H)) 0 :=
      (i.hasFDerivAt.comp (0 : H) hψd).const_add z
    exact h3.congr_of_eventuallyEq (hev.mono fun v hv' => hfib v hv')
  have heD : (e : H →L[ℝ] H) = 1 + HDeriv i L (F z) := by
    rw [he]; unfold HDeriv; rw [hxeq]
  have hinv : Ring.inverse (1 + HDeriv i L (F z)) = (e.symm : H →L[ℝ] H) := by
    rw [← heD, ContinuousLinearMap.ringInverse_equiv, ContinuousLinearMap.inverse_equiv]
  refine ⟨e, fun u => ?_, by rw [hinv]; exact h2, h2⟩
  have := congrArg (fun T : H →L[ℝ] H => T u) heD
  simpa [HDeriv] using this

end R045Aux

section R045Production
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "i" => cmEmbedding c s hs
local notation "P" => NlsGge.Ramer.headProj c

/-- R-045 helper: the head embedding `headToE` is the inclusion `i` on the head. -/
theorem r045_headToE_eq (m : ℕ) (v : NlsGge.Ramer.actualCMHead c m) :
    NlsGge.Ramer.headToE c s m v = i (v : H) := by
  apply NlsGge.Ramer.fullWeighted_ext c s
  intro n
  rw [NlsGge.Ramer.headToE_coord]
  exact (NlsGge.Pilot.cmToFullWeightedHilbert_apply c s (le_of_lt (by linarith : (0 : ℝ) < s))
    (v : H) n).symm

/-- R-045 helper: a continuous linear map on the finite head whose value at `w` is
`w + P m (A (e.symm w))`, with `e = 1 + D_L`, `D_L = (1 - P m) A`, `‖A‖ ≤ 1/2`, is a unit. -/
theorem r045_isUnit_head (K₂ L : E → H) (m : ℕ) (y : E) (e : H ≃L[ℝ] H)
    (hK : ContDiff ℝ 2 K₂)
    (hL : ∀ y : E, L y = K₂ y - P m (K₂ y))
    (he : ∀ u : H, e u = u + fderiv ℝ L y (i u))
    (hDK : ‖HDeriv i K₂ y‖ ≤ (1 / 2 : ℝ))
    (Gd : NlsGge.Ramer.actualCMHead c m →L[ℝ] NlsGge.Ramer.actualCMHead c m)
    (hGd : ∀ w : NlsGge.Ramer.actualCMHead c m,
      (Gd w : H) = (w : H) + P m (fderiv ℝ K₂ y (i (e.symm (w : H))))) :
    IsUnit Gd := by
  have hKd : Differentiable ℝ K₂ := hK.differentiable (by norm_num)
  have hdL' := ((hKd y).hasFDerivAt.sub ((P m).hasFDerivAt.comp y (hKd y).hasFDerivAt))
  have hdL'' : HasFDerivAt L _ y :=
    HasFDerivAt.congr_of_eventuallyEq hdL' (Eventually.of_forall fun x => hL x)
  have hdL : ∀ u : E, fderiv ℝ L y u = fderiv ℝ K₂ y u - P m (fderiv ℝ K₂ y u) :=
    fun u => congrArg (fun T => T u) hdL''.fderiv
  have hinj : ∀ w : NlsGge.Ramer.actualCMHead c m, Gd w = 0 → w = 0 := by
    intro w hw
    have hw' : (w : H) + P m (fderiv ℝ K₂ y (i (e.symm (w : H)))) = 0 := by
      rw [← hGd w, hw]; rfl
    set u : H := e.symm (w : H) with hu
    have hwu : (w : H) = u + (fderiv ℝ K₂ y (i u) - P m (fderiv ℝ K₂ y (i u))) := by
      have h1 : e u = (w : H) := e.apply_symm_apply (w : H)
      rw [← h1, he u, hdL (i u)]
    have hsum : u + fderiv ℝ K₂ y (i u) = 0 := by
      rw [hwu] at hw'
      have : u + (fderiv ℝ K₂ y (i u) - P m (fderiv ℝ K₂ y (i u))) +
          P m (fderiv ℝ K₂ y (i u)) = u + fderiv ℝ K₂ y (i u) := by abel
      rw [← this]; exact hw'
    have hu0 : u = 0 := by
      have hnorm : ‖u‖ = ‖fderiv ℝ K₂ y (i u)‖ :=
        (congrArg norm (eq_neg_of_add_eq_zero_left hsum)).trans (norm_neg _)
      have hle : ‖fderiv ℝ K₂ y (i u)‖ ≤ 1 / 2 * ‖u‖ :=
        ((HDeriv i K₂ y).le_opNorm u).trans (mul_le_mul_of_nonneg_right hDK (norm_nonneg u))
      have : ‖u‖ ≤ 0 := by linarith
      exact norm_le_zero_iff.mp this
    have h0 : fderiv ℝ K₂ y (i (0 : H)) = 0 := by
      rw [(i).map_zero]; exact (fderiv ℝ K₂ y).map_zero
    have hw0 : (w : H) = 0 := by
      rw [hwu, hu0, h0, (P m).map_zero]; abel
    exact Subtype.ext hw0
  have : CompleteSpace (NlsGge.Ramer.actualCMHead c m) :=
    FiniteDimensional.complete ℝ (NlsGge.Ramer.actualCMHead c m)
  have hinj' : Function.Injective (Gd : NlsGge.Ramer.actualCMHead c m →ₗ[ℝ]
      NlsGge.Ramer.actualCMHead c m) :=
    (injective_iff_map_eq_zero _).2 hinj
  have hsurj := LinearMap.injective_iff_surjective.1 hinj'
  exact ContinuousLinearMap.isUnit_iff_bijective.2 ⟨hinj', hsurj⟩

theorem differentiableAt_Sinv_fibre
    (K₂ L : E → H) (m : ℕ) (ε : ℝ)
    (hK : ContDiff ℝ 2 K₂)
    (hL : ∀ y : E, L y = K₂ y - P m (K₂ y))
    (hStep : NlsGge.Ramer.Step7Hyp i L ε)
    (hD : ∀ y ∈ closedBall (0 : E) ε,
      ‖HDeriv i K₂ y‖ ≤ (1 / 2 : ℝ))
    (Sinv : E → E) (hSinv : IsSmallInverse c s hs L ε Sinv) :
    ContinuousOn Sinv (ball (0 : E) (ε / 2)) ∧
    ∀ z ∈ ball (0 : E) (ε / 2),
      HasFDerivAt (fun h : H => Sinv (z + i h))
        (((i).comp (Ring.inverse (1 + HDeriv i L (Sinv z)))) : H →L[ℝ] E) 0 ∧
      DifferentiableAt ℝ
        (fun h : H => Sinv (z + i h) + i (K₂ (Sinv (z + i h)))) 0 ∧
      IsUnit (fderiv ℝ
        (fun v : NlsGge.Ramer.actualCMHead c m =>
          v + NlsGge.Ramer.cmTrunc c m
            (K₂ (Sinv (z + NlsGge.Ramer.headToE c s m v)))) 0) := by
  have hKd : Differentiable ℝ K₂ := hK.differentiable (by norm_num)
  have hFc : ContinuousOn Sinv (ball (0 : E) (ε / 2)) := by
    refine (NlsGge.Ramer.continuousOn_Sinv hStep).congr (fun z hz => ?_)
    exact NlsGge.Ramer.Sinv_unique hStep (hSinv z hz).1 (hSinv z hz).2 hz
  refine ⟨hFc, fun z hz => ?_⟩
  obtain ⟨e, he, hderI, hder⟩ := r045_hasFDerivAt_fibre i L ε hStep Sinv hFc hSinv hz
  have hSz : Sinv (z + i (0 : H)) = Sinv z := by simp
  refine ⟨hderI, ?_, ?_⟩
  · exact hder.differentiableAt.add
      ((i).differentiableAt.comp (0 : H) ((hKd _).comp (0 : H) hder.differentiableAt))
  · -- derivative of the finite-head map
    have hyb : Sinv z ∈ closedBall (0 : E) ε := (hSinv z hz).1
    have hK2 : HasFDerivAt K₂ (fderiv ℝ K₂ (Sinv z)) (Sinv (z + i (0 : H))) := by
      rw [hSz]; exact (hKd _).hasFDerivAt
    have hKF := hK2.comp (0 : H) hder
    have hTr := (NlsGge.Ramer.cmTrunc c m).hasFDerivAt.comp (0 : H) hKF
    have hι := (NlsGge.Ramer.actualCMHead c m).subtypeL.hasFDerivAt
      (x := (0 : NlsGge.Ramer.actualCMHead c m))
    have hTr' := HasFDerivAt.comp (0 : NlsGge.Ramer.actualCMHead c m) hTr hι
    have hG := (hasFDerivAt_id (0 : NlsGge.Ramer.actualCMHead c m)).add hTr'
    have hG' : HasFDerivAt
        (fun v : NlsGge.Ramer.actualCMHead c m =>
          v + NlsGge.Ramer.cmTrunc c m (K₂ (Sinv (z + NlsGge.Ramer.headToE c s m v)))) _ 0 :=
      HasFDerivAt.congr_of_eventuallyEq hG (Eventually.of_forall fun v => by
        show v + NlsGge.Ramer.cmTrunc c m (K₂ (Sinv (z + NlsGge.Ramer.headToE c s m v))) =
          v + NlsGge.Ramer.cmTrunc c m (K₂ (Sinv (z + i (v : H))))
        rw [r045_headToE_eq c s hs m v])
    rw [hG'.fderiv]
    exact r045_isUnit_head c s hs K₂ L m (Sinv z) e hK hL he (hD _ hyb) _ (fun w => rfl)

end R045Production

end
end NlsGge.ThirdConsultation.R
