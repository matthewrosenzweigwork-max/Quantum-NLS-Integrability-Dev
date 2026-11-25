import Mathlib
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST031
import NlsGge.Atomic.KST.KST036
import NlsGge.Atomic.KST.KST037
import NlsGge.Atomic.KST.KST038
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST039Host

/- KST-039 PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/Atomic/KST/KST039.lean,
   namespace NlsGge.ThirdConsultation.KST.  Head VERBATIM from design STATEMENTS/KST.md "## KST-039"
   (gpt6pro_followup10; no Pro round 5-12 entry touches KST-039).  No repair of the head.
   Route (source Proposition 5.1/(66)): by KST-037 ||dF - id|| <= 1/8 < 1 on the closed componentwise M ball, so dF is
   a unit (Neumann series, Mathlib `isUnit_one_sub_of_norm_lt_one`).  F is analytic on the open 2M ball (KST-036),
   hence strictly differentiable at each x0 of U; the inverse function theorem
   (`HasStrictFDerivAt.toOpenPartialHomeomorph`) gives a local homeomorphism R = F with R.symm analytic at F x0
   (`OpenPartialHomeomorph.hasFPowerSeriesAt_symm`).  By KST-038 injectivity on the closed M ball, the selected
   inverse `adaptedInverse` agrees with R.symm near F x0 (overlap agreement), so it is analytic on F '' U, and F '' U
   is open as a union of images of open sets. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST002

namespace NlsGge.ThirdConsultation.KST

theorem kst039_adaptedInverse_left (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (M : ℝ) (N : ℕ)
    (hinj : Set.InjOn (adaptedFourier ω hω N) (componentBall ω M))
    {x : Weighted ω} (hx : x ∈ componentBall ω M) :
    adaptedInverse ω hω M N (adaptedFourier ω hω N x) = x := by
  have h : ∃ x' ∈ componentBall ω M, adaptedFourier ω hω N x' = adaptedFourier ω hω N x := ⟨x, hx, rfl⟩
  unfold adaptedInverse
  rw [dif_pos h]
  exact hinj (Classical.choose_spec h).1 hx (Classical.choose_spec h).2

theorem kst039_componentOpenBall_isOpen (ω : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)] (R : ℝ) :
    IsOpen (componentOpenBall ω R) := by
  have : componentOpenBall ω R = ⋂ ch : Bool, {x : Weighted ω | ‖x ch‖ < R} := by
    ext x; simp [componentOpenBall]
  rw [this]
  refine isOpen_iInter_of_finite fun ch => ?_
  exact isOpen_lt (by fun_prop) continuous_const

theorem kst039 (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (v : ℤ → ℝ) (hv : SecondaryWeight v) :
  let ω := productWeight w v
  let hω := productOneLe hw.one_le hv.1.1
  letI := weightFact ω hω
  let F := adaptedFourier ω hω (adaptedThreshold w M)
  let G := adaptedInverse ω hω M (adaptedThreshold w M)
  let U := componentOpenBall ω M
  (∀ x ∈ componentBall ω M, IsUnit (fderiv ℂ F x)) ∧
  IsOpen (F '' U) ∧ AnalyticOnNhd ℂ G (F '' U) ∧
  (∀ x ∈ U, G (F x) = x) ∧
  (∀ y ∈ F '' U, G y ∈ U ∧ F (G y) = y) := by
  intro ω hω
  letI := weightFact ω hω
  intro F G U
  have hM0 : 0 < M := by linarith
  have h36 : AnalyticOnNhd ℂ F (componentOpenBall ω (2*M)) := kst036 w Cw M hM hw hunbounded v hv
  have h37 := kst037 w Cw M hM hw hunbounded v hv
  have hinj : Set.InjOn F (componentBall ω M) := (kst038 w Cw M hM hw hunbounded v hv).2.1
  have hUsub : U ⊆ componentBall ω M := fun x hx ch => (hx ch).le
  have hUsub2 : U ⊆ componentOpenBall ω (2*M) := fun x hx ch => lt_of_lt_of_le (hx ch) (by linarith)
  have hUopen : IsOpen U := kst039_componentOpenBall_isOpen ω M
  have hunit : ∀ x ∈ componentBall ω M, IsUnit (fderiv ℂ F x) := by
    intro x hx
    have hb : ‖ContinuousLinearMap.id ℂ (Weighted ω) - fderiv ℂ F x‖ < 1 := by
      rw [norm_sub_rev]; exact lt_of_le_of_lt (h37 x hx).2 (by norm_num)
    have h1 := isUnit_one_sub_of_norm_lt_one hb
    have e : (1 : Weighted ω →L[ℂ] Weighted ω) -
        (ContinuousLinearMap.id ℂ (Weighted ω) - fderiv ℂ F x) = fderiv ℂ F x := by
      ext z; simp
    rwa [e] at h1
  have hleft : ∀ x ∈ componentBall ω M, G (F x) = x := fun x hx =>
    kst039_adaptedInverse_left ω hω M (adaptedThreshold w M) hinj hx
  -- local inverse data at each point of U
  have key : ∀ x0 ∈ U, ∃ R : OpenPartialHomeomorph (Weighted ω) (Weighted ω),
      x0 ∈ R.source ∧ (∀ z, R z = F z) ∧ AnalyticAt ℂ R.symm (F x0) := by
    intro x0 hx0
    have han : AnalyticAt ℂ F x0 := h36 x0 (hUsub2 hx0)
    obtain ⟨u, hu⟩ := hunit x0 (hUsub hx0)
    let i : Weighted ω ≃L[ℂ] Weighted ω := ContinuousLinearEquiv.unitsEquiv ℂ (Weighted ω) u
    have hi : (i : Weighted ω →L[ℂ] Weighted ω) = fderiv ℂ F x0 := by
      ext z
      simp [i, ContinuousLinearEquiv.unitsEquiv_apply, ← hu]
    have hfd : HasStrictFDerivAt F (i : Weighted ω →L[ℂ] Weighted ω) x0 := by
      rw [hi]; exact han.hasStrictFDerivAt
    let R : OpenPartialHomeomorph (Weighted ω) (Weighted ω) := hfd.toOpenPartialHomeomorph F
    have hRc : ∀ z, R z = F z := fun z => by
      have := hfd.toOpenPartialHomeomorph_coe
      exact congrFun this z
    have hxR : x0 ∈ R.source := hfd.mem_toOpenPartialHomeomorph_source
    obtain ⟨p, hp⟩ := han
    have hpR : HasFPowerSeriesAt R p x0 :=
      hp.congr (Filter.Eventually.of_forall fun z => (hRc z).symm)
    have hp1 : p 1 = (continuousMultilinearCurryFin1 ℂ (Weighted ω) (Weighted ω)).symm i := by
      have h1 := hp.fderiv_eq
      rw [← hi] at h1
      rw [LinearIsometryEquiv.eq_symm_apply]
      exact h1.symm
    refine ⟨R, hxR, hRc, ?_⟩
    have h2 := (R.hasFPowerSeriesAt_symm hxR hpR hp1).analyticAt
    rwa [hRc x0] at h2
  refine ⟨hunit, ?_, ?_, ?_, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨x0, hx0, rfl⟩
    obtain ⟨R, hxR, hRc, -⟩ := key x0 hx0
    have hop : IsOpen (R '' (U ∩ R.source)) :=
      R.isOpen_image_of_subset_source (hUopen.inter R.open_source) Set.inter_subset_right
    have hsub : R '' (U ∩ R.source) ⊆ F '' U := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, hz.1, (hRc z).symm⟩
    refine Filter.mem_of_superset (hop.mem_nhds ?_) hsub
    exact ⟨x0, ⟨hx0, hxR⟩, hRc x0⟩
  · rintro _ ⟨x0, hx0, rfl⟩
    obtain ⟨R, hxR, hRc, hana⟩ := key x0 hx0
    refine hana.congr ?_
    have hT : R.target ∈ 𝓝 (F x0) := by
      rw [← hRc x0]; exact R.open_target.mem_nhds (R.map_source hxR)
    have hcont : ContinuousAt R.symm (R x0) := R.continuousAt_symm (R.map_source hxR)
    have hUn : U ∈ 𝓝 (R.symm (R x0)) := by
      rw [R.left_inv hxR]; exact hUopen.mem_nhds hx0
    have hV : R.symm ⁻¹' U ∈ 𝓝 (F x0) := by
      rw [← hRc x0]; exact hcont.preimage_mem_nhds hUn
    filter_upwards [hT, hV] with y hyT hyV
    have hFy : F (R.symm y) = y := by rw [← hRc]; exact R.right_inv hyT
    have := hleft (R.symm y) (hUsub hyV)
    rw [hFy] at this
    exact this.symm
  · intro x hx; exact hleft x (hUsub hx)
  · rintro _ ⟨x, hx, rfl⟩
    rw [hleft x (hUsub hx)]
    exact ⟨hx, rfl⟩

end NlsGge.ThirdConsultation.KST
end
