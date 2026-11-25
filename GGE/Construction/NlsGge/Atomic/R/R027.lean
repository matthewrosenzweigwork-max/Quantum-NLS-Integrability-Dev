import Mathlib
import NlsGge.Atomic.R.R026
import NlsGge.ThirdConsultation.R.RamerSetting06B
import NlsGge.Ramer.PatchingPrereqs

                                                                                                 
                                                                                                               
                                                                                                                             
                                                                                                   
                                                                                                                      
                                                           
                                                                                                                      
                                                                                                       
                                                                                                       
                                                                                                                                                                                                                                            
                                                                                                                       
                                                                                                                                             
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section LocalClosedDivR027
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s

/-- Scalar bump in the product-rule class: equal to `1` on `B(x₀, rad/2)`, zero off `B(x₀, rad)`. -/
theorem r027_bump (x₀ : E) {rad : ℝ} (hrad : 0 < rad) :
    ∃ η : E → ℝ, ProductRuleClass c s hs η ∧
      (∀ x ∈ ball x₀ (rad / 2), η x = 1) ∧ (∀ x, x ∉ ball x₀ rad → η x = 0) := by
  obtain ⟨η, hηc, hη0, hη1, hηin, hηout, Mη, hMη⟩ :=
    NlsGge.Ramer.exists_bump_generic x₀ (half_pos hrad)
  have hout : ∀ x, x ∉ ball x₀ rad → η x = 0 := by
    intro x hx
    apply hηout x
    rwa [show 2 * (rad / 2) = rad by ring]
  obtain ⟨Ci, _, hCi⟩ := (cmEmbedding c s hs).bound
  have hM0 : 0 ≤ Mη := (norm_nonneg _).trans (hMη x₀)
  refine ⟨η, ?_, hηin, hout⟩
  unfold ProductRuleClass
  refine ⟨hηc, max 1 (Mη * Ci), fun x => ⟨?_, ?_⟩⟩
  · rw [Real.norm_of_nonneg (hη0 x)]
    exact (hη1 x).trans (le_max_left _ _)
  · obtain ⟨v, hv⟩ : ∃ v, v = hgrad c s hs η x := ⟨_, rfl⟩
    rw [← hv]
    have hsq : inner ℝ v v = fderiv ℝ η x (cmEmbedding c s hs v) := by
      rw [hv]
      unfold hgrad
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    have hvv : ‖v‖ * ‖v‖ ≤ (Mη * Ci) * ‖v‖ := by
      calc ‖v‖ * ‖v‖ = inner ℝ v v := (real_inner_self_eq_norm_mul_norm v).symm
        _ = fderiv ℝ η x (cmEmbedding c s hs v) := hsq
        _ ≤ ‖fderiv ℝ η x‖ * ‖cmEmbedding c s hs v‖ :=
          (Real.le_norm_self _).trans (ContinuousLinearMap.le_opNorm _ _)
        _ ≤ Mη * (Ci * ‖v‖) := mul_le_mul (hMη x) (hCi v) (norm_nonneg _) hM0
        _ = (Mη * Ci) * ‖v‖ := by ring
    have hK1 : (Mη * Ci) * ‖v‖ ≤ max 1 (Mη * Ci) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v)
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < ‖v‖ := lt_trans (by norm_num) (lt_of_le_of_lt (le_max_left _ _) hcon)
    have h2 := mul_lt_mul_of_pos_right hcon hpos
    linarith

include hs in
/-- Local form of R-027 at one point of `U`: the two local closed divergences agree a.e. near `x₀`. -/
theorem r027_local (G₁ G₂ : E → H) (d₁ d₂ : E → ℝ) (U : Set E)
    (hEq : EqOn G₁ G₂ U) (h₁ : LocalClosedDiv c s G₁ d₁ U) (h₂ : LocalClosedDiv c s G₂ d₂ U)
    (x₀ : E) (hx₀ : x₀ ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball x₀ r ⊆ U ∧ d₁ =ᵐ[(μ).restrict (ball x₀ r)] d₂ := by
  obtain ⟨r₁, hr₁, hsub₁, Gw₁, e₁, hG1, hcd₁, hae₁⟩ := h₁ x₀ hx₀
  obtain ⟨r₂, hr₂, hsub₂, Gw₂, e₂, hG2, hcd₂, hae₂⟩ := h₂ x₀ hx₀
  obtain ⟨rad, hrad0, hrad₁, hrad₂⟩ : ∃ rad : ℝ, 0 < rad ∧ rad ≤ r₁ ∧ rad ≤ r₂ :=
    ⟨min r₁ r₂, lt_min hr₁ hr₂, min_le_left _ _, min_le_right _ _⟩
  have hballU : ball x₀ rad ⊆ U := (ball_subset_ball hrad₁).trans hsub₁
  have hGw : ∀ x ∈ ball x₀ rad, Gw₁ x = Gw₂ x := by
    intro x hx
    rw [hG1 (ball_subset_ball hrad₁ hx), hG2 (ball_subset_ball hrad₂ hx)]
    exact hEq (hballU hx)
  obtain ⟨η, hηP, hη1, hη0⟩ := r027_bump c s hs x₀ hrad0
  have hfun : (fun x => η x • Gw₂ x) = (fun x => η x • Gw₁ x) := by
    funext x
    by_cases hx : x ∈ ball x₀ rad
    · rw [hGw x hx]
    · simp [hη0 x hx]
  have key : ∀ (G G' : E → H) (d : E → ℝ), G = G' → IsClosedDiv c s G d →
      IsClosedDiv c s G' d := by
    intro G G' d h hd
    subst h
    exact hd
  have hA := IsClosedDiv.smul c s hs Gw₁ e₁ η hcd₁ hηP
  have hB := key _ _ _ hfun (IsClosedDiv.smul c s hs Gw₂ e₂ η hcd₂ hηP)
  have huniq := IsClosedDiv.unique c s hs _ _ _ hA hB
  have hin0 : ∀ x ∈ ball x₀ (rad / 2), ∀ w : H, inner ℝ (hgrad c s hs η x) w = 0 := by
    intro x hx w
    have hev : η =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hx) (fun y hy => hη1 y hy)
    have hD : fderiv ℝ η x = 0 := by
      rw [hev.fderiv_eq, fderiv_fun_const]
      rfl
    unfold hgrad
    rw [InnerProductSpace.toDual_symm_apply]
    simp [hD]
    rfl
  have hf1 : ∀ x ∈ ball x₀ (rad / 2),
      η x * e₁ x - inner ℝ (hgrad c s hs η x) (Gw₁ x) = e₁ x := by
    intro x hx
    rw [hη1 x hx, hin0 x hx (Gw₁ x), one_mul, sub_zero]
  have hf2 : ∀ x ∈ ball x₀ (rad / 2),
      η x * e₂ x - inner ℝ (hgrad c s hs η x) (Gw₂ x) = e₂ x := by
    intro x hx
    rw [hη1 x hx, hin0 x hx (Gw₂ x), one_mul, sub_zero]
  have hmeas : MeasurableSet (ball x₀ (rad / 2)) := measurableSet_ball
  have hae : e₁ =ᵐ[(μ).restrict (ball x₀ (rad / 2))] e₂ := by
    have h1 : ∀ᵐ x ∂(μ).restrict (ball x₀ (rad / 2)),
        η x * e₁ x - inner ℝ (hgrad c s hs η x) (Gw₁ x) =
          η x * e₂ x - inner ℝ (hgrad c s hs η x) (Gw₂ x) :=
      ae_restrict_of_ae huniq
    filter_upwards [h1, ae_restrict_mem hmeas] with x hx hxB
    exact (hf1 x hxB).symm.trans (hx.trans (hf2 x hxB))
  have hq1 : rad / 2 ≤ r₁ := by linarith
  have hq2 : rad / 2 ≤ r₂ := by linarith
  have hsub : ball x₀ (rad / 2) ⊆ ball x₀ rad := ball_subset_ball (by linarith)
  have hd₁ : d₁ =ᵐ[(μ).restrict (ball x₀ (rad / 2))] e₁ :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hq1) hae₁
  have hd₂ : d₂ =ᵐ[(μ).restrict (ball x₀ (rad / 2))] e₂ :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hq2) hae₂
  exact ⟨rad / 2, half_pos hrad0, hsub.trans hballU, hd₁.trans (hae.trans hd₂.symm)⟩

include hs in
/-- **R-027, locality and bump independence** (Pro round 6 head; `hs` explicit, see the file header). -/
theorem local_closedDiv_eq
    (G₁ G₂ : E → H) (d₁ d₂ : E → ℝ) (U : Set E)
    (hG₁ : ContDiff ℝ 2 G₁) (hG₂ : ContDiff ℝ 2 G₂)
    (hEq : EqOn G₁ G₂ U) (hU : IsOpen U)
    (h₁ : LocalClosedDiv c s G₁ d₁ U)
    (h₂ : LocalClosedDiv c s G₂ d₂ U) :
    d₁ =ᵐ[(μ).restrict U] d₂ := by
  have hloc : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
      d₁ =ᵐ[(μ).restrict (ball x r)] d₂ :=
    fun x hx => r027_local c s hs G₁ G₂ d₁ d₂ U hEq h₁ h₂ x hx
  choose! R hR0 hRsub hRae using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun i : U => Metric.ball (i : E) (R i)) (fun _ => Metric.isOpen_ball)
  have hall : (⋃ i : U, Metric.ball (i : E) (R i)) = U := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i => hRsub (i : E) i.2
    · intro x hx
      exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (hR0 x hx)⟩
  have hUeq : U = ⋃ i ∈ T, Metric.ball (i : E) (R i) := hall.symm.trans hTU.symm
  rw [hUeq]
  exact (ae_restrict_biUnion_iff (fun i : U => Metric.ball (i : E) (R i)) hTc
    (fun x => d₁ x = d₂ x)).2 (fun i _ => hRae (i : E) i.2)

end LocalClosedDivR027
end
end NlsGge.ThirdConsultation.R
