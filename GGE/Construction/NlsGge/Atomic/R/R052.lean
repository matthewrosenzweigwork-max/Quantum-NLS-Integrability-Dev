import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Atomic.R.R046
import NlsGge.Atomic.R.R047
import NlsGge.Ramer.RamerLemma54Eventually

                                                                                                           
                                                                                                             
                                                                                                                   
                                                                                                                      
                                                                                                                      
                                                                           
                                                                                                                
                                                                                                                   
                                                                                                               
                                                                                                            
                                                                                                                
                                                                                                     
                                                                                                                    
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

section R052Production
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "i" => cmEmbedding c s hs
local notation "J" => ramerJac c s hs
local notation "Smap" => TM c s hs

theorem ramerJac_comp_mul_eq_one_eventually
    (T : E ≃ₜ E) (K Kinv : E → H)
    (hT : RamerHomeomorphismData c s hs T K Kinv) :
    (∀ x : E, Kinv (T x) = -K x) ∧
    ∀ᵐ x ∂μ, J Kinv (T x) * J K x = 1 := by
  have hs0 : 0 ≤ s := le_of_lt (by linarith : (0 : ℝ) < s)
  have hinj : Function.Injective i :=
    NlsGge.Ramer.cmToFullWeightedHilbert_injective c s hs0
  obtain ⟨hK, hKi, hTK, hTKi⟩ := hT
  have hT' : ∀ x : E, T x = x + i (K x) := fun x => hTK x
  have hTi' : ∀ y : E, T.symm y = y + i (Kinv y) := fun y => hTKi y
  -- (1) the pointwise cancellation
  have hfirst : ∀ x : E, Kinv (T x) = -K x := by
    intro x
    have h1 := hTi' (T x)
    rw [T.symm_apply_apply] at h1
    have h2 : i (Kinv (T x)) = i (-K x) := by
      rw [map_neg]
      have h3 : x + i (K x) + i (Kinv (T x)) = x := by
        rw [← hT' x]; exact h1.symm
      have h4 : i (K x) + i (Kinv (T x)) = 0 := by
        have : x + (i (K x) + i (Kinv (T x))) = x + 0 := by
          rw [add_zero, ← add_assoc]; exact h3
        exact add_left_cancel this
      exact eq_neg_of_add_eq_zero_right h4
    exact hinj h2
  refine ⟨hfirst, ?_⟩
  -- (2)-(3) local statement around every point
  have hloc : ∀ x₀ : E, ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧
      ∀ᵐ x ∂μ, x ∈ V → J Kinv (T x) * J K x = 1 := by
    intro x₀
    have hU1 : IsUnit (1 + (hsDerivH c s hs K x₀).toCLM) :=
      (NlsGge.Ramer.step10_isUnit c s hs T K Kinv hT' hTi'
        (hK.of_le (by norm_num)) (hKi.of_le (by norm_num)) x₀).1
    obtain ⟨U, hUo, hxU, hnullU⟩ :=
      local_null_preserving c s hs T K Kinv ⟨hK, hKi, hTK, hTKi⟩ x₀
    obtain ⟨r, hr, hev⟩ := projField_nullPres_eventually c s hs K hK x₀ hU1
    refine ⟨U ∩ ball x₀ r, hUo.inter isOpen_ball, ⟨hxU, mem_ball_self hr⟩, ?_⟩
    have hTm : (Smap K) = ⇑T := (funext hT').symm
    have hNull : ∀ A : Set E, μ A = 0 → μ ((U ∩ ball x₀ r) ∩ (Smap K) ⁻¹' A) = 0 := by
      intro A hA
      refine measure_mono_null ?_ (hnullU A hA)
      intro y hy
      rw [hTm] at hy
      exact ⟨hy.1.1, hy.2⟩
    have hTrunc : ∀ᶠ N : ℕ in atTop, ∀ A : Set E, μ A = 0 →
        μ ((U ∩ ball x₀ r) ∩ (Smap (projField c s N K)) ⁻¹' A) = 0 := by
      filter_upwards [hev] with N hN A hA
      refine measure_mono_null ?_ (hN A hA)
      intro y hy
      exact ⟨hy.1.2, hy.2⟩
    have hGT : ∀ x ∈ U ∩ ball x₀ r, Kinv (Smap K x) = -K x := by
      intro x _
      have : Smap K x = T x := (hT' x).symm
      rw [this]; exact hfirst x
    have hmain := NlsGge.Ramer.ramerJac_comp_mul_eq_one_eventually c s hs (U ∩ ball x₀ r)
      (hUo.inter isOpen_ball) K Kinv hK hKi hNull hTrunc hGT
    have eJ : ∀ (M : E → H) (x : E), ramerJac c s hs M x = NlsGge.Ramer.ramerJac c s hs M x :=
      fun M x => (NlsGge.Ramer.ramerJac_eq c s hs M x).symm
    filter_upwards [hmain] with x hx hxV
    rw [eJ, eJ K]
    have : T x = Smap K x := hT' x
    rw [this]
    exact hx hxV
  -- (4) countable subcover and patching
  choose V hVo hxV hVae using hloc
  obtain ⟨t, htc, hcov⟩ := TopologicalSpace.countable_cover_nhds
    (f := V) (fun x => (hVo x).mem_nhds (hxV x))
  have hall : ∀ᵐ x ∂μ, ∀ y ∈ t, x ∈ V y → J Kinv (T x) * J K x = 1 :=
    (ae_ball_iff htc).2 fun y _ => hVae y
  filter_upwards [hall] with x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcov ▸ mem_univ x)
  exact hx y hy hxy

end R052Production

end
end NlsGge.ThirdConsultation.R
