import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Ramer.RamerLemma54

                                                                                                           
                                                                                                             
                                                                                                                    
                                                                                                                  
                                                                                                             
                                                                                                     
                                                                                                     
                                                                                                                
                                                               
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

/-- The Pro-level Jacobian `ramerJac` of the ActualRamerSetting host is the production Jacobian. -/
theorem r049_J_eq
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (M : RamerE c s → RamerH c) (x : RamerE c s) :
    ramerJac c s hs M x = NlsGge.Ramer.ramerJac c s hs M x :=
  (NlsGge.Ramer.ramerJac_eq c s hs M x).symm

/-- First nested limit for the fixed finite-rank outer field `F = P_m G`, with no null-set hypothesis:
a.e. `J^{K + F o T}(x) = Jc(T x) * J^K(x)` where `Jc` is the everywhere continuous finite-divergence
representative of `J^F`. -/
theorem r049_compField_proj_ae_cont
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (m : ℕ)
    (G K : RamerE c s → RamerH c) (hG : ContDiff ℝ 2 G) (hK : ContDiff ℝ 2 K) :
    ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s),
      NlsGge.Ramer.ramerJac c s hs
          (NlsGge.Ramer.compField c s hs K (NlsGge.Ramer.projField m G)) x =
        NlsGge.Ramer.ramerJE c s hs (NlsGge.Ramer.projField m G)
            (NlsGge.Ramer.ramerA c s (NlsGge.Ramer.zero_le_of_half_lt hs) m
              (NlsGge.Ramer.projField m G))
            (NlsGge.Ramer.TM c s hs K x) *
          NlsGge.Ramer.ramerJac c s hs K x := by
  obtain ⟨κ, hκ, hdiv⟩ := NlsGge.Ramer.ramerDiv_projField_subseq c s hs K hK
  have hdiv' : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => NlsGge.Ramer.ramerDiv c s hs (NlsGge.Ramer.projField (κ j) K) z) atTop
        (𝓝 (NlsGge.Ramer.ramerDiv c s hs K z)) := hdiv.mono fun z h => h.2
  have A := NlsGge.Ramer.tendsto_ramerJac_compField_proj c s hs m G K hG hK κ hκ hdiv'
  have D := NlsGge.Ramer.tendsto_ramerJac_projField_ae c s hs K hK κ hκ hdiv'
  have hGm : ContDiff ℝ 2 (NlsGge.Ramer.projField m G) := NlsGge.Ramer.contDiff_projField m G hG
  have C : ∀ x : RamerE c s,
      Tendsto (fun j => NlsGge.Ramer.ramerJE c s hs (NlsGge.Ramer.projField m G)
          (NlsGge.Ramer.ramerA c s (NlsGge.Ramer.zero_le_of_half_lt hs) m
            (NlsGge.Ramer.projField m G))
          (NlsGge.Ramer.TM c s hs (NlsGge.Ramer.projField (κ j) K) x)) atTop
        (𝓝 (NlsGge.Ramer.ramerJE c s hs (NlsGge.Ramer.projField m G)
          (NlsGge.Ramer.ramerA c s (NlsGge.Ramer.zero_le_of_half_lt hs) m
            (NlsGge.Ramer.projField m G))
          (NlsGge.Ramer.TM c s hs K x))) := fun x =>
    (((NlsGge.Ramer.continuous_ramerJE_ramerA c s hs m _ (hGm.of_le (by norm_num))).tendsto _).comp
      ((NlsGge.Ramer.tendsto_TM_projField c s hs K x).comp hκ.tendsto_atTop))
  have B : ∀ᵐ x ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s), ∀ j : ℕ,
      NlsGge.Ramer.ramerJac c s hs
          (NlsGge.Ramer.compField c s hs (NlsGge.Ramer.projField (κ j) K)
            (NlsGge.Ramer.projField m G)) x =
        NlsGge.Ramer.ramerJE c s hs (NlsGge.Ramer.projField m G)
            (NlsGge.Ramer.ramerA c s (NlsGge.Ramer.zero_le_of_half_lt hs) m
              (NlsGge.Ramer.projField m G))
            (NlsGge.Ramer.TM c s hs (NlsGge.Ramer.projField (κ j) K) x) *
          NlsGge.Ramer.ramerJac c s hs (NlsGge.Ramer.projField (κ j) K) x := by
    refine ae_all_iff.2 fun j => ?_
    have h₁ : ContDiff ℝ 2 (NlsGge.Ramer.projField (κ j) K) :=
      NlsGge.Ramer.contDiff_projField (κ j) K hK
    have hm₁ : ∀ x, NlsGge.Ramer.headProj c (max (κ j) m)
        (NlsGge.Ramer.projField (κ j) K x) = NlsGge.Ramer.projField (κ j) K x :=
      fun x => NlsGge.Ramer.headProj_projField_of_le (le_max_left _ _) K x
    have hm₂ : ∀ x, NlsGge.Ramer.headProj c (max (κ j) m)
        (NlsGge.Ramer.projField m G x) = NlsGge.Ramer.projField m G x :=
      fun x => NlsGge.Ramer.headProj_projField_of_le (le_max_right _ _) G x
    have h12 := NlsGge.Ramer.contDiff_compField c s hs _ _ h₁ hGm
    have hm12 := NlsGge.Ramer.headProj_compField c s hs _ _ hm₁ hm₂
    have a12 := NlsGge.Ramer.ramerDiv_coordE_ae_eq c s hs _ h12 hm12
    have a1 := NlsGge.Ramer.ramerDiv_coordE_ae_eq c s hs _ h₁ hm₁
    have hst : NlsGge.Ramer.ramerA c s (NlsGge.Ramer.zero_le_of_half_lt hs) (max (κ j) m)
        (NlsGge.Ramer.projField m G) =
        NlsGge.Ramer.ramerA c s (NlsGge.Ramer.zero_le_of_half_lt hs) m
          (NlsGge.Ramer.projField m G) :=
      NlsGge.Ramer.ramerA_eq_of_headValued (NlsGge.Ramer.zero_le_of_half_lt hs)
        (NlsGge.Ramer.projField m G) (hGm.differentiable (by norm_num))
        (fun x => NlsGge.Ramer.headProj_idem _ _) (le_max_right _ _)
    filter_upwards [a12, a1] with x x12 x1
    have key := NlsGge.Ramer.ramerJE_compField c s hs _ _ (h₁.of_le (by norm_num))
      (hGm.of_le (by norm_num)) hm₁ hm₂ x
    rw [hst] at key
    simp only [NlsGge.Ramer.ramerJac, NlsGge.Ramer.ramerJE_eq]
    rw [x12, x1]
    simp only [NlsGge.Ramer.ramerJE_eq] at key
    exact key
  filter_upwards [A, D, B] with x hA hD hB
  have lim2 := (C x).mul hD
  exact tendsto_nhds_unique hA (lim2.congr (fun j => (hB j).symm))

section R049Production
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "i" => cmEmbedding c s hs
local notation "J" => ramerJac c s hs
local notation "Smap" => TM c s hs

theorem ramerJac_compField_ae_on
    (K G : E → H) (hK : ContDiff ℝ 2 K) (hG : ContDiff ℝ 2 G)
    (m : ℕ) (U : Set E)
    (hNull : NullPreservingOn μ (Smap K) U) :
    ∀ᵐ x ∂μ, x ∈ U →
      J (fun y : E => K y + projField c s m G (Smap K y)) x =
        J (projField c s m G) (Smap K x) * J K x := by
  have hmain := r049_compField_proj_ae_cont c s hs m G K hG hK
  have hGm : ContDiff ℝ 2 (NlsGge.Ramer.projField m G) := NlsGge.Ramer.contDiff_projField m G hG
  have hae := NlsGge.Ramer.ramerDiv_coordE_ae_eq c s hs (NlsGge.Ramer.projField m G) hGm
    (fun x => NlsGge.Ramer.headProj_idem _ _)
  have a0 := NlsGge.Ramer.ae_on_comp (U := U) (T := NlsGge.Ramer.TM c s hs K) hNull hae
  filter_upwards [hmain, a0] with x h1 h2 hxU
  have hdiv : NlsGge.Ramer.ramerDiv c s hs (NlsGge.Ramer.projField m G)
      (NlsGge.Ramer.coordE c s (NlsGge.Ramer.TM c s hs K x)) =
      NlsGge.Ramer.ramerA c s (NlsGge.Ramer.zero_le_of_half_lt hs) m
        (NlsGge.Ramer.projField m G) (NlsGge.Ramer.coordE c s (NlsGge.Ramer.TM c s hs K x)) :=
    h2 hxU
  have e1 : ramerJac c s hs (fun y : E => K y + projField c s m G (TM c s hs K y)) x =
      NlsGge.Ramer.ramerJac c s hs
        (NlsGge.Ramer.compField c s hs K (NlsGge.Ramer.projField m G)) x :=
    r049_J_eq c s hs _ x
  have e2 : ramerJac c s hs (projField c s m G) (TM c s hs K x) =
      NlsGge.Ramer.ramerJE c s hs (NlsGge.Ramer.projField m G)
        (NlsGge.Ramer.ramerA c s (NlsGge.Ramer.zero_le_of_half_lt hs) m
          (NlsGge.Ramer.projField m G)) (NlsGge.Ramer.TM c s hs K x) := by
    have h0 : ramerJac c s hs (projField c s m G) (TM c s hs K x) =
        NlsGge.Ramer.ramerJac c s hs (NlsGge.Ramer.projField m G)
          (NlsGge.Ramer.TM c s hs K x) := r049_J_eq c s hs _ _
    rw [h0, NlsGge.Ramer.ramerJac_eq, NlsGge.Ramer.ramerJE_eq, hdiv]
  rw [e1, e2, r049_J_eq c s hs K x]
  exact h1

end R049Production

end
end NlsGge.ThirdConsultation.R
