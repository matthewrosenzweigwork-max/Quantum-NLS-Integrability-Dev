import Mathlib
import NlsGge.Atomic.G5.G5028Sup1
import NlsGge.Atomic.G5.G5028Sup2
import NlsGge.Atomic.G5.G5028Sup3
import NlsGge.Atomic.G6.G6020
import NlsGge.Atomic.G1.G1072
import NlsGge.Atomic.G5.G5018Asm
import NlsGge.Atomic.G5.G5018Dir
import NlsGge.Atomic.G5.G5001Host
import NlsGge.Atomic.G5.G5017Host
import NlsGge.GK38.DirichletRealContinuity

                                                                              
                                                                           
                                                                                                                  
                               
                                                                                                       
                                                                                                                                     
                                                                                                              
                                                                                                  
                                                                                                                              
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonMixed38 NlsGge.GK38.PoissonDirichlet38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5028 (k l : ℤ) (hkl : k ≠ l)
    (u₀ : PhysicalL2) (u : ℕ → PhysicalL2)
    (hk : gamma2 (realSlice u₀) k ≠ 0) (hl : gamma2 (realSlice u₀) l ≠ 0)
    (hleftk : gkMu u₀ k = actualGapLowerAllE02_38 u₀ k)
    (hleftl : gkMu u₀ l = actualGapLowerAllE02_38 u₀ l)
    (hiso : ∀ j : ℕ, u j ∈ isospectralSet u₀)
    (hinterior : ∀ j : ℕ, InteriorRealDirichletGap k (u j) ∧
      InteriorRealDirichletGap l (u j)) (hlim : Tendsto u atTop (𝓝 u₀)) :
  (∀ j : ℕ, antiDiscrim (realSlice (u j)) (muSeq (realSlice (u j)) k) ≠ 0 ∧
    antiDiscrim (realSlice (u j)) (muSeq (realSlice (u j)) l) ≠ 0) ∧
  Tendsto (fun j : ℕ =>
    let φ := realSlice (u j)
    pairPoisson (fun ψ => muSeq ψ k) (fun ψ => lamMinus ψ l) φ /
      (antiDiscrim φ (muSeq φ k) * antiDiscrim φ (muSeq φ l))) atTop (𝓝 0) := by
  refine ⟨fun j => ⟨g5018_antiDiscrim_ne_zero (u j) k (hinterior j).1,
    g5018_antiDiscrim_ne_zero (u j) l (hinterior j).2⟩, ?_⟩
  have hD : ∀ j : ℕ, discrim (realSlice (u j)) = discrim (realSlice u₀) :=
    fun j => funext (hiso j)
  have hPer : ∀ j : ℕ, perChar (realSlice (u j)) = perChar (realSlice u₀) := fun j => by
    funext z; simp only [perChar_eq, hiso j z]
  have hlamj : ∀ j : ℕ, lamMinus (realSlice (u j)) l = lamMinus (realSlice u₀) l := fun j => by
    unfold lamMinus; rw [lamSeq_eq_of_perChar_eq38 (hPer j)]
  obtain ⟨hL0, hLroot, hLsimple⟩ := NlsGge.Atomic.G5028.lower_endpoint_simple u₀ l hl
  obtain ⟨hK0, -, -⟩ := NlsGge.Atomic.G5028.lower_endpoint_simple u₀ k hk
  have hLLk : lamMinus (realSlice u₀) l ≠ lamMinus (realSlice u₀) k :=
    (NlsGge.Atomic.G5028.lamMinus_ne_of_open u₀ k l hkl hk hl).symm
  generalize lamMinus (realSlice u₀) l = L at hL0 hLroot hLsimple hlamj hLLk
  generalize lamMinus (realSlice u₀) k = Lk at hK0 hLLk
  have hmu := NlsGge.Atomic.G5028.mu_tendsto u₀ u hlim
  have ek : muSeq (realSlice u₀) k = Lk := by rw [muSeq_eq_gkMu38, hleftk, hK0]
  have el : muSeq (realSlice u₀) l = L := by rw [muSeq_eq_gkMu38, hleftl, hL0]
  have hmuk : Tendsto (fun j : ℕ => muSeq (realSlice (u j)) k) atTop (𝓝 Lk) := by
    simpa only [ek] using hmu k
  have hmul : Tendsto (fun j : ℕ => muSeq (realSlice (u j)) l) atTop (𝓝 L) := by
    simpa only [el] using hmu l
  have hφ : Tendsto (fun j : ℕ => realSlice (u j)) atTop (𝓝 (realSlice u₀)) :=
    (realSlice.continuous.tendsto u₀).comp hlim
  obtain ⟨C, hC⟩ := NlsGge.Atomic.G5028.dirichlet_lipschitz_along (fun j : ℕ => realSlice (u j))
    (realSlice u₀) (fun j : ℕ => muSeq (realSlice (u j)) l) L hφ hmul
    (fun j => muSeq_root38 _ l)
  have hD0 : deriv (dirichletChar (realSlice u₀)) Lk ≠ 0 := by
    rw [← ek]; exact (g5018dir_simple u₀ k).2
  obtain ⟨hTpos, hTev⟩ := NlsGge.Atomic.G5028.T_event u₀ u hlim k L Lk hmuk hLLk hD0
  have hne : ∀ᶠ j : ℕ in atTop, muSeq (realSlice (u j)) k ≠ L := hmuk.eventually_ne hLLk.symm
  have hPdiff : DifferentiableAt ℂ (perChar (realSlice u₀)) L := by
    have : perChar (realSlice u₀) = fun z => discrim (realSlice u₀) z ^ 2 - 4 :=
      funext fun z => perChar_eq _ _
    rw [this]
    exact (((analyticOnNhd_discrim_z _ L (mem_univ _)).differentiableAt).pow 2).sub_const 4
  obtain ⟨c, hc, hcev⟩ := NlsGge.Atomic.G5028.simple_zero_lower (perChar (realSlice u₀)) L hLroot
    hPdiff hLsimple
  have hcev' : ∀ᶠ j : ℕ in atTop, c * ‖muSeq (realSlice (u j)) l - L‖ ≤
      ‖perChar (realSlice (u j)) (muSeq (realSlice (u j)) l)‖ := by
    filter_upwards [hmul.eventually hcev] with j hj
    rwa [hPer j]
  have hΔ' : deriv (discrim (realSlice u₀)) L ≠ 0 :=
    periodic_simple_discrim_nonzero _ L hLsimple
  have hΔn : 0 < ‖deriv (discrim (realSlice u₀)) L‖ := norm_pos_iff.mpr hΔ'
  refine Tendsto.congr (fun j => (NlsGge.Atomic.G5028.hform_aux (u j) u₀ k l (hinterior j).1
    (hinterior j).2 (hD j) L (hlamj j)).symm) ?_
  exact NlsGge.Atomic.G5028.core_limit u₀ u k l L (deriv (discrim (realSlice u₀)) L) _ c C
    (fun j => (hinterior j).2) hΔn hc hTpos hmul hne hC (hTev) hcev'

end
end NlsGge.GKDefinitionDesign
