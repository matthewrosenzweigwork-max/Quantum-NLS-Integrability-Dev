import Mathlib
import NlsGge.Spectral.ActualActionSumE02_38
import NlsGge.GK38.EigenvalueCompactnessStrong
import NlsGge.GK38.ActionRealScalar
import NlsGge.GK38.PairPotential
import NlsGge.Atomic.LIB.LIB082
import NlsGge.Atomic.PhysicalSobolev
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Atomic.X.X006
import NlsGge.Atomic.G6.G6SupSeparable

                                                                                                                                 
                                                                                                                                   
                                                                                                                     
                                                                                                                                                       
                                                                                                                                                   
                                                                                                                                                    
                                                                                                                       
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev ActionSequence := lp (fun _ : ℤ => ℝ) 1

open scoped Classical in
def actionSequence (u : PhysicalL2) : ActionSequence :=
  if h : Memℓp (fun n => actualGapActionAllE02_38 u n) 1 then
    ⟨fun n => actualGapActionAllE02_38 u n, h⟩ else 0

theorem g6_action_hasSum (u : PhysicalL2) :
    HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖ ^ 2) :=
  (NlsGge.Atomic.ExistingPhysicalFamily.actualPhysicalLocalFamily.Phi_mass u).1

theorem g6_action_mem (u : PhysicalL2) :
    Memℓp (fun n : ℤ => actualGapActionAllE02_38 u n) 1 := by
  rw [memℓp_gen_iff (by norm_num)]
  have h := (g6_action_hasSum u).summable
  simpa [Real.norm_of_nonneg (NlsGge.GK38.actionNonnegative38 u _)] using h

theorem g6_actionSequence_apply (u : PhysicalL2) (n : ℤ) :
    actionSequence u n = actualGapActionAllE02_38 u n := by
  unfold actionSequence
  rw [dif_pos (g6_action_mem u)]

theorem g6_norm_nonneg_lp (I : ActionSequence) (h : ∀ n, 0 ≤ I n) :
    ‖I‖ = ∑' n : ℤ, I n := by
  have := lp.hasSum_norm (p := (1 : ℝ≥0∞)) (by norm_num) I
  have h2 : HasSum (fun n : ℤ => ‖I n‖) ‖I‖ := by simpa using this
  have h3 : (fun n : ℤ => ‖I n‖) = fun n => I n := funext fun n => Real.norm_of_nonneg (h n)
  rw [h3] at h2
  exact h2.tsum_eq.symm

theorem g6_norm_actionSequence (u : PhysicalL2) : ‖actionSequence u‖ = ‖u‖ ^ 2 := by
  rw [g6_norm_nonneg_lp _ (fun n => by rw [g6_actionSequence_apply]; exact NlsGge.GK38.actionNonnegative38 u n)]
  simp_rw [g6_actionSequence_apply]
  exact (g6_action_hasSum u).tsum_eq

theorem g6_lp_coord_tendsto {ι : Type*} {l : Filter ι} (a : ι → ActionSequence) (b : ActionSequence)
    (h : Tendsto a l (𝓝 b)) (n : ℤ) : Tendsto (fun j => a j n) l (𝓝 (b n)) := by
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with j hj
  rw [Real.dist_eq, ← Real.norm_eq_abs]
  have := lp.norm_apply_le_norm (p := (1 : ℝ≥0∞)) (by norm_num) (a j - b) n
  rw [lp.coeFn_sub] at this
  rw [dist_eq_norm] at hj
  simp only [Pi.sub_apply] at this
  exact lt_of_le_of_lt this hj

theorem G6004 (u : ℕ → PhysicalL2) (Istar : ActionSequence)
    (hI : Tendsto (fun j : ℕ => actionSequence (u j)) atTop (𝓝 Istar)) :
  Tendsto (fun j : ℕ => ‖u j‖^2) atTop (𝓝 (∑' n : ℤ, Istar n)) ∧
  Tendsto (fun j : ℕ => potNormSq38 (realSlice (u j))) atTop
    (𝓝 (2 * ∑' n : ℤ, Istar n)) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, ‖u j‖ ≤ C) ∧
  ∃ (v : PhysicalL2) (r : ℕ → ℕ), StrictMono r ∧
    ∀ L : PhysicalL2 →L[ℝ] ℝ, Tendsto (fun j : ℕ => L (u (r j))) atTop (𝓝 (L v)) := by
  have hnn : ∀ n, 0 ≤ Istar n := fun n =>
    ge_of_tendsto' (g6_lp_coord_tendsto _ _ hI n) fun j => by
      rw [g6_actionSequence_apply]; exact NlsGge.GK38.actionNonnegative38 _ n
  have h1 : Tendsto (fun j : ℕ => ‖u j‖ ^ 2) atTop (𝓝 (∑' n : ℤ, Istar n)) := by
    rw [← g6_norm_nonneg_lp Istar hnn]
    have := hI.norm
    simpa only [g6_norm_actionSequence] using this
  have h2 : Tendsto (fun j : ℕ => potNormSq38 (realSlice (u j))) atTop
      (𝓝 (2 * ∑' n : ℤ, Istar n)) := by
    simp_rw [potNormSq38_realSlice]
    exact h1.const_mul 2
  have hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, ‖u j‖ ≤ C := by
    obtain ⟨M, hM⟩ := h1.bddAbove_range
    refine ⟨Real.sqrt (max M 0), Real.sqrt_nonneg _, fun j => ?_⟩
    have : ‖u j‖ ^ 2 ≤ max M 0 := (hM ⟨j, rfl⟩).trans (le_max_left _ _)
    calc ‖u j‖ = Real.sqrt (‖u j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt this
  obtain ⟨C, hC0, hC⟩ := hb
  refine ⟨h1, h2, ⟨C, hC0, hC⟩, ?_⟩
  haveI := NlsGge.Atomic.G6Sup.physicalL2_separable
  obtain ⟨s, hs, v, hv⟩ := NlsGge.Atomic.LIB.bounded_hilbert_weak_subsequence (E := PhysicalL2) u ⟨C, hC⟩
  refine ⟨v, s, hs, fun L => ?_⟩
  have := hv ((InnerProductSpace.toDual ℝ PhysicalL2).symm L)
  simpa [InnerProductSpace.toDual_symm_apply] using this

end
end NlsGge.GKDefinitionDesign
