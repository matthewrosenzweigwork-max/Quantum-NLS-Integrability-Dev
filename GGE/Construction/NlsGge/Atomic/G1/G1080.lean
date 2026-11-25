import Mathlib
import NlsGge.Atomic.G2.G2041
import NlsGge.Atomic.G6.G6020
import NlsGge.Atomic.G6.G6SupSeparable
import NlsGge.Atomic.LIB.LIB082
import NlsGge.GK38.PairCompact
import NlsGge.GK38.DirichletRealWeakTransport

                                                                                                                                         
                                                                                                                                           
                                                                
                                                                                                                                          
                                                                                                                         
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g1080_norm_eq (u v : PhysicalL2) (h : v ∈ isospectralSet u) : ‖v‖ = ‖u‖ :=
  (G2_041 u v (fun z => (h z).symm)).symm

theorem g1080_inner_split (w y : PhysicalL2) :
    inner ℂ w y = (((inner ℂ w y).re : ℝ) : ℂ) + (((inner ℂ ((Complex.I : ℂ) • w) y).re : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp
  · simp [inner_smul_left]

theorem g1080_weakLim_of_re {x : ℕ → PhysicalL2} {v : PhysicalL2}
    (h : ∀ w : PhysicalL2, Tendsto (fun n => (inner ℂ w (x n)).re) atTop (𝓝 (inner ℂ w v).re)) :
    IsWeakLim x v := by
  intro w
  have key := (((Complex.continuous_ofReal.tendsto _).comp (h w)).add
    (((Complex.continuous_ofReal.tendsto _).comp (h ((Complex.I : ℂ) • w))).mul_const Complex.I))
  refine Tendsto.congr (fun n => (g1080_inner_split w (x n)).symm) ?_
  rw [g1080_inner_split w v]
  exact key

theorem g1080_compact (u : PhysicalL2) : IsCompact (isospectralSet u) := by
  haveI := NlsGge.Atomic.G6Sup.physicalL2_separable
  refine IsSeqCompact.isCompact ?_
  intro x hx
  have hb : ∃ C : ℝ, ∀ n, ‖x n‖ ≤ C := ⟨‖u‖, fun n => (g1080_norm_eq u _ (hx n)).le⟩
  obtain ⟨s, hs, v, hv⟩ : ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ v : PhysicalL2, ∀ w : PhysicalL2,
      Tendsto (fun n => (inner ℂ w (x (s n))).re) atTop (𝓝 (inner ℂ w v).re) := by
    letI : InnerProductSpace ℝ PhysicalL2 := InnerProductSpace.rclikeToReal ℂ PhysicalL2
    exact NlsGge.Atomic.LIB.bounded_hilbert_weak_subsequence (E := PhysicalL2) x hb
  have hw : IsWeakLim (x ∘ s) v := g1080_weakLim_of_re hv
  have hD := discrim_weakContinuous (weakLim_realSlice38 hw)
  have hvS : v ∈ isospectralSet u := by
    intro z
    have h1 : Tendsto (fun k => discrim (realSlice (x (s k))) z) atTop (𝓝 (discrim (realSlice v) z)) :=
      (hD.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ z)
    have h2 : (fun k => discrim (realSlice (x (s k))) z) = fun _ => discrim (realSlice u) z :=
      funext fun k => hx (s k) z
    rw [h2] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  refine ⟨v, hvS, s, hs, ?_⟩
  have hnv : ‖v‖ = ‖u‖ := g1080_norm_eq u v hvS
  have hin : Tendsto (fun k => (inner ℂ (x (s k)) v).re) atTop (𝓝 (inner ℂ v v).re) := by
    have e1 : ∀ y : PhysicalL2, (inner ℂ y v).re = (inner ℂ v y).re := fun y => by
      rw [← inner_conj_symm (𝕜 := ℂ) v y, Complex.conj_re]
    simp_rw [e1]
    exact hv v
  have hsq : Tendsto (fun k => ‖x (s k) - v‖ ^ 2) atTop (𝓝 0) := by
    have e : ∀ k, ‖x (s k) - v‖ ^ 2 = ‖x (s k)‖ ^ 2 - 2 * (inner ℂ (x (s k)) v).re + ‖v‖ ^ 2 :=
      fun k => norm_sub_sq (𝕜 := ℂ) _ _
    simp_rw [e, hnv, g1080_norm_eq u _ (hx _)]
    have := ((tendsto_const_nhds (x := ‖u‖ ^ 2)).sub (hin.const_mul 2)).add_const (‖v‖ ^ 2)
    have hvv : (inner ℂ v v).re = ‖v‖ ^ 2 := by
      have := inner_self_eq_norm_sq (𝕜 := ℂ) v
      simpa using this
    rw [hvv, hnv] at this
    have e0 : ‖u‖ ^ 2 - 2 * ‖u‖ ^ 2 + ‖u‖ ^ 2 = 0 := by ring
    rw [e0] at this
    exact this
  have h0 : Tendsto (fun k => ‖x (s k) - v‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact (tendsto_iff_norm_sub_tendsto_zero).2 h0

theorem G1_080 (u : PhysicalL2) :
    IsCompact (isospectralSet u) ∧
    (∀ v ∈ isospectralSet u, ‖v‖ = ‖u‖) ∧
    isospectralSet (0 : PhysicalL2) = {0} := by
  refine ⟨g1080_compact u, fun v hv => g1080_norm_eq u v hv, ?_⟩
  ext v
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · have := g1080_norm_eq 0 v hv
    simpa using this
  · rw [mem_singleton_iff] at hv
    subst hv
    exact fun z => rfl

end
end NlsGge.GKDefinitionDesign
