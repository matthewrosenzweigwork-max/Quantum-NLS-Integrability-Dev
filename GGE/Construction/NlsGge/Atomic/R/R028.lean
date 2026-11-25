import Mathlib
import NlsGge.Atomic.R.R027
import NlsGge.Atomic.R.R028G1
import NlsGge.Atomic.R.R028G2U
import NlsGge.Atomic.R.R028G3
import NlsGge.ThirdConsultation.R.RamerSetting06B

                                                                                                 
                                                                                                      
                                                                  
                                                                                      
                                                                                                          
                                                                                                                    
                                                                                                                     
                                                                                                                      
                                                                                                        
                                                                                                    
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section
section R028Main
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

/-- A local closed divergence of a single closed-divergence witness, on an open set. -/
theorem r028_localClosedDiv_of_isClosedDiv (G : RamerE c s → RamerH c) (e : RamerE c s → ℝ)
    (hC : IsClosedDiv c s G e) (U : Set (RamerE c s)) (hU : IsOpen U) :
    LocalClosedDiv c s G e U := by
  intro x₀ hx₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  exact ⟨r, hr, hball, G, e, fun _ _ => rfl, hC, Filter.EventuallyEq.refl _ _⟩

/-- Countable gluing on a countable open cover, with a.e. agreement on overlaps. -/
theorem r028_glue (B : ℕ → Set (RamerE c s)) (hcov : ∀ x : RamerE c s, ∃ n, x ∈ B n)
    (f : ℕ → RamerE c s → ℝ) (hfm : ∀ n, AEStronglyMeasurable (f n) (ramerGaussian c s))
    (hBo : ∀ n, MeasurableSet (B n))
    (hag : ∀ n m, f n =ᵐ[(ramerGaussian c s).restrict (B n ∩ B m)] f m) :
    ∃ d : RamerE c s → ℝ, AEStronglyMeasurable d (ramerGaussian c s) ∧
      ∀ n, d =ᵐ[(ramerGaussian c s).restrict (B n)] f n := by
  classical
  have hidx : ∀ x : RamerE c s, x ∈ B (Nat.find (hcov x)) := fun x => Nat.find_spec (hcov x)
  refine ⟨fun x => f (Nat.find (hcov x)) x, ?_, ?_⟩
  · have hU : (⋃ n, B n) = univ := Set.eq_univ_of_forall (fun x => Set.mem_iUnion.2 (hcov x))
    have hm : AEStronglyMeasurable (fun x : RamerE c s => f (Nat.find (hcov x)) x)
        ((ramerGaussian c s).restrict (⋃ n, B n)) := by
      rw [aestronglyMeasurable_iUnion_iff]
      intro n
      have hdn : (fun x : RamerE c s => f (Nat.find (hcov x)) x) =ᵐ[(ramerGaussian c s).restrict (B n)]
          f n := by
        have hall : ∀ᵐ x ∂(ramerGaussian c s).restrict (B n), ∀ m, x ∈ B m → f m x = f n x := by
          refine ae_all_iff.2 (fun m => ?_)
          have h1 : ∀ᵐ x ∂(ramerGaussian c s), x ∈ B n ∩ B m → f n x = f m x :=
            (ae_restrict_iff' ((hBo n).inter (hBo m))).1 (hag n m)
          have h2 : ∀ᵐ x ∂(ramerGaussian c s), x ∈ B n → x ∈ B m → f m x = f n x := by
            filter_upwards [h1] with x hx hxn hxm
            exact (hx ⟨hxn, hxm⟩).symm
          exact (ae_restrict_iff' (hBo n)).2 h2
        filter_upwards [hall] with x hx
        exact hx (Nat.find (hcov x)) (hidx x)
      exact ((hfm n).mono_measure Measure.restrict_le_self).congr hdn.symm
    rwa [hU, Measure.restrict_univ] at hm
  · intro n
    have hall : ∀ᵐ x ∂(ramerGaussian c s).restrict (B n), ∀ m, x ∈ B m → f m x = f n x := by
      refine ae_all_iff.2 (fun m => ?_)
      have h1 : ∀ᵐ x ∂(ramerGaussian c s), x ∈ B n ∩ B m → f n x = f m x :=
        (ae_restrict_iff' ((hBo n).inter (hBo m))).1 (hag n m)
      have h2 : ∀ᵐ x ∂(ramerGaussian c s), x ∈ B n → x ∈ B m → f m x = f n x := by
        filter_upwards [h1] with x hx hxn hxm
        exact (hx ⟨hxn, hxm⟩).symm
      exact (ae_restrict_iff' (hBo n)).2 h2
    filter_upwards [hall] with x hx
    exact hx (Nat.find (hcov x)) (hidx x)

/-- Indicator convergence: pointwise agreement on a measurable set `Bq` for `N ≥ N₀`, a.e. agreement of the limits
on `Bq`, and the `L²` convergence of the reference approximants give the `L²` convergence of the indicators. -/
theorem r028_indicator_tendsto (Bq : Set (RamerE c s)) (hBq : MeasurableSet Bq)
    (g h : ℕ → RamerE c s → ℝ) (d1 dn : RamerE c s → ℝ)
    (hd : ∀ᵐ x ∂(ramerGaussian c s), x ∈ Bq → d1 x = dn x) (N₀ : ℕ)
    (hN₀ : ∀ N : ℕ, N₀ ≤ N → ∀ x ∈ Bq, g N x = h N x)
    (hlim : Tendsto (fun N => eLpNorm (fun x => h N x - dn x) 2 (ramerGaussian c s)) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (Bq.indicator (fun x => g N x - d1 x)) 2 (ramerGaussian c s))
      atTop (𝓝 0) := by
  have hsq : Tendsto (fun N => eLpNorm (Bq.indicator (fun x => h N x - dn x)) 2
      (ramerGaussian c s)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun N => zero_le)
      (fun N => eLpNorm_indicator_le (fun x => h N x - dn x) hBq)
  refine hsq.congr' (eventually_atTop.2 ⟨N₀, fun N hN => ?_⟩)
  have hind : Bq.indicator (fun x => g N x - d1 x) =ᵐ[ramerGaussian c s]
      Bq.indicator (fun x => h N x - dn x) := by
    filter_upwards [hd] with x hx
    by_cases hxb : x ∈ Bq
    · rw [Set.indicator_of_mem hxb, Set.indicator_of_mem hxb, hN₀ N hN x hxb, hx hxb]
    · rw [Set.indicator_of_notMem hxb, Set.indicator_of_notMem hxb]
  exact (eLpNorm_congr_ae hind).symm

/-- **R-028, divergence identification** (Pro round 6 head, verbatim). -/
theorem divergence_identification (K : RamerE c s → RamerH c) (hK : ContDiff ℝ 2 K) :
    ∃ d : RamerE c s → ℝ, V2LocalClosedDivergence c s K d ∧ LocalRamerApproxLimit c s hs K d := by
  classical
  -- local bumps (G1) with bounded transports (G3), one for each centre
  have hloc : ∀ x : RamerE c s, ∃ r : ℝ, 0 < r ∧ ∃ G : RamerE c s → RamerH c, ContDiff ℝ 2 G ∧
      EqOn G K (ball x r) ∧ BoundedFieldAndDerivative G := by
    intro x
    obtain ⟨r, hr, G, hG, hEq, hB, -, -⟩ := r028_exists_bump c s hs K hK x
    exact ⟨r, hr, G, hG, hEq, hB⟩
  choose R hR0 F hF hFEq hFB using hloc
  have htr : ∀ x : RamerE c s, ∃ dG : RamerE c s → ℝ, IsClosedDiv c s (F x) dG ∧
      Tendsto (fun N : ℕ => eLpNorm (fun y : RamerE c s => ramerApprox c s hs (F x) N y - dG y) 2
        (ramerGaussian c s)) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => eLpNorm (fun y : RamerE c s => literalCylDiv c s (F x) N y - dG y) 2
        (ramerGaussian c s)) atTop (𝓝 0) :=
    fun x => r028_bounded_transport c s hs (F x) (hF x) (hFB x)
  choose D hDc hDr hDl using htr
  -- countable subcover by the open balls ball x (R x)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : RamerE c s => ball x (R x)) (fun x => isOpen_ball)
  have hne : T.Nonempty := by
    have h0 : (0 : RamerE c s) ∈ ⋃ x, ball x (R x) :=
      Set.mem_iUnion.2 ⟨0, mem_ball_self (hR0 0)⟩
    have h0' : (0 : RamerE c s) ∈ ⋃ i ∈ T, ball i (R i) := (Set.ext_iff.1 hTU _).2 h0
    obtain ⟨t, ht, -⟩ := Set.mem_iUnion₂.1 h0'
    exact ⟨t, ht⟩
  obtain ⟨σ, hσ⟩ := hTc.exists_eq_range hne
  have hcov : ∀ x : RamerE c s, ∃ n : ℕ, x ∈ ball (σ n) (R (σ n)) := by
    intro x
    have hx : x ∈ ⋃ i, ball i (R i) := Set.mem_iUnion.2 ⟨x, mem_ball_self (hR0 x)⟩
    have hx' : x ∈ ⋃ i ∈ T, ball i (R i) := (Set.ext_iff.1 hTU _).2 hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx'
    rw [hσ] at ht
    obtain ⟨n, rfl⟩ := ht
    exact ⟨n, hxt⟩
  -- pairwise agreement of the divergences on overlaps (R-027)
  have hag : ∀ n m, D (σ n) =ᵐ[(ramerGaussian c s).restrict
      (ball (σ n) (R (σ n)) ∩ ball (σ m) (R (σ m)))] D (σ m) := by
    intro n m
    have hU : IsOpen (ball (σ n) (R (σ n)) ∩ ball (σ m) (R (σ m))) :=
      isOpen_ball.inter isOpen_ball
    have hEq : EqOn (F (σ n)) (F (σ m)) (ball (σ n) (R (σ n)) ∩ ball (σ m) (R (σ m))) := by
      intro y hy
      have h1 : F (σ n) y = K y := hFEq (σ n) hy.1
      have h2 : F (σ m) y = K y := hFEq (σ m) hy.2
      rw [h1, h2]
    exact local_closedDiv_eq c s hs (F (σ n)) (F (σ m)) (D (σ n)) (D (σ m))
      (ball (σ n) (R (σ n)) ∩ ball (σ m) (R (σ m))) (hF _) (hF _) hEq hU
      (r028_localClosedDiv_of_isClosedDiv c s (F (σ n)) (D (σ n)) (hDc (σ n))
        (ball (σ n) (R (σ n)) ∩ ball (σ m) (R (σ m))) hU)
      (r028_localClosedDiv_of_isClosedDiv c s (F (σ m)) (D (σ m)) (hDc (σ m))
        (ball (σ n) (R (σ n)) ∩ ball (σ m) (R (σ m))) hU)
  obtain ⟨d, hdm, hdn⟩ := r028_glue c s (fun n => ball (σ n) (R (σ n))) hcov
    (fun n => D (σ n)) (fun n => (hDc (σ n)).2.1.aestronglyMeasurable)
    (fun n => measurableSet_ball) hag
  refine ⟨d, ⟨hdm, ?_⟩, ?_⟩
  · -- local closed divergence on the whole space
    intro x₀ _
    obtain ⟨n, hn⟩ := hcov x₀
    rw [Metric.mem_ball] at hn
    have hρ : 0 < R (σ n) - dist x₀ (σ n) := by linarith
    have hsub : ball x₀ (R (σ n) - dist x₀ (σ n)) ⊆ ball (σ n) (R (σ n)) :=
      ball_subset_ball' (by linarith)
    exact ⟨R (σ n) - dist x₀ (σ n), hρ, subset_univ _, F (σ n), D (σ n),
      (hFEq (σ n)).mono hsub, hDc (σ n), ae_restrict_of_ae_restrict_of_subset hsub (hdn n)⟩
  · -- L² convergence of both approximants on a smaller ball
    intro x₀
    obtain ⟨n, hn⟩ := hcov x₀
    rw [Metric.mem_ball] at hn
    have hρ : 0 < R (σ n) - dist x₀ (σ n) := by linarith
    have hsub : ball x₀ (R (σ n) - dist x₀ (σ n)) ⊆ ball (σ n) (R (σ n)) :=
      ball_subset_ball' (by linarith)
    have hEqK : EqOn K (F (σ n)) (ball x₀ (R (σ n) - dist x₀ (σ n))) :=
      fun y hy => (hFEq (σ n) (hsub hy)).symm
    obtain ⟨N₀, hN₀⟩ := r028_locality_uniform c s hs x₀ _ hρ K (F (σ n)) hEqK
    have hqsub : ball x₀ ((R (σ n) - dist x₀ (σ n)) / 4) ⊆ ball (σ n) (R (σ n)) :=
      (ball_subset_ball (by linarith)).trans hsub
    have hd' : ∀ᵐ x ∂(ramerGaussian c s), x ∈ ball x₀ ((R (σ n) - dist x₀ (σ n)) / 4) →
        d x = D (σ n) x :=
      (ae_restrict_iff' measurableSet_ball).1
        (ae_restrict_of_ae_restrict_of_subset hqsub (hdn n))
    refine ⟨(R (σ n) - dist x₀ (σ n)) / 4, div_pos hρ (by norm_num), ?_, ?_⟩
    · exact r028_indicator_tendsto c s _ measurableSet_ball
        (fun N => ramerApprox c s hs K N) (fun N => ramerApprox c s hs (F (σ n)) N) d (D (σ n)) hd' N₀
        (fun N hN x hx => (hN₀ N hN x hx).1) (hDr (σ n))
    · exact r028_indicator_tendsto c s _ measurableSet_ball
        (fun N => literalCylDiv c s K N) (fun N => literalCylDiv c s (F (σ n)) N) d (D (σ n)) hd' N₀
        (fun N hN x hx => (hN₀ N hN x hx).2) (hDl (σ n))

end R028Main
end
end NlsGge.ThirdConsultation.R
