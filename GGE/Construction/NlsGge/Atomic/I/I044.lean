                                                                                        
                                                                                 
                                                                              
import Mathlib
import NlsGge.Atomic.I.I042
import NlsGge.Atomic.I.I043
import NlsGge.Atomic.I.IEnsembleCore
import NlsGge.ThirdConsultation.I.ActualInverseBridge
import NlsGge.ThirdConsultation.I.I044Sup
import NlsGge.Birkhoff.H03Monotone38

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology BoundedContinuousFunction
open NlsGge (coefficient)
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.HierarchyRiccati.Core NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I

theorem i044 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    ∃ Nk : ℕ → ℕ, StrictMono Nk ∧ (∀ k : ℕ, k ≤ Nk k) ∧
      (∀ k : ℕ, 2 ≤ k → ∀ N : ℕ, Nk k ≤ N → ∀ r : ℕ, r < k →
        IsProbabilityMeasure (finiteOrderFourierLaw c.val r k N) ∧
        IsProbabilityMeasure (finiteOrderLaw c.val r k) ∧
        boundedLipschitzDistance (finiteOrderFourierLaw c.val r k N)
          (finiteOrderLaw c.val r k) ≤ 1 / (k : ℝ)) ∧
      let m := diagOrder38 Nk
      (∀ N : ℕ, 2 ≤ m N) ∧
      (∀ N : ℕ, N < Nk 2 → m N = 2) ∧
      (∀ N : ℕ, Nk 2 ≤ N → Nk (m N) ≤ N ∧
        ∀ k : ℕ, 2 ≤ k → Nk k ≤ N → k ≤ m N) ∧
      Monotone m ∧ Tendsto m atTop atTop ∧
      (∀ (N : ℕ) (w : FourierPlane N),
        EmPlane38 (m N) (coefficient c.val) N w =
          ∑ j ∈ Finset.range (m N + 1), coefficient c.val j * localCharge38 (planeReal N w) j) ∧
      ∀ (r : ℕ) (F : SobolevHilbert (r : ℝ) →ᵇ ℝ),
        Tendsto (fun N : ℕ => ∫ u : SobolevHilbert (r : ℝ), F u
          ∂finiteOrderFourierLaw c.val r (m N) N) atTop
          (𝓝 (∫ u : PhysicalL2, F (physFS38 r u) ∂physicalLaw (weight c.val))) := by
  classical
  obtain ⟨Nk, hstrict, hindex, hthreshold⟩ := i043 lower upper c
  let m : ℕ → ℕ := diagOrder38 Nk
  have hm : Tendsto m atTop atTop := tendsto_diagOrder38 Nk hindex
  refine ⟨Nk, hstrict, hindex, hthreshold, ?_⟩
  refine ⟨two_le_diagOrder38 Nk, ?_, ?_, monotone_diagOrder38 Nk, hm, ?_, ?_⟩
  · intro N hN
    have hzero : Nat.findGreatest (fun k => 2 ≤ k ∧ Nk k ≤ N) N = 0 := by
      apply Nat.findGreatest_eq_zero_iff.mpr
      intro k _hk _hkN hP
      exact (not_le_of_gt hN) ((hstrict.monotone hP.1).trans hP.2)
    change max 2 (Nat.findGreatest (fun k => 2 ≤ k ∧ Nk k ≤ N) N) = 2
    rw [hzero]
    norm_num
  · intro N hN
    exact ⟨diagOrder38_spec Nk hindex N hN,
      fun k hk hNk => le_diagOrder38 Nk hindex hk N hNk⟩
  · intro N w
    change energySobolev38 (m N) (coefficient c.val)
      (planeElement38 (m N : ℝ) N w) = _
    unfold energySobolev38
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg (fun a : ℝ => coefficient c.val j * a)
    exact chargeSobolev38_smooth (m N + 1) j
      (by have htwo := two_le_diagOrder38 Nk N; change 2 ≤ m N at htwo; omega)
      (by have hjlt := Finset.mem_range.mp hj; omega)
      (planeReal N w) (planeReal_smooth38 N w) (planeReal_periodic N w)
      _ (planeElement_hsource38 _ N w)
  · intro r F
    let limLaw : Measure (SobolevHilbert (r : ℝ)) :=
      (physicalLaw (weight c.val)).map (physFS38 r)
    have hphys : IsProbabilityMeasure (physicalLaw (weight c.val)) := by
      have hhouse := PDE.actualBirkhoffTop38.isProbabilityMeasure_muW38
        lower upper c.val c.property.1
        (fun j => (c.property.2.2 j).1) (fun j => (c.property.2.2 j).2)
      exact (NlsGge.ThirdConsultation.IEnsC.muW_eq_of PDE.actualBirkhoffTop38
        actual_inverse_eq_physicalOfSequence lower upper c) ▸ hhouse
    have hlimProb : IsProbabilityMeasure limLaw :=
      (Measure.isProbabilityMeasure_map_iff (measurable_physFS38 r).aemeasurable).2 hphys
    have hmap (G : SobolevHilbert (r : ℝ) →ᵇ ℝ) :
        (∫ u, G u ∂limLaw) =
          ∫ u : PhysicalL2, G (physFS38 r u) ∂physicalLaw (weight c.val) :=
      integral_map (measurable_physFS38 r).aemeasurable G.continuous.aestronglyMeasurable
    have hfinite (G : SobolevHilbert (r : ℝ) →ᵇ ℝ) :
        Tendsto (fun k : ℕ => ∫ u, G u ∂finiteOrderLaw c.val r k)
          atTop (𝓝 (∫ u, G u ∂limLaw)) := by
      rw [hmap G]
      apply (tendsto_add_atTop_iff_nat (max 2 (r + 1))).mp
      simpa only [Nat.add_comm] using (i042 lower upper c).2.2.2.2 r G
    let nu : ℕ → Measure (SobolevHilbert (r : ℝ)) :=
      fun N => finiteOrderFourierLaw c.val r (m N) N
    let eta : ℕ → Measure (SobolevHilbert (r : ℝ)) :=
      fun N => finiteOrderLaw c.val r (m N)
    have hnu (N : ℕ) : IsProbabilityMeasure (nu N) :=
      i043_isProbabilityMeasure_finiteOrderFourierLaw lower upper c
        (m N) r N (two_le_diagOrder38 Nk N)
    have heta (N : ℕ) : IsProbabilityMeasure (eta N) :=
      i043_isProbabilityMeasure_finiteOrderLaw lower upper c
        (m N) r (two_le_diagOrder38 Nk N)
    letI : ∀ N : ℕ, IsProbabilityMeasure (nu N) := hnu
    letI : ∀ N : ℕ, IsProbabilityMeasure (eta N) := heta
    letI : IsProbabilityMeasure limLaw := hlimProb
    have herr : Tendsto (fun N : ℕ => boundedLipschitzDistance (nu N) (eta N))
        atTop (𝓝 0) := by
      have hrec : Tendsto (fun k : ℕ => 1 / (k : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      refine squeeze_zero' (Eventually.of_forall fun N =>
        I044Aux.boundedLipschitzDistance_nonneg (nu N) (eta N)) ?_ (hrec.comp hm)
      filter_upwards [hm.eventually (eventually_gt_atTop r),
        eventually_ge_atTop (Nk 2)] with N hrN hN
      exact (hthreshold (m N) (two_le_diagOrder38 Nk N) N
        (diagOrder38_spec Nk hindex N hN) r hrN).2.2
    have hetaLim : Tendsto (fun N : ℕ => boundedLipschitzDistance (eta N) limLaw)
        atTop (𝓝 0) :=
      boundedLipschitzDistance_tendsto_zero_of_weak eta limLaw heta hlimProb
        (fun G => (hfinite G).comp hm)
    have hsum : Tendsto (fun N : ℕ =>
        boundedLipschitzDistance (nu N) (eta N) +
          boundedLipschitzDistance (eta N) limLaw) atTop (𝓝 0) := by
      simpa only [add_zero] using herr.add hetaLim
    have hBL : Tendsto (fun N : ℕ => boundedLipschitzDistance (nu N) limLaw)
        atTop (𝓝 0) :=
      squeeze_zero (fun N => I044Aux.boundedLipschitzDistance_nonneg (nu N) limLaw)
        (fun N => I044Aux.boundedLipschitzDistance_triangle (nu N) (eta N) limLaw) hsum
    have h := I044Aux.integral_tendsto_of_boundedLipschitzDistance_tendsto_zero
      nu limLaw hnu hlimProb hBL F
    rw [hmap F] at h
    exact h

end NlsGge.ThirdConsultation.I

end
