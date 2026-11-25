import Mathlib
import NlsGge.Atomic.M.M010Support1
import NlsGge.ThirdConsultation.G2.G2037P5B
import NlsGge.Atomic.M.M016CxOmegaProduct
import NlsGge.Atomic.M.M016ChartG

/- M016 CHART CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M016ChartCore.lean. The complex finite-gap exterior chart (Pro R16 §1.1, proof §3 steps 1-3, 5-reduction),
   stated with the UNFOLDED bodies of the not-yet-landed `ExteriorPrimitiveRepresentative` (R14 L1316-1321, owner M-052)
   and `finiteGapPair` (R14 L1311-1312: `{n | gap φ n ≠ 0}.Finite`); these are NOT re-hosted here.
   * chart_core: for φ ∈ gkW finite-gap: the literal primitive, glued through every exterior collapsed gap
     (removable singularity; collapsed points isolated by the landed disjoint isolating discs), is holomorphic outside
     one disc, has derivative -i·Q(1/z) (finitegap_pair_omega_eq_product + landed G2037P5.product_expansion), hence
     F(z) + iz = G(1/z) with G analytic at 0 (same F). Thin instantiation of the lane-checked
     M016ChartG.exterior_chart_generic (6d382fd8); geometric lemmas lane-checked verbatim in M016Chart_GEO_SELFTEST01
     (bf9aafb7) with copies of the small landed defs.
   * finitegap_pair_primitive_meromorphic_infinity_of_ray: the full chart conclusion, CONDITIONAL on the explicit ray
     calibration `primitive(φ, it) - t → 0` (the output of R16 §3 step 5: Dyson ray estimate + gkW connectedness +
     vacuum value), which remains open. Status: conditional_proved once probed.
   Needs ROOT MAIN PROBE (M009/M010/G2037/M016CxOmegaProduct absent from the mirror). -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M016ChartAux

open NlsGge.ThirdConsultation.MPrimitive

/-- Exterior points lie in the endpoint closure; non-cut-free exterior points are collapsed endpoints. -/
theorem exterior_point (φ : PotPair) (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ NlsGge.GKDefinitionDesign.gap φ n ≠ 0) {B : ℝ}
    (hB : ∀ n ∈ S, ‖lamMinus φ n‖ + ‖lamPlus φ n‖ < B) {z : ℂ} (hz : B < ‖z‖) :
    z ∈ cutFreeFiber φ ∨ ∃ k : ℤ, k ∉ S ∧ z = lamMinus φ k ∧ lamPlus φ k = lamMinus φ k := by
  by_cases hc : z ∈ cutFreeFiber φ
  · exact Or.inl hc
  · right
    simp only [cutFreeFiber, gapSegments38, mem_setOf_eq, not_not, mem_iUnion] at hc
    obtain ⟨k, hk⟩ := hc
    have hkS : k ∉ S := by
      intro hkS
      obtain ⟨s, t, hs, ht, hst, rfl⟩ := hk
      have h1 : ‖s • lamMinus φ k + t • lamPlus φ k‖ ≤ ‖lamMinus φ k‖ + ‖lamPlus φ k‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_of_nonneg hs]
          exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
        · rw [norm_smul, Real.norm_of_nonneg ht]
          exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
      linarith [hB k hkS]
    have hg : lamPlus φ k - lamMinus φ k = 0 := by
      by_contra hne
      exact hkS ((hS k).2 hne)
    have heq : lamPlus φ k = lamMinus φ k := sub_eq_zero.mp hg
    rw [heq, segment_same] at hk
    exact ⟨k, hkS, hk, heq⟩

theorem mem_closure_of_exterior (φ : PotPair) (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ NlsGge.GKDefinitionDesign.gap φ n ≠ 0) {B : ℝ}
    (hB : ∀ n ∈ S, ‖lamMinus φ n‖ + ‖lamPlus φ n‖ < B) {z : ℂ} (hz : B < ‖z‖) :
    z ∈ endpointClosureFiber φ := by
  rcases exterior_point φ S hS hB hz with h | ⟨k, -, rfl, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, Or.inl rfl⟩

/-- A collapsed endpoint is isolated from all cuts: its isolating disc minus the point is cut-free. -/
theorem collapsed_isolated (φ : PotPair) (hW : φ ∈ gkW) (k : ℤ)
    (hk : lamPlus φ k = lamMinus φ k) :
    lamMinus φ k ∈ discU φ k ∧ discU φ k \ {lamMinus φ k} ⊆ cutFreeFiber φ := by
  obtain ⟨c, N, -, hspec⟩ := isolating_family38 φ hW
  have hsegU : ∀ j : ℤ, segment ℝ (lamMinus φ j) (lamPlus φ j) ⊆ discU φ j := fun j => (hspec.1 j).1
  refine ⟨hsegU k (left_mem_segment ℝ _ _), fun w hw => ?_⟩
  obtain ⟨hwU, hwne⟩ := hw
  simp only [cutFreeFiber, gapSegments38, mem_setOf_eq, mem_iUnion, not_exists]
  intro j hj
  by_cases hjk : j = k
  · subst hjk
    rw [hk, segment_same] at hj
    exact hwne hj
  · exact Set.disjoint_left.mp ((isolating φ hW).1 hjk) (hsegU j hj) hwU

/-- **Chart core** (instantiation of `exterior_chart_generic`). -/
theorem chart_core (φ : PotPair) (hW : φ ∈ gkW)
    (hfg : {n : ℤ | NlsGge.GKDefinitionDesign.gap φ n ≠ 0}.Finite) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      (0 < R ∧ ∀ z : ℂ, R < ‖z‖ →
        ∃ hz : φ ∈ gkW ∧ z ∈ endpointClosureFiber φ,
          F z = NlsGge.ThirdConsultation.M.primitive ⟨(φ, z), hz⟩) ∧
      ExteriorHolomorphic F ∧
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ ∃ R' : ℝ, 0 < R' ∧
        ∀ z : ℂ, R' < ‖z‖ → F z + Complex.I * z = G z⁻¹ := by
  classical
  set S : Finset ℤ := hfg.toFinset with hSdef
  have hS : ∀ n : ℤ, n ∈ S ↔ NlsGge.GKDefinitionDesign.gap φ n ≠ 0 := fun n => by
    rw [hSdef, Set.Finite.mem_toFinset]; rfl
  set B : ℝ := 1 + ∑ n ∈ S, (‖lamMinus φ n‖ + ‖lamPlus φ n‖) with hBdef
  have hB0 : 0 < B := by
    have : 0 ≤ ∑ n ∈ S, (‖lamMinus φ n‖ + ‖lamPlus φ n‖) :=
      Finset.sum_nonneg fun n _ => add_nonneg (norm_nonneg _) (norm_nonneg _)
    linarith
  have hB : ∀ n ∈ S, ‖lamMinus φ n‖ + ‖lamPlus φ n‖ < B := fun n hn => by
    have := Finset.single_le_sum (f := fun n => ‖lamMinus φ n‖ + ‖lamPlus φ n‖)
      (fun n _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hn
    linarith
  obtain ⟨P, L, hP, hPL, hval⟩ := symmetric_value_data_lim φ hW
  let F : ℂ → ℂ := fun z => if h : z ∈ endpointClosureFiber φ then
    NlsGge.ThirdConsultation.M.primitive ⟨(φ, z), ⟨hW, h⟩⟩ else 0
  have hFL : ∀ z ∈ endpointClosureFiber φ, F z = L z - L (lamMinus φ 0) := fun z hz => by
    simp only [F, dif_pos hz]; exact hval z hz
  obtain ⟨Q, hQa, hQ0, R1, -, hQid⟩ := NlsGge.G2037P5.product_expansion S
    (fun n => tauN φ n) (fun n => gamma2 φ n) (fun n => lamDot φ n)
  have hω : ∀ z ∈ cutFreeFiber φ, R1 < ‖z‖ → MContour.omega φ z = -Complex.I * Q z⁻¹ :=
    fun z hz hzR => by
      have hom := NlsGge.ThirdConsultation.M.finitegap_pair_omega_eq_product φ hW S hS z ⟨hW, hz⟩
      exact (show MContour.omega φ z = NlsGge.ThirdConsultation.M.omega φ z from rfl).trans
        (hom.trans (hQid z hzR))
  have hpt : ∀ z : ℂ, B < ‖z‖ → z ∈ cutFreeFiber φ ∨ (z ∈ endpointClosureFiber φ ∧
      ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U \ {z} ⊆ cutFreeFiber φ) := fun z hz => by
    rcases exterior_point φ S hS hB hz with h | ⟨k, -, rfl, hk⟩
    · exact Or.inl h
    · obtain ⟨hcU, hUc⟩ := collapsed_isolated φ hW k hk
      exact Or.inr ⟨Or.inr ⟨k, Or.inl rfl⟩, discU φ k, isOpen_ball, hcU, hUc⟩
  obtain ⟨R', hR'0, hanal, G, hG, R'', hR'', hFG⟩ := exterior_chart_generic (cutFreeFiber φ)
    (endpointClosureFiber φ) (cutFreeFiber_isOpen φ hW) (fun z hz => Or.inl hz) P L
    (MContour.omega φ) F (L (lamMinus φ 0)) hP hPL hFL hB0 hpt Q hQa hQ0 hω
  refine ⟨B, F, ⟨hB0, fun z hz => ?_⟩, ⟨R', hR'0, hanal⟩, G, hG, R'', hR'', hFG⟩
  have hcl := mem_closure_of_exterior φ S hS hB hz
  exact ⟨⟨hW, hcl⟩, by simp only [F, dif_pos hcl]⟩

end NlsGge.ThirdConsultation.M016ChartAux

namespace NlsGge.ThirdConsultation.M

open NlsGge.ThirdConsultation.MPrimitive NlsGge.ThirdConsultation.M016ChartAux

/-- **Complex finite-gap chart, conditional on the ray calibration** (R16 §1.1 conclusion with the unfolded
`ExteriorPrimitiveRepresentative`/`finiteGapPair` bodies). The hypothesis `hray` is the output of R16 §3 step 5. -/
theorem finitegap_pair_primitive_meromorphic_infinity_of_ray
    (φ : PotPair) (hW : φ ∈ gkW)
    (hfg : {n : ℤ | NlsGge.GKDefinitionDesign.gap φ n ≠ 0}.Finite)
    (hray : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T < t →
      ∀ h : φ ∈ gkW ∧ Complex.I * (t : ℂ) ∈ endpointClosureFiber φ,
        ‖primitive ⟨(φ, Complex.I * (t : ℂ)), h⟩ - t‖ < ε) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      (0 < R ∧ ∀ z : ℂ, R < ‖z‖ →
        ∃ hz : φ ∈ gkW ∧ z ∈ endpointClosureFiber φ, F z = primitive ⟨(φ, z), hz⟩) ∧
      ExteriorHolomorphic F ∧
      AnalyticAtInfinity (fun z : ℂ => F z + Complex.I * z) ∧
      HasValueAtInfinity (fun z : ℂ => F z + Complex.I * z) 0 := by
  obtain ⟨R, F, ⟨hR, hrep⟩, hhol, G, hG, R', hR', hFG⟩ := chart_core φ hW hfg
  have hFray : Tendsto (fun t : ℝ => F (Complex.I * t) - t) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨T, hT⟩ := hray ε hε
    refine ⟨max T (max R 0) + 1, fun t ht => ?_⟩
    have htT : T < t := by linarith [le_max_left T (max R 0)]
    have htR : R < ‖Complex.I * (t : ℂ)‖ := by
      have h0 : 0 ≤ t := by linarith [le_max_right R 0, le_max_right T (max R 0)]
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg h0]
      linarith [le_max_left R 0, le_max_right T (max R 0)]
    obtain ⟨hz, hFz⟩ := hrep _ htR
    rw [dist_zero_right, hFz]
    exact hT t htT hz
  have hG0 := G0_of_ray F G hG.continuousAt hFG hFray
  exact ⟨R, F, ⟨hR, hrep⟩, hhol, infinity_of_G F G hR' hG hG0 hFG⟩

end NlsGge.ThirdConsultation.M
