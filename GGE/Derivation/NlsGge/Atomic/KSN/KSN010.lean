import Mathlib
import NlsGge.Atomic.KSN.KSN002
import NlsGge.Atomic.KSN.KSN003
import NlsGge.Atomic.KSN.KSN004
import NlsGge.Atomic.KSN.KSN006
import NlsGge.Atomic.KSN.KSN007
import NlsGge.Atomic.KSN.KSN008Host
import NlsGge.Atomic.KSN.KSN009
import NlsGge.Atomic.KSN.KSN010Host
import NlsGge.Atomic.G4.G4019
import NlsGge.Atomic.G4.G4021
import NlsGge.Atomic.G4.G4031
import NlsGge.Atomic.G4.G4030Reg
import NlsGge.Atomic.G4.G4048

set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSN

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace KSN010Aux

private theorem exp_sub_one_bound (x : ℂ) :
    ‖Complex.exp x - 1‖ ≤ 2 * ‖x‖ * Real.exp ‖x‖ := by
  by_cases hx : ‖x‖ ≤ 1
  · have h := Complex.norm_exp_sub_one_le hx
    have he : (1 : ℝ) ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg x)
    calc ‖Complex.exp x - 1‖ ≤ 2 * ‖x‖ := h
      _ = (2 * ‖x‖) * 1 := by ring
      _ ≤ (2 * ‖x‖) * Real.exp ‖x‖ :=
        mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num) (norm_nonneg x))
      _ = 2 * ‖x‖ * Real.exp ‖x‖ := by ring
  · have hx' : 1 < ‖x‖ := lt_of_not_ge hx
    have he : (1 : ℝ) ≤ Real.exp ‖x‖ := Real.one_le_exp (norm_nonneg x)
    calc ‖Complex.exp x - 1‖ ≤ ‖Complex.exp x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖Complex.exp x‖ + 1 := by simp
      _ ≤ Real.exp ‖x‖ + 1 := add_le_add (Complex.norm_exp_le_exp_norm x) le_rfl
      _ ≤ 2 * Real.exp ‖x‖ := by linarith
      _ ≤ 2 * ‖x‖ * Real.exp ‖x‖ := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_nonneg _)

private theorem prefactor_identity (n a : ℤ) (φ : PotPair)
    (hδ : deltaFactor n φ (muSeq φ n) ≠ 0)
    (hanti : antiDiscrim φ (muSeq φ n) =
      2 * Complex.I * terminalRoot n φ * deltaFactor n φ (muSeq φ n)) :
    (tauN φ n - muSeq φ n) - (a : ℂ) * Complex.I * antiDiscrim φ (muSeq φ n) /
        (2 * deltaFactor n φ (muSeq φ n)) =
      (tauN φ n - muSeq φ n) + (a : ℂ) * terminalRoot n φ := by
  rw [hanti]
  have hden : (2 : ℂ) * deltaFactor n φ (muSeq φ n) ≠ 0 :=
    mul_ne_zero (by norm_num) hδ
  field_simp [hden]
  ring_nf
  rw [Complex.I_sq]
  ring

end KSN010Aux

theorem KSN010_main :
  (∀ φ ∈ sourceBetaW, ∀ n a : ℤ, (a = 1 ∨ a = -1) →
    deltaFactor n φ (muSeq φ n) ≠ 0 ∧
    sourceZ n a φ =
      ((tauN φ n - muSeq φ n) - (a : ℂ) * Complex.I *
        antiDiscrim φ (muSeq φ n) / (2 * deltaFactor n φ (muSeq φ n))) * eta n a φ) ∧
  (∀ φ₀ ∈ sourceBetaW, ∃ (U : Set PotPair) (C : ℝ),
    IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ sourceBetaW ∧ 0 ≤ C ∧
    ∀ φ ∈ U, ∀ n a : ℤ, (a = 1 ∨ a = -1) →
      ‖eta n a φ - 1‖ ≤ C *
        (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖)) := by
  constructor
  · intro φ hφ n a ha
    have hbase := (KSN002_main n).2 φ hφ
    have hδ := hbase.2.1
    have hanti := hbase.2.2.1
    refine ⟨hδ, ?_⟩
    have hCart := G4031Aux.cartesianZ_unified n a ha φ
    have hPref := KSN010Aux.prefactor_identity n a φ hδ hanti
    have hEta : eta n a φ = Complex.exp
        (-((a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n))) := by
      unfold eta
      congr 1
      rw [NlsGge.ThirdConsultation.KSN.ksn_terminalRoot_eq_native n φ]
      ring
    calc sourceZ n a φ = cartesianZExtended n a φ / 2 := rfl
      _ = ((2 * (tauN φ n - muSeq φ n) +
          2 * (a : ℂ) * terminalRoot n φ) *
            Complex.exp (-((a : ℂ) * terminalRoot n φ *
              ownCorrection n φ (muSeq φ n)))) / 2 := by rw [hCart]
      _ = ((tauN φ n - muSeq φ n) + (a : ℂ) * terminalRoot n φ) *
            Complex.exp (-((a : ℂ) * terminalRoot n φ *
              ownCorrection n φ (muSeq φ n))) := by ring
      _ = ((tauN φ n - muSeq φ n) - (a : ℂ) * Complex.I *
            antiDiscrim φ (muSeq φ n) /
              (2 * deltaFactor n φ (muSeq φ n))) * eta n a φ := by
          rw [← hPref, hEta]
  · intro φ₀ hφ₀
    have hG4019 := G4019 φ₀ hφ₀
    rcases hG4019 with ⟨V1, hV1n, hV1o, hV1B, hData⟩
    rcases hData with ⟨Cc, R, r, ε, M, hε, hM, hfam, hrR, hcol, hder⟩
    obtain ⟨V2, hV2n, hV2B, C2, hC2, hZeta⟩ := G4021 φ₀ hφ₀
    have hφ1 : φ₀ ∈ V1 := mem_of_mem_nhds hV1n
    obtain ⟨c, N, hgeom, _hs⟩ := hfam φ₀ hφ1
    obtain ⟨Rm, hRm0, hRm⟩ := g2019_radius_bound Cc R c N hgeom
    have hVS : V1 ∩ V2 ⊆ sourceBetaW := inter_subset_left.trans hV1B
    have hrle : ∀ n : ℤ, r n ≤ R n := by
      intro n
      have hn : r n < r n + ε := lt_add_of_pos_right _ hε
      exact (hn.trans (hrR n).2).le
    have hreg := G4030Aux.g4030_regular_bound (V1 ∩ V2) hVS Cc R r M hM.le hrle
      (fun φ hφ => hfam φ hφ.1) (fun φ hφ => hcol φ hφ.1) (fun φ hφ => hder φ hφ.1)
    have hGapBound : NormalizedZetaGapBound (V1 ∩ V2) C2 := by
      refine ⟨hC2.le, inter_subset_right.trans hV2B, fun φ hφ n => ?_⟩
      have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W (hVS hφ))
      exact (hZeta φ hφ.2 n).1 (tauN φ n) (g4036_tau_mem φ hgk n)
    obtain ⟨Cd, hCd, hconstant⟩ := G4048 (V1 ∩ V2) C2 hGapBound
    have hsize : ∀ φ ∈ V1 ∩ V2, ∀ n : ℤ,
        ‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖ ≤ 4 * Rm := by
      intro φ hφ n
      have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W (hVS hφ))
      obtain ⟨hgap, hmu⟩ := hcol φ hφ.1 n
      have hlm : lamMinus φ n ∈ Metric.ball (Cc n) (r n) :=
        hgap (left_mem_segment ℝ _ _)
      have hlp : lamPlus φ n ∈ Metric.ball (Cc n) (r n) :=
        hgap (right_mem_segment ℝ _ _)
      have hτ : tauN φ n ∈ Metric.ball (Cc n) (r n) :=
        hgap (g4036_tau_mem φ hgk n)
      have hgap' : ‖lamPlus φ n - lamMinus φ n‖ ≤ 2 * r n := by
        rw [← dist_eq_norm]
        have ht := dist_triangle_right (lamPlus φ n) (lamMinus φ n) (Cc n)
        rw [Metric.mem_ball] at hlm hlp
        linarith
      have hmu' : ‖muSeq φ n - tauN φ n‖ ≤ 2 * r n := by
        rw [← dist_eq_norm]
        have ht := dist_triangle_right (muSeq φ n) (tauN φ n) (Cc n)
        rw [Metric.mem_ball] at hmu hτ
        linarith
      have hR := hRm n
      have hr := hrle n
      linarith
    let A : ℝ := (Real.pi / 2) * M + Cd * C2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    let B : ℝ := A * (4 * Rm)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    let U : Set PotPair := interior (V1 ∩ V2)
    have hUn : V1 ∩ V2 ∈ 𝓝 φ₀ := inter_mem hV1n hV2n
    refine ⟨U, 2 * A * Real.exp B, isOpen_interior,
      mem_interior_iff_mem_nhds.mpr hUn, interior_subset.trans hVS, by positivity, ?_⟩
    intro φ hφ n a ha
    have hφ12 : φ ∈ V1 ∩ V2 := interior_subset hφ
    have hR := hreg φ hφ12 n
    have hC := hconstant φ hφ12 n
    have hS := hsize φ hφ12 n
    have hsum :
        ‖regularEtaIntegral n φ + constantEtaCorrection n φ‖ ≤
          A * (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) := by
      calc ‖regularEtaIntegral n φ + constantEtaCorrection n φ‖
          ≤ ‖regularEtaIntegral n φ‖ + ‖constantEtaCorrection n φ‖ := norm_add_le _ _
        _ ≤ ((Real.pi / 2) * M) *
              (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) +
            (Cd * C2) *
              (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) :=
          add_le_add hR hC
        _ = _ := by dsimp [A]; ring
    have hX : regularEtaIntegral n φ + constantEtaCorrection n φ =
        localRootAtDirichlet n φ * ownCorrection n φ (muSeq φ n) := by
      unfold regularEtaIntegral
      ring
    have hexp : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
        -((a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n)) =
          (s : ℂ) * (regularEtaIntegral n φ + constantEtaCorrection n φ) := by
      rw [hX]
      rcases G4031Aux.terminalRoot_eq_pm n φ
          (sourceFamily.W_gk (sourceFamily.V_W (hVS hφ12))) with hT | hT
      · rcases ha with rfl | rfl
        · exact ⟨-1, Or.inr rfl, by rw [hT]; push_cast; ring⟩
        · exact ⟨1, Or.inl rfl, by rw [hT]; push_cast; ring⟩
      · rcases ha with rfl | rfl
        · exact ⟨1, Or.inl rfl, by rw [hT]; push_cast; ring⟩
        · exact ⟨-1, Or.inr rfl, by rw [hT]; push_cast; ring⟩
    obtain ⟨s, hs, hExponent⟩ := hexp
    have hExponentNorm :
        ‖-((a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n))‖ ≤
          A * (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) := by
      rw [hExponent]
      rcases hs with rfl | rfl
      · simpa using hsum
      · rw [Int.cast_neg, Int.cast_one, neg_one_mul, norm_neg]
        simpa [add_comm] using hsum
    have hExponentBound :
        ‖-((a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n))‖ ≤ B := by
      calc _ ≤ A * (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) :=
            hExponentNorm
        _ ≤ A * (4 * Rm) := mul_le_mul_of_nonneg_left hS hA
        _ = B := rfl
    have hExpMono := Real.exp_le_exp.mpr hExponentBound
    have hmul :
        2 * ‖-((a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n))‖ ≤
          2 * (A * (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖)) :=
      mul_le_mul_of_nonneg_left hExponentNorm (by norm_num)
    have hEta : eta n a φ = Complex.exp
        (-((a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n))) := by
      unfold eta
      congr 1
      rw [NlsGge.ThirdConsultation.KSN.ksn_terminalRoot_eq_native n φ]
      ring
    rw [hEta]
    calc ‖Complex.exp (-((a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n))) - 1‖
        ≤ 2 * ‖-((a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n))‖ *
            Real.exp ‖-((a : ℂ) * terminalRoot n φ * ownCorrection n φ (muSeq φ n))‖ :=
          KSN010Aux.exp_sub_one_bound _
      _ ≤ 2 * (A * (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖)) *
            Real.exp B := by
          exact mul_le_mul hmul hExpMono (by positivity) (by positivity)
      _ = (2 * A * Real.exp B) *
            (‖lamPlus φ n - lamMinus φ n‖ + ‖muSeq φ n - tauN φ n‖) := by ring

end
end NlsGge.GKDefinitionDesign
