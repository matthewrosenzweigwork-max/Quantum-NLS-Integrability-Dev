import Mathlib
import NlsGge.Hierarchy.ALEnergyAnalytic38
import NlsGge.Hierarchy.ALComplexExteriorLog38
import NlsGge.Hierarchy.ALComplexMonodromy38
import NlsGge.Hierarchy.ALPoissonLiouville38
import NlsGge.Hierarchy.ALLaurent38
import NlsGge.Hierarchy.ALQuadraticPart38
import NlsGge.Hierarchy.ALPositiveDecompositions38

                                                                                                                      
                                                                                                                                     
                                                                                                                                                             
                                                                                                                                             
                                                                                                                                                   
                                                                                                
set_option autoImplicit false
open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory Metric
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core NlsGge.Pilot
namespace NlsGge.ThirdConsultation.AL
noncomputable section

theorem al031_star_field {L : ℕ} {a : ZMod L → ℂ} (ha : IsALField38 a) :
    IsALField38 (fun j => star (a j)) := fun j => by
  rw [norm_star]; exact ha j

theorem al031_swap_iota {L : ℕ} [NeZero L] (a : ZMod L → ℂ) :
    (alIota38 a).swap = alIota38 (fun j => star (a j)) := by
  rw [alIota38_apply, alIota38_apply]
  ext j <;> simp

theorem al031 {L : ℕ} [NeZero L]
    (K : Set (ZMod L → ℂ)) (hK : IsCompact K) (hKD : K ⊆ alDisk38 L) :
  ∃ (U : Set ((ZMod L → ℂ) × (ZMod L → ℂ))) (R C : ℝ),
    IsOpen U ∧ alIota38 '' K ⊆ U ∧ U ⊆ alComplexDomain38 L ∧
    (∀ p ∈ U, p.swap ∈ U) ∧ 1 < R ∧ 0 ≤ C ∧
    AnalyticOnNhd ℂ
      (fun q : ℂ × ((ZMod L → ℂ) × (ZMod L → ℂ)) =>
        alComplexLog38 q.2.1 q.2.2 q.1)
      (Metric.closedBall (0 : ℂ) R⁻¹ ×ˢ U) ∧
    (∀ p ∈ U, ∀ ζ ∈ Metric.closedBall (0 : ℂ) R⁻¹,
      alComplexD38 p.1 p.2 ζ ∈ Complex.slitPlane ∧
      alComplexG38 p.1 p.2 ζ ∈ Complex.slitPlane ∧
      Complex.exp (alComplexLog38 p.1 p.2 ζ) = alComplexG38 p.1 p.2 ζ ∧
      ‖alComplexLog38 p.1 p.2 ζ‖ ≤ C) ∧
    (∀ a : ZMod L → ℂ, IsALField38 a → alIota38 a ∈ U →
      ∀ ζ ∈ Metric.closedBall (0 : ℂ) R⁻¹,
        alComplexLog38 a (fun j => star (a j)) ζ = alLog38 a ζ) ∧
    ∀ p ∈ U, ∀ z : ℂ, ‖z‖ = R →
      ‖alComplexLog38 p.1 p.2 z⁻¹‖ ≤ C := by
  classical
  set X := (ZMod L → ℂ) × (ZMod L → ℂ) with hX
  set st : (ZMod L → ℂ) → (ZMod L → ℂ) := fun a j => star (a j) with hst
  have hstc : Continuous st := continuous_pi fun j => continuous_star.comp (continuous_apply j)
  set K' : Set (ZMod L → ℂ) := K ∪ st '' K with hK'
  have hK'c : IsCompact K' := hK.union (hK.image hstc)
  have hK'D : ∀ a ∈ K', IsALField38 a := by
    intro a ha
    rcases ha with ha | ⟨b, hb, rfl⟩
    · exact hKD ha
    · exact al031_star_field (hKD hb)
  set S : Set X := alIota38 '' K' with hS
  have hSc : IsCompact S := hK'c.image alIota38.continuous
  -- local data at each point of S
  have hloc : ∀ p ∈ S, ∃ (Up : Set X) (ρ s Cp : ℝ), IsOpen Up ∧ p ∈ Up ∧ Up ⊆ alComplexDomain38 L ∧
      0 < ρ ∧ ρ ≤ 1 ∧ 0 < s ∧ closedBall p s ⊆ Up ∧ 0 ≤ Cp ∧
      (∀ ζ ∈ ball (0 : ℂ) ρ, ∀ q ∈ Up,
        alComplexD38 q.1 q.2 ζ ∈ Complex.slitPlane ∧ alComplexG38 q.1 q.2 ζ ∈ Complex.slitPlane) ∧
      (∀ ζ ∈ ball (0 : ℂ) ρ, ∀ q ∈ Up,
        AnalyticAt ℂ (fun r : ℂ × X => alComplexLog38 r.2.1 r.2.2 r.1) (ζ, q)) ∧
      (∀ ζ ∈ ball (0 : ℂ) ρ, ∀ q ∈ Up,
        Complex.exp (alComplexLog38 q.1 q.2 ζ) = alComplexG38 q.1 q.2 ζ) ∧
      (∀ α : ZMod L → ℂ, IsALField38 α → alIota38 α ∈ Up →
        ∀ ζ ∈ ball (0 : ℂ) ρ, alComplexLog38 α (fun j => star (α j)) ζ = alLog38 α ζ) ∧
      (∀ ζ ∈ closedBall (0 : ℂ) (ρ / 2), ∀ q ∈ closedBall p s,
        ‖alComplexLog38 q.1 q.2 ζ‖ ≤ Cp) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨U, ρ, hUo, hpU, hUd, hρ, hρ1, hslit, hana, hexp, hreal⟩ :=
      exists_alComplexLogNhd38 (hK'D a ha)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo _ hpU
    have hs : 0 < ε / 2 := by positivity
    have hcb : closedBall (alIota38 a) (ε / 2) ⊆ U := fun q hq =>
      hball (lt_of_le_of_lt (mem_closedBall.1 hq) (by linarith))
    have hT : IsCompact (closedBall (0 : ℂ) (ρ / 2) ×ˢ closedBall (alIota38 a) (ε / 2)) :=
      (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
    have hcont : ContinuousOn
        (fun r : ℂ × X => alComplexLog38 r.2.1 r.2.2 r.1)
        (closedBall (0 : ℂ) (ρ / 2) ×ˢ closedBall (alIota38 a) (ε / 2)) := by
      intro r hr
      refine (hana r.1 ?_ r.2 (hcb hr.2)).continuousAt.continuousWithinAt
      rw [mem_ball, dist_zero_right]
      have := mem_closedBall_zero_iff.1 hr.1
      linarith
    obtain ⟨C0, hC0⟩ := hT.exists_bound_of_continuousOn hcont
    refine ⟨U, ρ, ε / 2, max C0 0, hUo, hpU, hUd, hρ, hρ1, hs, hcb, le_max_right _ _,
      hslit, hana, hexp, hreal, fun ζ hζ q hq => ?_⟩
    exact (hC0 (ζ, q) ⟨hζ, hq⟩).trans (le_max_left _ _)
  choose! Up ρ s Cp hUo hpU hUd hρ0 hρ1 hs0 hcb hCp0 hslit hana hexp hreal hbd using hloc
  obtain ⟨t, htS, hcov⟩ := hSc.elim_nhds_subcover (fun p => ball p (s p))
    (fun p hp => ball_mem_nhds p (hs0 p hp))
  set R : ℝ := 2 + ∑ p ∈ t, 2 / ρ p with hR
  have hsum0 : 0 ≤ ∑ p ∈ t, 2 / ρ p :=
    Finset.sum_nonneg fun p hp => (div_pos two_pos (hρ0 p (htS p hp))).le
  have hR2 : 2 ≤ R := by rw [hR]; linarith
  have hRpos : 0 < R := by linarith
  have hrρ : ∀ p ∈ t, R⁻¹ ≤ ρ p / 2 := by
    intro p hp
    have hρp := hρ0 p (htS p hp)
    have h1 : 2 / ρ p ≤ ∑ q ∈ t, 2 / ρ q :=
      Finset.single_le_sum (f := fun q => 2 / ρ q) (fun q hq => (div_pos two_pos (hρ0 q (htS q hq))).le) hp
    rw [inv_le_comm₀ hRpos (by positivity)]
    calc (ρ p / 2)⁻¹ = 2 / ρ p := by field_simp
      _ ≤ R := by rw [hR]; linarith
  set C : ℝ := ∑ p ∈ t, Cp p with hC
  have hCnn : 0 ≤ C := Finset.sum_nonneg fun p hp => hCp0 p (htS p hp)
  set V : Set X := ⋃ p ∈ t, ball p (s p) with hV
  have hVo : IsOpen V := isOpen_biUnion fun p _ => isOpen_ball
  have hVmem : ∀ q ∈ V, ∃ p ∈ t, q ∈ ball p (s p) := by
    intro q hq
    simpa [hV] using hq
  have hSV : S ⊆ V := fun q hq => by
    have := hcov hq
    simpa [hV] using this
  refine ⟨V ∩ Prod.swap ⁻¹' V, R, C, hVo.inter (hVo.preimage continuous_swap), ?_, ?_, ?_,
    by linarith, hCnn, ?_, ?_, ?_, ?_⟩
  · rintro q ⟨a, ha, rfl⟩
    refine ⟨hSV ⟨a, Or.inl ha, rfl⟩, ?_⟩
    show Prod.swap (alIota38 a) ∈ V
    rw [al031_swap_iota]
    exact hSV ⟨_, Or.inr ⟨a, ha, rfl⟩, rfl⟩
  · intro q hq
    obtain ⟨p, hp, hqp⟩ := hVmem q hq.1
    exact hUd p (htS p hp) (hcb p (htS p hp) (ball_subset_closedBall hqp))
  · intro q hq
    exact ⟨hq.2, by simpa using hq.1⟩
  · rintro ⟨ζ, q⟩ ⟨hζ, hq⟩
    obtain ⟨p, hp, hqp⟩ := hVmem q hq.1
    have hζρ : ζ ∈ ball (0 : ℂ) (ρ p) := by
      rw [mem_ball, dist_zero_right]
      have := mem_closedBall_zero_iff.1 hζ
      have := hrρ p hp
      have := hρ0 p (htS p hp)
      linarith
    exact hana p (htS p hp) ζ hζρ q (hcb p (htS p hp) (ball_subset_closedBall hqp) |> fun h => h)
  · intro q hq ζ hζ
    obtain ⟨p, hp, hqp⟩ := hVmem q hq.1
    have hpS := htS p hp
    have hqU : q ∈ Up p := hcb p hpS (ball_subset_closedBall hqp)
    have hζρ : ζ ∈ ball (0 : ℂ) (ρ p) := by
      rw [mem_ball, dist_zero_right]
      have := mem_closedBall_zero_iff.1 hζ
      have := hrρ p hp
      have := hρ0 p hpS
      linarith
    refine ⟨(hslit p hpS ζ hζρ q hqU).1, (hslit p hpS ζ hζρ q hqU).2, hexp p hpS ζ hζρ q hqU, ?_⟩
    have hζ2 : ζ ∈ closedBall (0 : ℂ) (ρ p / 2) :=
      mem_closedBall_zero_iff.2 ((mem_closedBall_zero_iff.1 hζ).trans (hrρ p hp))
    calc ‖alComplexLog38 q.1 q.2 ζ‖ ≤ Cp p :=
          hbd p hpS ζ hζ2 q (ball_subset_closedBall hqp)
      _ ≤ C := Finset.single_le_sum (f := fun p => Cp p) (fun p hp => hCp0 p (htS p hp)) hp
  · intro a ha haU ζ hζ
    obtain ⟨p, hp, hqp⟩ := hVmem _ haU.1
    have hpS := htS p hp
    have hζρ : ζ ∈ ball (0 : ℂ) (ρ p) := by
      rw [mem_ball, dist_zero_right]
      have := mem_closedBall_zero_iff.1 hζ
      have := hrρ p hp
      have := hρ0 p hpS
      linarith
    exact hreal p hpS a ha (hcb p hpS (ball_subset_closedBall hqp)) ζ hζρ
  · intro q hq z hz
    obtain ⟨p, hp, hqp⟩ := hVmem q hq.1
    have hpS := htS p hp
    have hζ : ‖z⁻¹‖ = R⁻¹ := by rw [norm_inv, hz]
    have hζ2 : z⁻¹ ∈ closedBall (0 : ℂ) (ρ p / 2) :=
      mem_closedBall_zero_iff.2 (hζ ▸ hrρ p hp)
    calc ‖alComplexLog38 q.1 q.2 z⁻¹‖ ≤ Cp p :=
          hbd p hpS z⁻¹ hζ2 q (ball_subset_closedBall hqp)
      _ ≤ C := Finset.single_le_sum (f := fun p => Cp p) (fun p hp => hCp0 p (htS p hp)) hp

end
end NlsGge.ThirdConsultation.AL
