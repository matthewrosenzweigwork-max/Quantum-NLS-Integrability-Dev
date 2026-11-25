import QuantumNLS.TerraMultiRound85FlowScalingL2

/-! Common unit-phase covariance of the actual cubic physical flow. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Global
open QuantumNLS.H1Bridge QuantumNLS.L2Flow QuantumNLS.DuhamelDuality
open QuantumNLS.TerraMultiRound85H1Bridge QuantumNLS.TerraMultiRound85H1Density
namespace QuantumNLS.TerraMultiRound85PhaseFlow
variable {L : ℝ} [Fact (0 < L)]

/-- The cubic map commutes with every unit complex phase. -/
theorem Fh_unit_phase {s : ℝ} (hs : 1 ≤ s) (c : ℂ) (hc : ‖c‖ = 1) (a : h04 L s) :
    Fh hs (c • a) = c • Fh hs a := by
  apply WSeq.ext
  funext n
  change coeff L (nlRep L ((c • a).val)) n = c * coeff L (nlRep L a.val) n
  have hn : nlRep L ((c • a).val) = fun x => c * nlRep L a.val x := by
    funext x
    have hval : (c • a).val = fun n => c * a.val n := by funext k; rfl
    rw [hval]
    simp only [nlRep, seriesRep_smul', norm_mul, hc, one_mul]
    ring
  rw [hn, coeff_const_mul]

/-- A global mild solution remains mild after a constant unit phase. -/
theorem phase_mild {κ : ℝ} (c : ℂ) (hc : ‖c‖ = 1) (u0 : h04 L 1) (u : ℝ → h04 L 1)
    (hu : IsMild (le_refl (1 : ℝ)) κ Set.univ u0 u) :
    IsMild (le_refl (1 : ℝ)) κ Set.univ (c • u0) (fun t => c • u t) := by
  refine ⟨Set.mem_univ _, Set.ordConnected_univ, ?_, ?_⟩
  · exact ((continuousOn_univ.mp hu.cont).const_smul c).continuousOn
  · intro t ht
    have h := hu.duhamel_eq t (Set.mem_univ t)
    unfold duhamel at h ⊢
    simp_rw [Fh_unit_phase _ c hc, map_smul, intervalIntegral.integral_smul]
    rw [h, smul_sub]
    simp only [smul_smul]
    congr 1
    congr 1
    ring

/-- On all H¹ data the actual flow commutes with constant phases. -/
theorem phase_flow_H1 {κ : ℝ} (hκ : 0 ≤ κ) (c : ℂ) (hc : ‖c‖ = 1) (g : h04 L 1) (t : ℝ) :
    flowMap hκ (c • emb g) t = c • flowMap hκ (emb g) t := by
  let u := umax (le_refl (1 : ℝ)) κ g
  have hu := umax_mild (hs := le_refl (1 : ℝ)) hκ g
  rw [Imax1_eq_univ hκ g] at hu
  have h := flowMap_of_global_mild hκ (c • g) (fun t => c • u t) (phase_mild c hc g u hu) t
  rw [flowMap_H1 hκ g t]
  simpa only [map_smul] using h

/-- By dense H¹ approximation, the actual L² flow commutes with phases. -/
theorem phase_flow {κ : ℝ} (hκ : 0 ≤ κ) (c : ℂ) (hc : ‖c‖ = 1) (u : HL L) (t : ℝ) :
    flowMap hκ (c • u) t = c • flowMap hκ u t := by
  have hscalar : Continuous (fun u : HL L => c • u) := by fun_prop
  have h1 : Continuous (fun u : HL L => flowMap hκ (c • u) t) :=
    (continuous_flowMap hκ t).comp hscalar
  have h2 : Continuous (fun u : HL L => c • flowMap hκ u t) :=
    hscalar.comp (continuous_flowMap hκ t)
  have he := Continuous.ext_on (denseRange_emb (L := L)) h1 h2 (by
    rintro _ ⟨g, rfl⟩
    exact phase_flow_H1 hκ c hc g t)
  exact congrFun he u

#print axioms Fh_unit_phase
#print axioms phase_mild
#print axioms phase_flow_H1
#print axioms phase_flow
end QuantumNLS.TerraMultiRound85PhaseFlow
