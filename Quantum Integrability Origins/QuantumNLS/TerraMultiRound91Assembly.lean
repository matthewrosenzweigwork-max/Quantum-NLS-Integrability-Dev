import QuantumNLS.TerraMultiRound91Comparison
import QuantumNLS.TerraMultiRound88Zero

/-! R-B2E70586 intermediate: full torus from the exact printed fixed-product
mixed convergence input. The accepted predecessor must replace that named
input before a final unconditional theorem is declared. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096
noncomputable section
open Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.CountRotations
open QuantumNLS.HighAngleRotations QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.ActualModelQuantumR52a QuantumNLS.TerraMultiRound91Mixed
open QuantumNLS.TerraMultiRound91Comparison QuantumNLS.TerraMultiRound91QuantumTruncation
namespace QuantumNLS.TerraMultiRound91Assembly
variable {L κ : ℝ} [Fact (0 < L)]

theorem full_zero_error (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (orders : Finset ℕ) (T : ℕ → ℝ) (N : ℕ) (hk : 0 ≤ N+1) :
    fullError hκ u orders T 0 N hk = 0 := by
  apply le_antisymm _ bot_le
  unfold fullError
  apply iSup_le
  intro t
  apply iSup_le
  intro θ
  let b := Def044D1SpectralR51a.basis (L := L) hκ N
  let z := quantumRotation b θ (chargeUnitary hκ orders t.val N (HighMomentsOps.wvec (N+1) (physical u)))
  have hz : ‖z.val‖ = 1 := by
    change ‖z‖ = 1
    change ‖quantumRotation b θ (chargeUnitary hκ orders t.val N (HighMomentsOps.wvec (N+1) (physical u)))‖ = 1
    rw [(quantumRotation b θ).norm_map, (chargeUnitary hκ orders t.val N).norm_map]
    change ‖TensorCarrier.htpow (N+1) (physical u)‖ = 1
    rw [TensorCarrier.norm_htpow, hu, one_pow]
  let C := ActualModelBindingR53a.chart (L := L) hκ
  let F : HigherFlows L κ := higher (ActualModelBindingR53a.hierarchy_intermediate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))
  let x := C.Ψ (ActionTorus.rotate θ⁻¹ (C.Φ (physical (jointSmooth (hamFlows F orders) t.val u))))
  change TraceClass.traceNorm (reducedDensityN (N+1) 0 hk z.val - Prop025OInputs.tensorProj 0 x) ≤ 0
  rw [TerraMultiRound88Zero.rank_zero_marginal (N+1) z.val hz x, sub_self, Fidelity.traceNorm_zero]

/-- Exact printed mixed input for this fixed profile and charge family is the
sole explicit hypothesis. Particle number tends to infinity first for fixed
cutoffs; the quantum cutoff and then the energy cutoff are subsequently
removed. This is an intermediate theorem pending the accepted predecessor. -/
theorem full_torus_intermediate (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (orders : Finset ℕ) (MixedFiniteInput : MixedFiniteInput hκ u orders)
    (k : ℕ) (T : ℕ → ℝ) (hT : ∀ r ∈ orders, 0 ≤ T r) :
    Tendsto (fun N => if hk : k ≤ N+1 then fullError hκ u orders T k N hk else 0)
      atTop (𝓝 0) := by
  by_cases hk0 : k = 0
  · subst k
    have heq : (fun N : ℕ => if hk : 0 ≤ N+1 then fullError hκ u orders T 0 N hk else 0) =
        fun _ => (0 : ℝ≥0∞) := by
      funext N
      simp [full_zero_error hκ u hu orders T N]
    rw [heq]
    exact tendsto_const_nhds
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r, _, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr : 0 < r := ENNReal.ofReal_pos.mp hr0
  let C := ChargeEnergy.energyH1 κ (physical u : AddCircle L → ℂ)
  have hfrac : Tendsto (fun E : ℝ => C / E) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hfrac
  have hroot : Tendsto (fun E : ℝ => 4 * Real.sqrt (C / E)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, mul_zero] using hsqrt.const_mul (4 : ℝ)
  have hevent : ∀ᶠ E : ℝ in atTop, 2 * C < E ∧ 4 * Real.sqrt (C / E) < r / 4 :=
    (eventually_gt_atTop (2 * C)).and (hroot.eventually (Iio_mem_nhds (by linarith)))
  obtain ⟨E, hE, hEs⟩ := hevent.exists
  obtain ⟨NE, η, hNE, hη, hlim, hcomp⟩ := cutoff_comparison hκ u hu orders T k hk E hE
  obtain ⟨R₀, hR₀⟩ := hcomp (r / 4) (by positivity)
  have hR : ∀ᶠ R : ℕ in atTop, R₀ ≤ R ∧ η R < r / 4 :=
    (eventually_ge_atTop R₀).and (hlim.eventually (Iio_mem_nhds (by linarith)))
  obtain ⟨R, hRge, hRs⟩ := hR.exists
  have hm : ∀ᶠ N : ℕ in atTop,
      (if hkN : k ≤ N+1 then mixedError hκ u orders (angleBox R) T k N hkN else 0) ≤
        ENNReal.ofReal (r / 4) :=
    ENNReal.tendsto_nhds_zero.mp (MixedFiniteInput (angleBox R) k T hT)
      (ENNReal.ofReal (r / 4)) (ENNReal.ofReal_pos.mpr (by positivity))
  filter_upwards [hm, eventually_ge_atTop NE, eventually_ge_atTop k] with N hmN hN hkN
  have hkN' : k ≤ N+1 := hkN.trans (Nat.le_succ N)
  have hN' : NE ≤ N+1 := hN.trans (Nat.le_succ N)
  rw [dif_pos hkN'] at hmN ⊢
  have hbound := hR₀ R hRge N hN' hkN'
  have hsmall : 4 * Real.sqrt (C / E) + η R + r / 4 + r / 4 ≤ r := by linarith
  have hηR : 0 ≤ η R := hη R
  have hsum : ENNReal.ofReal (4 * Real.sqrt (C / E) + η R) +
      ENNReal.ofReal (r / 4) + ENNReal.ofReal (r / 4) ≤ ENNReal.ofReal r := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hsmall
  exact (hbound.trans ((add_le_add (add_le_add le_rfl hmN) le_rfl).trans hsum)).trans hrε.le

#print axioms full_zero_error
#print axioms full_torus_intermediate
#print MixedFiniteInput
end QuantumNLS.TerraMultiRound91Assembly
