import QuantumNLS.AllOrderEnergyRankTwoR56a
import QuantumNLS.AllOrderEnergyInputsR57a
import QuantumNLS.AllOrderEnergyQuantumR56a

/-! On the physical marginals of the exact charge evolution, assemble the
energy identity, the compact contact limit and the positive trace upgrade. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.AllOrderEnergyAssemblyR57a
open EnergyPreparationDef PhysicalEnergy PhysicalTensor TensorCarrier
open BetheCoefficientTransform BethePhysicalTransfer ContactOperator
open CollisionIdentification MarginalEnergy TraceClass EnergyTraceConvergence Ext025B10EnergyFamily
open Def033HierarchyR24m ActualModelTargetR53a AllOrderEnergyInputsR56a
open scoped InnerProductSpace
open AllOrderEnergyPairR56a AllOrderEnergyPhysicalR56a AllOrderEnergyIdentityR56a
open AllOrderEnergyProductR56a AllOrderEnergyQuantumR56a AllOrderEnergyTraceR55a
variable {L κ : ℝ} [Fact (0 < L)]

/-- A bounded form on physical H¹, with the usual conjugate-linear test
slot and linear state slot. Its target is the continuous anti-dual of H¹. -/
abbrev BoundedForm (L : ℝ) [Fact (0 < L)] (k : ℕ) :=
  PhysH1 L k →L⋆[ℂ] PhysH1 L k →L[ℂ] ℂ

/-- The physical A_k-root coordinate map, from H¹ to tensor L². -/
def formCoordinates (L : ℝ) [Fact (0 < L)] (k : ℕ) : PhysH1 L k ≃ₗᵢ[ℂ] Xk L k :=
  (PhysH1.unitary (L := L) (k := k)).trans (physUnitary (L := L) (N := k)).symm

/-- Riesz representation of the bounded form in A_k-root coordinates. -/
def formSandwich {k : ℕ} (C : BoundedForm L k) : Xk L k →L[ℂ] Xk L k :=
  let e := (formCoordinates L k).symm.toContinuousLinearEquiv.toContinuousLinearMap
  (InnerProductSpace.continuousLinearMapOfBilin (C.bilinearComp e e)).adjoint

theorem formSandwich_pairing {k : ℕ} (C : BoundedForm L k) (f g : PhysH1 L k) :
    ⟪formCoordinates L k f, formSandwich C (formCoordinates L k g)⟫_ℂ = C f g := by
  rw [formSandwich]
  rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  simp [formCoordinates]

theorem formCoordinates_eq_root {k : ℕ} (f : PhysH1 L k) :
    ∃ hf : (physUnitary (L := L) (N := k)).symm f.val ∈ (AhalfT L k).domain,
      formCoordinates L k f = AhalfT L k ⟨_, hf⟩ := by
  refine ⟨(AllOrderEnergyPairR56a.toHalf f).property, ?_⟩
  exact (physUnitary (L := L) (N := k)).symm_apply_eq.mpr
    (AllOrderEnergyPairR56a.root_toHalf f).symm

/-- Physical form expectation of a positive density with finite kinetic trace. -/
def formExpectation {k : ℕ} (C : BoundedForm L k) (ρ : FiniteEnergy L k) : ℂ :=
  EnergyFormPass.expectation (formSandwich C) ρ

/-- Pairing with a pure density is the original bounded form on its wave function. -/
theorem formExpectation_pure {k : ℕ} (C : BoundedForm L k) (f : PhysH1 L k) :
    formExpectation C (EnergyTraceConvergence.pure (toHalf f)) = C f f := by
  rw [formExpectation, EnergyFormPass.expectation, EnergyTraceConvergence.sandwich_pure,
    Ext025A12Normal.trace_rankOne_left]
  have h : AhalfT L k (toHalf f) = formCoordinates L k f :=
    ((physUnitary (L := L) (N := k)).symm_apply_eq.mpr (root_toHalf f).symm).symm
  rw [h]
  exact formSandwich_pairing C f f

private theorem source_val {N : ℕ} {ψ : HN L N} {x : VSym L N}
    (hx : valSym x = symmetricPosition L N ψ) :
    x.val.val = physUnitary ψ.val := congrArg (fun z : SymL2 L N => z.val) hx

private def sourceMarginal {N : ℕ} {ψ : HN L N} (x : VSym L N)
    (hx : valSym x = symmetricPosition L N ψ)
    (k : ℕ) (f : (AhalfT L k).domain) : FiniteEnergy L k :=
  if hk : k ≤ N then
    marginal hk ψ.val x.val (source_val hx)
  else EnergyTraceConvergence.pure f

private theorem sourceMarginal_val {N : ℕ} {ψ : HN L N} (x : VSym L N)
    (hx : valSym x = symmetricPosition L N ψ)
    {k : ℕ} (hk : k ≤ N) (f : (AhalfT L k).domain) :
    (sourceMarginal x hx k f).val = reducedDensityN N k hk ψ.val := by
  rw [sourceMarginal, dite_eq_left hk]
  rfl

private theorem source_trace_one {N k : ℕ} {ψ : HN L N} (x : VSym L N)
    (hx : valSym x = symmetricPosition L N ψ) (hψ : ‖ψ‖ = 1)
    (f : (AhalfT L k).domain) (hf : ‖(f : Xk L k)‖ = 1) :
    posTrace (sourceMarginal x hx k f).val = 1 := by
  by_cases hk : k ≤ N
  · simp only [sourceMarginal, dite_eq_left hk]
    exact marginal_trace_one hk ψ.val x.val (source_val hx) hψ
  · simp only [sourceMarginal, dite_eq_right hk]
    change posTrace (InnerProductSpace.rankOne ℂ (f : Xk L k) (f : Xk L k)) = 1
    rw [Fidelity.posTrace_rankOne_self, hf, one_pow, ENNReal.ofReal_one]

private theorem source_rank_trace {N k : ℕ} (hk : k ≤ N) (h1 : 1 ≤ N) {ψ : HN L N}
    (x : VSym L N) (hx : valSym x = symmetricPosition L N ψ) (hψ : ‖ψ‖ = 1)
    (f : (AhalfT L k).domain) (fOne : (AhalfT L 1).domain) (a : Fin N) :
    (energyTrace (sourceMarginal x hx k f).val).toReal =
      1 + (k : ℝ) * ((energyTrace (sourceMarginal x hx 1 fOne).val).toReal - 1) := by
  simp only [sourceMarginal, dite_eq_left hk, dite_eq_left h1]
  let z := ‖gradientCLM a x.val‖ ^ 2
  have hK : energyTrace (marginal hk ψ.val x.val (source_val hx)).val =
      ENNReal.ofReal (1 + (k : ℝ) * z) :=
    marginal_energy_sym hk ψ.val x.val (source_val hx) hψ x.property a
  have hOne : energyTrace (marginal h1 ψ.val x.val (source_val hx)).val =
      ENNReal.ofReal (1 + z) := by
    simpa only [Nat.cast_one, one_mul] using
      marginal_energy_sym h1 ψ.val x.val (source_val hx) hψ x.property a
  have hz : 0 ≤ z := sq_nonneg _
  rw [hK, hOne, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 + (k : ℝ) * z),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 + z), add_sub_cancel_left]

private theorem graph_on_profile {T : Type*} [TopologicalSpace T]
    (v : T → Smooth L) (hv : ∀ t, ‖physical (v t)‖ = 1) (hV : Continuous v) (k : ℕ) :
    Continuous (fun t =>
      let f := productHalf k (hv t) (PhysicalProductPreparation.oneH1_smooth (v t).property)
      ((f : Xk L k), AhalfT L k f)) := by
  let U := {u : Smooth L // ‖physical u‖ = 1}
  let v' : T → U := fun t => ⟨v t, hv t⟩
  have hv' : Continuous v' :=
    Continuous.subtype_mk (p := fun u : Smooth L => ‖physical u‖ = 1) hV hv
  let g : U → Xk L k × Xk L k := fun u =>
    let f := productHalf k u.property (PhysicalProductPreparation.oneH1_smooth u.val.property)
    ((f : Xk L k), AhalfT L k f)
  have hg : Continuous g := continuous_productHalf_graph (L := L) k
  have hc : Continuous (g ∘ v') := hg.comp hv'
  refine hc.congr ?_
  intro t
  rfl

private def kinetic (u : Smooth L) : ℝ := ChargeEnergy.kinetic ((physical u : L2T L) : AddCircle L → ℂ)
private def quartic (u : Smooth L) : ℝ := ChargeEnergy.quartic ((physical u : L2T L) : AddCircle L → ℂ)

private theorem kinetic_nonneg (u : Smooth L) : 0 ≤ kinetic u :=
  tsum_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem quartic_nonneg (u : Smooth L) : 0 ≤ quartic u :=
  MeasureTheory.integral_nonneg fun _ => by positivity

private theorem joint_unit (hκ : 0 < κ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (R : Finset ℕ) (t : ℕ → ℝ) (u : Smooth L) (hu : ‖physical u‖ = 1) :
    ‖physical (jointSmooth (hamFlows (flows hκ HierarchyInput) R) t u)‖ = 1 := by
  have h := joint_charge_conserved hκ HierarchyInput u R t 1
  rw [ClassicalCharges.charge_one_L2 (L := L) κ (jointSmooth
    (hamFlows (flows hκ HierarchyInput) R) t u).property,
    ClassicalCharges.charge_one_L2 (L := L) κ u.property] at h
  change ((‖physical (jointSmooth (hamFlows (flows hκ HierarchyInput) R) t u)‖ ^ 2 : ℝ) : ℂ) =
    ((‖physical u‖ ^ 2 : ℝ) : ℂ) at h
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    (by simpa only [hu, one_pow] using Complex.ofReal_injective h)

private theorem joint_I3 (hκ : 0 < κ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (R : Finset ℕ) (t : ℕ → ℝ) (u : Smooth L) :
    I3 κ (physical (jointSmooth (hamFlows (flows hκ HierarchyInput) R) t u)) =
      I3 κ (physical u) := by
  have h := joint_charge_conserved hκ HierarchyInput u R t 3
  rw [charge_three_eq_I3 κ (jointSmooth (hamFlows (flows hκ HierarchyInput) R) t u).property,
    charge_three_eq_I3 κ u.property] at h
  exact Complex.ofReal_injective h

/-- Uniform trace convergence and all bounded physical form expectations
for the exact evolved marginals and the hierarchy tensor projector. -/
def EnergyLimit (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (u : Smooth L) (ψ : ∀ n : ℕ, HN L (n+1))
    (R : Finset ℕ) (K : Set (ℕ → ℝ)) (k : ℕ) : Prop :=
    let v (t : K) := jointSmooth (hamFlows (flows hκ H) R) t.val u
    (Tendsto (fun n => if hk : k ≤ n+1 then
      ⨆ t : K, additiveEnergyTraceNorm
        (reducedDensityN (n+1) k hk (ActualModelQuantumR52a.chargeUnitary hκ R t.val n (ψ n)).val -
          Prop025OInputs.tensorProj k (physical (v t)))
      else 0) atTop (𝓝 0)) ∧
    ∃ (ρ : ℕ → K → FiniteEnergy L k) (σ : K → FiniteEnergy L k),
      (∀ n t (hk : k ≤ n+1), (ρ n t).val =
        reducedDensityN (n+1) k hk (ActualModelQuantumR52a.chargeUnitary hκ R t.val n (ψ n)).val) ∧
      (∀ t, (σ t).val = Prop025OInputs.tensorProj k (physical (v t))) ∧
      ∀ C : BoundedForm L k, TendstoUniformly (fun n t => formExpectation C (ρ n t))
        (fun t => formExpectation C (σ t)) atTop

/-- Physical energy convergence for the norm-close, form-prepared
sequence, conditional on the printed hierarchy and actual-model inputs. -/
theorem physical_energy_intermediate (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (ActualModelRE679E41DInput : AllOrderEnergyInputsR57a.ActualModelRE679E41DInput (L := L) hκ HierarchyR7B122087Input)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (ψ : ∀ n : ℕ, HN L (n+1)) (hψ : ∀ n, ‖ψ n‖ = 1)
    (x : ∀ n : ℕ, VSym L (n+1)) (hx : ∀ n, valSym (x n) = symmetricPosition L (n+1) (ψ n))
    (hprep : Tendsto (fun n => ActualModelCorollaryR53a.preparationError u n (ψ n)) atTop (𝓝 0))
    (hUpper : limsup (fun n => ((hN κ (n+1) (x n).val / (n+1 : ℕ) : ℝ) : EReal))
      atTop ≤ (I3 κ (physical u) : EReal))
    (R : Finset ℕ) (K : Set (ℕ → ℝ)) (hK : IsCompact K) (k : ℕ) :
    EnergyLimit hκ HierarchyR7B122087Input u ψ R K k := by
  classical
  unfold EnergyLimit
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let v (t : K) := jointSmooth (hamFlows (flows hκ HierarchyR7B122087Input) R) t.val u
  let hv (t : K) : ‖physical (v t)‖ = 1 := joint_unit hκ HierarchyR7B122087Input R t.val u hu
  let hH (t : K) := PhysicalProductPreparation.oneH1_smooth (v t).property
  let f (j : ℕ) (t : K) := productHalf j (hv t) (hH t)
  let f₀ (j : ℕ) := productHalf j hu (PhysicalProductPreparation.oneH1_smooth u.property)
  let E (n : ℕ) : ℝ := hN κ (n+1) (x n).val / (n+1 : ℕ)
  let w (n : ℕ) : ℝ := 1 - ((n+1 : ℕ) : ℝ)⁻¹
  let ψt (n : ℕ) (t : K) := ActualModelQuantumR52a.chargeUnitary hκ R t.val n (ψ n)
  have hy (n : ℕ) (t : K) : ∃ y : VSym L (n+1),
      valSym y = symmetricPosition L (n+1) (ψt n t) ∧ hN κ (n+1) y.val = hN κ (n+1) (x n).val := by
    obtain ⟨y, hy, hE⟩ := chargeUnitary_form hκ R t.val n (x n)
    rw [hx n] at hy
    exact ⟨y, by simpa only [positionChargeUnitary, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.symm_apply_apply] using hy, hE⟩
  choose y hval hE using hy
  have huψ (n : ℕ) (t : K) : ‖ψt n t‖ = 1 := by
    simp only [ψt, LinearIsometryEquiv.norm_map, hψ]
  let ρ (j : ℕ) (n : ℕ) (t : K) := sourceMarginal (y n t) (hval n t) j (f j t)
  let ρ₀ (j : ℕ) (n : ℕ) := sourceMarginal (x n) (hx n) j (f₀ j)
  have fval (j : ℕ) (t : K) : (EnergyTraceConvergence.pure (f j t)).val = Prop025OInputs.tensorProj j (physical (v t)) := by
    change InnerProductSpace.rankOne ℂ (f j t : Xk L j) (f j t : Xk L j) = _
    rw [Prop025OInputs.tensorProj]
    have h := productHalf_val j (hv t) (hH t)
    change (f j t : Xk L j) = htpow j (physical (v t)) at h
    rw [h]
  have fval₀ (j : ℕ) : (EnergyTraceConvergence.pure (f₀ j)).val = Prop025OInputs.tensorProj j (physical u) := by
    change InnerProductSpace.rankOne ℂ (f₀ j : Xk L j) (f₀ j : Xk L j) = _
    rw [Prop025OInputs.tensorProj]
    have h := productHalf_val j hu (PhysicalProductPreparation.oneH1_smooth u.property)
    change (f₀ j : Xk L j) = htpow j (physical u) at h
    rw [h]
  have hOrd (j : ℕ) : Tendsto (fun n => ⨆ t, traceNorm ((ρ j n t).val - (EnergyTraceConvergence.pure (f j t)).val)) atTop (𝓝 0) := by
    apply (compact_box_ordinary_limit hκ HierarchyR7B122087Input ActualModelRE679E41DInput
      u hu R K hK j ψ hψ hprep).congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    have hj : j ≤ n+1 := by omega
    simp only [dite_eq_left hj, ρ, sourceMarginal_val _ _ hj, ψt, fval, v]
  have hOrd₀ (j : ℕ) : Tendsto (fun n => traceNorm ((ρ₀ j n).val - (EnergyTraceConvergence.pure (f₀ j)).val)) atTop (𝓝 0) := by
    apply (AllOrderEnergyInputsR55a.initial_trace_limit u hu ψ hψ hprep j).congr'
    filter_upwards [eventually_ge_atTop j] with n hn
    have hj : j ≤ n+1 := by omega
    simp only [dite_eq_left hj, ρ₀, sourceMarginal_val _ _ hj, fval₀]
  have hconserve (t : K) : kinetic u + κ * quartic u = kinetic (v t) + κ * quartic (v t) :=
    (joint_I3 hκ HierarchyR7B122087Input R t.val u).symm
  have hU : limsup (fun n => (E n : EReal)) atTop ≤ ((kinetic u + κ * quartic u : ℝ) : EReal) := hUpper
  let C := contactSandwich (L := L) (0 : Fin 2) 1 (by decide)
  have hI₀ : ∀ᶠ n in atTop, E n = (energyTrace (ρ₀ 1 n).val).toReal - 1 +
      w n * (κ * (EnergyFormPass.expectation C (ρ₀ 2 n)).re) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hk2 : 2 ≤ n+1 := by omega
    have hk1 : 1 ≤ n+1 := by omega
    have h := marginal_energy_identity hk2 κ (ψ n).val (hψ n) (x n).val
      (source_val (hx n)) (x n).property
    simp only [ρ₀, sourceMarginal, dite_eq_left hk1, dite_eq_left hk2, C, E, w]
    rw [h, mul_assoc κ, mul_left_comm κ]
  have hI : ∀ᶠ n in atTop, ∀ t, E n = (energyTrace (ρ 1 n t).val).toReal - 1 +
      w n * (κ * (EnergyFormPass.expectation C (ρ 2 n t)).re) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    intro t
    have hk2 : 2 ≤ n+1 := by omega
    have hk1 : 1 ≤ n+1 := by omega
    have h := marginal_energy_identity hk2 κ (ψt n t).val (huψ n t) (y n t).val
      (source_val (hval n t)) (y n t).property
    rw [hE n t] at h
    simp only [ρ, sourceMarginal, dite_eq_left hk1, dite_eq_left hk2, C, E, w]
    rw [h, mul_assoc κ, mul_left_comm κ]
  let M := kinetic u + κ * quartic u + 1
  let B := 1 + 2 * M
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity [kinetic_nonneg u, quartic_nonneg u, hκ]
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hEu : ∀ᶠ n in atTop, E n ≤ M := (EnergyPreparationDef.limsup_le_iff E _).mp hU 1 zero_lt_one
  have hbnd (t : K) : 1 + 2 * kinetic (v t) ≤ B := by
    dsimp only [B, M]
    linarith only [hconserve t, mul_nonneg hκ.le (quartic_nonneg (v t))]
  have hbndU : 1 + 2 * kinetic u ≤ B := by
    dsimp only [B, M]
    linarith only [mul_nonneg hκ.le (quartic_nonneg u)]
  have hρB : ∀ᶠ n in atTop, ∀ t, energyTrace (ρ 2 n t).val ≤ ENNReal.ofReal B := by
    filter_upwards [eventually_ge_atTop 2, hEu] with n hn hnE
    intro t
    have hk : 2 ≤ n+1 := by omega
    simp only [ρ, sourceMarginal, dite_eq_left hk]
    refine (marginal_energy_bound hk (ψt n t).val (y n t).val
      (source_val (hval n t)) (huψ n t) (ψt n t).property
      (by decide : 1 ≤ 2) κ hκ.le).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hE n t]
    change 1 + (2 / ((n+1 : ℕ) : ℝ)) * hN κ (n+1) (x n).val ≤ B
    have hscaled : (2 / ((n+1 : ℕ) : ℝ)) * hN κ (n+1) (x n).val = 2 * E n := by
      unfold E
      rw [div_mul_eq_mul_div, mul_div_assoc]
    rw [hscaled]
    exact add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_left hnE (by norm_num : (0 : ℝ) ≤ 2))
  have hρ₀B : ∀ᶠ n in atTop, ∀ _ : Unit, energyTrace (ρ₀ 2 n).val ≤ ENNReal.ofReal B := by
    filter_upwards [eventually_ge_atTop 2, hEu] with n hn hnE
    intro _
    have hk : 2 ≤ n+1 := by omega
    simp only [ρ₀, sourceMarginal, dite_eq_left hk]
    refine (marginal_energy_bound hk (ψ n).val (x n).val
      (source_val (hx n)) (hψ n) (ψ n).property
      (by decide : 1 ≤ 2) κ hκ.le).trans (ENNReal.ofReal_le_ofReal ?_)
    change 1 + (2 / ((n+1 : ℕ) : ℝ)) * hN κ (n+1) (x n).val ≤ B
    have hscaled : (2 / ((n+1 : ℕ) : ℝ)) * hN κ (n+1) (x n).val = 2 * E n := by
      unfold E
      rw [div_mul_eq_mul_div, mul_div_assoc]
    rw [hscaled]
    exact add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_left hnE (by norm_num : (0 : ℝ) ≤ 2))
  have hContact := compact_contact_limit (ρ 2) (fun t => physical (v t)) hv hH B hB hρB hbnd (hOrd 2)
  have hContact₀ := compact_contact_limit (fun n (_ : Unit) => ρ₀ 2 n)
    (fun _ => physical u) (fun _ => hu) (fun _ => PhysicalProductPreparation.oneH1_smooth u.property)
    B hB hρ₀B (fun _ => hbndU) (by simpa only [iSup_const] using hOrd₀ 2)
  have hW : Tendsto w atTop (𝓝 1) := by
    have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [w, Function.comp_apply, sub_zero] using tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp hn)
  have hGraph : Continuous (fun t => ((f k t : Xk L k), AhalfT L k (f k t))) :=
    graph_on_profile v hv (AllOrderEnergyInputsR57a.joint_smooth_continuous hκ HierarchyR7B122087Input R u K hK) k
  have hUnit (t : K) : ‖(f k t : Xk L k)‖ = 1 := by
    have h := productHalf_val k (hv t) (hH t)
    change (f k t : Xk L k) = htpow k (physical (v t)) at h
    rw [h, norm_htpow, hv, one_pow]
  have hRank : ∀ᶠ n in atTop, ∀ t, (energyTrace (ρ k n t).val).toReal =
      1 + (k : ℝ) * ((energyTrace (ρ 1 n t).val).toReal - 1) := by
    filter_upwards [eventually_ge_atTop k] with n hn
    intro t
    have hk : k ≤ n+1 := by omega
    have hk1 : 1 ≤ n+1 := by omega
    exact source_rank_trace hk hk1 (y n t) (hval n t) (huψ n t) (f k t) (f 1 t) 0
  have hTrace (n : ℕ) (t : K) : posTrace (ρ k n t).val = 1 :=
    source_trace_one (y n t) (hval n t) (huψ n t) (f k t) (hUnit t)
  have hContactB (t : K) : |κ * quartic (v t)| ≤ M := by
    rw [abs_of_nonneg (mul_nonneg hκ.le (quartic_nonneg (v t)))]
    dsimp only [M]
    linarith only [hconserve t, kinetic_nonneg (v t)]
  have hA₀ : energyTrace (EnergyTraceConvergence.pure (f₀ 1)).val =
      ENNReal.ofReal (1 + kinetic u) := by
    change energyTrace (InnerProductSpace.rankOne ℂ (f₀ 1 : Xk L 1) (f₀ 1 : Xk L 1)) = _
    rw [pure_energy (f₀ 1)]
    have h := productHalf_energy 1 hu (PhysicalProductPreparation.oneH1_smooth u.property)
    exact congrArg ENNReal.ofReal (by simpa only [kinetic, Nat.cast_one, one_mul] using h)
  obtain ⟨_, hlim, hforms⟩ := contact_energy_upgrade (L := L) (k := k) (T := K) E w hW (ρ₀ 1) (EnergyTraceConvergence.pure (f₀ 1))
    (kinetic u) (κ * quartic u) (kinetic_nonneg u)
    hA₀
    (hOrd₀ 1) (fun n => κ * (EnergyFormPass.expectation C (ρ₀ 2 n)).re)
    ((hContact₀.tendsto_at ()).const_mul κ) hI₀ hU (f k) hGraph hUnit (ρ k) hTrace (hOrd k)
    (fun n t => (energyTrace (ρ 1 n t).val).toReal - 1)
    (fun n t => κ * (EnergyFormPass.expectation C (ρ 2 n t)).re)
    (fun t => kinetic (v t)) (fun t => κ * quartic (v t)) hI hconserve
    (Real.uniformContinuous_const_mul (x := κ) |>.comp_tendstoUniformly hContact) M hContactB hM hRank (fun t => productHalf_energy k (hv t) (hH t))
  refine ⟨?_, ρ k, (fun t => EnergyTraceConvergence.pure (f k t)), ?_, fval k, ?_⟩
  · apply hlim.congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    have hk : k ≤ n+1 := by omega
    simp only [dite_eq_left hk, ρ, sourceMarginal_val _ _ hk, ψt, fval, v]
  · intro n t hk
    exact sourceMarginal_val (y n t) (hval n t) hk _
  · intro C
    exact hforms (formSandwich C)

end QuantumNLS.AllOrderEnergyAssemblyR57a
