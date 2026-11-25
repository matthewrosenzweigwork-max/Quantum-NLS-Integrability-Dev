import QuantumNLS.TerraMultiRound23ParityResolvent
import QuantumNLS.Local002Hyp

/-! Contour covariance for the sign flip, conditional on the contour
resolvent and integrability properties. These hypotheses are intermediate
conditions, not a claim of LOCAL-003. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
namespace QuantumNLS.LocalSpectral.Round24
open Round23

/-- The sign flip as a complex-linear bounded operator on the actual L² space. -/
def parityOp (L : ℝ) : H2 L →L[ℂ] H2 L where
  toLinearMap := {
    toFun := liftFiber L parityFlipIsometry
    map_add' := fun x y => map_add (parityFlipIsometry.toContinuousLinearMap.compLpₗ 2 (μI L)) x y
    map_smul' := fun c x => liftFiber_parity_smul L c x }
  cont := (parityFlipIsometry.toContinuousLinearMap.compLpL 2 (μI L)).continuous

/-- A bounded linear intertwiner commutes with a circle integral of
operator-valued functions. -/
theorem circle_intertwine {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (J : H →L[ℂ] H) (F G : ℂ → H →L[ℂ] H)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hF : CircleIntegrable F c r) (hG : CircleIntegrable G c r)
    (h : ∀ z ∈ Metric.sphere c r, ∀ x, G z (J x) = J (F z x)) (x : H) :
    (circleIntegral G c r) (J x) = J ((circleIntegral F c r) x) := by
  unfold circleIntegral
  rw [ContinuousLinearMap.intervalIntegral_apply hG.out,
    ContinuousLinearMap.intervalIntegral_apply hF.out]
  rw [← J.intervalIntegral_comp_comm ⟨hF.out.1.apply_continuousLinearMap x, hF.out.2.apply_continuousLinearMap x⟩]
  apply intervalIntegral.integral_congr
  intro θ hθ
  simp only [smul_apply, map_smul]
  rw [h _ (circleMap_mem_sphere c hr θ) x]

/-- Riesz projection covariance when both contour resolvents exist and the
operator-valued resolvents are circle integrable. -/
theorem riesz_parity (L κ : ℝ) (u : ℝ → ℂ) (σ : ℤˣ) (n : ℤ) (r : ℝ)
    (hr : 0 ≤ r)
    (hR : ∀ z ∈ Metric.sphere (center L n) r,
      ∃ R, IsResolvent L κ u σ z R)
    (hS : ∀ z ∈ Metric.sphere (center L n) r,
      ∃ S, IsResolvent L κ (fun x => -u x) σ z S)
    (hF : CircleIntegrable (fun z => resolvent L κ u σ z) (center L n) r)
    (hG : CircleIntegrable (fun z => resolvent L κ (fun x => -u x) σ z) (center L n) r)
    (x : H2 L) :
    rieszProj L κ (fun x => -u x) σ n r (parityOp L x) =
      parityOp L (rieszProj L κ u σ n r x) := by
  unfold rieszProj
  simp only [smul_apply, map_smul]
  congr 1
  apply circle_intertwine (parityOp L) _ _ _ _ hr hF hG
  intro z hz v
  obtain ⟨R, hRz⟩ := hR z hz
  obtain ⟨S, hSz⟩ := hS z hz
  rw [QuantumNLS.Local002.resolvent_eq hRz, QuantumNLS.Local002.resolvent_eq hSz]
  exact resolvent_parity_intertwines L κ u σ z R S hRz hSz v


/-- The same sign covariance holds for the dressed contour integral. -/
theorem dressed_parity (L κ : ℝ) (u : ℝ → ℂ) (n : ℤ) (r : ℝ)
    (hr : 0 ≤ r)
    (hR : ∀ z ∈ Metric.sphere (center L n) r,
      ∃ R, IsResolvent L κ u (parity n) z R)
    (hS : ∀ z ∈ Metric.sphere (center L n) r,
      ∃ S, IsResolvent L κ (fun x => -u x) (parity n) z S)
    (hF : CircleIntegrable (fun z => resolvent L κ u (parity n) z) (center L n) r)
    (hG : CircleIntegrable (fun z => resolvent L κ (fun x => -u x) (parity n) z) (center L n) r)
    (x : H2 L) :
    dressedIntegral L κ (fun x => -u x) n r (parityOp L x) =
      parityOp L (dressedIntegral L κ u n r x) := by
  unfold dressedIntegral
  simp only [smul_apply, map_smul]
  congr 1
  apply circle_intertwine (parityOp L) _ _ _ _ hr
    (hF.fun_continuousOn_smul (continuousOn_id.sub continuousOn_const))
    (hG.fun_continuousOn_smul (continuousOn_id.sub continuousOn_const))
  intro z hz v
  simp only [smul_apply, map_smul]
  obtain ⟨R, hRz⟩ := hR z hz
  obtain ⟨S, hSz⟩ := hS z hz
  rw [QuantumNLS.Local002.resolvent_eq hRz, QuantumNLS.Local002.resolvent_eq hSz]
  exact congrArg (fun w => (z - center L n) • w)
    (resolvent_parity_intertwines L κ u (parity n) z R S hRz hSz v)

end QuantumNLS.LocalSpectral.Round24
#print axioms QuantumNLS.LocalSpectral.Round24.parityOp
#print axioms QuantumNLS.LocalSpectral.Round24.circle_intertwine
#print axioms QuantumNLS.LocalSpectral.Round24.riesz_parity
#print axioms QuantumNLS.LocalSpectral.Round24.dressed_parity
