import QuantumNLS.ReconstructionInputsR33m
import QuantumNLS.DynSeedR47b
import QuantumNLS.TerraMultiRound88Input
import QuantumNLS.TerraMultiRound89FiniteAngle
import QuantumNLS.RB7BindChart
import QuantumNLS.RB7Commute
import QuantumNLS.RB7BindTopology

/-! Restriction of the printed actual-model estimate to finite circle angles.
The actual flow, charge unitary and classical chart agree on both sides. -/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
noncomputable section

open Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace QuantumNLS.DynamicGaugeMixedR34m

open ActualModelTargetR53a Def033HierarchyR24m PhysicalTensor
open CountRotations DynSeedInputR47b
open ReconstructionR33m (flows)
open ActualModelCorollaryR53a (boxError convergence)
open TerraMultiRound89FiniteAngle (representative representative_bound)
open BetheCoefficientTransform

variable {L κ : ℝ} [Fact (0 < L)]

/-- The existing coordinate formula applies to the selected Hamiltonian
flows. Derivative frequencies are constant on each fixed modulus torus. -/
theorem orbit_coordinates (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L)
    (R : Finset ℕ) (t : ℕ → ℝ) (j : ℤ) :
    let C := Def021ChartR41b.chart L κ hκ
    let hReg := Reg015HFinal.REG015_final (L := L) hκ
    let CF := RB7BindChart.chartFactsOf C
    C.Φ (classicalOrbit hκ F u R t) j =
      Complex.exp (((-(∑ r ∈ R, t r * RB7.FreqSeq ((RB7.SOf r : ℝ≥0) : ℝ)
        (RB7.Fd hReg CF r) (fun m => C.Φ (physical u) m) j) : ℝ) : ℂ) *
        Complex.I) * C.Φ (physical u) j := by
  let C := Def021ChartR41b.chart L κ hκ
  let hReg := Reg015HFinal.REG015_final (L := L) hκ
  let CF := RB7BindChart.chartFactsOf C
  let G := hamFlows F R
  have hj : ClassicalCharges.SmoothPeriodic L (HierarchyFlow.jointClassicalFlow G t u.val) := by
    rw [← RB7BindTopology.jointSmooth_val G t u]
    exact (jointSmooth G t u).property
  have hw := RB7.joint_rotation_form hReg CF G t u.property hj j
  have he : SmoothScalarMomentsPhysical.smoothL2 hj =
      physical (jointSmooth G t u) :=
    RB7.smoothL2_congr (RB7BindTopology.jointSmooth_val G t u).symm hj
      (jointSmooth G t u).property
  rw [he] at hw
  exact hw

theorem orbit_moduli (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L)
    (R : Finset ℕ) (t : ℕ → ℝ) (j : ℤ) :
    ‖(Def021ChartR41b.chart L κ hκ).Φ (classicalOrbit hκ F u R t) j‖ =
      ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) j‖ := by
  rw [orbit_coordinates, norm_mul, Complex.norm_exp]
  simp

theorem target_eq_angle_orbit (hκ : 0 < κ) (F : HigherFlows L κ) (u : Smooth L)
    (I : Finset ℤ) (R : Finset ℕ) (t : ℕ → ℝ) (θ : AngleTorus) (hθ : ∀ j ∉ I, θ j = 1) :
    target (Def021ChartR41b.chart L κ hκ) F I R (representative θ) t u =
      physicalAngle hκ θ (classicalOrbit hκ F u R t) := by
  let C := Def021ChartR41b.chart L κ hκ
  let v := rotateSmooth C I (representative θ) u
  let hReg := Reg015HFinal.REG015_final (L := L) hκ
  let CF := RB7BindChart.chartFactsOf C
  have htr : HighAngleRotations.truncate I θ = θ := by
    funext j
    by_cases hj : j ∈ I <;> simp [HighAngleRotations.truncate, hj, hθ]
  have hv : ∀ j, C.Φ (physical v) j = (((θ j)⁻¹ : Circle) : ℂ) * C.Φ (physical u) j := by
    intro j
    rw [rotateSmooth_physical]
    unfold rotate
    rw [C.right_inverse, TerraMultiRound89FiniteAngle.classical_angle_same_parameter, htr,
      ActionTorus.rotate_apply]
    rfl
  have hω (r : ℕ) (j : ℤ) :
      RB7.FreqSeq ((RB7.SOf r : ℝ≥0) : ℝ) (RB7.Fd hReg CF r)
        (fun m => C.Φ (physical v) m) j =
      RB7.FreqSeq ((RB7.SOf r : ℝ≥0) : ℝ) (RB7.Fd hReg CF r)
        (fun m => C.Φ (physical u) m) j := by
    have h := RB7.omegaOf_congr hReg CF r u.property v.property (fun j => (θ j)⁻¹)
      (fun m => hv m) j
    exact (RB7.omegaOf_eq_FreqSeq hReg CF r v.property j).symm.trans
      (h.trans (RB7.omegaOf_eq_FreqSeq hReg CF r u.property j))
  change classicalOrbit hκ F v R t = physicalAngle hκ θ (classicalOrbit hκ F u R t)
  apply (Function.LeftInverse.injective C.left_inverse)
  apply lp.ext
  funext j
  change C.Φ (classicalOrbit hκ F v R t) j =
    C.Φ (C.Ψ (coordinateRotation θ (C.Φ (classicalOrbit hκ F u R t)))) j
  rw [C.right_inverse, coordinateRotation, ActionTorus.rotate_apply,
    orbit_coordinates hκ F v R t j, orbit_coordinates hκ F u R t j, hv j]
  dsimp only
  have hsum :
      (∑ r ∈ R, t r * RB7.FreqSeq ((RB7.SOf r : ℝ≥0) : ℝ) (RB7.Fd hReg CF r)
        (fun m => C.Φ (physical v) m) j) =
      ∑ r ∈ R, t r * RB7.FreqSeq ((RB7.SOf r : ℝ≥0) : ℝ) (RB7.Fd hReg CF r)
        (fun m => C.Φ (physical u) m) j :=
    Finset.sum_congr rfl (fun r _ => by rw [hω])
  rw [hsum, mul_left_comm]

theorem joint_inactive (F : HigherFlows L κ) (R : Finset ℕ)
    (t s : ℕ → ℝ) (h : ∀ r ∈ R, t r = s r) (u : Smooth L) :
    jointSmooth (hamFlows F R) t u = jointSmooth (hamFlows F R) s u := by
  have hs (r : ℕ) (v : Smooth L) :
      smoothStep (hamFlows F R) r (t r) v = smoothStep (hamFlows F R) r (s r) v := by
    by_cases hr : r ∈ R
    · rw [h r hr]
    · simp [smoothStep, hr]
  unfold jointSmooth
  generalize R.sort (· ≤ ·) = rs
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.foldr_cons, hs]

theorem mixed_finite_ofInput (hκ : 0 < κ)
    (HierarchyR7B122087Input : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (RE679E41DInput : TerraMultiRound88Input.RE679E41DInput hκ HierarchyR7B122087Input)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ) :
    MixedFinite hκ (flows hκ HierarchyR7B122087Input) u R := by
  intro I k lo hi
  let T : ℕ → ℝ := fun r => max |lo r| |hi r|
  have hT (r : ℕ) : 0 ≤ T r := (abs_nonneg _).trans (le_max_left _ _)
  let Θ : ℤ → ℝ := fun _ => Real.pi
  let F := flows hκ HierarchyR7B122087Input
  let C := Def021ChartR41b.chart L κ hκ
  let Ω (n : ℕ) := HighMomentsOps.wvec (n+1) (physical u)
  have hlim := TerraMultiRound88Input.finite_box_product_intermediate hκ
    HierarchyR7B122087Input RE679E41DInput u hu I R k Θ T
    (fun _ _ => Real.pi_pos.le) (fun r _ => hT r)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [] with n
    by_cases hn : k ≤ n+1
    · simp only [dite_eq_left hn]
      apply iSup_le
      intro t
      apply iSup_le
      intro θ
      have ht (r : ℕ) (hr : r ∈ R) : |t.val r| ≤ T r := by
        have he : t.val r ∈ Set.Icc (lo r) (hi r) := by simpa [hr] using t.property r
        exact abs_le_max_abs_abs he.1 he.2
      have htr : HighAngleRotations.truncate I θ.val = θ.val := by
        funext j
        by_cases hj : j ∈ I <;> simp [HighAngleRotations.truncate, hj, θ.property]
      have he := TerraMultiRound89FiniteAngle.count_unitary_eq_rotation hκ I θ.val n (Ω n)
      rw [htr] at he
      let Tbox := {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r}
      let Abox := {θ : ℤ → ℝ // ∀ j ∈ I, |θ j| ≤ Θ j}
      let M (s : Tbox) (a : Abox) :=
        marginalError n k hn (ActualModelQuantumR52a.chargeUnitary hκ R s.val n
          (ActualModelQuantumR52a.countUnitary hκ I a.val n (Ω n)))
          (target C F I R a.val s.val u)
      let s : Tbox := ⟨t.val, ht⟩
      let a : Abox := ⟨representative θ.val, fun j _ => representative_bound _ j⟩
      have hbound := (le_iSup (M s) a).trans (le_iSup (fun s => ⨆ a, M s a) s)
      change marginalError n k hn (ActualModelQuantumR52a.chargeUnitary hκ R t.val n
          (ActualModelQuantumR52a.countUnitary hκ I (representative θ.val) n (Ω n)))
        (target C F I R (representative θ.val) t.val u) ≤ _ at hbound
      rw [he, target_eq_angle_orbit hκ F u I R t.val θ.val θ.property] at hbound
      exact hbound
    · simp [hn]

end QuantumNLS.DynamicGaugeMixedR34m
