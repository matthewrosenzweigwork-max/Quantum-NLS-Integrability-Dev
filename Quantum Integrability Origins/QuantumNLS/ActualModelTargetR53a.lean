import QuantumNLS.ActualModelBindingR53a
import QuantumNLS.RB7Smooth

/-! The mixed classical target uses the same chart and physical hierarchy as
DEF-044. Smoothness of the angle-rotated datum follows from preservation of
every weighted sequence norm and the ambient Sobolev inverse. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter Topology MeasureTheory
namespace QuantumNLS.ActualModelTargetR53a
open PhysicalTensor Def033HierarchyR24m ClassicalCharges HierarchyFlow
open Def024LowFlows Def024LowEquivariance
variable {L κ : ℝ} [Fact (0 < L)]

/-- Keep one higher-order witness family, with its uniqueness witness. -/
structure HigherFlows (L κ : ℝ) where
  Φ : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)
  ham : ∀ r, 2 ≤ r → IsHamFlow L (hamiltonian L κ r) (Φ r)
  unique : ∀ r, 2 ≤ r → UniqueHamFlow L (hamiltonian L κ r) (Φ r)
  commute : ∀ r s, 2 ≤ r → 2 ≤ s → ∀ u : Smooth L, ∀ t τ,
    Φ r t (Φ s τ u.val) = Φ s τ (Φ r t u.val)

theorem higher_exists (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (H : HierarchyInputR25m.HierarchyConclusion (κ := κ) C.Φ (Def044ChartR51a.action hκ)) :
    Nonempty (HigherFlows L κ) := by
  obtain ⟨Φ, hΦ, hu, hc, _⟩ := H
  exact ⟨⟨Φ, hΦ, hu, hc⟩⟩

def higher {hκ : 0 < κ} {C : Def021ChartR41b.Chart L κ hκ}
    (H : HierarchyInputR25m.HierarchyConclusion (κ := κ) C.Φ (Def044ChartR51a.action hκ)) :
    HigherFlows L κ :=
  Classical.choice (higher_exists hκ C H)

def flowMap (F : HigherFlows L κ) : ℕ → ℝ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0 => phaseFlow
  | 1 => transFlow
  | r + 2 => F.Φ (r + 2)

omit [Fact (0 < L)] in
theorem flow_isHam (F : HigherFlows L κ) (r : ℕ) :
    IsHamFlow L (hamiltonian L κ r) (flowMap F r) := by
  match r with
  | 0 => exact phase_isHamFlow κ
  | 1 => exact trans_isHamFlow κ
  | r + 2 => exact F.ham (r + 2) (by omega)

theorem flow_unique (F : HigherFlows L κ) (r : ℕ) :
    UniqueHamFlow L (hamiltonian L κ r) (flowMap F r) := by
  match r with
  | 0 => exact (unique_low (Fact.out : 0 < L) κ).1
  | 1 => exact (unique_low (Fact.out : 0 < L) κ).2
  | r + 2 => exact F.unique (r + 2) (by omega)

omit [Fact (0 < L)] in
theorem flow_commute (F : HigherFlows L κ) (r s : ℕ) (u : Smooth L) (t τ : ℝ) :
    flowMap F r t (flowMap F s τ u.val) = flowMap F s τ (flowMap F r t u.val) := by
  match r, s with
  | 0, 0 => simp only [flowMap, phase_add, add_comm t τ]
  | 0, 1 => exact phase_trans_comm t τ u.val
  | 1, 0 => exact (phase_trans_comm τ t u.val).symm
  | 1, 1 => simp only [flowMap, trans_add, add_comm t τ]
  | 0, s + 2 => exact (comm_low_of_unique κ _ (F.ham _ (by omega)) (F.unique _ (by omega))
      u.property τ t).1.symm
  | 1, s + 2 => exact (comm_low_of_unique κ _ (F.ham _ (by omega)) (F.unique _ (by omega))
      u.property τ t).2.symm
  | r + 2, 0 => exact (comm_low_of_unique κ _ (F.ham _ (by omega)) (F.unique _ (by omega))
      u.property t τ).1
  | r + 2, 1 => exact (comm_low_of_unique κ _ (F.ham _ (by omega)) (F.unique _ (by omega))
      u.property t τ).2
  | r + 2, s + 2 => exact F.commute _ _ (by omega) (by omega) u t τ

def hamFlows (F : HigherFlows L κ) (R : Finset ℕ) : HamFlows L κ R :=
  ⟨flowMap F, fun r _ => flow_isHam F r⟩

def angle (I : Finset ℤ) (θ : ℤ → ℝ) (n : ℤ) : Circle :=
  if n ∈ I then Circle.exp (-θ n) else 1

def rotate {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ)
    (I : Finset ℤ) (θ : ℤ → ℝ) (u : L2T L) : L2T L :=
  C.Ψ (ActionTorus.rotate (angle I θ) (C.Φ u))

theorem rotate_coordinate {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ)
    (I : Finset ℤ) (θ : ℤ → ℝ) (u : L2T L) (n : ℤ) :
    C.Φ (rotate C I θ u) n =
      (if n ∈ I then Complex.exp (-(θ n : ℂ) * Complex.I) else 1) * C.Φ u n := by
  rw [rotate, C.right_inverse, ActionTorus.rotate_apply]
  congr 1
  by_cases hn : n ∈ I
  · simp [angle, hn, Circle.coe_exp, Complex.exp_neg]
  · simp [angle, hn]

theorem rotate_action {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ)
    (I : Finset ℤ) (θ : ℤ → ℝ) (u : L2T L) (n : ℤ) :
    ‖C.Φ (rotate C I θ u) n‖ ^ 2 = ‖C.Φ u n‖ ^ 2 := by
  rw [rotate, C.right_inverse, ActionTorus.rotate_apply, norm_mul, Circle.norm_coe, one_mul]

/-- The rotation equals the physical Hamiltonian torus action from the
accepted chart theorem, with the sign fixed by its intertwining formula. -/
theorem rotate_eq_action {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ)
    (I : Finset ℤ) (θ : ℤ → ℝ) (u : L2T L) :
    rotate C I θ u = RF535Final.Tact hκ (angle I θ)⁻¹ u := by
  let c := Def021ChartR41b.localChart L
  have H := (RF535Final.global_actual_chart L).2 c.d c.CL c.Φ c.Ψ
    c.positive c.nonnegative c.spec κ hκ
  obtain ⟨_, _, w, _, _, _, _, _, _, _, _, hw, _, _, _, _, _, _, _, hLocal, _, _, _, hAct, _⟩ := H.2
  have hz := AnalyticIdentity.identity_of_vanishing_ball_direct
    (fun v => C.Φ v - w v) (fun v => (C.analytic v).sub (hw v))
    (div_pos c.positive (Real.sqrt_pos.2 hκ))
    (fun v hv => sub_eq_zero.mpr ((C.local_agreement v hv).trans (hLocal v hv).symm))
  have hsame (v : L2T L) : C.Φ v = w v := sub_eq_zero.mp (hz v)
  apply (Function.LeftInverse.injective C.left_inverse)
  rw [rotate, C.right_inverse, hsame (RF535Final.Tact hκ (angle I θ)⁻¹ u),
    hAct, inv_inv, ← hsame u]

/-- The physical angle rotation of a smooth datum has a smooth representative. -/
theorem rotate_smooth {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ)
    (I : Finset ℤ) (θ : ℤ → ℝ) (u : Smooth L) :
    ∃ v : Smooth L, physical v = rotate C I θ (physical u) := by
  let z := ActionTorus.rotate (angle I θ) (C.Φ (physical u))
  have hsmooth := RB7.smooth_of_memHs (C.Ψ z) (by
    intro s
    let q : ℝ := max 0 s
    have hq : 0 ≤ q := le_max_left _ _
    obtain ⟨E, hForward, hInverse⟩ := ActualModelChartR52a.sobolev_restrictions hκ C q hq
    let uq : Sobolev.H02 L q := Sobolev.WField.mk (physical u) (RB7.memHs_of_smooth u.property q)
    have hz : Fourier.MemHs L q (fun n => z n) := by
      have hu := Sobolev.h02_mem L q (E uq)
      have he (n : ℤ) : (E uq).val n = C.Φ (physical u) n :=
        (Reg015Setting.toBase_apply q hq (E uq) n).symm.trans
          (congrArg (fun a : REF88Chart.K => a n) (hForward uq))
      unfold Fourier.MemHs at hu ⊢
      simpa only [z, ActionTorus.rotate_apply, norm_mul, Circle.norm_coe, one_mul, he] using hu
    let zq : Sobolev.h02 L q := Sobolev.h02.ofMem hz
    have hToBase : Reg015Setting.toBase q hq zq = z := by
      apply lp.ext
      funext n
      exact Reg015Setting.toBase_apply q hq zq n
    have hv : (E.symm zq).val = C.Ψ z := (hInverse zq).trans (congrArg C.Ψ hToBase)
    have hm := (Sobolev.H02.mono (le_max_right 0 s) (E.symm zq)).summable
    change Fourier.MemHsLp L s (E.symm zq).val at hm
    rwa [hv] at hm)
  obtain ⟨v, hv, he⟩ := hsmooth
  exact ⟨⟨v, hv⟩, he⟩

def rotateSmooth {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ)
    (I : Finset ℤ) (θ : ℤ → ℝ) (u : Smooth L) : Smooth L :=
  Classical.choose (rotate_smooth C I θ u)

theorem rotateSmooth_physical {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ)
    (I : Finset ℤ) (θ : ℤ → ℝ) (u : Smooth L) :
    physical (rotateSmooth C I θ u) = rotate C I θ (physical u) :=
  Classical.choose_spec (rotate_smooth C I θ u)

/-- Apply the exact action angles first, then the actual joint Riccati flow. -/
def target {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ) (F : HigherFlows L κ)
    (I : Finset ℤ) (R : Finset ℕ) (θ : ℤ → ℝ) (t : ℕ → ℝ) (u : Smooth L) : L2T L :=
  physical (jointSmooth (hamFlows F R) t (rotateSmooth C I θ u))

end QuantumNLS.ActualModelTargetR53a

#print axioms QuantumNLS.ActualModelTargetR53a.flow_commute
#print axioms QuantumNLS.ActualModelTargetR53a.rotate_coordinate
#print axioms QuantumNLS.ActualModelTargetR53a.rotate_eq_action
#print axioms QuantumNLS.ActualModelTargetR53a.rotate_smooth
#print axioms QuantumNLS.ActualModelTargetR53a.target
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelTargetR53a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelTargetR53a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R53a aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
