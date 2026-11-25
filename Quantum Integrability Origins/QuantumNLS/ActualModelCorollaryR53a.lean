import QuantumNLS.ActualModelTargetR53a

/-! R-E679E41D, cor:MP-actual-model (mixed_propagation.tex:102).
Intermediate deduction using the exact PROP-025 estimate at the printed
DEF-044 interfaces and the shared R25m hierarchy predecessor. The positive
particle number is N+1, in both the spectral data and the unchanged rate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter Topology MeasureTheory
open scoped ENNReal
namespace QuantumNLS.ActualModelCorollaryR53a
open PhysicalTensor TensorCarrier TraceClass Def033HierarchyR24m BetheCoefficientTransform
open ActualModelQuantumR52a ActualModelTargetR53a
variable {L κ : ℝ} [Fact (0 < L)]

/-- The norm supremum over the fixed boxes, expressed in the existing
extended nonnegative trace norm. -/
def boxError (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (F : HigherFlows L κ) (u : Smooth L) (I : Finset ℤ) (R : Finset ℕ)
    (Θ : ℤ → ℝ) (T : ℕ → ℝ) (k N : ℕ) (hk : k ≤ N + 1) (ψ : HN L (N + 1)) : ℝ≥0∞ :=
  ⨆ t : {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r},
  ⨆ θ : {θ : ℤ → ℝ // ∀ n ∈ I, |θ n| ≤ Θ n},
    traceNorm (reducedDensityN (N + 1) k hk
      (chargeUnitary hκ R t.val N (countUnitary hκ I θ.val N ψ) :
        HilbertTensorPower ℂ (L2T L) (N + 1)) -
      Prop025OInputs.tensorProj k (target C F I R θ.val t.val u))

def preparationError (u : Smooth L) (N : ℕ) (ψ : HN L (N + 1)) : ℝ :=
  ‖ψ - HighMomentsOps.wvec (N + 1) (physical u)‖

/-- The uniform bound with a fixed finite-action error sequence. -/
def EstimateWithZeta (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (F : HigherFlows L κ) (u : Smooth L) (I : Finset ℤ) (R : Finset ℕ)
    (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ) (A : ℝ) (ζ : ℕ → ℝ) : Prop :=
  let d := max 2 (R.sup id)
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ hk : k ≤ N + 1,
    ∀ ψ : HN L (N + 1), ‖ψ‖ = 1 →
      boxError hκ C F u I R Θ T k N hk ψ ≤
        ENNReal.ofReal (2 * preparationError u N ψ + A * ζ (N + 1) +
          A * ((N + 1 : ℕ) : ℝ) ^ (-(1 / (224 * ((d : ℝ) + 1)))))

/-- The estimate (MP-main). The constants, sequence and threshold are
chosen before either time parameter or the normalized preparation.
The finite-order set is fixed and may include orders zero and one. -/
def MainEstimate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (F : HigherFlows L κ) (u : Smooth L) (I : Finset ℤ) (R : Finset ℕ)
    (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ζ : ℕ → ℝ,
    Tendsto ζ atTop (𝓝 0) ∧ (I = ∅ → ∀ N, ζ N = 0) ∧
    EstimateWithZeta hκ C F u I R k Θ T A ζ

/-- The printed convergence consequence follows from the uniform estimate
along every normalized preparation with vanishing norm error. -/
theorem convergence (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (F : HigherFlows L κ) (u : Smooth L) (I : Finset ℤ) (R : Finset ℕ)
    (k : ℕ) (Θ : ℤ → ℝ) (T : ℕ → ℝ)
    (H : MainEstimate hκ C F u I R k Θ T)
    (ψ : ∀ N : ℕ, HN L (N + 1)) (hψ : ∀ N, ‖ψ N‖ = 1)
    (hprep : Tendsto (fun N => preparationError u N (ψ N)) atTop (𝓝 0)) :
    Tendsto (fun N => if hk : k ≤ N + 1 then boxError hκ C F u I R Θ T k N hk (ψ N)
      else 0) atTop (𝓝 0) := by
  obtain ⟨A, _, ζ, hζ, _, N₀, hbound⟩ := H
  let d := max 2 (R.sup id)
  have hp : 0 < (1 / (224 * ((d : ℝ) + 1)) : ℝ) := by positivity
  have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hζ' : Tendsto (fun n : ℕ => ζ (n + 1)) atTop (𝓝 0) :=
    hζ.comp (tendsto_add_atTop_nat 1)
  have hrate := (tendsto_rpow_neg_atTop hp).comp hN
  have hsum : Tendsto (fun n : ℕ => 2 * preparationError u n (ψ n) + A * ζ (n + 1) +
      A * ((n + 1 : ℕ) : ℝ) ^ (-(1 / (224 * ((d : ℝ) + 1)))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero, add_zero] using
      ((hprep.const_mul (2 : ℝ)).add (hζ'.const_mul A)).add (hrate.const_mul A)
  have hUpper := ENNReal.tendsto_ofReal hsum
  rw [ENNReal.ofReal_zero] at hUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop k] with N hN₀ hk
    have hk' : k ≤ N + 1 := hk.trans (Nat.le_succ N)
    rw [dite_eq_left hk']
    exact hbound N hN₀ hk' (ψ N) (hψ N)

/-- The fixed-action packet sequence is chosen at the profile, label and
angle-box data. The rate constant and cutoff may depend on the fixed charge
family and rank. -/
def PacketEstimate (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (F : HigherFlows L κ) (u : Smooth L) (I : Finset ℤ) (Θ : ℤ → ℝ) : Prop :=
  ∃ ζ : ℕ → ℝ, Tendsto ζ atTop (𝓝 0) ∧ (I = ∅ → ∀ N, ζ N = 0) ∧
    ∀ (R : Finset ℕ) (k : ℕ) (T : ℕ → ℝ), (∀ r ∈ R, 0 ≤ T r) →
      ∃ A : ℝ, 0 ≤ A ∧ EstimateWithZeta hκ C F u I R k Θ T A ζ

theorem packet_at_box (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (F : HigherFlows L κ) (u : Smooth L) (I : Finset ℤ) (Θ : ℤ → ℝ)
    (H : PacketEstimate hκ C F u I Θ) (R : Finset ℕ) (k : ℕ) (T : ℕ → ℝ)
    (hT : ∀ r ∈ R, 0 ≤ T r) :
    MainEstimate hκ C F u I R k Θ T := by
  obtain ⟨ζ, hζ, hEmpty, hPacket⟩ := H
  obtain ⟨A, hA, hEstimate⟩ := hPacket R k T hT
  exact ⟨A, hA, ζ, hζ, hEmpty, hEstimate⟩

/-- Exact PROP-025 at its DEF-044 interface. The convergence clause follows
from the displayed estimate by convergence and packet_at_box. -/
def PROP025Input (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L) (hu : ‖physical u‖ = 1) (M : Def044BindingR26m.MixedInterface hκ u hu)
    (I : Finset ℤ) (Θ : ℤ → ℝ), (∀ n ∈ I, 0 ≤ Θ n) →
    PacketEstimate hκ M.chart.chart (higher M.dynamics.hierarchy) u I Θ

/-- The common-order differential is taken on the restriction of exactly
the physical Riccati charge minus the printed contour functional. -/
theorem window_error_eq_printed (hκ : 0 < κ) (d r : ℕ) (hr : r ≤ d) (h : ℝ) (l : ℕ)
    (u : Sobolev.H02 L (Q07TailBindingR24.regularity d)) (f : Smooth L)
    (hf : u.val = SmoothScalarMomentsPhysical.smoothL2 f.property) :
    Def044InterfacesR51a.windowError hκ d r hr h l u =
      (ClassicalCharges.charge L κ f.val (r + 1)).re -
        Q07IntegratedHessiansR16.windowContour hκ r (PROP017UniformN.cutSeq L l) h u.val := by
  let v := Sobolev.H02.mono (Def044InterfacesR51a.regularity_mono hr) u
  have hv : v.val = u.val := Sobolev.fieldIncl_val _ _ _ _ _
  have he := Q07GradientRemovalR24.T_eq_printed hκ r l h v f.property (hv.trans hf)
  rw [hv] at he
  exact he

/-- At the designated large cuts, the contour functional is the OInputs
physical window Hamiltonian throughout a full L² neighborhood. -/
theorem window_hamiltonian_near (hκ : 0 < κ) (d r : ℕ) {h : ℝ} (hh : 0 < h)
    (u : Sobolev.H02 L (Q07TailBindingR24.regularity d)) :
    ∃ η : ℝ, 0 < η ∧ ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∀ v : L2T L, ‖v - u.val‖ < η →
      Q07IntegratedHessiansR16.windowContour hκ r (PROP017UniformN.cutSeq L l) h v =
        Prop025OInputs.windowHam κ r (PROP017UniformN.cutSeq L l) v := by
  obtain ⟨_, η, hη, l₀, _, _, hwindow⟩ := Q07BUniformCutsR16.q07Buniformcuts (L := L) hκ
    (Q07TailBindingR24.regularity_pos d) ‖u‖ hh r
  refine ⟨η, hη, l₀, fun l hl v hv => ?_⟩
  exact ((hwindow l hl).2 u.val ⟨u, le_rfl, rfl⟩ v hv).2.1

def WindowEstimate (F : HigherFlows L κ) : Prop :=
    ∀ (d : ℕ), 2 ≤ d → ∀ (R : Finset ℕ), (∀ r ∈ R, 2 ≤ r ∧ r ≤ d) →
    ∀ T : ℕ → ℝ, (∀ r, 0 ≤ T r) → ∀ K : Set (Smooth L), IsCompact K →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l → ∀ u ∈ K,
      ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      ∀ y : ℝ → L2T L,
        Prop025OInputs.IsWindowTrajectory κ R t (PROP017UniformN.cutSeq L l) (physical u) y →
        ‖y 1 - physical (jointSmooth (hamFlows F R) t u)‖ ≤
          A * (PROP017UniformN.cutSeq L l) ^ (-(1/4 : ℝ))

/-- Apply the printed window theorem to the same higher-order flow map used
by the classical target. The accepted scalar gradient estimate is supplied
by the frozen OInputs adapter. -/
theorem actual_window_intermediate (hκ : 0 < κ)
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (F : HigherFlows L κ) : WindowEstimate F := by
  intro d hd R hR T hT K hK
  exact Prop025OInputs.window_spec hκ WindowInput (ActualModelBindingR53a.chart (L := L) hκ).Φ
    (ActualModelBindingR53a.printed_chart hκ) (ActualModelBindingR53a.sobolev hκ)
    (flowMap F) (fun r _ => flow_isHam F r) d hd R hR T hT K hK

/-- Conditional assembly of the actual-model corollary. Its interface is
constructed from R52a spectral witnesses and the R26m chart/window clauses.
All preparations use the original product with coefficient exactly two. -/
theorem cor_MP_actual_model_intermediate (hκ : 0 < κ)
    (PROP025Input : PROP025Input (L := L) hκ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (Θ : ℤ → ℝ) (hΘ : ∀ n ∈ I, 0 ≤ Θ n) :
    PacketEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ)
      (higher (ActualModelBindingR53a.hierarchy_intermediate hκ HierarchyInput)) u I Θ :=
  PROP025Input u hu (ActualModelBindingR53a.DEF044_intermediate hκ HierarchyInput u hu) I Θ hΘ

/-- The source proof's window verification and the corollary estimate,
assembled at the same chart and hierarchy with each printed input visible. -/
theorem actual_model_intermediate (hκ : 0 < κ)
    (PROP025Input : PROP025Input (L := L) hκ)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (I : Finset ℤ) (Θ : ℤ → ℝ) (hΘ : ∀ n ∈ I, 0 ≤ Θ n) :
    let F := higher (ActualModelBindingR53a.hierarchy_intermediate hκ HierarchyInput)
    WindowEstimate F ∧ PacketEstimate hκ (ActualModelBindingR53a.chart (L := L) hκ) F u I Θ :=
  ⟨actual_window_intermediate hκ WindowInput _,
    cor_MP_actual_model_intermediate hκ PROP025Input HierarchyInput u hu I Θ hΘ⟩

end QuantumNLS.ActualModelCorollaryR53a

#print axioms QuantumNLS.ActualModelCorollaryR53a.convergence
#print axioms QuantumNLS.ActualModelCorollaryR53a.window_error_eq_printed
#print axioms QuantumNLS.ActualModelCorollaryR53a.window_hamiltonian_near
#print axioms QuantumNLS.ActualModelCorollaryR53a.actual_window_intermediate
#print axioms QuantumNLS.ActualModelCorollaryR53a.cor_MP_actual_model_intermediate
#print axioms QuantumNLS.ActualModelCorollaryR53a.actual_model_intermediate
#print QuantumNLS.ActualModelCorollaryR53a.PROP025Input
#print QuantumNLS.ActualModelCorollaryR53a.cor_MP_actual_model_intermediate
#print QuantumNLS.ActualModelCorollaryR53a.actual_model_intermediate
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelCorollaryR53a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelCorollaryR53a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") ||
          n == ``QuantumNLS.Def044HierarchyR26m.HierarchyR7B122087Input ||
          n == ``QuantumNLS.ActualModelHierarchyR52a.HierarchyInput ||
          n == ``QuantumNLS.Def044InterfacesR51a.Def033Input then
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
