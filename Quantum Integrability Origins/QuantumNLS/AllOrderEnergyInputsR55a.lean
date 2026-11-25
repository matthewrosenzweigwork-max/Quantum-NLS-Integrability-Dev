import QuantumNLS.ActualModelCorollaryR53a
import QuantumNLS.AuditWeightedAssemblyR50a
import QuantumNLS.RB7BindFinal
import QuantumNLS.EnergyPreparationDef

/-! The printed predecessor statements available to the R-568BCDF8
intermediate. The input types state the predecessor results, and the energy sandwich is
handled by the separate physical form argument. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology MeasureTheory
open scoped ENNReal InnerProductSpace
namespace QuantumNLS.AllOrderEnergyInputsR55a
open PhysicalTensor TensorCarrier Def033HierarchyR24m BetheCoefficientTransform HierarchyFlow
open ActualModelBindingR53a ActualModelTargetR53a ActualModelCorollaryR53a
open BetheLabels EmpiricalRapidity BulkResponseActual ClassicalCharges SmoothScalarMomentsPhysical
open CommonBethePacket AuditWeightedProbabilityR49a
variable {L κ : ℝ} [Fact (0 < L)]

/-- The shared R25m hierarchy at the actual DEF-021 chart. The frozen
`RB7BindFinal` discharges the compact orbit and joint-continuity clauses of
`RB7BindMain.hierarchyInputR25m_holds`. -/
theorem hierarchy (hκ : 0 < κ) :
    HierarchyInputR25m.HierarchyConclusion (κ := κ) (chart (L := L) hκ).Φ
      (Def044ChartR51a.action hκ) :=
  hierarchy_intermediate hκ (RB7BindFinal.hierarchyInputR25m_unconditional hκ)

/-- The physical hierarchy flow used by the actual-model estimate. -/
def flows (hκ : 0 < κ) : HigherFlows L κ := higher (hierarchy hκ)

/-- R-E59628C9, with the preceding scalar estimate and new chart as in the
printed antecedent. Quantification over the fixed finite orders includes 0
and 1. Singleton initial classes give the fixed-datum statement. -/
def WindowRE59628C9Input (hκ : 0 < κ) : Prop :=
  ∀ w : L2T L → REF88Chart.K, REF88PrintedChart.PrintedChart hκ w →
    HierarchyInputR25m.SobolevHomeomorphisms w →
    Prop025OInputs.GradientRemovalAntecedent (L := L) hκ →
    ∀ (d : ℕ), 2 ≤ d → ∀ (R : Finset ℕ), (∀ r ∈ R, r ≤ d) →
    ∀ (F : HamFlows L κ R) (T : ℕ → ℝ), (∀ r, 0 ≤ T r) →
    ∀ K : Set (Smooth L), IsCompact K →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l₀ : ℕ, ∀ l ≥ l₀, ∀ u ∈ K,
      ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      (∃ y, Prop025OInputs.IsWindowTrajectory κ R t (PROP017UniformN.cutSeq L l) (physical u) y) ∧
      ∀ y, Prop025OInputs.IsWindowTrajectory κ R t (PROP017UniformN.cutSeq L l) (physical u) y →
        ‖y 1 - physical (jointSmooth F t u)‖ ≤ C * (PROP017UniformN.cutSeq L l)^(-(1/4 : ℝ))

/-- R-E679E41D as the frozen R53a exact-error estimate at the actual model,
for every fixed label set, charge set, rank and box. The target definition
retains the signed Hamiltonian action angles and physical charge flows. -/
def ActualModelRE679E41DInput (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
  ∀ (I : Finset ℤ) (Θ : ℤ → ℝ), (∀ n ∈ I, 0 ≤ Θ n) →
    PacketEstimate hκ (chart (L := L) hκ) (flows hκ) u I Θ

/-- R-115CAA16, using the body of the frozen R50a statement. The exponent
here weights integer occupations by `(1+n²)^(p/2)` only. This expression
has a positive base for every label. The consumer needs only charge 2 of
the common packet clause. -/
def WeightedR115CAA16Input (hκ : 0 < κ) : Prop :=
  ∀ (f : ℝ → ℂ) (hf : SmoothPeriodic L f) (hu : ‖smoothL2 hf‖ = 1),
    (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu
        {m | ε < error hκ (smoothL2 hf) p N m}) atTop (𝓝 0)) ∧
    (∀ r : ℕ, QuantumNLS.BornConvergence.TendstoInProbability
      (fun N => bornMeasure (physBasis L hκ N) (smoothL2 hf) hu)
      (fun N m => QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ))
      (charge L κ f (r+1)).re) ∧
    ∃ P : (N : ℕ) → Packet (physBasis L hκ N),
      Tendsto (fun N => ‖vector (P N)-productVec L N (smoothL2 hf)‖) atTop (𝓝 0) ∧
      (∀ r ε, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        |QuantumNLS.BetheSpectralCharges.eigenvalue L N (κ/N) r m/(N : ℝ)-(charge L κ f (r+1)).re| ≤ ε) ∧
      (∀ p : ℝ, 0 ≤ p → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        error hκ (smoothL2 hf) p N m ≤ ε) ∧
      ∀ N (ev : MArr N → ℝ), vector (P N) ∈
        (QuantumNLS.BetheSpectralCharges.multiplier (physBasis L hκ N) ev).domain

/-- Partial-trace contraction at the initial datum, without any requirement
that the joint-time box contain the origin. -/
theorem initial_trace_limit (u : Smooth L) (hu : ‖physical u‖ = 1)
    (ψ : ∀ N : ℕ, HN L (N + 1)) (hψ : ∀ N, ‖ψ N‖ = 1)
    (hprep : Tendsto (fun N => preparationError u N (ψ N)) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun N => if hk : k ≤ N + 1 then
      TraceClass.traceNorm (reducedDensityN (N + 1) k hk
        (ψ N : HilbertTensorPower ℂ (L2T L) (N + 1)) - Prop025OInputs.tensorProj k (physical u))
      else 0) atTop (𝓝 0) := by
  have hUpper : Tendsto (fun N => ENNReal.ofReal (preparationError u N (ψ N) * 2)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal (hprep.mul_const (2 : ℝ))
    simpa only [zero_mul, ENNReal.ofReal_zero] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [eventually_ge_atTop k] with N hN
    have hk : k ≤ N + 1 := hN.trans (Nat.le_succ _)
    rw [dite_eq_left hk]
    have h := traceNorm_reducedDensityN_sub_product_le (N + 1) k hk (physical u) hu
      (ψ N : HilbertTensorPower ℂ (L2T L) (N + 1))
    have hn : ‖(ψ N : HilbertTensorPower ℂ (L2T L) (N + 1))‖ = 1 := hψ N
    have htwo : (1 : ℝ) + 1 = 2 := by norm_num
    have hcast : ‖ψ N - HighMomentsOps.wvec (N + 1) (physical u)‖ =
        ‖(ψ N : HilbertTensorPower ℂ (L2T L) (N + 1)) - htpow (N + 1) (physical u)‖ := rfl
    simpa only [hn, htwo, preparationError, hcast, Prop025OInputs.tensorProj] using h

/-- Continuous periodic representatives are determined by their physical
L² class. -/
theorem physical_injective : Function.Injective (physical (L := L)) := by
  intro u v h
  have hu := PhysicalProductPreparation.smoothClass_ae u.property
  have hv := PhysicalProductPreparation.smoothClass_ae v.property
  change PhysicalProductPreparation.smoothClass u.property = PhysicalProductPreparation.smoothClass v.property at h
  rw [h] at hu
  let F := WeakDerivatives.liftC u.property.smooth.continuous u.property.periodic
  let G := WeakDerivatives.liftC v.property.smooth.continuous v.property.periodic
  have he : (F : AddCircle L → ℂ) = (G : AddCircle L → ℂ) :=
    MeasureTheory.Measure.eq_of_ae_eq (hu.symm.trans hv) F.continuous G.continuous
  apply Subtype.ext
  funext x
  simpa only [F, G, WeakDerivatives.liftC_coe] using congrFun he (x : AddCircle L)

/-- With no action angles, the exact count evolution is the identity. -/
theorem countUnitary_empty (hκ : 0 < κ) (θ : ℤ → ℝ) (N : ℕ) (ψ : HN L (N + 1)) :
    ActualModelQuantumR52a.countUnitary hκ ∅ θ N ψ = ψ := by
  let b := Def044D1SpectralR51a.basis (L := L) hκ N
  apply b.repr.injective
  ext m
  change b.repr (BetheSpectralCharges.evolution b (ActualModelQuantumR52a.countSymbol ∅ θ N) 1 ψ) m = _
  simp only [HilbertBasis.repr_apply_apply, BetheSpectralCharges.evolution_coord,
    DiagonalMultiplier.phase, ActualModelQuantumR52a.countSymbol, Finset.sum_empty, mul_zero,
    Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul]

/-- With no action angles the classical target is the joint Riccati flow of
the given initial datum. -/
theorem target_empty (hκ : 0 < κ) (R : Finset ℕ) (θ : ℤ → ℝ) (t : ℕ → ℝ) (u : Smooth L) :
    target (chart (L := L) hκ) (flows hκ) ∅ R θ t u =
      physical (jointSmooth (hamFlows (flows hκ) R) t u) := by
  let C := chart (L := L) hκ
  have he : rotateSmooth C ∅ θ u = u := by
    apply physical_injective
    rw [rotateSmooth_physical]
    apply (Function.LeftInverse.injective C.left_inverse)
    ext n
    rw [rotate_coordinate]
    simp
  simp only [target, C] at he ⊢
  rw [he]

/-- Exactly the ordinary marginal convergence invoked in the energy proof.
This uses the accepted hierarchy carrier and the named actual-model input
with the action set empty. -/
theorem empty_action_trace_limit (hκ : 0 < κ)
    (ActualModelInput : ActualModelRE679E41DInput (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (T : ℕ → ℝ) (hT : ∀ r ∈ R, 0 ≤ T r) (k : ℕ)
    (ψ : ∀ N : ℕ, HN L (N + 1)) (hψ : ∀ N, ‖ψ N‖ = 1)
    (hprep : Tendsto (fun N => preparationError u N (ψ N)) atTop (𝓝 0)) :
    Tendsto (fun N => if hk : k ≤ N + 1 then
      ⨆ t : {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r},
        TraceClass.traceNorm (reducedDensityN (N + 1) k hk
          (ActualModelQuantumR52a.chargeUnitary hκ R t.val N (ψ N) : HilbertTensorPower ℂ (L2T L) (N + 1)) -
          Prop025OInputs.tensorProj k (physical (jointSmooth (hamFlows (flows hκ) R) t.val u)))
      else 0) atTop (𝓝 0) := by
  let Θ : ℤ → ℝ := fun _ => 0
  have hes := ActualModelInput u hu ∅ Θ (by simp)
  have hm := packet_at_box hκ (chart (L := L) hκ) (flows hκ) u ∅ Θ hes R k T hT
  have hout := convergence hκ (chart (L := L) hκ) (flows hκ) u ∅ R k Θ T hm ψ hψ hprep
  have hθ : Nonempty {θ : ℤ → ℝ // ∀ n ∈ (∅ : Finset ℤ), |θ n| ≤ Θ n} := ⟨⟨Θ, by simp⟩⟩
  letI := hθ
  simpa only [boxError, countUnitary_empty, target_empty, iSup_const] using hout

/-- Restrict the accepted joint smooth continuity to a fixed profile and a
compact box. The supplied smooth family is the very one in the model estimate. -/
theorem joint_smooth_continuous (hκ : 0 < κ) (R : Finset ℕ) (u : Smooth L)
    (K : Set (ℕ → ℝ)) (hK : IsCompact K) :
    Continuous (fun t : K => jointSmooth (hamFlows (flows hκ) R) t.val u) := by
  have h := RB7BindMain.joint_continuous (RB7HBridge.jointContInput_of hκ R)
    (hamFlows (flows hκ) R) {u} isCompact_singleton K hK
  exact h.comp_continuous (continuous_const.prodMk continuous_subtype_val) (fun t => ⟨rfl, t.property⟩)

/-- Conservation on the chosen higher-order solution follows from uniqueness
and the shared hierarchy theorem. The first two orders use the accepted
physical phase and translation laws. -/
theorem flow_charge_conserved (hκ : 0 < κ) (u : Smooth L) (r : ℕ) (t : ℝ) (j : ℕ) :
    charge L κ (flowMap (flows (L := L) hκ) r t u.val) j = charge L κ u.val j := by
  match r with
  | 0 => exact (Def024LowEquivariance.charge_conserved_low L κ u.property t j).1
  | 1 => exact (Def024LowEquivariance.charge_conserved_low L κ u.property t j).2
  | r + 2 =>
    let F := flows (L := L) hκ
    obtain ⟨Φ, hΦ, hUnique, _, _, _, _, _, hCharge, _⟩ := hierarchy (L := L) hκ
    have he := hUnique (r+2) (by omega) (F.Φ (r+2)) (F.ham (r+2) (by omega)) u.val u.property t
    change charge L κ (F.Φ (r+2) t u.val) j = _
    rw [he]
    exact hCharge (r+2) (by omega) u t j

theorem joint_charge_conserved (hκ : 0 < κ) (u : Smooth L) (R : Finset ℕ) (t : ℕ → ℝ) (j : ℕ) :
    charge L κ (jointSmooth (hamFlows (flows hκ) R) t u).val j = charge L κ u.val j := by
  let F := hamFlows (flows (L := L) hκ) R
  have hs (r) (v : Smooth L) : charge L κ (smoothStep F r (t r) v).val j = charge L κ v.val j := by
    unfold smoothStep
    split_ifs
    · exact flow_charge_conserved hκ v r (t r) j
    · rfl
  change charge L κ ((R.sort (· ≤ ·)).foldr (fun r v => smoothStep F r (t r) v) u).val j = _
  induction R.sort (· ≤ ·) with
  | nil => rfl
  | cons r rs ih => exact (hs r _).trans ih

/-- The named R-E59628C9 input is applied at the same actual chart and full
Riccati family. The scalar gradient antecedent is a proved predecessor. -/
theorem actual_window_rate (hκ : 0 < κ) (WindowInput : WindowRE59628C9Input (L := L) hκ)
    (d : ℕ) (hd : 2 ≤ d) (R : Finset ℕ) (hR : ∀ r ∈ R, r ≤ d)
    (T : ℕ → ℝ) (hT : ∀ r, 0 ≤ T r) (K : Set (Smooth L)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l₀ : ℕ, ∀ l ≥ l₀, ∀ u ∈ K,
      ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      (∃ y, Prop025OInputs.IsWindowTrajectory κ R t (PROP017UniformN.cutSeq L l) (physical u) y) ∧
      ∀ y, Prop025OInputs.IsWindowTrajectory κ R t (PROP017UniformN.cutSeq L l) (physical u) y →
        ‖y 1 - physical (jointSmooth (hamFlows (flows hκ) R) t u)‖ ≤ C * (PROP017UniformN.cutSeq L l)^(-(1/4 : ℝ)) :=
  WindowInput (chart (L := L) hκ).Φ (printed_chart hκ) (sobolev hκ) (Prop025OInputs.gradient_removal hκ)
    d hd R hR (hamFlows (flows hκ) R) T hT K hK

/-- The product preparation satisfies exactly DEF-031 at every smooth unit
datum. This uses only the contact form energy and no higher moment. -/
theorem exact_product_prepared (κ : ℝ) (u : Smooth L) (hu : ‖physical u‖ = 1) :
    EnergyPreparationDef.EnergyPreparation κ (physical u)
      (fun N => (htpow N (physical u) : HilbertTensorPower ℂ (L2T L) N)) :=
  EnergyPreparationDef.product_energyPreparation hu (PhysicalProductPreparation.oneH1_smooth u.property) κ

/-- Select the energy-charge clause of the same common finite packets
provided by the exact R-115CAA16 input. Its stronger all-order conclusions
are retained in the input type. -/
theorem common_energy_packets (hκ : 0 < κ)
    (WeightedInput : WeightedR115CAA16Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) :
    ∃ P : (N : ℕ) → Packet (physBasis L hκ N),
      Tendsto (fun N => ‖vector (P N) - productVec L N (physical u)‖) atTop (𝓝 0) ∧
      (∀ ε > (0 : ℝ), ∀ᶠ N in atTop, ∀ m ∈ support (P N),
        |BetheSpectralCharges.eigenvalue L N (κ/N) 2 m/(N : ℝ) - EnergyPreparationDef.I3 κ (physical u)| ≤ ε) ∧
      ∀ N (ev : MArr N → ℝ), vector (P N) ∈ (BetheSpectralCharges.multiplier (physBasis L hκ N) ev).domain := by
  have hunit : ‖smoothL2 u.property‖ = 1 := hu
  obtain ⟨_, _, P, hclose, hcharge, _, hdom⟩ := WeightedInput u.val u.property hunit
  refine ⟨P, hclose, fun ε hε => ?_, hdom⟩
  have h := hcharge 2 ε hε
  rw [EnergyPreparationDef.charge_three_eq_I3 κ u.property, Complex.ofReal_re] at h
  exact h

/-- The source's Cauchy–Schwarz bound on the energy error of a unit vector,
with the intensive Hamiltonian applied in its exact operator domain. -/
theorem packet_energy_error {N : ℕ} (x y : HN L N) (hx : ‖x‖ = 1) (I₃ : ℝ) :
    |(⟪x, y⟫_ℂ).re - I₃| ≤ ‖y - (I₃ : ℂ) • x‖ := by
  have h : (⟪x, y - (I₃ : ℂ) • x⟫_ℂ).re = (⟪x, y⟫_ℂ).re - I₃ := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
    simp
  rw [← h]
  exact (Complex.abs_re_le_norm _).trans (by simpa only [hx, one_mul] using norm_inner_le_norm x (y - (I₃ : ℂ) • x))

/-- The ordinary convergence restricts to any fixed compact joint-time box.
A coordinatewise enclosing centered box uses only continuous evaluation. -/
theorem compact_box_ordinary_limit (hκ : 0 < κ)
    (ActualModelInput : ActualModelRE679E41DInput (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (K : Set (ℕ → ℝ)) (hK : IsCompact K) (k : ℕ)
    (ψ : ∀ N : ℕ, HN L (N + 1)) (hψ : ∀ N, ‖ψ N‖ = 1)
    (hprep : Tendsto (fun N => preparationError u N (ψ N)) atTop (𝓝 0)) :
    Tendsto (fun N => if hk : k ≤ N + 1 then
      ⨆ t : K, TraceClass.traceNorm (reducedDensityN (N + 1) k hk
          (ActualModelQuantumR52a.chargeUnitary hκ R t.val N (ψ N) : HilbertTensorPower ℂ (L2T L) (N + 1)) -
          Prop025OInputs.tensorProj k (physical (jointSmooth (hamFlows (flows hκ) R) t.val u)))
      else 0) atTop (𝓝 0) := by
  have hbound (r : ℕ) : ∃ b : ℝ, ∀ t ∈ K, ‖t r‖ ≤ b :=
    hK.exists_bound_of_continuousOn ((continuous_apply r).continuousOn)
  choose B hB using hbound
  let T : ℕ → ℝ := fun r => max (B r) 0
  have hT : ∀ r ∈ R, 0 ≤ T r := fun _ _ => le_max_right _ _
  have hbig := empty_action_trace_limit hκ ActualModelInput u hu R T hT k ψ hψ hprep
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbig
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [eventually_ge_atTop k] with N hN
    have hk : k ≤ N + 1 := hN.trans (Nat.le_succ _)
    simp only [dite_eq_left hk]
    let E (s : ℕ → ℝ) : ℝ≥0∞ := TraceClass.traceNorm (reducedDensityN (N + 1) k hk
      (ActualModelQuantumR52a.chargeUnitary hκ R s N (ψ N) : HilbertTensorPower ℂ (L2T L) (N + 1)) -
      Prop025OInputs.tensorProj k (physical (jointSmooth (hamFlows (flows hκ) R) s u)))
    change (⨆ t : K, E t.val) ≤ ⨆ t : {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r}, E t.val
    apply iSup_le
    intro t
    have ht : ∀ r ∈ R, |t.val r| ≤ T r := fun r _ =>
      (by simpa only [Real.norm_eq_abs] using hB r t t.property : |t.val r| ≤ B r).trans (le_max_left _ _)
    let v : {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r} := ⟨t.val, ht⟩
    exact le_iSup (fun s : {t : ℕ → ℝ // ∀ r ∈ R, |t r| ≤ T r} => E s.val) v

end QuantumNLS.AllOrderEnergyInputsR55a
set_option maxHeartbeats 15000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := env.constants.toList.filterMap fun (n, _) =>
    if n.toString.startsWith "QuantumNLS.AllOrderEnergyInputsR55a." then some n else none
  let roots := pending.length
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := ci.type.getUsedConstants.toList ++ pending
        if let some v := ci.value? (allowOpaque := true) then
          pending := v.getUsedConstants.toList ++ pending
      else throwError "Missing dependency: {n}"
  Lean.logInfo m!"R55a audit PASS: {roots} namespace constants; {seen.size} transitive constants."
