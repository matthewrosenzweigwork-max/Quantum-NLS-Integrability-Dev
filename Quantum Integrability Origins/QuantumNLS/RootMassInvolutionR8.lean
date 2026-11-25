import QuantumNLS.DEF014Round5
import QuantumNLS.RootIndexedMasses
import QuantumNLS.RootCauchyFullBracketR8
import QuantumNLS.Ext025ASymplectic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! R-507DD869, proved clauses on the printed full physical phase space.
The arbitrary distinct positive-mass bracket is an explicit remaining gap.
No bracket-vanishing premise is imposed. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Topology MeasureTheory
namespace QuantumNLS.RootMassInvolutionR8
open PhysicalTensor (L2T)
open SymplecticBracket
attribute [local instance] InnerProductSpace.complexToReal
variable {L κ : ℝ} [Fact (0 < L)]

abbrev mass (hκ : 0 < κ) (n : ℤ) (u : L2T L) : ℝ :=
  (RootIndexedMasses.masses hκ u).1 n

/-- Nonnegativity makes the full differential vanish at every zero mass.
This includes every physically collapsed interval whose mass is zero. -/
theorem fderiv_mass_eq_zero (hκ : 0 < κ) (n : ℤ) (u : L2T L)
    (hz : mass hκ n u = 0) : fderiv ℝ (mass hκ n) u = 0 := by
  have hm : IsLocalMin (mass hκ n) u := by
    apply Filter.Eventually.of_forall
    intro v
    rw [hz]
    exact (PhysicalSourceFinal.sourceFacts hκ v).masses.2 n
  exact hm.fderiv_eq_zero

theorem bracket_zero_of_mass_zero (hκ : 0 < κ) (n m : ℤ) (u : L2T L)
    (hz : mass hκ n u = 0 ∨ mass hκ m u = 0) :
    pbR (mass hκ n) (mass hκ m) u = 0 := by
  rcases hz with hn | hm
  · exact DFunLike.congr_fun (fderiv_mass_eq_zero hκ n u hn) (hamField (mass hκ m) u)
  · have hzero : pbR (mass hκ m) (mass hκ n) u = 0 :=
      DFunLike.congr_fun (fderiv_mass_eq_zero hκ m u hm) (hamField (mass hκ n) u)
    calc
      _ = - pbR (mass hκ m) (mass hκ n) u := pbR_swap _ _ _
      _ = -(0 : ℝ) := congrArg Neg.neg hzero
      _ = 0 := neg_zero

/-- The total quantum mass generates common-phase rotation on the full
Hilbert space, with the source normalization 2 Im inner. -/
theorem gradient_total_mass (u : L2T L) :
    SymplecticBracket.gradient (fun v : L2T L => ‖v‖^2) u = u := by
  unfold SymplecticBracket.gradient
  rw [Ext025A.gp06_action_real_gradient]
  exact inv_smul_smul₀ (by norm_num : (2 : ℝ) ≠ 0) u

theorem mass_bracket_total_mass (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    pbR (mass hκ n) (fun v : L2T L => ‖v‖^2) u = 0 := by
  have hi : fderiv ℝ (mass hκ n) u (Complex.I • u) = 0 := by
    apply RootGReduced.fderiv_I_smul_eq_zero L
      (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n u).differentiableAt
    intro c hc v
    exact congrArg (fun x => x.1 n) (RootIndexedMasses.masses_phase hκ v hc)
  calc
    _ = fderiv ℝ (mass hκ n) u ((-Complex.I) • u) :=
      congrArg (fun v : L2T L => fderiv ℝ (mass hκ n) u ((-Complex.I) • v))
        (gradient_total_mass u)
    _ = fderiv ℝ (mass hκ n) u (-(Complex.I • u)) :=
      congrArg (fderiv ℝ (mass hκ n) u) (neg_smul Complex.I u)
    _ = -(fderiv ℝ (mass hκ n) u (Complex.I • u)) := map_neg _ _
    _ = -(0 : ℝ) := congrArg Neg.neg hi
    _ = 0 := neg_zero

theorem density_pos_iff (hκ : 0 < κ) (u : L2T L) (t : ℝ) :
    0 < RootDensityIdentification.dens κ u t ↔
      2 < |(L2SpatialTransfer.discriminant κ u (t : ℂ)).re| := by
  unfold RootDensityIdentification.dens
  rw [mul_pos_iff_of_pos_left (inv_pos.mpr (mul_pos Real.pi_pos hκ)), RootDensity.hfun_pos_iff]

/-- A nonempty open positive-density spectral interval in the cell with
integer label n. This is a condition on the physical discriminant and
separators, not a zero-measure or zero-mass premise. -/
def HasOpenSpectralInterval (hκ : 0 < κ) (u : L2T L) (n : ℤ) : Prop :=
  ∃ a b : ℝ, a < b ∧
    Ioo a b ⊆ Ioo (RootIndexedPhase.separator hκ u (n-1))
      (RootIndexedPhase.separator hκ u n) ∧
    ∀ t ∈ Ioo a b, 2 < |(L2SpatialTransfer.discriminant κ u (t : ℂ)).re|

/-- The spectral condition is literally the existence of an open
positive-density interval of the actual physical density in this cell. -/
theorem hasOpenSpectralInterval_iff_density (hκ : 0 < κ) (u : L2T L) (n : ℤ) :
    HasOpenSpectralInterval hκ u n ↔
      ∃ a b : ℝ, a < b ∧
        Ioo a b ⊆ Ioo (RootIndexedPhase.separator hκ u (n-1))
          (RootIndexedPhase.separator hκ u n) ∧
        ∀ t ∈ Ioo a b, 0 < RootDensityIdentification.dens κ u t := by
  simp only [HasOpenSpectralInterval, density_pos_iff hκ]

/-- Absence of an open positive-density spectral interval forces the
whole separator cell to have zero physical measure. This supplies the
geometric implication missing from the r7 sixth conjunct. -/
theorem collapsed_cell_measure_zero (hκ : 0 < κ) (u : L2T L) (n : ℤ)
    (hc : ¬ HasOpenSpectralInterval hκ u n) :
    PhysicalQuantumMeasure.measure hκ u
      (Ioo (RootIndexedPhase.separator hκ u (n-1))
        (RootIndexedPhase.separator hκ u n)) = 0 := by
  apply DEF014Phase.measure_band_zero ((⟨κ,hκ⟩,u) : DEF014Phase.Param L) measurableSet_Ioo
  intro t ht
  by_contra hn
  have hgt : 2 < |(L2SpatialTransfer.discriminant κ u (t : ℂ)).re| := lt_of_not_ge hn
  have hcont : Continuous (fun x : ℝ => |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re|) :=
    (Complex.continuous_re.comp ((L2DiscriminantRegularity.continuous_discriminant κ u).comp
      Complex.continuous_ofReal)).abs
  have hopen : IsOpen {x : ℝ | x ∈ Ioo (RootIndexedPhase.separator hκ u (n-1))
      (RootIndexedPhase.separator hκ u n) ∧ 2 < |(L2SpatialTransfer.discriminant κ u (x : ℂ)).re|} :=
    isOpen_Ioo.inter (isOpen_lt continuous_const hcont)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨ht,hgt⟩)
  apply hc
  refine ⟨t-δ/2,t+δ/2,by linarith,?_,?_⟩
  · intro x hx
    apply (hball ?_).1
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  · intro x hx
    apply (hball ?_).2
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith [hx.1,hx.2]

theorem collapsed_mass_zero (hκ : 0 < κ) (u : L2T L) (n : ℤ)
    (hc : ¬ HasOpenSpectralInterval hκ u n) : mass hκ n u = 0 := by
  change (PhysicalQuantumMeasure.measure hκ u _).toReal = 0
  rw [collapsed_cell_measure_zero hκ u n hc]
  rfl

/-- No norm-one, nonzero, regularity, or involution hypothesis is added.
The remaining full distinct positive-mass bracket is not claimed here. -/
theorem root_mass_involution_proved_clauses (hκ : 0 < κ) (u : L2T L) :
    (∀ n : ℤ, AnalyticAt ℝ (mass hκ n) u) ∧
    (∀ n : ℤ, pbR (mass hκ n) (mass hκ n) u = 0) ∧
    (∀ n m : ℤ, mass hκ n u = 0 ∨ mass hκ m u = 0 →
      pbR (mass hκ n) (mass hκ m) u = 0) ∧
    (∀ n m : ℤ, pbR (mass hκ n) (mass hκ m) (0 : L2T L) = 0) ∧
    (∀ n : ℤ, pbR (mass hκ n) (fun v : L2T L => ‖v‖^2) u = 0) ∧
    (∀ n : ℤ, fderiv ℝ (mass hκ n) u (Complex.I • u) = 0) ∧
    (∀ n : ℤ, ¬ HasOpenSpectralInterval hκ u n → mass hκ n u = 0 ∧
      ∀ m : ℤ, pbR (mass hκ n) (mass hκ m) u = 0) ∧
    (∀ z w : ℂ, RootMeasureComplex.HighHalf L (κ * ‖u‖^2) z →
      RootMeasureComplex.HighHalf L (κ * ‖u‖^2) w →
      pbC (RootCauchyFullBracketR8.G hκ z) (RootCauchyFullBracketR8.G hκ w) u = 0 ∧
      pbC (RootCauchyFullBracketR8.G hκ z)
        (fun v => (starRingEnd ℂ) (RootCauchyFullBracketR8.G hκ w v)) u = 0) := by
  refine ⟨fun n => DEF014MassAnalytic.analyticAt_physical_coordinate hκ n u,
    fun n => pbR_self _ _, fun n m => bracket_zero_of_mass_zero hκ n m u,
    ?_, fun n => mass_bracket_total_mass hκ n u, ?_, ?_, ?_⟩
  · intro n m
    apply bracket_zero_of_mass_zero hκ n m 0
    left
    change (PhysicalQuantumMeasure.measure hκ 0 _).toReal = 0
    rw [PhysicalQuantumMeasure.measure_zero]
    simp
  · intro n
    apply RootGReduced.fderiv_I_smul_eq_zero L
      (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n u).differentiableAt
    intro c hc v
    exact congrArg (fun x => x.1 n) (RootIndexedMasses.masses_phase hκ v hc)
  · intro n hc
    have hz := collapsed_mass_zero hκ u n hc
    exact ⟨hz,fun m => bracket_zero_of_mass_zero hκ n m u (Or.inl hz)⟩
  · intro z w hz hw
    exact RootCauchyFullBracketR8.G_full_high_bracket_zero hκ z w u hz.1 hz.2 hw.1 hw.2
end QuantumNLS.RootMassInvolutionR8
#print axioms QuantumNLS.RootMassInvolutionR8.hasOpenSpectralInterval_iff_density
#print axioms QuantumNLS.RootMassInvolutionR8.collapsed_cell_measure_zero
#print axioms QuantumNLS.RootMassInvolutionR8.fderiv_mass_eq_zero
#print axioms QuantumNLS.RootMassInvolutionR8.root_mass_involution_proved_clauses

#check @QuantumNLS.RootMassInvolutionR8.root_mass_involution_proved_clauses

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootMassInvolutionR8." ||
        n.toString.startsWith "_private.QuantumNLS.RootMassInvolutionR8." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"RootMassInvolutionR8 audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
