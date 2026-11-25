import QuantumNLS.Def044ChartR51a
import QuantumNLS.Reg015HFinal
import QuantumNLS.RootScalarUniquenessR28
import QuantumNLS.Round10ScalarReconstructionBatch

/-! DEF-044 clause (2), with existential fixed contours. The local logarithm
is the actual Taylor-branch formula of eq:B4-local-functions, rather than a
free function. Neither a prescribed circle nor joint analyticity in (z,w)
is imposed on the interface. Circles are witnesses provided by frozen R10. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.Def044ChartR26m
open PhysicalTensor QuantumFourierSpecification Def044ChartR51a Reg015Setting
variable {L κ : ℝ} [Fact (0 < L)]

/-- Any fixed positive circle is permitted. The definition existentially
chooses it; the implementation below chooses R10's separating circles. -/
def period (hκ : 0 < κ) (base : L2T L) (c : ℂ) (ρ : ℝ) (v : L2T L) : ℝ :=
  -(2 * Real.pi * κ)⁻¹ * (∮ z in C(c, ρ),
    RootScalarPeriodR10.lambda hκ base z (NormalizedTransfer.productSymbol L κ v z)).re

/-- Source's existential fixed-contour assertion at full mass and every
selected label, including zero actions. No joint-branch premise is added. -/
def FullOpenPeriods (hκ : 0 < κ) : Prop :=
  ∀ base : L2T L, ∀ F : Finset ℤ, ∃ U : Set (L2T L), IsOpen U ∧ base ∈ U ∧
    ∀ n ∈ F, ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      (∀ v ∈ U, ∀ z ∈ Metric.sphere c ρ,
        RootScalarPeriodR10.lambda hκ base z (NormalizedTransfer.productSymbol L κ v z) =
          Complex.I * κ * EmpiricalRapidity.cauchyTransform (PhysicalQuantumMeasure.measure hκ v) z) ∧
      (∀ v ∈ U, period hκ base c ρ v = action hκ v n) ∧
      (∀ v ∈ U, AnalyticAt ℝ (period hκ base c ρ) v) ∧
      (∀ v ∈ U, fderiv ℝ (period hκ base c ρ) v = fderiv ℝ (fun w => action hκ w n) v)

/-- Apply the existing literal logarithmic-period theorem, not just its
Cauchy-period precursor. It constructs witnesses for the existential scope. -/
theorem full_open_periods (hκ : 0 < κ) : FullOpenPeriods (L := L) hκ := by
  intro base F
  obtain ⟨U, hU, hb, hn⟩ := RootScalarPeriodR10.audit_scalar_period hκ base F
  refine ⟨U, hU, hb, fun n hnF => ?_⟩
  obtain ⟨hρ, he, hp, ha, hd, _⟩ := hn n hnF
  refine ⟨(RootScalarPeriodR8.center hκ base n : ℂ), RootScalarPeriodR8.radius hκ base n,
    hρ, ?_, ?_, ?_, ?_⟩
  · simpa only [RootScalarPeriodR10.symbol, RootScalarPeriodR10.exponent,
      RootCauchyFullBracketR8.G] using he
  · exact hp
  · exact ha
  · exact hd

/-- Both maps of the same actual chart restrict on every nonnegative scale. -/
def baseHomeo (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) : L2T L ≃ₜ Seq where
  toFun := C.Φ
  invFun := C.Ψ
  left_inv := C.left_inverse
  right_inv := C.right_inverse
  continuous_toFun := continuous_iff_continuousAt.mpr fun u => (C.analytic u).continuousAt
  continuous_invFun := continuous_iff_continuousAt.mpr fun z => (C.inverse_analytic z).continuousAt

def targetUniv (s : ℝ) (hs : 0 ≤ s) : Sobolev.h02 L s ≃ₜ Target (L := L) univ s hs where
  toFun z := ⟨z, mem_univ _⟩
  invFun z := z.val
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

theorem sobolev_restrictions (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) :
    SobolevRestrictions hκ C := by
  let e : L2T L ≃ₜ (univ : Set Seq) :=
    (baseHomeo hκ C).trans (Homeomorph.Set.univ Seq).symm
  intro s hs
  obtain ⟨F, hF⟩ := (Reg015HFinal.REG015_final hκ s hs).2.2 univ e C.actions
  let G : Sobolev.H02 L s ≃ₜ Sobolev.h02 L s := F.trans (targetUniv s hs).symm
  have hG : ∀ u, toBase s hs (G u) = C.Φ u.val := by
    intro u
    apply lp.ext
    funext n
    rw [toBase_apply]
    exact hF u n
  refine ⟨G, hG, fun z => ?_⟩
  have hx := hG (G.symm z)
  rw [G.apply_symm_apply] at hx
  calc
    (G.symm z).val = C.Ψ (C.Φ (G.symm z).val) := (C.left_inverse _).symm
    _ = C.Ψ (toBase s hs z) := congrArg C.Ψ hx.symm

/-- Indexed actions determine both entire transfer and full physical measure. -/
theorem action_determination (hκ : 0 < κ) : ActionDetermination (L := L) hκ := by
  intro u v he
  have hm := (RootScalarUniquenessR28.root_scalar_uniqueness hκ).1 u v he
  have hdisc : L2SpatialTransfer.discriminant κ u = L2SpatialTransfer.discriminant κ v := by
    have hU := (PhysicalUpperTraceIdentity.entire_discriminant κ u).differentiableOn.analyticOnNhd isOpen_univ
    have hV := (PhysicalUpperTraceIdentity.entire_discriminant κ v).differentiableOn.analyticOnNhd isOpen_univ
    apply hU.eq_of_eventuallyEq hV (z₀ := Complex.I)
    filter_upwards [PhysicalPhaseHolomorphic.isOpen_upper.mem_nhds
      (show Complex.I ∈ PhysicalPhaseHolomorphic.upper by simp [PhysicalPhaseHolomorphic.upper])]
      with z hz
    rw [← PhysicalUnconditionalTrace.upper_cosine hκ u hz,
      ← PhysicalUnconditionalTrace.upper_cosine hκ v hz, hm]
  refine ⟨?_, hm⟩
  funext z
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-(Complex.I*z*L/2)))
  rw [RootTraceSymbolFinal.traceSymbol_all hκ.le u z,
    RootTraceSymbolFinal.traceSymbol_all hκ.le v z, hdisc]

/-- Clause (2) without the extra R51a branch assumption. -/
structure ChartInterface (hκ : 0 < κ) where
  chart : Def021ChartR41b.Chart L κ hκ
  sobolev : SobolevRestrictions hκ chart
  action_determination : ActionDetermination (L := L) hκ
  full_open_periods : FullOpenPeriods (L := L) hκ

/-- Construct every field; no ChartInterface is an input. REG-015's inherited
conditional status remains visible in the review record rather than promoted. -/
def chart_interface (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ) :
    ChartInterface (L := L) hκ :=
  ⟨C, sobolev_restrictions hκ C, action_determination hκ, full_open_periods hκ⟩

theorem full_directions (hκ : 0 < κ) (base : L2T L) (F : Finset ℤ) :
    ∃ U : Set (L2T L), IsOpen U ∧ base ∈ U ∧ ∀ n ∈ F,
      ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ v ∈ U, ∀ h : L2T L,
        fderiv ℝ (period hκ base c ρ) v h =
          fderiv ℝ (fun w => action hκ w n) v h := by
  obtain ⟨U, hU, hb, hn⟩ := full_open_periods (L := L) hκ base F
  refine ⟨U, hU, hb, fun n hnF => ?_⟩
  obtain ⟨c, ρ, hρ, _, _, _, hd⟩ := hn n hnF
  exact ⟨c, ρ, hρ, fun v hv h => DFunLike.congr_fun (hd v hv) h⟩

theorem exact_actions (hκ : 0 < κ) (C : ChartInterface (L := L) hκ) (v : L2T L) (n : ℤ) :
    action hκ v n = ‖C.chart.Φ v n‖^2 ∧
    action hκ v n = ‖reflected (C.chart.Φ v) (-n)‖^2/2 := by
  have h := (C.chart.actions v n).symm
  exact ⟨h, h.trans (Def044ChartR51a.reflected_action (C.chart.Φ v) n).symm⟩

end QuantumNLS.Def044ChartR26m
#print axioms QuantumNLS.Def044ChartR26m.full_open_periods
#print axioms QuantumNLS.Def044ChartR26m.sobolev_restrictions
#print axioms QuantumNLS.Def044ChartR26m.action_determination
#print axioms QuantumNLS.Def044ChartR26m.chart_interface
#print axioms QuantumNLS.Def044ChartR26m.full_directions
