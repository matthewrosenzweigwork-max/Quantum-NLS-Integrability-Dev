import QuantumNLS.CartesianOccupationTransfer

/-! DEF-027. Complete-array partial shift and its gauged Bethe pullback.
The polar symbol has a positive-endpoint DOMAIN, supplied by the actual
parametric DEF-014 data; no quotient at a zero action is specified. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.UnitPhaseTransfer
open BetheLabels BetheCoefficientTransform BetheOccupationGauge Occupation
open QuantumFourierSpecification IndexedMassProperness
variable {L κ : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The complete-array partial shift, with coefficient exactly one. -/
def auxiliary (N : ℕ) (a b : ℤ) : OccupationHilbert.H N →L[ℂ] OccupationHilbert.H N :=
  OccupationHilbert.W N a b

theorem auxiliary_basis (N : ℕ) (a b : ℤ) (m : Arr N) :
    auxiliary N a b (lp.single 2 m 1) =
      if hd : DonorOK a m.1 then lp.single 2 (shiftArr a b m hd) 1 else 0 := by
  simpa only [auxiliary, OccupationHilbert.W, one_mul] using
    OccupationHilbert.transferOp_single N a b (fun _ => 1) (by intro d; simp) m 1

theorem auxiliary_norm_le (N : ℕ) (a b : ℤ) : ‖auxiliary N a b‖ ≤ 1 :=
  OccupationHilbert.W_norm_le N a b

/-- Pullback through the SAME literal COT1 gauged coefficient isometry. -/
def physical (b : BetheBasis L N) (g : Gauge) (a c : ℤ) : HN L N →L[ℂ] HN L N :=
  (CartesianOccupationTransfer.coordinates b g).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    auxiliary N a c ∘L
      (CartesianOccupationTransfer.coordinates b g).toContinuousLinearEquiv.toContinuousLinearMap

theorem physical_coordinates (b : BetheBasis L N) (g : Gauge) (a c : ℤ) (ψ : HN L N) :
    CartesianOccupationTransfer.coordinates b g (physical b g a c ψ) =
      auxiliary N a c (CartesianOccupationTransfer.coordinates b g ψ) :=
  (CartesianOccupationTransfer.coordinates b g).apply_symm_apply _

theorem physical_basis (b : BetheBasis L N) (g : Gauge) (a c : ℤ) (m : MArr N) :
    physical b g a c (gaugedBasis b g m) =
      if hd : DonorOK a (marrArr N m).1 then
        gaugedBasis b g ((marrArr N).symm (shiftArr a c (marrArr N m) hd)) else 0 := by
  apply (CartesianOccupationTransfer.coordinates b g).injective
  rw [physical_coordinates, CartesianOccupationTransfer.coordinates_basis, auxiliary_basis]
  split_ifs with hd
  · rw [CartesianOccupationTransfer.coordinates_basis, Equiv.apply_symm_apply]
  · simp

/-- The Cartesian transfer is the positive coefficient times this unit shift
on every occupied donor, in the same literal COT1 gauged basis. -/
theorem cartesian_basis_factor (b : BetheBasis L N) (g : Gauge) (a c : ℤ) (hac : a ≠ c)
    (m : MArr N) (hd : DonorOK a (marrArr N m).1) :
    CartesianOccupationTransfer.physical b g a c (gaugedBasis b g m) =
      ((Real.sqrt (((marrArr N m).1 a : ℝ) * (((marrArr N m).1 c : ℝ) + 1)) / N : ℝ) : ℂ) •
        physical b g a c (gaugedBasis b g m) := by
  rw [CartesianOccupationTransfer.physical_offdiag b g a c hac m hd,
    physical_basis, dite_eq_left hd]

theorem physical_norm_le (b : BetheBasis L N) (g : Gauge) (a c : ℤ) :
    ‖physical b g a c‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  rw [one_mul, ← (CartesianOccupationTransfer.coordinates b g).norm_map, physical_coordinates]
  calc
    _ ≤ ‖auxiliary N a c‖ * ‖CartesianOccupationTransfer.coordinates b g ψ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖CartesianOccupationTransfer.coordinates b g ψ‖ :=
      mul_le_mul_of_nonneg_right (auxiliary_norm_le _ _ _) (norm_nonneg _)
    _ = ‖ψ‖ := by rw [one_mul, (CartesianOccupationTransfer.coordinates b g).norm_map]

/-- Distinct labels and strictly positive actual indexed masses at both ends. -/
def Endpoints (D : IndexedMassData L κ) (a b : ℤ) :=
  {u : PhysicalField L // a ≠ b ∧ 0 < D.seq u a ∧ 0 < D.seq u b}

/-- Literal polar symbol, defined only on the admissible endpoint subtype. -/
def symbol (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates) (a b : ℤ)
    (u : Endpoints D a b) : ℂ :=
  CartesianOccupationTransfer.symbol w a b u.1 / (Real.sqrt (D.seq u.1 a * D.seq u.1 b) : ℂ)

theorem denominator_pos (D : IndexedMassData L κ) (a b : ℤ) (u : Endpoints D a b) :
    0 < Real.sqrt (D.seq u.1 a * D.seq u.1 b) :=
  Real.sqrt_pos.2 (mul_pos u.2.2.1 u.2.2.2)

/-- The exact-action part of QNF1 supplies the modulus; no candidate existence. -/
theorem symbol_norm (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates)
    (h : Specification D w) (a b : ℤ) (u : Endpoints D a b) : ‖symbol D w a b u‖ = 1 := by
  have hn : ‖CartesianOccupationTransfer.symbol w a b u.1‖ =
      Real.sqrt (D.seq u.1 a * D.seq u.1 b) := by
    rw [← CartesianOccupationTransfer.symbol_norm D w h a b u.1, Real.sqrt_sq (norm_nonneg _)]
  rw [symbol, norm_div, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (denominator_pos D a b u), div_self (ne_of_gt (denominator_pos D a b u))]

theorem cartesian_eq_polar (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates)
    (a b : ℤ) (u : Endpoints D a b) :
    symbol D w a b u * (Real.sqrt (D.seq u.1 a * D.seq u.1 b) : ℂ) =
      CartesianOccupationTransfer.symbol w a b u.1 := by
  exact div_mul_cancel₀ _ (by exact_mod_cast (ne_of_gt (denominator_pos D a b u)))

/-- A zero action at either end is excluded from the polar-symbol domain. -/
theorem zero_endpoint_excluded (D : IndexedMassData L κ) (a b : ℤ) (u : PhysicalField L)
    (hz : D.seq u a = 0 ∨ D.seq u b = 0) :
    ¬ (a ≠ b ∧ 0 < D.seq u a ∧ 0 < D.seq u b) := by
  intro h
  rcases hz with ha | hb
  · linarith [h.2.1]
  · linarith [h.2.2]

/-- Fixed physical sector selection, conditional exactly as frozen BOG1. -/
def selectedPhysical (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (a b : ℤ) :
    HN L N →L[ℂ] HN L N :=
  physical (BetheOccupationGauge.sectorBasis hcont L κ hκ N) (s L Fact.out κ hκ) a b

def selectedMeanFieldPhysical (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (a b : ℤ) :
    HN L N →L[ℂ] HN L N :=
  physical (BetheConditionalBasis.meanField_physicalBasis hcont L N hN hκ) (s L Fact.out κ hκ) a b

end QuantumNLS.UnitPhaseTransfer

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.UnitPhaseTransfer.auxiliary
#print axioms QuantumNLS.UnitPhaseTransfer.auxiliary_basis
#print axioms QuantumNLS.UnitPhaseTransfer.auxiliary_norm_le
#print axioms QuantumNLS.UnitPhaseTransfer.physical
#print axioms QuantumNLS.UnitPhaseTransfer.physical_coordinates
#print axioms QuantumNLS.UnitPhaseTransfer.physical_basis
#print axioms QuantumNLS.UnitPhaseTransfer.cartesian_basis_factor
#print axioms QuantumNLS.UnitPhaseTransfer.physical_norm_le
#print axioms QuantumNLS.UnitPhaseTransfer.Endpoints
#print axioms QuantumNLS.UnitPhaseTransfer.symbol
#print axioms QuantumNLS.UnitPhaseTransfer.denominator_pos
#print axioms QuantumNLS.UnitPhaseTransfer.symbol_norm
#print axioms QuantumNLS.UnitPhaseTransfer.cartesian_eq_polar
#print axioms QuantumNLS.UnitPhaseTransfer.zero_endpoint_excluded
#print axioms QuantumNLS.UnitPhaseTransfer.selectedPhysical
#print axioms QuantumNLS.UnitPhaseTransfer.selectedMeanFieldPhysical

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.UnitPhaseTransfer.auxiliary,
    ``QuantumNLS.UnitPhaseTransfer.auxiliary_basis,
    ``QuantumNLS.UnitPhaseTransfer.auxiliary_norm_le,
    ``QuantumNLS.UnitPhaseTransfer.physical,
    ``QuantumNLS.UnitPhaseTransfer.physical_coordinates,
    ``QuantumNLS.UnitPhaseTransfer.physical_basis,
    ``QuantumNLS.UnitPhaseTransfer.cartesian_basis_factor,
    ``QuantumNLS.UnitPhaseTransfer.physical_norm_le,
    ``QuantumNLS.UnitPhaseTransfer.Endpoints,
    ``QuantumNLS.UnitPhaseTransfer.symbol,
    ``QuantumNLS.UnitPhaseTransfer.denominator_pos,
    ``QuantumNLS.UnitPhaseTransfer.symbol_norm,
    ``QuantumNLS.UnitPhaseTransfer.cartesian_eq_polar,
    ``QuantumNLS.UnitPhaseTransfer.zero_endpoint_excluded,
    ``QuantumNLS.UnitPhaseTransfer.selectedPhysical,
    ``QuantumNLS.UnitPhaseTransfer.selectedMeanFieldPhysical]
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
  let mut todo := #[``QuantumNLS.UnitPhaseTransfer.auxiliary,
    ``QuantumNLS.UnitPhaseTransfer.auxiliary_basis,
    ``QuantumNLS.UnitPhaseTransfer.auxiliary_norm_le,
    ``QuantumNLS.UnitPhaseTransfer.physical,
    ``QuantumNLS.UnitPhaseTransfer.physical_coordinates,
    ``QuantumNLS.UnitPhaseTransfer.physical_basis,
    ``QuantumNLS.UnitPhaseTransfer.cartesian_basis_factor,
    ``QuantumNLS.UnitPhaseTransfer.physical_norm_le,
    ``QuantumNLS.UnitPhaseTransfer.Endpoints,
    ``QuantumNLS.UnitPhaseTransfer.symbol,
    ``QuantumNLS.UnitPhaseTransfer.denominator_pos,
    ``QuantumNLS.UnitPhaseTransfer.symbol_norm,
    ``QuantumNLS.UnitPhaseTransfer.cartesian_eq_polar,
    ``QuantumNLS.UnitPhaseTransfer.zero_endpoint_excluded]
  let mut checked : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless checked.contains n do
      checked := checked.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Generic definition reached EXT-001: {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
  Lean.logInfo m!"UnitPhaseTransfer aggregate audit PASS: {seen.size} transitive constants. Generic declarations independent of EXT-001."
