import QuantumNLS.QuantumFourierSpecification
import QuantumNLS.BetheOccupationGauge
import QuantumNLS.OccupationConjugacy

/-! DEF-026 on BOG1 and the DEF-020 specification. The auxiliary operator
is the already realized normalized creation/annihilation collective, retaining
ALL arrays. Every positive N is 1+q. Pullback is through the literal gauged
DEF-007 transform. The classical symbol is defined for any candidate w;
no existence, symbol convergence or target-gauge conclusion is presumed. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.CartesianOccupationTransfer
open BetheLabels BetheCoefficientTransform BetheOccupationGauge Occupation
open QuantumFourierSpecification OccupationUnitary
variable {L κ : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The actual bounded N^-1 a_b^* a_a on Sym^N ell²(Z), N positive. -/
def auxiliary (q : ℕ) (a b : ℤ) : Boson (1+q) →L[ℂ] Boson (1+q) :=
  OccupationConjugacy.collective q a b

theorem auxiliary_offdiag (q : ℕ) (a b : ℤ) (hab : a ≠ b) (m : Arr (1+q))
    (hd : DonorOK a m.1) :
    auxiliary q a b (basisVector m) =
      ((Real.sqrt ((m.1 a : ℝ) * ((m.1 b : ℝ) + 1)) / (1+q : ℕ) : ℝ) : ℂ) •
        basisVector (shiftArr a b m hd) := OccupationConjugacy.collective_offdiag q a b hab m hd

theorem auxiliary_diag (q : ℕ) (a : ℤ) (m : Arr (1+q)) :
    auxiliary q a a (basisVector m) =
      (((m.1 a : ℝ) / (1+q : ℕ) : ℝ) : ℂ) • basisVector m :=
  OccupationConjugacy.collective_diag q a m

theorem auxiliary_empty (q : ℕ) (a b : ℤ) (m : Arr (1+q)) (hd : ¬ DonorOK a m.1) :
    auxiliary q a b (basisVector m) = 0 := OccupationConjugacy.collective_empty q a b m hd

theorem auxiliary_norm_le (q : ℕ) (a b : ℤ) : ‖auxiliary q a b‖ ≤ 1 :=
  OccupationConjugacy.collective_norm_le q a b

/-- Full coefficient transform of the literally rephased BOG1 basis. -/
def coordinates (b : BetheBasis L N) (g : Gauge) : HN L N ≃ₗᵢ[ℂ] OccupationHilbert.H N :=
  occupationCoefficient (gaugedBasis b g)

/-- E^q = J_g^* E J_g. This is a constructed bounded operator. -/
def physical (b : BetheBasis L N) (g : Gauge) (a c : ℤ) : HN L N →L[ℂ] HN L N :=
  (coordinates b g).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    OccupationHilbert.E N a c ∘L (coordinates b g).toContinuousLinearEquiv.toContinuousLinearMap

theorem physical_coordinates (b : BetheBasis L N) (g : Gauge) (a c : ℤ) (ψ : HN L N) :
    coordinates b g (physical b g a c ψ) = OccupationHilbert.E N a c (coordinates b g ψ) := by
  exact (coordinates b g).apply_symm_apply _

/-- Pullback agrees with the actual symmetric-tensor collective. -/
theorem physical_fock (q : ℕ) (b : BetheBasis L (1+q)) (g : Gauge) (a c : ℤ)
    (ψ : HN L (1+q)) :
    fockTransform (gaugedBasis b g) (physical b g a c ψ) =
      auxiliary q a c (fockTransform (gaugedBasis b g) ψ) := by
  apply (U4 (1+q)).injective
  change U4 (1+q) ((U4 (1+q)).symm (coordinates b g (physical b g a c ψ))) =
    U4 (1+q) (OccupationConjugacy.collective q a c ((U4 (1+q)).symm (coordinates b g ψ)))
  rw [LinearIsometryEquiv.apply_symm_apply, OccupationConjugacy.U4_collective,
    LinearIsometryEquiv.apply_symm_apply, physical_coordinates]

/-- Complete normalized Bethe basis vector in the coefficient coordinates. -/
theorem coordinates_basis (b : BetheBasis L N) (g : Gauge) (m : MArr N) :
    coordinates b g (gaugedBasis b g m) = lp.single 2 (marrArr N m) 1 := by
  change (reindexBasis (marrArr N) (gaugedBasis b g)).repr _ = _
  have he : reindexBasis (marrArr N) (gaugedBasis b g) (marrArr N m) = gaugedBasis b g m := by
    rw [reindexBasis_apply, Equiv.symm_apply_apply]
  rw [← he, HilbertBasis.repr_self]

/-- Exact physical matrix coefficient, including empty donors and all labels. -/
theorem physical_basis (b : BetheBasis L N) (g : Gauge) (a c : ℤ) (m : MArr N) :
    physical b g a c (gaugedBasis b g m) =
      if hd : DonorOK a (marrArr N m).1 then
        (coef N a c (marrArr N m).1 : ℂ) •
          gaugedBasis b g ((marrArr N).symm (shiftArr a c (marrArr N m) hd)) else 0 := by
  apply (coordinates b g).injective
  rw [physical_coordinates, coordinates_basis, OccupationHilbert.E_single]
  split_ifs with hd
  · rw [map_smul, coordinates_basis, Equiv.apply_symm_apply]
    rw [← lp.single_smul]
    simp only [smul_eq_mul, mul_one]
  · simp

/-- Literal off-diagonal coefficient after gauged Bethe pullback. -/
theorem physical_offdiag (b : BetheBasis L N) (g : Gauge) (a c : ℤ) (hac : a ≠ c)
    (m : MArr N) (hd : DonorOK a (marrArr N m).1) :
    physical b g a c (gaugedBasis b g m) =
      ((Real.sqrt (((marrArr N m).1 a : ℝ) * (((marrArr N m).1 c : ℝ) + 1)) / N : ℝ) : ℂ) •
        gaugedBasis b g ((marrArr N).symm (shiftArr a c (marrArr N m) hd)) := by
  rw [physical_basis, dite_eq_left hd, coef_offdiag hac]

/-- Literal diagonal fraction, also when the diagonal donor is empty. -/
theorem physical_diag (b : BetheBasis L N) (g : Gauge) (a : ℤ) (m : MArr N) :
    physical b g a a (gaugedBasis b g m) =
      ((((marrArr N m).1 a : ℝ) / N : ℝ) : ℂ) • gaugedBasis b g m := by
  rw [physical_basis]
  split_ifs with hd
  · have hs : shiftArr a a (marrArr N m) hd = marrArr N m := Subtype.ext (shift_self hd)
    rw [hs, Equiv.symm_apply_apply, coef_diag]
  · have hz : (marrArr N m).1 a = 0 := by
      have : ¬ 1 ≤ (marrArr N m).1 a := hd
      omega
    simp [hz]

theorem physical_norm_le (b : BetheBasis L N) (g : Gauge) (a c : ℤ) :
    ‖physical b g a c‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  rw [one_mul, ← (coordinates b g).norm_map, physical_coordinates]
  calc
    ‖OccupationHilbert.E N a c (coordinates b g ψ)‖ ≤
        ‖OccupationHilbert.E N a c‖ * ‖coordinates b g ψ‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖coordinates b g ψ‖ := mul_le_mul_of_nonneg_right (OccupationHilbert.E_norm_le _ _ _) (norm_nonneg _)
    _ = ‖ψ‖ := by rw [one_mul, (coordinates b g).norm_map]

/-- Receiver minus donor, with the literal complete-array destination. -/
def spectralGap (Λ : MArr N → ℝ) (a c : ℤ) (m : MArr N)
    (hd : DonorOK a (marrArr N m).1) : ℝ :=
  Λ ((marrArr N).symm (shiftArr a c (marrArr N m) hd)) - Λ m

/-- Literal Cartesian symbol. It remains defined at zero endpoint actions. -/
def symbol (w : PhysicalField L → Coordinates) (a b : ℤ) (u : PhysicalField L) : ℂ := w u a * conj (w u b)

/-- The inner-product convention fixes donor a, receiver b in this order. -/
theorem symbol_matrixUnit (w : PhysicalField L → Coordinates) (a b : ℤ) (u : PhysicalField L) :
    ⟪w u, OccupationConjugacy.matrixUnit a b (w u)⟫_ℂ = symbol w a b u := by
  simp only [OccupationConjugacy.matrixUnit, InnerProductSpace.rankOne_apply, inner_smul_right,
    oneBasis_apply, lp.inner_single_left, lp.inner_single_right]
  simp [symbol, mul_comm]

theorem symbol_norm (D : IndexedMassProperness.IndexedMassData L κ) (w : PhysicalField L → Coordinates)
    (h : Specification D w) (a b : ℤ) (u : PhysicalField L) :
    ‖symbol w a b u‖ ^ 2 = D.seq u a * D.seq u b := by
  rw [symbol, norm_mul, Complex.norm_conj, mul_pow, h.2.2, h.2.2]

theorem symbol_zero_left (w : PhysicalField L → Coordinates) (a b : ℤ) (u : PhysicalField L)
    (ha : w u a = 0) : symbol w a b u = 0 := by simp [symbol, ha]

/-- The fixed parameter selection is made before labels, profiles or tests.
Only the actual N>=2 physical complete-basis instantiation uses EXT-001. -/
def selectedPhysical (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (a b : ℤ) :
    HN L N →L[ℂ] HN L N :=
  physical (BetheOccupationGauge.sectorBasis hcont L κ hκ N) (s L Fact.out κ hκ) a b

/-- Mean-field c_N=kappa/N, with the same once-for-all phase selection at L,kappa. -/
def selectedMeanFieldPhysical (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (a b : ℤ) :
    HN L N →L[ℂ] HN L N :=
  physical (BetheConditionalBasis.meanField_physicalBasis hcont L N hN hκ) (s L Fact.out κ hκ) a b

end QuantumNLS.CartesianOccupationTransfer

#print axioms QuantumNLS.CartesianOccupationTransfer.auxiliary
#print axioms QuantumNLS.CartesianOccupationTransfer.auxiliary_offdiag
#print axioms QuantumNLS.CartesianOccupationTransfer.auxiliary_diag
#print axioms QuantumNLS.CartesianOccupationTransfer.auxiliary_empty
#print axioms QuantumNLS.CartesianOccupationTransfer.auxiliary_norm_le
#print axioms QuantumNLS.CartesianOccupationTransfer.coordinates
#print axioms QuantumNLS.CartesianOccupationTransfer.physical
#print axioms QuantumNLS.CartesianOccupationTransfer.physical_coordinates
#print axioms QuantumNLS.CartesianOccupationTransfer.physical_fock
#print axioms QuantumNLS.CartesianOccupationTransfer.coordinates_basis
#print axioms QuantumNLS.CartesianOccupationTransfer.physical_basis
#print axioms QuantumNLS.CartesianOccupationTransfer.physical_offdiag
#print axioms QuantumNLS.CartesianOccupationTransfer.physical_diag
#print axioms QuantumNLS.CartesianOccupationTransfer.physical_norm_le
#print axioms QuantumNLS.CartesianOccupationTransfer.spectralGap
#print axioms QuantumNLS.CartesianOccupationTransfer.symbol
#print axioms QuantumNLS.CartesianOccupationTransfer.symbol_matrixUnit
#print axioms QuantumNLS.CartesianOccupationTransfer.symbol_norm
#print axioms QuantumNLS.CartesianOccupationTransfer.symbol_zero_left
#print axioms QuantumNLS.CartesianOccupationTransfer.selectedPhysical
#print axioms QuantumNLS.CartesianOccupationTransfer.selectedMeanFieldPhysical

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.CartesianOccupationTransfer.auxiliary,
    ``QuantumNLS.CartesianOccupationTransfer.auxiliary_offdiag,
    ``QuantumNLS.CartesianOccupationTransfer.auxiliary_diag,
    ``QuantumNLS.CartesianOccupationTransfer.auxiliary_empty,
    ``QuantumNLS.CartesianOccupationTransfer.auxiliary_norm_le,
    ``QuantumNLS.CartesianOccupationTransfer.coordinates,
    ``QuantumNLS.CartesianOccupationTransfer.physical,
    ``QuantumNLS.CartesianOccupationTransfer.physical_coordinates,
    ``QuantumNLS.CartesianOccupationTransfer.physical_fock,
    ``QuantumNLS.CartesianOccupationTransfer.coordinates_basis,
    ``QuantumNLS.CartesianOccupationTransfer.physical_basis,
    ``QuantumNLS.CartesianOccupationTransfer.physical_offdiag,
    ``QuantumNLS.CartesianOccupationTransfer.physical_diag,
    ``QuantumNLS.CartesianOccupationTransfer.physical_norm_le,
    ``QuantumNLS.CartesianOccupationTransfer.spectralGap,
    ``QuantumNLS.CartesianOccupationTransfer.symbol,
    ``QuantumNLS.CartesianOccupationTransfer.symbol_matrixUnit,
    ``QuantumNLS.CartesianOccupationTransfer.symbol_norm,
    ``QuantumNLS.CartesianOccupationTransfer.symbol_zero_left,
    ``QuantumNLS.CartesianOccupationTransfer.selectedPhysical,
    ``QuantumNLS.CartesianOccupationTransfer.selectedMeanFieldPhysical]
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
            throwError "Cartesian occupation transfer nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  let mut todo := #[``QuantumNLS.CartesianOccupationTransfer.auxiliary,
    ``QuantumNLS.CartesianOccupationTransfer.auxiliary_offdiag,
    ``QuantumNLS.CartesianOccupationTransfer.auxiliary_diag,
    ``QuantumNLS.CartesianOccupationTransfer.auxiliary_empty,
    ``QuantumNLS.CartesianOccupationTransfer.auxiliary_norm_le,
    ``QuantumNLS.CartesianOccupationTransfer.coordinates,
    ``QuantumNLS.CartesianOccupationTransfer.physical,
    ``QuantumNLS.CartesianOccupationTransfer.physical_coordinates,
    ``QuantumNLS.CartesianOccupationTransfer.physical_fock,
    ``QuantumNLS.CartesianOccupationTransfer.coordinates_basis,
    ``QuantumNLS.CartesianOccupationTransfer.physical_basis,
    ``QuantumNLS.CartesianOccupationTransfer.physical_offdiag,
    ``QuantumNLS.CartesianOccupationTransfer.physical_diag,
    ``QuantumNLS.CartesianOccupationTransfer.physical_norm_le,
    ``QuantumNLS.CartesianOccupationTransfer.spectralGap,
    ``QuantumNLS.CartesianOccupationTransfer.symbol,
    ``QuantumNLS.CartesianOccupationTransfer.symbol_matrixUnit,
    ``QuantumNLS.CartesianOccupationTransfer.symbol_norm,
    ``QuantumNLS.CartesianOccupationTransfer.symbol_zero_left]
  let mut checked : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless checked.contains n do
      checked := checked.insert n
      if n.toString == "QuantumNLS.BetheConditionalBasis.AbstractContinuity" then
        throwError "Generic definition reached EXT-001 premise: {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
  Lean.logInfo m!"Cartesian occupation transfer aggregate audit PASS: {seen.size} transitive constants. Generic definitions independent of EXT-001; actual BCB1 instantiation carries its explicit Prop premise."
