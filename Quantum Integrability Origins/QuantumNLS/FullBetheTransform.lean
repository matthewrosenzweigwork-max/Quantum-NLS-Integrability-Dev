import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.BetheOccupationGauge

/-! R-098A4CF1 / A03:unitary, A03.tex:64–104.
The physical basis is UBB1, with arbitrary once-for-all unit phases. The
map is the literal DEF-007 fockTransform into the realized symmetric
occupation sector; all HasSum statements use the net of finite subsets.
ACP1 is a proved import, with no remaining continuity hypothesis. -/
noncomputable section
open scoped BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace QuantumNLS.FullBetheTransform
open PhysicalTensor BetheLabels BetheCoefficientTransform BetheOccupationGauge
local instance (α : Type) : DecidableEq α := Classical.decEq α
variable (L : ℝ) [Fact (0 < L)] (N : ℕ) (hN : 1 ≤ N) (c : ℝ) (hc : 0 < c) (g : Gauge)

def basis : BetheBasis L N := gaugedBasis (UnconditionalBetheBasis.physicalBasis L N hN c hc) g

theorem basis_phase (m : MArr N) : basis L N hN c hc g m =
    (g N m).val • UnconditionalBetheBasis.physicalBasis L N hN c hc m :=
  gaugedBasis_apply _ _ _

def transform : physSector L N ≃ₗᵢ[ℂ] OccupationUnitary.Boson N :=
  fockTransform (basis L N hN c hc g)

def occupation (m : MArr N) : OccupationUnitary.Boson N :=
  OccupationUnitary.occupationBasis N (marrArr N m)

theorem occupation_coord (m : MArr N) : OccupationUnitary.U4 N (occupation N m) =
    lp.single 2 (marrArr N m) 1 := (OccupationUnitary.occupationBasis N).repr_self _

theorem transform_coord (f : physSector L N) (m : MArr N) :
    OccupationUnitary.U4 N (transform L N hN c hc g f) (marrArr N m) =
      ⟪basis L N hN c hc g m, f⟫_ℂ := fockTransform_coord _ _ _

theorem transform_basis (m : MArr N) :
    transform L N hN c hc g (basis L N hN c hc g m) = occupation N m := by
  apply (OccupationUnitary.U4 N).injective
  rw [occupation_coord]
  ext k
  obtain ⟨j, rfl⟩ := (marrArr N).surjective k
  rw [transform_coord]
  simpa [HilbertBasis.repr_apply_apply, lp.single_apply, Pi.single_apply, (marrArr N).injective.eq_iff] using
    congrArg (fun a => a j) ((basis L N hN c hc g).repr_self m)

theorem unique (V : physSector L N ≃ₗᵢ[ℂ] OccupationUnitary.Boson N)
    (hV : ∀ m, V (basis L N hN c hc g m) = occupation N m) :
    V = transform L N hN c hc g := by
  ext f
  have hs := coefficientTransform_expansion (basis L N hN c hc g) f
  have h1 := hs.mapL V.toContinuousLinearEquiv.toContinuousLinearMap
  have h2 := hs.mapL (transform L N hN c hc g).toContinuousLinearEquiv.toContinuousLinearMap
  change HasSum (fun m => V (⟪basis L N hN c hc g m, f⟫_ℂ • basis L N hN c hc g m)) (V f) at h1
  change HasSum (fun m => transform L N hN c hc g
    (⟪basis L N hN c hc g m, f⟫_ℂ • basis L N hN c hc g m)) (transform L N hN c hc g f) at h2
  simp only [map_smul, hV] at h1
  simp only [map_smul, transform_basis] at h2
  exact congrArg Subtype.val (h1.unique h2)

theorem exists_unique_unitary : ∃! V : physSector L N ≃ₗᵢ[ℂ] OccupationUnitary.Boson N,
    ∀ m, V (basis L N hN c hc g m) = occupation N m :=
  ⟨transform L N hN c hc g, transform_basis L N hN c hc g,
    fun V hV => unique L N hN c hc g V hV⟩

theorem expansion (f : physSector L N) :
    HasSum (fun m => ⟪basis L N hN c hc g m, f⟫_ℂ • occupation N m)
      (transform L N hN c hc g f) := by
  have h := (coefficientTransform_expansion (basis L N hN c hc g) f).mapL
    (transform L N hN c hc g).toContinuousLinearEquiv.toContinuousLinearMap
  change HasSum (fun m => transform L N hN c hc g
    (⟪basis L N hN c hc g m, f⟫_ℂ • basis L N hN c hc g m))
    (transform L N hN c hc g f) at h
  simpa only [map_smul, transform_basis] using h

theorem synthesis (a : lp (fun _ : MArr N => ℂ) 2) :
    HasSum (fun m => a m • basis L N hN c hc g m)
      ((coefficientTransform (basis L N hN c hc g)).symm a) :=
  coefficientTransform_symm_apply _ _

theorem inverse_expansion (v : OccupationUnitary.Boson N) :
    HasSum (fun m => OccupationUnitary.U4 N v (marrArr N m) • basis L N hN c hc g m)
      ((transform L N hN c hc g).symm v) := by
  have h := coefficientTransform_expansion (basis L N hN c hc g)
    ((transform L N hN c hc g).symm v)
  have he (m : MArr N) := transform_coord L N hN c hc g
    ((transform L N hN c hc g).symm v) m
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  simpa only [← he] using h

theorem synthesis_transform (a : lp (fun _ : MArr N => ℂ) 2) :
    HasSum (fun m => a m • occupation N m)
      (transform L N hN c hc g ((coefficientTransform (basis L N hN c hc g)).symm a)) := by
  have h := (synthesis L N hN c hc g a).mapL
    (transform L N hN c hc g).toContinuousLinearEquiv.toContinuousLinearMap
  change HasSum (fun m => transform L N hN c hc g (a m • basis L N hN c hc g m))
    (transform L N hN c hc g ((coefficientTransform (basis L N hN c hc g)).symm a)) at h
  simpa only [map_smul, transform_basis] using h

theorem inverse_series (a : lp (fun _ : MArr N => ℂ) 2)
    (v : OccupationUnitary.Boson N) (hv : HasSum (fun m => a m • occupation N m) v) :
    HasSum (fun m => a m • basis L N hN c hc g m) ((transform L N hN c hc g).symm v) := by
  have h := hv.mapL (transform L N hN c hc g).symm.toContinuousLinearEquiv.toContinuousLinearMap
  change HasSum (fun m => (transform L N hN c hc g).symm (a m • occupation N m))
    ((transform L N hN c hc g).symm v) at h
  simpa only [map_smul, ← transform_basis L N hN c hc g,
    LinearIsometryEquiv.symm_apply_apply] using h

theorem parseval (f : physSector L N) :
    HasSum (fun m => ‖⟪basis L N hN c hc g m, f⟫_ℂ‖ ^ 2) (‖f‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num)
    (coefficientTransform (basis L N hN c hc g) f)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_coefficientTransform,
    coefficientTransform_apply] using h

theorem synthesis_parseval (a : lp (fun _ : MArr N => ℂ) 2) :
    HasSum (fun m => ‖a m‖ ^ 2)
      (‖(coefficientTransform (basis L N hN c hc g)).symm a‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) a
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using h

theorem full_unitary : Function.Surjective (transform L N hN c hc g) ∧
    (∀ f, ‖transform L N hN c hc g f‖ = ‖f‖) ∧
    (∀ f v, ⟪transform L N hN c hc g f, transform L N hN c hc g v⟫_ℂ = ⟪f,v⟫_ℂ) :=
  ⟨(transform L N hN c hc g).surjective, (transform L N hN c hc g).norm_map,
    (transform L N hN c hc g).inner_map_map⟩
end QuantumNLS.FullBetheTransform

#print axioms QuantumNLS.FullBetheTransform.basis
#print axioms QuantumNLS.FullBetheTransform.basis_phase
#print axioms QuantumNLS.FullBetheTransform.transform
#print axioms QuantumNLS.FullBetheTransform.occupation
#print axioms QuantumNLS.FullBetheTransform.occupation_coord
#print axioms QuantumNLS.FullBetheTransform.transform_coord
#print axioms QuantumNLS.FullBetheTransform.transform_basis
#print axioms QuantumNLS.FullBetheTransform.unique
#print axioms QuantumNLS.FullBetheTransform.exists_unique_unitary
#print axioms QuantumNLS.FullBetheTransform.expansion
#print axioms QuantumNLS.FullBetheTransform.synthesis
#print axioms QuantumNLS.FullBetheTransform.inverse_expansion
#print axioms QuantumNLS.FullBetheTransform.synthesis_transform
#print axioms QuantumNLS.FullBetheTransform.inverse_series
#print axioms QuantumNLS.FullBetheTransform.parseval
#print axioms QuantumNLS.FullBetheTransform.synthesis_parseval
#print axioms QuantumNLS.FullBetheTransform.full_unitary

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FullBetheTransform.basis,
    ``QuantumNLS.FullBetheTransform.basis_phase,
    ``QuantumNLS.FullBetheTransform.transform,
    ``QuantumNLS.FullBetheTransform.occupation,
    ``QuantumNLS.FullBetheTransform.occupation_coord,
    ``QuantumNLS.FullBetheTransform.transform_coord,
    ``QuantumNLS.FullBetheTransform.transform_basis,
    ``QuantumNLS.FullBetheTransform.unique,
    ``QuantumNLS.FullBetheTransform.exists_unique_unitary,
    ``QuantumNLS.FullBetheTransform.expansion,
    ``QuantumNLS.FullBetheTransform.synthesis,
    ``QuantumNLS.FullBetheTransform.inverse_expansion,
    ``QuantumNLS.FullBetheTransform.synthesis_transform,
    ``QuantumNLS.FullBetheTransform.inverse_series,
    ``QuantumNLS.FullBetheTransform.parseval,
    ``QuantumNLS.FullBetheTransform.synthesis_parseval,
    ``QuantumNLS.FullBetheTransform.full_unitary]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.FullBetheTransform." then
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
            throwError "Result nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; all own and generated constants standard-only; ACP1 supplies proved continuity, no hcont premise."
