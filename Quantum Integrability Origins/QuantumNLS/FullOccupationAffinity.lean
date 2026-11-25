import QuantumNLS.UnitPhaseTransfer

/-! DEF-055. Sums over donor-supported COMPLETE occupation arrays.
Unit phases and a unit normalized coefficient vector are explicit inputs.
Absolute convergence is derived from the actual ell² coefficients, never assumed.
This definition asserts neither residual convergence nor finite-cell gauge existence. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace QuantumNLS.FullOccupationAffinity
open Occupation OccupationHilbert BetheCoefficientTransform BetheOccupationGauge
variable {N : ℕ} {L : ℝ} [Fact (0 < L)]

/-- Unit complex scalar; used for both edge and target phases. -/
def Phase := {z : ℂ // ‖z‖ = 1}

/-- Normalized full-sector coefficient vector. -/
def UnitCoefficients (N : ℕ) := {g : H N // ‖g‖ = 1}

/-- All exterior occupations remain coordinates of each donor array. -/
def sourceCoefficients (a : ℤ) (g : H N) : L2 (Donor N a) :=
  restrictL2 (Subtype.val : Donor N a → Arr N) Subtype.val_injective g

def targetCoefficients (a b : ℤ) (g : H N) : L2 (Donor N a) :=
  restrictL2 (destination N a b) (destination_injective N a b) g

/-- Literal positive summand |g_m| |g_(m-e_a+e_b)|. -/
def affinityTerm (a b : ℤ) (g : H N) (m : Donor N a) : ℝ :=
  ‖g m.1‖ * ‖g (destination N a b m)‖

theorem summable_affinityTerm (a b : ℤ) (g : H N) : Summable (affinityTerm a b g) := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]; norm_num
  refine (lp.summable_mul hp (sourceCoefficients a g) (targetCoefficients a b g)).congr ?_
  intro m
  simp only [affinityTerm, sourceCoefficients, targetCoefficients, restrictL2_apply]

/-- Full occupation affinity, not a marginal on selected counts. -/
def affinity (a b : ℤ) (g : H N) : ℝ := ∑' m : Donor N a, affinityTerm a b g m

theorem affinity_nonneg (a b : ℤ) (g : H N) : 0 ≤ affinity a b g :=
  tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem affinity_le_norm_sq (a b : ℤ) (g : H N) : affinity a b g ≤ ‖g‖ ^ 2 := by
  have hp : (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    rw [Real.holderConjugate_iff]; norm_num
  calc
    affinity a b g = ∑' m : Donor N a,
        ‖sourceCoefficients a g m‖ * ‖targetCoefficients a b g m‖ := by
      apply tsum_congr
      intro m
      simp only [affinityTerm, sourceCoefficients, targetCoefficients, restrictL2_apply]
    _ ≤ ‖sourceCoefficients a g‖ * ‖targetCoefficients a b g‖ :=
      lp.tsum_mul_le_mul_norm' hp (sourceCoefficients a g) (targetCoefficients a b g)
    _ ≤ ‖g‖ * ‖g‖ := mul_le_mul (restrictL2_norm_le _ _ g) (restrictL2_norm_le _ _ g)
      (norm_nonneg _) (norm_nonneg _)
    _ = ‖g‖ ^ 2 := (pow_two _).symm

theorem affinity_le_one (a b : ℤ) (g : UnitCoefficients N) : affinity a b g.1 ≤ 1 := by
  simpa only [g.2, one_pow] using affinity_le_norm_sq a b g.1

/-- Literal directed edge coefficient, with donor/receiver order fixed. -/
def overlapTerm (a b : ℤ) (α : Donor N a → Phase) (g : H N) (m : Donor N a) : ℂ :=
  (α m).1 * g m.1 * conj (g (destination N a b m))

theorem norm_overlapTerm (a b : ℤ) (α : Donor N a → Phase) (g : H N) (m : Donor N a) :
    ‖overlapTerm a b α g m‖ = affinityTerm a b g m := by
  simp only [overlapTerm, affinityTerm, norm_mul, Complex.norm_conj, (α m).2, one_mul]

theorem summable_overlapTerm (a b : ℤ) (α : Donor N a → Phase) (g : H N) :
    Summable (overlapTerm a b α g) :=
  Summable.of_norm_bounded (summable_affinityTerm a b g) (fun m => (norm_overlapTerm a b α g m).le)

/-- The complex coefficient sum in the report's inner-product convention. -/
def overlap (a b : ℤ) (α : Donor N a → Phase) (g : H N) : ℂ :=
  ∑' m : Donor N a, overlapTerm a b α g m

/-- D has no factor of two. -/
def defect (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N) : ℝ :=
  affinity a b g - (conj ζ.1 * overlap a b α g).re

def defectTerm (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N) (m : Donor N a) : ℝ :=
  affinityTerm a b g m - (conj ζ.1 * overlapTerm a b α g m).re

theorem summable_rotated (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N) :
    Summable (fun m => conj ζ.1 * overlapTerm a b α g m) :=
  (summable_overlapTerm a b α g).mul_left _

theorem summable_defectTerm (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N) :
    Summable (defectTerm a b α ζ g) :=
  (summable_affinityTerm a b g).sub ((Complex.hasSum_re (summable_rotated a b α ζ g).hasSum).summable)

theorem defect_eq_tsum (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N) :
    defect a b α ζ g = ∑' m : Donor N a, defectTerm a b α ζ g m := by
  rw [defect, overlap, ← tsum_mul_left, Complex.re_tsum (summable_rotated a b α ζ g)]
  exact ((summable_affinityTerm a b g).tsum_sub
    (Complex.hasSum_re (summable_rotated a b α ζ g).hasSum).summable).symm

theorem defectTerm_nonneg (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N)
    (m : Donor N a) : 0 ≤ defectTerm a b α ζ g m := by
  have h := Complex.re_le_norm (conj ζ.1 * overlapTerm a b α g m)
  rw [norm_mul, Complex.norm_conj, ζ.2, one_mul, norm_overlapTerm] at h
  exact sub_nonneg.mpr h

theorem defect_nonneg (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N) :
    0 ≤ defect a b α ζ g := by
  rw [defect_eq_tsum]
  exact tsum_nonneg (defectTerm_nonneg a b α ζ g)

/-- The concrete partial transfer with arbitrary unit edge phases. -/
def transfer (a b : ℤ) (α : Donor N a → Phase) : H N →L[ℂ] H N :=
  transferOp N a b (fun m => (α m).1) (fun m => (α m).2.le)

theorem transfer_basis (a b : ℤ) (α : Donor N a → Phase) (m : Arr N) :
    transfer a b α (lp.single 2 m 1) =
      if hd : DonorOK a m.1 then
        (α ⟨m,hd⟩).1 • lp.single 2 (shiftArr a b m hd) 1 else 0 := by
  rw [transfer, transferOp_single]
  split_ifs with hd
  · rw [← lp.single_smul]; simp only [smul_eq_mul, mul_one]
  · rfl

theorem transfer_norm_le (a b : ℤ) (α : Donor N a → Phase) : ‖transfer a b α‖ ≤ 1 :=
  transferOp_norm_le _ _ _ _ _

/-- Checks the exact conjugation and orientation against the constructed operator. -/
theorem inner_transfer (a b : ℤ) (α : Donor N a → Phase) (g : H N) :
    ⟪g, transfer a b α g⟫_ℂ = overlap a b α g := by
  change ⟪g, (injectL2 (destination N a b) (destination_injective N a b)).toContinuousLinearMap
    (diagonal (fun m => (α m).1) 1 zero_le_one (fun m => (α m).2.le)
      (sourceCoefficients a g))⟫_ℂ = _
  rw [← ContinuousLinearMap.adjoint_inner_left, lp.inner_eq_tsum]
  apply tsum_congr
  intro m
  change ⟪(targetCoefficients a b g) m,
    (diagonal (fun m => (α m).1) 1 zero_le_one (fun m => (α m).2.le)
      (sourceCoefficients a g)) m⟫_ℂ = _
  rw [OccupationHilbert.diagonal_apply]
  simp only [RCLike.inner_apply, sourceCoefficients, targetCoefficients, restrictL2_apply, overlapTerm]

theorem real_inner_eq_affinity_sub_defect (a b : ℤ) (α : Donor N a → Phase)
    (ζ : Phase) (g : H N) :
    (conj ζ.1 * ⟪g, transfer a b α g⟫_ℂ).re = affinity a b g - defect a b α ζ g := by
  rw [inner_transfer, defect]; ring

/-- DEF-007/025 coefficients in exactly the COT1 full-array coordinates. -/
def physicalCoefficients (b : BetheBasis L N) (γ : Gauge) (ψ : {ψ : HN L N // ‖ψ‖ = 1}) :
    UnitCoefficients N :=
  ⟨CartesianOccupationTransfer.coordinates b γ ψ.1, by
    rw [(CartesianOccupationTransfer.coordinates b γ).norm_map, ψ.2]⟩

/-- Literal agreement with the gauged DEF-007 coefficient of each full Bethe label. -/
theorem physicalCoefficients_apply (b : BetheBasis L N) (γ : Gauge)
    (ψ : {ψ : HN L N // ‖ψ‖ = 1}) (m : BetheLabels.MArr N) :
    (physicalCoefficients b γ ψ).1 (marrArr N m) = ⟪gaugedBasis b γ m, ψ.1⟫_ℂ :=
  occupationCoefficient_apply _ _ _

/-- Edge phases from an actual BOG1 full-sector scalar gauge. -/
def gaugeEdge (γ : Gauge) (a b : ℤ) (m : Donor N a) : Phase :=
  ⟨(γ N ((marrArr N).symm m.1)).1 *
    conj (γ N ((marrArr N).symm (destination N a b m))).1, by
      rw [norm_mul, Complex.norm_conj,
        (γ N ((marrArr N).symm m.1)).2,
        (γ N ((marrArr N).symm (destination N a b m))).2, one_mul]⟩

/-- The canonical DEF-027 shift is the unit-edge specialization. -/
theorem transfer_identity (a b : ℤ) :
    transfer a b (fun _ => ⟨1, norm_one⟩) = UnitPhaseTransfer.auxiliary N a b := rfl

/-- Selected physical coefficients retain exactly the existing EXT-001 premise. -/
def selectedCoefficients (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ)
    (ψ : {ψ : HN L N // ‖ψ‖ = 1}) : UnitCoefficients N :=
  physicalCoefficients (BetheOccupationGauge.sectorBasis hcont L κ hκ N) (s L Fact.out κ hκ) ψ

def selectedMeanFieldCoefficients (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (ψ : {ψ : HN L N // ‖ψ‖ = 1}) : UnitCoefficients N :=
  physicalCoefficients (BetheConditionalBasis.meanField_physicalBasis hcont L N hN hκ)
    (s L Fact.out κ hκ) ψ

end QuantumNLS.FullOccupationAffinity

-- BEGIN COMPLETE DECLARATION AUDIT
#print axioms QuantumNLS.FullOccupationAffinity.Phase
#print axioms QuantumNLS.FullOccupationAffinity.UnitCoefficients
#print axioms QuantumNLS.FullOccupationAffinity.sourceCoefficients
#print axioms QuantumNLS.FullOccupationAffinity.targetCoefficients
#print axioms QuantumNLS.FullOccupationAffinity.affinityTerm
#print axioms QuantumNLS.FullOccupationAffinity.summable_affinityTerm
#print axioms QuantumNLS.FullOccupationAffinity.affinity
#print axioms QuantumNLS.FullOccupationAffinity.affinity_nonneg
#print axioms QuantumNLS.FullOccupationAffinity.affinity_le_norm_sq
#print axioms QuantumNLS.FullOccupationAffinity.affinity_le_one
#print axioms QuantumNLS.FullOccupationAffinity.overlapTerm
#print axioms QuantumNLS.FullOccupationAffinity.norm_overlapTerm
#print axioms QuantumNLS.FullOccupationAffinity.summable_overlapTerm
#print axioms QuantumNLS.FullOccupationAffinity.overlap
#print axioms QuantumNLS.FullOccupationAffinity.defect
#print axioms QuantumNLS.FullOccupationAffinity.defectTerm
#print axioms QuantumNLS.FullOccupationAffinity.summable_rotated
#print axioms QuantumNLS.FullOccupationAffinity.summable_defectTerm
#print axioms QuantumNLS.FullOccupationAffinity.defect_eq_tsum
#print axioms QuantumNLS.FullOccupationAffinity.defectTerm_nonneg
#print axioms QuantumNLS.FullOccupationAffinity.defect_nonneg
#print axioms QuantumNLS.FullOccupationAffinity.transfer
#print axioms QuantumNLS.FullOccupationAffinity.transfer_basis
#print axioms QuantumNLS.FullOccupationAffinity.transfer_norm_le
#print axioms QuantumNLS.FullOccupationAffinity.inner_transfer
#print axioms QuantumNLS.FullOccupationAffinity.real_inner_eq_affinity_sub_defect
#print axioms QuantumNLS.FullOccupationAffinity.physicalCoefficients
#print axioms QuantumNLS.FullOccupationAffinity.physicalCoefficients_apply
#print axioms QuantumNLS.FullOccupationAffinity.gaugeEdge
#print axioms QuantumNLS.FullOccupationAffinity.transfer_identity
#print axioms QuantumNLS.FullOccupationAffinity.selectedCoefficients
#print axioms QuantumNLS.FullOccupationAffinity.selectedMeanFieldCoefficients

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.FullOccupationAffinity.Phase,
    ``QuantumNLS.FullOccupationAffinity.UnitCoefficients,
    ``QuantumNLS.FullOccupationAffinity.sourceCoefficients,
    ``QuantumNLS.FullOccupationAffinity.targetCoefficients,
    ``QuantumNLS.FullOccupationAffinity.affinityTerm,
    ``QuantumNLS.FullOccupationAffinity.summable_affinityTerm,
    ``QuantumNLS.FullOccupationAffinity.affinity,
    ``QuantumNLS.FullOccupationAffinity.affinity_nonneg,
    ``QuantumNLS.FullOccupationAffinity.affinity_le_norm_sq,
    ``QuantumNLS.FullOccupationAffinity.affinity_le_one,
    ``QuantumNLS.FullOccupationAffinity.overlapTerm,
    ``QuantumNLS.FullOccupationAffinity.norm_overlapTerm,
    ``QuantumNLS.FullOccupationAffinity.summable_overlapTerm,
    ``QuantumNLS.FullOccupationAffinity.overlap,
    ``QuantumNLS.FullOccupationAffinity.defect,
    ``QuantumNLS.FullOccupationAffinity.defectTerm,
    ``QuantumNLS.FullOccupationAffinity.summable_rotated,
    ``QuantumNLS.FullOccupationAffinity.summable_defectTerm,
    ``QuantumNLS.FullOccupationAffinity.defect_eq_tsum,
    ``QuantumNLS.FullOccupationAffinity.defectTerm_nonneg,
    ``QuantumNLS.FullOccupationAffinity.defect_nonneg,
    ``QuantumNLS.FullOccupationAffinity.transfer,
    ``QuantumNLS.FullOccupationAffinity.transfer_basis,
    ``QuantumNLS.FullOccupationAffinity.transfer_norm_le,
    ``QuantumNLS.FullOccupationAffinity.inner_transfer,
    ``QuantumNLS.FullOccupationAffinity.real_inner_eq_affinity_sub_defect,
    ``QuantumNLS.FullOccupationAffinity.physicalCoefficients,
    ``QuantumNLS.FullOccupationAffinity.physicalCoefficients_apply,
    ``QuantumNLS.FullOccupationAffinity.gaugeEdge,
    ``QuantumNLS.FullOccupationAffinity.transfer_identity,
    ``QuantumNLS.FullOccupationAffinity.selectedCoefficients,
    ``QuantumNLS.FullOccupationAffinity.selectedMeanFieldCoefficients]
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
  let mut todo := #[``QuantumNLS.FullOccupationAffinity.Phase,
    ``QuantumNLS.FullOccupationAffinity.UnitCoefficients,
    ``QuantumNLS.FullOccupationAffinity.sourceCoefficients,
    ``QuantumNLS.FullOccupationAffinity.targetCoefficients,
    ``QuantumNLS.FullOccupationAffinity.affinityTerm,
    ``QuantumNLS.FullOccupationAffinity.summable_affinityTerm,
    ``QuantumNLS.FullOccupationAffinity.affinity,
    ``QuantumNLS.FullOccupationAffinity.affinity_nonneg,
    ``QuantumNLS.FullOccupationAffinity.affinity_le_norm_sq,
    ``QuantumNLS.FullOccupationAffinity.affinity_le_one,
    ``QuantumNLS.FullOccupationAffinity.overlapTerm,
    ``QuantumNLS.FullOccupationAffinity.norm_overlapTerm,
    ``QuantumNLS.FullOccupationAffinity.summable_overlapTerm,
    ``QuantumNLS.FullOccupationAffinity.overlap,
    ``QuantumNLS.FullOccupationAffinity.defect,
    ``QuantumNLS.FullOccupationAffinity.defectTerm,
    ``QuantumNLS.FullOccupationAffinity.summable_rotated,
    ``QuantumNLS.FullOccupationAffinity.summable_defectTerm,
    ``QuantumNLS.FullOccupationAffinity.defect_eq_tsum,
    ``QuantumNLS.FullOccupationAffinity.defectTerm_nonneg,
    ``QuantumNLS.FullOccupationAffinity.defect_nonneg,
    ``QuantumNLS.FullOccupationAffinity.transfer,
    ``QuantumNLS.FullOccupationAffinity.transfer_basis,
    ``QuantumNLS.FullOccupationAffinity.transfer_norm_le,
    ``QuantumNLS.FullOccupationAffinity.inner_transfer,
    ``QuantumNLS.FullOccupationAffinity.real_inner_eq_affinity_sub_defect,
    ``QuantumNLS.FullOccupationAffinity.physicalCoefficients,
    ``QuantumNLS.FullOccupationAffinity.physicalCoefficients_apply,
    ``QuantumNLS.FullOccupationAffinity.gaugeEdge,
    ``QuantumNLS.FullOccupationAffinity.transfer_identity]
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
  Lean.logInfo m!"FullOccupationAffinity aggregate audit PASS: {seen.size} transitive constants. Generic declarations independent of EXT-001."
