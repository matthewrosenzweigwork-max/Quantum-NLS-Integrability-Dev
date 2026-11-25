import QuantumNLS.BetheSpectralCharges

/-! DEF-025, definitions.tex:151, on the complete DEF-006 arrays and the
realized DEF-007 transform. A selection has only period and coupling
arguments. No target-retargeting theorem or equality with intrinsic
collision-positive normalization is assumed. -/
noncomputable section
open scoped BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.BetheOccupationGauge
open BetheLabels BetheCoefficientTransform PhysicalTensor BetheSpectralCharges
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- One phase for every complete array in EVERY number sector. -/
def Gauge : Type := ∀ N : ℕ, MArr N → {z : ℂ // ‖z‖ = 1}

/-- A once-for-all selection at fixed physical parameters. There are no
profile, test, action vector, chosen label or time arguments. -/
def UniversalSelection : Type := (L : ℝ) → 0 < L → (c : ℝ) → 0 < c → Gauge

def identityGauge : Gauge := fun _ _ => ⟨1, norm_one⟩

def identitySelection : UniversalSelection := fun _ _ _ _ => identityGauge

/-- Universal choices exist already at the level of this definition;
any subsequent target property is a separate theorem. -/
theorem selection_exists : Nonempty UniversalSelection := ⟨identitySelection⟩

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- Diagonal unitary on the entire occupation coefficient space. -/
def diagonal (g : Gauge) (N : ℕ) :
    lp (fun _ : MArr N => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : MArr N => ℂ) 2 :=
  phaseUnitary (fun m => (g N m).val) (fun m => (g N m).property)

theorem diagonal_apply (g : Gauge) (v : lp (fun _ : MArr N => ℂ) 2) (m : MArr N) :
    diagonal g N v m = (g N m).val * v m := rfl

/-- The coefficient transform of vectors rephased by g uses conjugate g,
since the inner product is conjugate linear in its first argument. -/
def gaugedTransform (b : BetheBasis L N) (g : Gauge) :
    HN L N ≃ₗᵢ[ℂ] lp (fun _ : MArr N => ℂ) 2 :=
  (coefficientTransform b).trans (diagonal g N).symm

def gaugedBasis (b : BetheBasis L N) (g : Gauge) : BetheBasis L N :=
  HilbertBasis.ofRepr (gaugedTransform b g)

theorem gaugedTransform_apply (b : BetheBasis L N) (g : Gauge) (ψ : HN L N) (m : MArr N) :
    gaugedTransform b g ψ m = (starRingEnd ℂ) (g N m).val * ⟪b m, ψ⟫_ℂ := by
  change (starRingEnd ℂ) (g N m).val * b.repr ψ m = _
  rw [HilbertBasis.repr_apply_apply]

/-- The new complete normalized basis consists literally of g(m) Ψ_m. -/
theorem gaugedBasis_apply (b : BetheBasis L N) (g : Gauge) (m : MArr N) :
    gaugedBasis b g m = (g N m).val • b m := by
  apply (gaugedTransform b g).injective
  change (gaugedBasis b g).repr (gaugedBasis b g m) = _
  rw [HilbertBasis.repr_self]
  ext k
  rw [gaugedTransform_apply, inner_smul_right]
  by_cases h : k = m
  · subst k
    have hi : ⟪b m, b m⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
      norm_num
    simp only [lp.single_apply, Pi.single_eq_same, hi, mul_one]
    rw [Complex.conj_mul', (g N m).property]
    norm_num
  · rw [b.orthonormal.inner_eq_zero h]
    simp [lp.single_apply, h]

/-- Exactly the frozen DEF-007 transform instantiated with the new basis. -/
theorem coefficientTransform_gaugedBasis (b : BetheBasis L N) (g : Gauge) :
    coefficientTransform (gaugedBasis b g) = gaugedTransform b g := rfl

/-- Rephasing in the realized normalized occupation basis of Sym^N ell²(Z). -/
theorem fockTransform_gauged (b : BetheBasis L N) (g : Gauge) (ψ : HN L N) (m : MArr N) :
    ⟪OccupationUnitary.occupationVector (marrArr N m),
      (fockTransform (gaugedBasis b g) ψ : OccupationUnitary.Tensor N)⟫_ℂ =
        (starRingEnd ℂ) (g N m).val * ⟪b m, ψ⟫_ℂ := by
  rw [fockTransform_coord', gaugedBasis_apply, inner_smul_left]

/-- Born weights do not change under rephasing, pointwise on the FULL array set. -/
theorem bornLaw_invariant (b : BetheBasis L N) (g : Gauge) (u : L2T L) (m : MArr N) :
    bornLaw (gaugedBasis b g) u m = bornLaw b u m := by
  simp only [bornLaw, gaugedBasis_apply, inner_smul_left, norm_mul, Complex.norm_conj,
    (g N m).property, one_mul]

/-- All maximal spectral charge domains are invariant under occupation gauge. -/
theorem domain_invariant (b : BetheBasis L N) (g : Gauge) (ev : MArr N → ℝ) (ψ : HN L N) :
    ψ ∈ domain (gaugedBasis b g) ev ↔ ψ ∈ domain b ev := by
  rw [mem_domain, mem_domain]
  simp only [gaugedBasis_apply, inner_smul_left, norm_mul, Complex.norm_conj,
    (g N _).property, one_mul]

/-- Rephasing changes neither a spectral charge nor its maximal domain. -/
theorem multiplier_invariant (b : BetheBasis L N) (g : Gauge) (ev : MArr N → ℝ) :
    multiplier (gaugedBasis b g) ev = multiplier b ev := by
  apply LinearPMap.ext (Submodule.ext (fun ψ => domain_invariant b g ev ψ))
  intro ψ hnew hold
  apply b.repr.injective
  ext m
  simp only [HilbertBasis.repr_apply_apply]
  have hn : (starRingEnd ℂ) (g N m).val ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [Complex.norm_conj, (g N m).property]
    norm_num
  apply mul_left_cancel₀ hn
  have hcoord := multiplier_coord (gaugedBasis b g) ev ⟨ψ,hnew⟩ m
  rw [gaugedBasis_apply, inner_smul_left, inner_smul_left] at hcoord
  calc
    _ = (ev m : ℂ) * ((starRingEnd ℂ) (g N m).val * ⟪b m, ψ⟫_ℂ) := hcoord
    _ = _ := by rw [multiplier_coord]; ring

/-- Vacuum is the canonical realized zero-particle occupation basis;
N=1 uses BOP1 directly and N>=2 is exactly the frozen interacting BCB1 basis. -/
def sectorBasis (hcont : BetheConditionalBasis.AbstractContinuity) (L : ℝ) [Fact (0 < L)]
    (c : ℝ) (hc : 0 < c) : (N : ℕ) → BetheBasis L N
  | 0 => BetheSpectralCharges.sectorBasis hcont L c hc 0
  | 1 => BetheSpectralCharges.sectorBasis hcont L c hc 1
  | n+2 => BetheSpectralCharges.sectorBasis hcont L c hc (n+2)

/-- The chosen family is instantiated once at L,c; every complete label
in each sector then receives the phase prescribed by that same family. -/
def selectedBasis (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) (N : ℕ) : BetheBasis L N :=
  gaugedBasis (sectorBasis hcont L c hc N) (s L Fact.out c hc)

theorem selectedBasis_apply (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) (N : ℕ) (m : MArr N) :
    selectedBasis hcont s L c hc N m =
      (s L Fact.out c hc N m).val • sectorBasis hcont L c hc N m :=
  gaugedBasis_apply _ _ _

/-- Literal selected DEF-007 coefficient transform. -/
def selectedTransform (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (c : ℝ) (hc : 0 < c) (N : ℕ) :
    HN L N ≃ₗᵢ[ℂ] lp (fun _ : MArr N => ℂ) 2 :=
  coefficientTransform (selectedBasis hcont s L c hc N)

/-- Fixed physical kappa selects the SAME whole-sector phase family before
N, while the Bethe basis uses the prescribed coupling c_N=kappa/N. -/
def selectedMeanFieldBasis (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) : BetheBasis L N :=
  gaugedBasis (BetheConditionalBasis.meanField_physicalBasis hcont L N hN hκ) (s L Fact.out κ hκ)

def selectedMeanFieldTransform (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) :
    HN L N ≃ₗᵢ[ℂ] lp (fun _ : MArr N => ℂ) 2 :=
  coefficientTransform (selectedMeanFieldBasis hcont s L κ hκ N hN)

/-- The definition permits choices different from intrinsic normalization. -/
def negativeGauge : Gauge := fun _ _ => ⟨-1, by simp⟩

theorem negative_phase_ne_identity (N : ℕ) (m : MArr N) :
    (negativeGauge N m).val ≠ (identityGauge N m).val := by
  change (-1 : ℂ) ≠ 1
  norm_num

end QuantumNLS.BetheOccupationGauge

#print axioms QuantumNLS.BetheOccupationGauge.Gauge
#print axioms QuantumNLS.BetheOccupationGauge.UniversalSelection
#print axioms QuantumNLS.BetheOccupationGauge.identityGauge
#print axioms QuantumNLS.BetheOccupationGauge.identitySelection
#print axioms QuantumNLS.BetheOccupationGauge.selection_exists
#print axioms QuantumNLS.BetheOccupationGauge.diagonal
#print axioms QuantumNLS.BetheOccupationGauge.diagonal_apply
#print axioms QuantumNLS.BetheOccupationGauge.gaugedTransform
#print axioms QuantumNLS.BetheOccupationGauge.gaugedBasis
#print axioms QuantumNLS.BetheOccupationGauge.gaugedTransform_apply
#print axioms QuantumNLS.BetheOccupationGauge.gaugedBasis_apply
#print axioms QuantumNLS.BetheOccupationGauge.coefficientTransform_gaugedBasis
#print axioms QuantumNLS.BetheOccupationGauge.fockTransform_gauged
#print axioms QuantumNLS.BetheOccupationGauge.bornLaw_invariant
#print axioms QuantumNLS.BetheOccupationGauge.domain_invariant
#print axioms QuantumNLS.BetheOccupationGauge.multiplier_invariant
#print axioms QuantumNLS.BetheOccupationGauge.sectorBasis
#print axioms QuantumNLS.BetheOccupationGauge.selectedBasis
#print axioms QuantumNLS.BetheOccupationGauge.selectedBasis_apply
#print axioms QuantumNLS.BetheOccupationGauge.selectedTransform
#print axioms QuantumNLS.BetheOccupationGauge.selectedMeanFieldBasis
#print axioms QuantumNLS.BetheOccupationGauge.selectedMeanFieldTransform
#print axioms QuantumNLS.BetheOccupationGauge.negativeGauge
#print axioms QuantumNLS.BetheOccupationGauge.negative_phase_ne_identity

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheOccupationGauge.Gauge,
    ``QuantumNLS.BetheOccupationGauge.UniversalSelection,
    ``QuantumNLS.BetheOccupationGauge.identityGauge,
    ``QuantumNLS.BetheOccupationGauge.identitySelection,
    ``QuantumNLS.BetheOccupationGauge.selection_exists,
    ``QuantumNLS.BetheOccupationGauge.diagonal,
    ``QuantumNLS.BetheOccupationGauge.diagonal_apply,
    ``QuantumNLS.BetheOccupationGauge.gaugedTransform,
    ``QuantumNLS.BetheOccupationGauge.gaugedBasis,
    ``QuantumNLS.BetheOccupationGauge.gaugedTransform_apply,
    ``QuantumNLS.BetheOccupationGauge.gaugedBasis_apply,
    ``QuantumNLS.BetheOccupationGauge.coefficientTransform_gaugedBasis,
    ``QuantumNLS.BetheOccupationGauge.fockTransform_gauged,
    ``QuantumNLS.BetheOccupationGauge.bornLaw_invariant,
    ``QuantumNLS.BetheOccupationGauge.domain_invariant,
    ``QuantumNLS.BetheOccupationGauge.multiplier_invariant,
    ``QuantumNLS.BetheOccupationGauge.sectorBasis,
    ``QuantumNLS.BetheOccupationGauge.selectedBasis,
    ``QuantumNLS.BetheOccupationGauge.selectedBasis_apply,
    ``QuantumNLS.BetheOccupationGauge.selectedTransform,
    ``QuantumNLS.BetheOccupationGauge.selectedMeanFieldBasis,
    ``QuantumNLS.BetheOccupationGauge.selectedMeanFieldTransform,
    ``QuantumNLS.BetheOccupationGauge.negativeGauge,
    ``QuantumNLS.BetheOccupationGauge.negative_phase_ne_identity]
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
            throwError "Occupation gauge nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  let mut todo := #[``QuantumNLS.BetheOccupationGauge.Gauge,
    ``QuantumNLS.BetheOccupationGauge.UniversalSelection,
    ``QuantumNLS.BetheOccupationGauge.identityGauge,
    ``QuantumNLS.BetheOccupationGauge.identitySelection,
    ``QuantumNLS.BetheOccupationGauge.selection_exists,
    ``QuantumNLS.BetheOccupationGauge.diagonal,
    ``QuantumNLS.BetheOccupationGauge.diagonal_apply,
    ``QuantumNLS.BetheOccupationGauge.gaugedTransform,
    ``QuantumNLS.BetheOccupationGauge.gaugedBasis,
    ``QuantumNLS.BetheOccupationGauge.gaugedTransform_apply,
    ``QuantumNLS.BetheOccupationGauge.gaugedBasis_apply,
    ``QuantumNLS.BetheOccupationGauge.coefficientTransform_gaugedBasis,
    ``QuantumNLS.BetheOccupationGauge.fockTransform_gauged,
    ``QuantumNLS.BetheOccupationGauge.bornLaw_invariant,
    ``QuantumNLS.BetheOccupationGauge.domain_invariant,
    ``QuantumNLS.BetheOccupationGauge.multiplier_invariant,
    ``QuantumNLS.BetheOccupationGauge.negativeGauge,
    ``QuantumNLS.BetheOccupationGauge.negative_phase_ne_identity]
  let mut checked : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless checked.contains n do
      checked := checked.insert n
      if n == ``QuantumNLS.BetheConditionalBasis.AbstractContinuity then
        throwError "Generic definition reached EXT-001 premise: {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
  Lean.logInfo m!"Occupation gauge aggregate audit PASS: {seen.size} transitive constants. Generic definitions independent of EXT-001; actual BCB1 instantiation carries its explicit Prop premise."
