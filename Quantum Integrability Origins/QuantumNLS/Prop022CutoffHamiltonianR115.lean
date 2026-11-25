import QuantumNLS.Prop022FactorialCoefficientsR115
import QuantumNLS.Ext005FormCutoffR109

/-! Actual bounded finite-sector regularizations of the physical quadratic
Hamiltonian, with exact form pairing and cutoff-uniform form estimates.
This constructs generators, not their nonautonomous evolutions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace ComplexConjugate Topology
open ContinuousLinearMap
namespace QuantumNLS.Prop022CutoffHamiltonianR115
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005FormCutoffR109 Ext005ComplexRieszR113 Ext005PhysicalNumberFormR114
open Ext005PhysicalSymmetryR114 Ext005QuadraticEnergyR108 Ext005MomentEnergyR108
open Prop022FactorialCoefficientsR115 Prop022FactorialMajorantR115
variable {L : ℝ} [Fact (0 < L)]

/-- Compression of the completed physical form by the actual number cutoff. -/
def cutoffHamiltonian (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (N : ℕ) :
    Fock L →L[ℂ] Fock L :=
  (rootCutoff 1 N).adjoint ∘L formOperator (quadraticContinuous a b) ∘L rootCutoff 1 N

lemma cutoff_pair (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (N : ℕ) (x y : Fock L) :
    ⟪x, cutoffHamiltonian a b N y⟫_ℂ =
      quadraticContinuous a b (rootCutoff 1 N y) (rootCutoff 1 N x) := by
  change ⟪x, (rootCutoff 1 N).adjoint
    (formOperator (quadraticContinuous a b) (rootCutoff 1 N y))⟫_ℂ = _
  rw [adjoint_inner_right, form_pair]

lemma cutoff_symmetric (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a)
    (b : HN L 2) (N : ℕ) : (cutoffHamiltonian a b N).IsSymmetric := by
  intro x y
  change ⟪cutoffHamiltonian a b N x, y⟫_ℂ = ⟪x, cutoffHamiltonian a b N y⟫_ℂ
  rw [← inner_conj_symm]
  calc
    _ = starRingEnd ℂ (quadraticContinuous a b (rootCutoff 1 N x) (rootCutoff 1 N y)) :=
      congrArg (starRingEnd ℂ) (cutoff_pair a b N y x)
    _ = quadraticContinuous a b (rootCutoff 1 N y) (rootCutoff 1 N x) :=
      quadraticContinuous_symmetric a ha b _ _
    _ = _ := (cutoff_pair a b N x y).symm

lemma cutoff_adjoint (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a)
    (b : HN L 2) (N : ℕ) :
    (cutoffHamiltonian a b N).adjoint = cutoffHamiltonian a b N := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [adjoint_inner_right]
  exact cutoff_symmetric a ha b N y x

lemma cutoff_diagonal (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (N : ℕ)
    (x : momentDomain (L := L) 1) :
    ⟪x.val, cutoffHamiltonian a b N x.val⟫_ℂ =
      quadraticForm a b ⟨cutoff N x.val, cutoff_mem 1 N x.val⟩ := by
  rw [cutoff_pair]
  simp only [rootCutoff_eq 1 N x, ← root_cutoff 1 N x]
  exact quadraticContinuous_operatorDomain a b ⟨cutoff N x.val, cutoff_mem 1 N x.val⟩

/-- Form domination is uniform in the cutoff. -/
lemma cutoff_form_bound (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (N : ℕ)
    (x : momentDomain (L := L) 1) :
    ‖⟪x.val, cutoffHamiltonian a b N x.val⟫_ℂ‖ ≤ (‖a‖ + ‖b‖) * energy 1 x.val := by
  rw [cutoff_diagonal]
  exact (quadraticForm_bound a b ⟨cutoff N x.val, cutoff_mem 1 N x.val⟩).trans
    (mul_le_mul_of_nonneg_left (cutoff_energy_le 1 N x) (by positivity))

lemma factorial_cutoff_bound (B : ∀ m, HN L m →L[ℂ] HN L m)
    (M A : ℝ) (hA : 0 ≤ A) (hB : FactorialBound B M A)
    (u : PhysicalTensor.L2T L) (hu : ‖u‖ = 1) (N : ℕ)
    (x : momentDomain (L := L) 1) :
    ‖⟪x.val, cutoffHamiltonian (numberCoefficient B u) (pairCoefficient B u) N x.val⟫_ℂ‖ ≤
      M * (numberMajorant A + pairMajorant A) * energy 1 x.val := by
  have ha := numberCoefficient_bound B M A hA hB u hu
  have hb := pairCoefficient_bound B M A hA hB u hu
  apply (cutoff_form_bound _ _ N x).trans
  have hh := mul_le_mul_of_nonneg_right (add_le_add ha hb) (energy_nonneg 1 x.val)
  nlinarith only [hh]

/-- The actual cutoff form pairings converge on the common first-moment domain. -/
lemma cutoff_pair_tendsto (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (x y : momentDomain (L := L) 1) :
    Filter.Tendsto (fun N => ⟪y.val, cutoffHamiltonian a b N x.val⟫_ℂ)
      Filter.atTop (𝓝 (quadraticContinuous a b (momentRoot 1 x) (momentRoot 1 y))) := by
  have hx := ((formOperator (quadraticContinuous a b)).continuous.tendsto (momentRoot 1 x)).comp
    (cutoff_tendsto (momentRoot 1 x))
  have hy := cutoff_tendsto (momentRoot 1 y)
  have h := Filter.Tendsto.inner (𝕜 := ℂ) hy hx
  simpa only [Function.comp_apply, cutoff_pair, rootCutoff_eq 1 _ x, rootCutoff_eq 1 _ y, form_pair] using h

end QuantumNLS.Prop022CutoffHamiltonianR115
#print axioms QuantumNLS.Prop022CutoffHamiltonianR115.cutoff_pair
#print axioms QuantumNLS.Prop022CutoffHamiltonianR115.cutoff_pair_tendsto
#print axioms QuantumNLS.Prop022CutoffHamiltonianR115.cutoff_symmetric
#print axioms QuantumNLS.Prop022CutoffHamiltonianR115.cutoff_adjoint
#print axioms QuantumNLS.Prop022CutoffHamiltonianR115.factorial_cutoff_bound

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop022CutoffHamiltonianR115." ||
        n.toString.startsWith "_private.QuantumNLS.Prop022CutoffHamiltonianR115." then
      pending := pending.push n
  let roots := pending.size
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"R115 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
