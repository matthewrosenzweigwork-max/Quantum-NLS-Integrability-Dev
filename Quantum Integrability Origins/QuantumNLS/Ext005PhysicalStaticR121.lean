import QuantumNLS.Ext005SameComparisonR121
import QuantumNLS.Prop022CutoffCommutatorR119

/-! The actual quadratic form on every genuine number-moment form domain.
The comparison commutator is identified off the diagonal, with its full
operator-domain premises, before the two-sided bound is applied. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate LinearPMap
open ContinuousLinearMap
namespace QuantumNLS.Ext005PhysicalStaticR121
open BetheCoefficientTransform Ext025B3PhysicalSectors Ext005Moments
open Ext005MomentEnergyR108 Ext005MomentDomainR33b Ext005OperatorFormR113
open Ext005FormScaleR109 Ext005PhysicalNumberFormR114 Ext005PhysicalPairFormR114
open Ext005PhysicalHalfPairR114 Ext005PhysicalSymmetryR114 Ext005QuadraticEnergyR108
open Ext005AlgebraicFormR114 Ext005PairSector Ext005PairCommutatorR108
open Prop022PhysicalCommutatorR115
variable {L : ℝ} [Fact (0 < L)]

def firstDomainMap (j : ℕ) (hj : 1 ≤ j) :
    FormDomain (momentPositive (L := L) j) →ₗ[ℂ] momentDomain (L := L) 1 where
  toFun u := ⟨Ext005OperatorFormR113.inclusion (momentPositive j) u,
    domain_mono hj (inclusion_mem_root j u)⟩
  map_add' u v := Subtype.ext (map_add _ u v)
  map_smul' c u := Subtype.ext (map_smul _ c u)

lemma firstRoot_bound (j : ℕ) (hj : 1 ≤ j)
    (u : FormDomain (momentPositive (L := L) j)) :
    ‖momentRoot 1 (firstDomainMap j hj u)‖ ≤ ‖u‖ := by
  have he := energy_mono hj (inclusion_mem_root j u)
  change energy 1 (firstDomainMap j hj u).val ≤ _ at he
  rw [energy_eq_root 1 (firstDomainMap j hj u)] at he
  have hn := moment_form_norm_sq j u
  change ‖u‖ ^ 2 = energy j (Ext005OperatorFormR113.inclusion (momentPositive j) u) at hn
  rw [← hn] at he
  nlinarith [norm_nonneg u, norm_nonneg (momentRoot 1 (firstDomainMap j hj u))]

def firstRoot (j : ℕ) (hj : 1 ≤ j) :
    FormDomain (momentPositive (L := L) j) →L[ℂ] Fock L :=
  LinearMap.mkContinuous ((momentRoot 1).toFun.comp (firstDomainMap j hj)) 1
    (fun u => by
      change ‖momentRoot 1 (firstDomainMap j hj u)‖ ≤ 1 * ‖u‖
      rw [one_mul]
      exact firstRoot_bound j hj u)

lemma firstRoot_embedding (j : ℕ) (hj : 1 ≤ j)
    (u : FormDomain (momentPositive (L := L) j)) :
    embedding 1 (firstRoot j hj u) = Ext005OperatorFormR113.inclusion (momentPositive j) u :=
  embedding_root 1 (firstDomainMap j hj u)

/-- Literal number plus one-half pair form, with the completed-root bridge. -/
def physicalForm (j : ℕ) (hj : 1 ≤ j)
    (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) :
    RawForm (FormDomain (momentPositive (L := L) j)) where
  toFun u :=
    { toFun v := quadraticContinuous a b (firstRoot j hj u) (firstRoot j hj v)
      map_add' v w := by simp
      map_smul' c v := by simp }
  map_add' u v := by ext w; simp
  map_smul' c u := by ext v; simp

lemma physicalForm_symmetric (j : ℕ) (hj : 1 ≤ j)
    (a : HN L 1 →L[ℂ] HN L 1) (ha : a.adjoint = a) (b : HN L 2) :
    Hermitian (physicalForm j hj a b) :=
  fun u v => quadraticContinuous_symmetric a ha b (firstRoot j hj u) (firstRoot j hj v)

lemma physicalForm_bound (j : ℕ) (hj : 1 ≤ j)
    (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (u : FormDomain (momentPositive (L := L) j)) :
    ‖physicalForm j hj a b u u‖ ≤ (‖a‖ + ‖b‖) * ‖u‖ ^ 2 := by
  apply (quadraticContinuous_diagonal_bound a b (firstRoot j hj u)).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (firstRoot_bound j hj u) 2) (by positivity)

lemma physicalForm_diagonal (j : ℕ) (hj : 1 ≤ j)
    (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (u : FormDomain (momentPositive (L := L) j)) :
    physicalForm j hj a b u u = quadraticForm a b (firstDomainMap j hj u) :=
  quadraticContinuous_operatorDomain a b (firstDomainMap j hj u)

/-- The exact form commutator equals the proved physical sector commutator. -/
lemma physicalForm_commutator (j : ℕ) (hj : 1 ≤ j)
    (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (u : FormDomain (momentPositive (L := L) j))
    (hu : Ext005OperatorFormR113.inclusion (momentPositive j) u ∈ (momentPositive j).op.domain)
    (v : FormDomain (momentPositive (L := L) j))
    (hv : Ext005OperatorFormR113.inclusion (momentPositive j) v =
      (momentPositive j).op ⟨Ext005OperatorFormR113.inclusion (momentPositive j) u, hu⟩) :
    Complex.I * (physicalForm j hj a b v u - physicalForm j hj a b u v) =
      physicalCommutator j b (Ext005OperatorFormR113.inclusion (momentPositive j) u) := by
  let x := Ext005OperatorFormR113.inclusion (momentPositive j) u
  have hw (n : ℕ) : Ext005OperatorFormR113.inclusion (momentPositive j) v n =
      (momentWeight j n : ℂ) • x n := congrArg (fun z : Fock L => z n) hv
  have hn : numberContinuous a (firstRoot j hj v) (firstRoot j hj u) =
      numberContinuous a (firstRoot j hj u) (firstRoot j hj v) := by
    rw [numberContinuous_offDiagonal, numberContinuous_offDiagonal]
    apply tsum_congr
    intro n
    rw [firstRoot_embedding, firstRoot_embedding, hw,
      map_smul, inner_smul_right, inner_smul_left, Complex.conj_ofReal]
  have hp : annihilationForm b (firstRoot j hj u) (firstRoot j hj v) -
      annihilationForm b (firstRoot j hj v) (firstRoot j hj u) =
        ∑' n, differenceTerm j b x n := by
    change (∑' n, sectorTerm b (firstRoot j hj u) (firstRoot j hj v) n) -
      (∑' n, sectorTerm b (firstRoot j hj v) (firstRoot j hj u) n) = _
    rw [← (sectorTerm_summable b (firstRoot j hj u) (firstRoot j hj v)).tsum_sub
      (sectorTerm_summable b (firstRoot j hj v) (firstRoot j hj u))]
    apply tsum_congr
    intro n
    simp only [sectorTerm, firstRoot_embedding, hw, inner_smul_left,
      Complex.conj_ofReal, map_smul, inner_smul_right, differenceTerm,
      Complex.ofReal_sub, Nat.add_comm 2 n]
    ring
  rw [physicalCommutator_identity]
  change Complex.I * ((numberContinuous a (firstRoot j hj v) (firstRoot j hj u) +
    (1/2 : ℂ) * (annihilationForm b (firstRoot j hj v) (firstRoot j hj u) +
      starRingEnd ℂ (annihilationForm b (firstRoot j hj u) (firstRoot j hj v)))) -
    (numberContinuous a (firstRoot j hj u) (firstRoot j hj v) +
    (1/2 : ℂ) * (annihilationForm b (firstRoot j hj u) (firstRoot j hj v) +
      starRingEnd ℂ (annihilationForm b (firstRoot j hj v) (firstRoot j hj u))))) = _
  rw [hn]
  unfold diagonalCommutator
  rw [← hp]
  simp only [star_sub, starRingEnd_apply]
  ring

lemma physicalForm_commutator_bound (j : ℕ) (hj : 1 ≤ j)
    (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (u : FormDomain (momentPositive (L := L) j))
    (hu : Ext005OperatorFormR113.inclusion (momentPositive j) u ∈ (momentPositive j).op.domain)
    (v : FormDomain (momentPositive (L := L) j))
    (hv : Ext005OperatorFormR113.inclusion (momentPositive j) v =
      (momentPositive j).op ⟨Ext005OperatorFormR113.inclusion (momentPositive j) u, hu⟩) :
    |(Complex.I * (physicalForm j hj a b v u - physicalForm j hj a b u v)).re| ≤
      (differenceConstant j * ‖b‖) * ‖u‖ ^ 2 := by
  rw [physicalForm_commutator j hj a b u hu v hv]
  apply (Complex.abs_re_le_norm _).trans
  have hh := physicalCommutator_bound j hj b
    ⟨Ext005OperatorFormR113.inclusion (momentPositive j) u, inclusion_mem_root j u⟩
  have he := moment_form_norm_sq j u
  change ‖u‖ ^ 2 = energy j (Ext005OperatorFormR113.inclusion (momentPositive j) u) at he
  simpa only [← he] using hh

end QuantumNLS.Ext005PhysicalStaticR121
#print axioms QuantumNLS.Ext005PhysicalStaticR121.physicalForm_commutator_bound
#print axioms QuantumNLS.Ext005PhysicalStaticR121.physicalForm_diagonal

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PhysicalStaticR121." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PhysicalStaticR121." then
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
  Lean.logInfo m!"R121 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
