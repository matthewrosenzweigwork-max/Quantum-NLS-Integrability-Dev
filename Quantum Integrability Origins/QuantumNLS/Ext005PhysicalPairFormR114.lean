import QuantumNLS.Ext005AlgebraicFormR114
import QuantumNLS.Ext005FormScaleR109

/-! An actual continuous off-diagonal physical pair form, constructed from
the normalized annihilation/creation sector blocks. This is a static
construction; neither a Hessian identification nor evolution is presumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005PhysicalPairFormR114
open Ext005AlgebraicFormR114 Ext005ComplexRieszR113 Ext005PairSector
open Ext005Moments Ext005FormScaleR109 Ext005MomentEnergyR108
open Ext025B3PhysicalSectors BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]

/-- Matrix element of the literal normalized physical annihilation block,
in the complete first-moment coordinates. -/
def sectorTerm (b : HN L 2) (u v : Fock L) (n : ℕ) : ℂ :=
  ⟪embedding 1 v n, annihilation b n (embedding 1 u (2 + n))⟫_ℂ

lemma sectorTerm_summable (b : HN L 2) (u v : Fock L) :
    Summable (sectorTerm b u v) := by
  let x := embedding (L := L) 1 u
  let y := embedding (L := L) 1 v
  let qx := fun n => momentWeight 1 n * ‖x n‖ ^ 2
  let qy := fun n => momentWeight 1 n * ‖y n‖ ^ 2
  have hx : Summable qx := (momentDomain_iff 1 x).mp (embedding_mem 1 u)
  have hy : Summable qy := (momentDomain_iff 1 y).mp (embedding_mem 1 v)
  have hs : Summable (fun n => ‖b‖ * ((qy n + qx (n + 2)) / 2)) :=
    (hy.add ((summable_nat_add_iff 2).mpr hx)).div_const 2 |>.mul_left ‖b‖
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hs
  intro n
  have hp := Ext005PairBounds.pair_sector n ‖y n‖ ‖x (n + 2)‖
  have hb := annihilation_bound b n (x (2 + n))
  have hn : (n : ℝ) + 2 ≤ (n + 2 : ℕ) + 1 := by push_cast; linarith
  have hq : (((n : ℝ) + 1) * ‖y n‖ ^ 2 + ((n : ℝ) + 2) * ‖x (n + 2)‖ ^ 2) / 2 ≤
      (qy n + qx (n + 2)) / 2 := by
    dsimp [qx, qy, momentWeight]
    simp only [pow_one]
    push_cast
    nlinarith [sq_nonneg ‖x (n + 2)‖]
  calc
    ‖sectorTerm b u v n‖ ≤ ‖y n‖ * ‖annihilation b n (x (2 + n))‖ := norm_inner_le_norm _ _
    _ ≤ ‖y n‖ * (‖b‖ * Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖x (2 + n)‖) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖b‖ * (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖y n‖ * ‖x (n + 2)‖) := by
      rw [Nat.add_comm 2 n]; ring
    _ ≤ ‖b‖ * ((qy n + qx (n + 2)) / 2) :=
      mul_le_mul_of_nonneg_left (hp.trans hq) (norm_nonneg _)

/-- The algebraic annihilation form, without continuity as an input. -/
def annihilationForm (b : HN L 2) : RawForm (Fock L) where
  toFun u :=
    { toFun v := ∑' n, sectorTerm b u v n
      map_add' v w := by
        have he : sectorTerm b u (v + w) = fun n => sectorTerm b u v n + sectorTerm b u w n := by
          funext n
          simp only [sectorTerm, map_add, lp.coeFn_add, Pi.add_apply, inner_add_left]
        rw [he, (sectorTerm_summable b u v).tsum_add (sectorTerm_summable b u w)]
      map_smul' c v := by
        have he : sectorTerm b u (c • v) = fun n => starRingEnd ℂ c * sectorTerm b u v n := by
          funext n
          simp only [sectorTerm, map_smul, lp.coeFn_smul, Pi.smul_apply, inner_smul_left]
        rw [he, tsum_mul_left]
        rfl }
  map_add' u w := by
    ext v
    have he : sectorTerm b (u + w) v = fun n => sectorTerm b u v n + sectorTerm b w v n := by
      funext n
      simp only [sectorTerm, map_add, lp.coeFn_add, Pi.add_apply, inner_add_right]
    change (∑' n, sectorTerm b (u + w) v n) =
      (∑' n, sectorTerm b u v n) + (∑' n, sectorTerm b w v n)
    rw [he, (sectorTerm_summable b u v).tsum_add (sectorTerm_summable b w v)]
  map_smul' c u := by
    ext v
    have he : sectorTerm b (c • u) v = fun n => c * sectorTerm b u v n := by
      funext n
      simp only [sectorTerm, map_smul, lp.coeFn_smul, Pi.smul_apply, inner_smul_right]
    change (∑' n, sectorTerm b (c • u) v n) = c * (∑' n, sectorTerm b u v n)
    rw [he, tsum_mul_left]

/-- The algebraic adjoint form; its transpose is complex conjugated. -/
def adjointForm (f : RawForm (Fock L)) : RawForm (Fock L) where
  toFun u :=
    { toFun v := starRingEnd ℂ (f v u)
      map_add' v w := by simp
      map_smul' c v := by simp }
  map_add' u w := by ext v; simp
  map_smul' c u := by ext v; simp

/-- Annihilation plus its actual adjoint creation form. -/
def pairRaw (b : HN L 2) : RawForm (Fock L) := annihilationForm b + adjointForm (annihilationForm b)

lemma pairRaw_symmetric (b : HN L 2) : Hermitian (pairRaw b) := by
  intro u v
  change starRingEnd ℂ (annihilationForm b u v + starRingEnd ℂ (annihilationForm b v u)) =
    annihilationForm b v u + starRingEnd ℂ (annihilationForm b u v)
  simp [add_comm]

lemma pairRaw_diagonal (b : HN L 2) (u : Fock L) :
    pairRaw b u u = pairHamiltonian b ⟨embedding 1 u, embedding_mem 1 u⟩ := rfl

lemma pairRaw_diagonal_bound (b : HN L 2) (u : Fock L) :
    |(pairRaw b u u).re| ≤ (2 * ‖b‖) * ‖u‖ ^ 2 := by
  apply (Complex.abs_re_le_norm _).trans
  rw [pairRaw_diagonal]
  have hb := pairHamiltonian_bound b ⟨embedding 1 u, embedding_mem 1 u⟩
  exact hb.trans_eq (congrArg (fun z : Fock L => 2 * ‖b‖ * ‖z‖ ^ 2) (root_embedding 1 u))

/-- Continuous full pair form in the first-moment completion. -/
def pairContinuous (b : HN L 2) : Form (Fock L) :=
  continuousForm (pairRaw b) (2 * ‖b‖) (by positivity) (pairRaw_symmetric b) (pairRaw_diagonal_bound b)

lemma pairContinuous_diagonal (b : HN L 2) (u : Fock L) :
    pairContinuous b u u = pairHamiltonian b ⟨embedding 1 u, embedding_mem 1 u⟩ := rfl

/-- Exact creation/annihilation interpretation off the diagonal. -/
lemma pairContinuous_offDiagonal (b : HN L 2) (u v : Fock L) :
    pairContinuous b u v = (∑' n, sectorTerm b u v n) +
      ∑' n, ⟪embedding 1 v (2 + n), creation b n (embedding 1 u n)⟫_ℂ := by
  change (∑' n, sectorTerm b u v n) + starRingEnd ℂ (∑' n, sectorTerm b v u n) = _
  congr 1
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  change starRingEnd ℂ ⟪embedding 1 u n, annihilation b n (embedding 1 v (2 + n))⟫_ℂ = _
  rw [inner_conj_symm]
  exact (ContinuousLinearMap.adjoint_inner_right (annihilation b n)
    (embedding 1 v (2 + n)) (embedding 1 u n)).symm

end QuantumNLS.Ext005PhysicalPairFormR114
#print axioms QuantumNLS.Ext005PhysicalPairFormR114.pairContinuous_diagonal
#print axioms QuantumNLS.Ext005PhysicalPairFormR114.pairContinuous_offDiagonal

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PhysicalPairFormR114." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PhysicalPairFormR114." then
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
  Lean.logInfo m!"R114 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
