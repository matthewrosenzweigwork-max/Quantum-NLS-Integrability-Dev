import QuantumNLS.Ext005PhysicalHalfPairR114
import QuantumNLS.Ext005QuadraticEnergyR108

/-! Construct the actual number-preserving form in complete first-moment
coordinates, and assemble the literal full static quadratic form. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace Topology ComplexConjugate
open ContinuousLinearMap InnerProductSpace Set Filter MeasureTheory
namespace QuantumNLS.Ext005PhysicalNumberFormR114
open Ext005PhysicalPairFormR114 Ext005PhysicalHalfPairR114 Ext005ComplexRieszR113
open Ext005AntidualR113 Ext005PairSector Ext005Moments Ext005FormScaleR109
open Ext005QuadraticEnergyR108 Ext025B3PhysicalSectors BetheCoefficientTransform
variable {L : ℝ} [Fact (0 < L)]

def normalizedBlock (a : HN L 1 →L[ℂ] HN L 1) (n : ℕ) : HN L n →L[ℂ] HN L n :=
  ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) • numberBlock a n

lemma normalizedBlock_bound (a : HN L 1 →L[ℂ] HN L 1) (n : ℕ) (x : HN L n) :
    ‖normalizedBlock a n x‖ ≤ ‖a‖ * ‖x‖ := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hfrac : ((n : ℝ) + 1)⁻¹ * (n : ℝ) ≤ 1 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_le_one hn).mpr (by linarith)
  simp only [normalizedBlock, smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ ((n : ℝ) + 1)⁻¹ * (‖a‖ * (n : ℝ) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (numberBlock_bound a n x) (inv_nonneg.mpr hn.le)
    _ = (((n : ℝ) + 1)⁻¹ * (n : ℝ)) * (‖a‖ * ‖x‖) := by ring
    _ ≤ 1 * (‖a‖ * ‖x‖) := mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = _ := one_mul _

lemma numberImage_mem (a : HN L 1 →L[ℂ] HN L 1) (u : Fock L) :
    Memℓp (fun n => normalizedBlock a n (u n)) 2 := by
  apply ((lp.memℓp u).const_smul (‖a‖ : ℂ)).mono'
  intro n
  change ‖normalizedBlock a n (u n)‖ ≤ ‖(‖a‖ : ℂ) • u n‖
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
  exact normalizedBlock_bound a n (u n)

/-- Actual second-quantized number block in first-moment coordinates. -/
def numberCoordinates (a : HN L 1 →L[ℂ] HN L 1) : Fock L →L[ℂ] Fock L :=
  LinearMap.mkContinuous
    { toFun u := ⟨fun n => normalizedBlock a n (u n), numberImage_mem a u⟩
      map_add' u v := by
        apply Subtype.ext
        funext n
        exact map_add (normalizedBlock a n) (u n) (v n)
      map_smul' c u := by
        apply Subtype.ext
        funext n
        exact map_smul (normalizedBlock a n) c (u n) }
    ‖a‖ (by
      intro u
      calc
        _ ≤ ‖(‖a‖ : ℂ) • u‖ := by
          apply lp.norm_mono (by norm_num)
          intro n
          change ‖normalizedBlock a n (u n)‖ ≤ ‖(‖a‖ : ℂ) • u n‖
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
          exact normalizedBlock_bound a n (u n)
        _ = ‖a‖ * ‖u‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)])

def numberContinuous (a : HN L 1 →L[ℂ] HN L 1) : Form (Fock L) :=
  (innerSLFlip ℂ).comp (numberCoordinates a)

lemma numberContinuous_offDiagonal (a : HN L 1 →L[ℂ] HN L 1) (u v : Fock L) :
    numberContinuous a u v = ∑' n, ⟪embedding 1 v n, numberBlock a n (embedding 1 u n)⟫_ℂ := by
  change ⟪v, numberCoordinates a u⟫_ℂ = _
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  have hc : (Real.sqrt (momentWeight 1 n))⁻¹ * (Real.sqrt (momentWeight 1 n))⁻¹ =
      ((n : ℝ) + 1)⁻¹ := by
    rw [← sq, inv_pow, Real.sq_sqrt (momentWeight_nonneg 1 n)]
    simp only [momentWeight, pow_one]
  have hcC := congrArg (fun r : ℝ => (r : ℂ)) hc
  simp only [Complex.ofReal_mul] at hcC
  change ⟪v n, normalizedBlock a n (u n)⟫_ℂ = _
  simp only [normalizedBlock, smul_apply, inner_smul_right, embedding_apply,
    map_smul, inner_smul_left, Complex.conj_ofReal]
  rw [← mul_assoc, hcC]

lemma numberContinuous_diagonal (a : HN L 1 →L[ℂ] HN L 1) (u : Fock L) :
    numberContinuous a u u = numberForm a (embedding 1 u) :=
  numberContinuous_offDiagonal a u u

/-- Full static PROP-022 quadratic form, including the one-half pair term. -/
def quadraticContinuous (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) : Form (Fock L) :=
  numberContinuous a + halfPair b

lemma quadraticContinuous_diagonal (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2) (u : Fock L) :
    quadraticContinuous a b u u = quadraticForm a b ⟨embedding 1 u, embedding_mem 1 u⟩ := by
  change numberContinuous a u u + halfPair b u u = _
  rw [numberContinuous_diagonal, halfPair_diagonal]
  rfl

lemma quadraticContinuous_operatorDomain (a : HN L 1 →L[ℂ] HN L 1) (b : HN L 2)
    (x : momentDomain (L := L) 1) :
    quadraticContinuous a b (momentRoot 1 x) (momentRoot 1 x) = quadraticForm a b x := by
  rw [quadraticContinuous_diagonal]
  have hx : (⟨embedding 1 (momentRoot 1 x), embedding_mem 1 (momentRoot 1 x)⟩ :
      momentDomain (L := L) 1) = x := Subtype.ext (embedding_root 1 x)
  rw [hx]

end QuantumNLS.Ext005PhysicalNumberFormR114
#print axioms QuantumNLS.Ext005PhysicalNumberFormR114.numberContinuous_offDiagonal
#print axioms QuantumNLS.Ext005PhysicalNumberFormR114.quadraticContinuous_operatorDomain

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext005PhysicalNumberFormR114." ||
        n.toString.startsWith "_private.QuantumNLS.Ext005PhysicalNumberFormR114." then
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
