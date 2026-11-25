import QuantumNLS.Ext006NumberPhase

/-! The exponential-to-polynomial step of PROP-023 on the actual completed
physical Fock space. In particular finiteness of the polynomial spectral
series implies membership in the actual maximal multiplier domain. These are
analytic implication lemmas, not a proof of the quasifree exponential law. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped ENNReal
namespace QuantumNLS.Prop023SpectralMoments
open Ext006NumberPhase Ext025B3PhysicalSectors BetheCoefficientTransform

lemma pointwise_polynomial_bound (Q : ℝ) (hQ : 1 ≤ Q) (j : ℕ) (hj : 1 ≤ j)
    (t : ℝ) (ht : 0 ≤ t) :
    (t+j)^j ≤ (16*Q*j)^j * Real.exp (t/(16*Q)) := by
  have hQ0 : 0 < Q := by linarith
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  let C : ℝ := 16*Q*j
  have hC : 0 < C := by dsimp [C]; positivity
  let y : ℝ := (t+j)/C
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hb : y ≤ Real.exp (y-1) := by
    have := Real.add_one_le_exp (y-1)
    linarith
  have hp := pow_le_pow_left₀ hy hb j
  have harg : (j : ℝ)*(y-1) ≤ t/(16*Q) := by
    dsimp [y, C]
    have he : (j : ℝ)*((t+j)/(16*Q*j)-1) = t/(16*Q) + j/(16*Q)-j := by
      field_simp
    rw [he]
    have hd : (j : ℝ)/(16*Q) ≤ j := (div_le_iff₀ (by positivity)).2 (by nlinarith)
    linarith
  have he : C^j * y^j = (t+j)^j := by
    rw [← mul_pow]
    dsimp [y]
    rw [mul_div_cancel₀ _ hC.ne']
  calc
    (t+j)^j = C^j * y^j := he.symm
    _ ≤ C^j * (Real.exp (y-1))^j := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = C^j * Real.exp ((j : ℝ)*(y-1)) := by rw [Real.exp_nat_mul]
    _ ≤ (16*Q*j)^j * Real.exp (t/(16*Q)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)

lemma exp_quarter_le_two : Real.exp (1/4 : ℝ) ≤ 2 := by
  have h := Real.exp_le_two_add_div_two_sub (x := (1/4 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  linarith

variable {L : ℝ} [Fact (0 < L)]

/-- The exact second spectral moment bound follows from the first one;
no polynomial-moment or domain conclusion is supplied as a premise. -/
theorem polynomial_of_exponential (x : Fock L) (Q : ℝ) (hQ : 1 ≤ Q)
    (hExp : exponentialMoment Q x ≤ ENNReal.ofReal (Real.exp (1/4 : ℝ)))
    (j : ℕ) (hj : 1 ≤ j) :
    polynomialMoment j x ≤ ENNReal.ofReal ((32*Q*j)^j) := by
  have hQ0 : 0 < Q := by linarith
  have hC : 0 ≤ (16*Q*j)^j := by positivity
  have htwo : Real.exp (1/4 : ℝ) ≤ (2 : ℝ)^j := by
    apply exp_quarter_le_two.trans
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hj
  calc
    polynomialMoment j x ≤ ENNReal.ofReal ((16*Q*j)^j) * exponentialMoment Q x := by
      unfold polynomialMoment exponentialMoment numberExpectation
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← mul_assoc, ← ENNReal.ofReal_mul hC]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        (pointwise_polynomial_bound Q hQ j hj n (Nat.cast_nonneg n))) le_rfl
    _ ≤ ENNReal.ofReal ((16*Q*j)^j) * ENNReal.ofReal (Real.exp (1/4 : ℝ)) :=
      mul_le_mul' le_rfl hExp
    _ ≤ ENNReal.ofReal ((16*Q*j)^j) * ENNReal.ofReal ((2 : ℝ)^j) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal htwo)
    _ = ENNReal.ofReal ((32*Q*j)^j) := by
      rw [← ENNReal.ofReal_mul hC, ← mul_pow]
      congr 2
      ring

/-- Exact squared sector norm of the literal (N+j)^(j/2) multiplier. -/
lemma root_sector_norm_sq (x : Fock L) (j n : ℕ) :
    ‖polynomialRootFamily (L := L) j n (x n)‖^2 =
      ((n : ℝ)+j)^j * ‖x n‖^2 := by
  have hb : 0 ≤ (n : ℝ)+j := by positivity
  have hp : (Real.rpow ((n : ℝ)+j) ((j : ℝ)/2))^2 = ((n : ℝ)+j)^j := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hb]
    simp only [Nat.cast_ofNat, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      Real.rpow_natCast]
  change ‖((Real.rpow ((n : ℝ)+j) ((j : ℝ)/2) : ℝ) : ℂ) • x n‖^2 = _
  simp only [Real.rpow_eq_pow] at hp ⊢
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hb _), mul_pow, hp]

/-- Finiteness of the spectral series gives the genuine maximal operator
 domain. There is no boundedness assumption on the full number multiplier. -/
theorem mem_polynomialRoot_of_finite (x : Fock L) (j : ℕ)
    (hfin : polynomialMoment j x ≠ ⊤) : x ∈ (polynomialRoot (L := L) j).domain := by
  change Memℓp (fun n => polynomialRootFamily j n (x n)) 2
  apply memℓp_gen
  have he : (∑' n, ENNReal.ofReal (‖polynomialRootFamily j n (x n)‖^2)) =
      polynomialMoment j x := by
    unfold polynomialMoment numberExpectation
    apply tsum_congr
    intro n
    rw [root_sector_norm_sq, ENNReal.ofReal_mul (by positivity)]
  have hs := ENNReal.summable_toReal (he ▸ hfin)
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofNat,
    Real.rpow_two] using hs

lemma root_apply (j : ℕ) (x : (polynomialRoot (L := L) j).domain) (n : ℕ) :
    polynomialRoot j x n = polynomialRootFamily j n (x.val n) := rfl

/-- The spectral definition and actual operator norm agree exactly. -/
theorem root_norm_sq (j : ℕ) (x : (polynomialRoot (L := L) j).domain) :
    ENNReal.ofReal (‖polynomialRoot j x‖^2) = polynomialMoment j x.val := by
  have hs := lp.hasSum_norm (E := fun n => HN L n) (p := 2) (by norm_num)
    (polynomialRoot j x)
  have he : ‖polynomialRoot j x‖^2 =
      ∑' n, ‖polynomialRootFamily j n (x.val n)‖^2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, root_apply] using hs.tsum_eq.symm
  rw [he, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)]
  · unfold polynomialMoment numberExpectation
    apply tsum_congr
    intro n
    rw [root_sector_norm_sq, ENNReal.ofReal_mul (by positivity)]
  · simpa only [ENNReal.toReal_ofNat, Real.rpow_two, root_apply] using hs.summable

/-- The report's norm bound and domain membership, on the physical carrier,
follow from its exponential bound with the precise constants 16 and 32. -/
theorem norm_of_exponential (x : Fock L) (Q : ℝ) (hQ : 1 ≤ Q)
    (hExp : exponentialMoment Q x ≤ ENNReal.ofReal (Real.exp (1/4 : ℝ)))
    (j : ℕ) (hj : 1 ≤ j) :
    ∃ hx : x ∈ (polynomialRoot (L := L) j).domain,
      ‖polynomialRoot j ⟨x,hx⟩‖ ≤ Real.rpow (32*Q*j) ((j : ℝ)/2) := by
  have hm := polynomial_of_exponential x Q hQ hExp j hj
  have hx := mem_polynomialRoot_of_finite x j
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm)
  refine ⟨hx, ?_⟩
  have hb : 0 ≤ 32*Q*j := by positivity
  have hr : (Real.rpow (32*Q*j) ((j : ℝ)/2))^2 = (32*Q*j)^j := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hb]
    simp only [Nat.cast_ofNat, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      Real.rpow_natCast]
  rw [← root_norm_sq j ⟨x,hx⟩] at hm
  have hsq : ‖polynomialRoot j ⟨x,hx⟩‖^2 ≤ (32*Q*j)^j :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hm
  have hpos := Real.rpow_nonneg hb ((j : ℝ)/2)
  simp only [Real.rpow_eq_pow] at hr ⊢
  nlinarith

end QuantumNLS.Prop023SpectralMoments

#print axioms QuantumNLS.Prop023SpectralMoments.pointwise_polynomial_bound
#print axioms QuantumNLS.Prop023SpectralMoments.polynomial_of_exponential
#print axioms QuantumNLS.Prop023SpectralMoments.root_sector_norm_sq
#print axioms QuantumNLS.Prop023SpectralMoments.mem_polynomialRoot_of_finite
#print axioms QuantumNLS.Prop023SpectralMoments.root_norm_sq
#print axioms QuantumNLS.Prop023SpectralMoments.norm_of_exponential

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop023SpectralMoments." then
      pending := pending.push n
      roots := roots + 1
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
