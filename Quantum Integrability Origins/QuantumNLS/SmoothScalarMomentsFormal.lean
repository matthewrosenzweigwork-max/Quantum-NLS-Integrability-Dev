import QuantumNLS.SmoothScalarMomentsReality

/-! Binding the formal logarithmic identity to the actual smooth charge recursion.
No analytic Riccati existence/expansion theorem is implemented here. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory PowerSeries Finset
open scoped ComplexConjugate
namespace QuantumNLS.SmoothScalarMomentsFormal
open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsReality

variable {L : ℝ} {u : ℝ → ℂ}

def ofSmooth (hu : SmoothPeriodic L u) : A L := ⟨u, hu⟩

def cseq (κ : ℝ) (hu : SmoothPeriodic L u) (n : ℕ) : A L :=
  ⟨vseq κ u n, ⟨(vseq_regular κ hu n).1, (vseq_regular κ hu n).2⟩⟩

def conjugate (L : ℝ) : A L →+* A L where
  toFun f := ⟨fun x => conj (f.1 x), Complex.conjCLE.contDiff.comp f.2.smooth,
    fun x => by rw [f.2.periodic x]⟩
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' f g := by ext x; simp
  map_mul' f g := by ext x; simp

@[simp] lemma conjugate_apply (f : A L) (x : ℝ) :
    (conjugate L f).1 x = conj (f.1 x) := rfl

lemma spatialD_conjugate (f : A L) :
    spatialD L (conjugate L f) = conjugate L (spatialD L f) := by
  apply Subtype.ext; funext x
  change deriv (fun x => conj (f.1 x)) x = conj (deriv f.1 x)
  exact (((contDiff_infty_iff_deriv.mp f.2.smooth).1 x).hasDerivAt.star).deriv

lemma coeffD_conjugate (F : PowerSeries (A L)) :
    coeffD (spatialD L) (PowerSeries.map (conjugate L) F) =
      PowerSeries.map (conjugate L) (coeffD (spatialD L) F) := by
  ext n
  simp only [coeff_coeffD, coeff_map, spatialD_conjugate]

lemma coeff_square {B : Type*} [CommRing B] (F : PowerSeries B)
    (h0 : coeff 0 F = 0) (n : ℕ) :
    coeff (n + 1) (F ^ 2) = ∑ a ∈ Icc 1 n, coeff a F * coeff (n + 1 - a) F := by
  rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun p : ℕ × ℕ => coeff p.1 F * coeff p.2 F)]
  symm
  apply Finset.sum_subset
  · intro a ha
    simp only [mem_Icc] at ha
    simp only [mem_range]
    omega
  · intro a ha hnot
    simp only [mem_range] at ha
    simp only [mem_Icc, not_and_or, not_le] at hnot
    have h : a = 0 ∨ a = n + 1 := by omega
    rcases h with rfl | rfl <;> simp [h0]

def W (κ : ℝ) (hu : SmoothPeriodic L u) : PowerSeries (A L) := mk (cseq κ hu)

def j (L : ℝ) : A L := algebraMap ℂ (A L) Complex.I

def k (L κ : ℝ) : A L := algebraMap ℂ (A L) (κ : ℂ)

lemma j_sq : j L ^ 2 = -1 := by
  unfold j
  rw [← map_pow, Complex.I_sq, map_neg, map_one]

lemma conjugate_j : conjugate L (j L) = -j L := by
  ext x
  simp [j, conjugate]

lemma conjugate_k (κ : ℝ) : conjugate L (k L κ) = k L κ := by
  ext x
  simp [k, conjugate]

lemma spatialD_j : spatialD L (j L) = 0 := by
  exact (spatialD L).map_algebraMap Complex.I

lemma spatialD_k (κ : ℝ) : spatialD L (k L κ) = 0 := by
  exact (spatialD L).map_algebraMap (κ : ℂ)

lemma cseq_zero (κ : ℝ) (hu : SmoothPeriodic L u) : cseq κ hu 0 = 0 := by
  apply Subtype.ext; funext x
  simp [cseq, vseq]

lemma cseq_one (κ : ℝ) (hu : SmoothPeriodic L u) : cseq κ hu 1 = (ofSmooth hu) := by
  apply Subtype.ext; funext x
  simp [cseq, vseq_one, ofSmooth]

lemma cseq_succ (κ : ℝ) (hu : SmoothPeriodic L u) (n : ℕ) :
    cseq κ hu (n + 2) = -j L * spatialD L (cseq κ hu (n + 1)) +
      k L κ * conjugate L (ofSmooth hu) *
        ∑ a ∈ Icc 1 n, cseq κ hu a * cseq κ hu (n + 1 - a) := by
  apply Subtype.ext
  funext x
  have h := congrFun (vseq_succ κ u n) x
  simpa [cseq, j, k, conjugate, spatialD, ofSmooth] using h

/-- Formal charge-series equation, coefficientwise equivalent to DEF-022. -/
lemma W_equation (κ : ℝ) (hu : SmoothPeriodic L u) :
    X * coeffD (spatialD L) (W κ hu) =
      C (j L) * W κ hu - X * C (j L * (ofSmooth hu)) -
      X * C (j L * k L κ * conjugate L (ofSmooth hu)) * W κ hu ^ 2 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [W, cseq_zero]
  | succ n =>
    simp only [mul_assoc, coeff_succ_X_mul, coeff_coeffD, W, coeff_mk, map_sub, coeff_C_mul]
    cases n with
    | zero => simp [cseq_zero, cseq_one, coeff_zero_eq_constantCoeff]
    | succ n =>
      simp only [coeff_C, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, sub_zero]
      have h0 : coeff 0 (W κ hu) = 0 := by simp [W, cseq_zero]
      have hs := coeff_square (W κ hu) h0 n
      have hr := cseq_succ κ hu n
      have hjs := j_sq (L := L)
      simp only [W, coeff_mk] at hs
      simp only [Nat.add_assoc, Nat.reduceAdd] at hr ⊢
      rw [hs]
      linear_combination -j L * hr + spatialD L (cseq κ hu (n + 1)) * hjs

/-- The source's two formal Laurent series r and s. -/
def R (κ : ℝ) (hu : SmoothPeriodic L u) : PowerSeries (A L) := C (j L) * W κ hu

def S (κ : ℝ) (hu : SmoothPeriodic L u) : PowerSeries (A L) :=
  C (-j L) * PowerSeries.map (conjugate L) (W κ hu)

lemma coeff_R (κ : ℝ) (hu : SmoothPeriodic L u) (n : ℕ) :
    coeff n (R κ hu) = j L * cseq κ hu n := by
  unfold R W
  rw [coeff_C_mul, coeff_mk]

lemma coeff_S (κ : ℝ) (hu : SmoothPeriodic L u) (n : ℕ) :
    coeff n (S κ hu) = -j L * conjugate L (cseq κ hu n) := by
  unfold S W
  rw [coeff_C_mul, coeff_map, coeff_mk]

lemma coeffD_C {B : Type*} [CommRing B] [Algebra ℂ B]
    (D : Derivation ℂ B B) (b : B) : coeffD D (C b) = C (D b) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_coeffD, coeff_C]
  split_ifs <;> simp

lemma R_equation (κ : ℝ) (hu : SmoothPeriodic L u) :
    X * coeffD (spatialD L) (R κ hu) =
      X * C ((ofSmooth hu) : A L) + C (j L) * R κ hu -
      X * C (k L κ * conjugate L (ofSmooth hu)) * R κ hu ^ 2 := by
  have hW := W_equation κ hu
  have hj : C (j L) ^ 2 = (-1 : PowerSeries (A L)) := by rw [← map_pow, j_sq, map_neg, map_one]
  have hD : coeffD (spatialD L) (C (j L)) = 0 := by
    rw [coeffD_C, spatialD_j, map_zero]
  unfold R
  simp only [Derivation.leibniz, smul_eq_mul, hD, mul_zero, add_zero]
  simp only [map_mul] at hW ⊢
  linear_combination C (j L) * hW - X * C ((ofSmooth hu) : A L) * hj

lemma S_equation (κ : ℝ) (hu : SmoothPeriodic L u) :
    X * coeffD (spatialD L) (S κ hu) =
      X * C (conjugate L (ofSmooth hu)) - C (j L) * S κ hu -
      X * C (k L κ * ((ofSmooth hu) : A L)) * S κ hu ^ 2 := by
  have hW := congrArg (PowerSeries.map (conjugate L)) (W_equation κ hu)
  have hconjconj : conjugate L (conjugate L (ofSmooth hu)) = ((ofSmooth hu) : A L) := by ext x; simp
  simp only [map_mul, map_sub, PowerSeries.map_X, PowerSeries.map_C, map_pow,
    ← coeffD_conjugate, conjugate_j, conjugate_k, hconjconj, map_neg] at hW
  have hj : C (j L) ^ 2 = (-1 : PowerSeries (A L)) := by rw [← map_pow, j_sq, map_neg, map_one]
  have hD : coeffD (spatialD L) (C (j L)) = 0 := by
    rw [coeffD_C, spatialD_j, map_zero]
  unfold S
  simp only [map_neg, Derivation.leibniz, smul_eq_mul, hD, neg_zero, mul_zero, add_zero]
  simp only [map_mul] at hW ⊢
  linear_combination -C (j L) * hW - X * C (conjugate L (ofSmooth hu)) * hj

def P (κ : ℝ) (hu : SmoothPeriodic L u) : PowerSeries (A L) :=
  C (k L κ) * R κ hu * S κ hu

def Q (κ : ℝ) (hu : SmoothPeriodic L u) : PowerSeries (A L) :=
  C (k L κ) * (C (conjugate L (ofSmooth hu)) * R κ hu +
    C ((ofSmooth hu) : A L) * S κ hu)

lemma product_identity (κ : ℝ) (hu : SmoothPeriodic L u) :
    coeffD (spatialD L) (P κ hu) = Q κ hu * (1 - P κ hu) := by
  have hR := R_equation κ hu
  have hS := S_equation κ hu
  have hD : coeffD (spatialD L) (C (k L κ)) = 0 := by
    rw [coeffD_C, spatialD_k, map_zero]
  apply PowerSeries.X_mul_cancel
  unfold P Q
  simp only [Derivation.leibniz, smul_eq_mul, hD, mul_zero, add_zero]
  simp only [map_mul] at hR hS ⊢
  linear_combination C (k L κ) * S κ hu * hR + C (k L κ) * R κ hu * hS

/-- The all-order formal reality lemma used BEFORE the positive moment argument.
The charges are the existing literal DEF-022 recursion, at arbitrary smooth mass.
No moment identity or analytic Riccati expansion is a premise. -/
theorem charge_real {κ : ℝ} (hκ : 0 < κ) (hu : SmoothPeriodic L u) (n : ℕ) :
    (charge L κ u n).im = 0 := by
  have hP : constantCoeff (P κ hu) = 0 := by simp [P, R, S, W, cseq_zero]
  have hR0 : constantCoeff (R κ hu) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_R, cseq_zero, mul_zero]
  have hS0 : constantCoeff (S κ hu) = 0 := by
    rw [← coeff_zero_eq_constantCoeff, coeff_S, cseq_zero, map_zero, mul_zero]
  have hQ : constantCoeff (Q κ hu) = 0 := by simp [Q, hR0, hS0]
  have hi := integral_coeff_eq_zero L (P κ hu) (Q κ hu) hP hQ (product_identity κ hu) n
  have hpoint : ∀ x : ℝ, (coeff n (Q κ hu)).1 x =
      Complex.I * (κ : ℂ) * (conj (u x) * vseq κ u n x - conj (conj (u x) * vseq κ u n x)) := by
    intro x
    unfold Q
    rw [coeff_C_mul, map_add, coeff_C_mul, coeff_C_mul, coeff_R, coeff_S]
    simp [j, k, cseq, conjugate, ofSmooth]
    ring
  simp_rw [hpoint] at hi
  have hA : IntervalIntegrable (fun x => conj (u x) * vseq κ u n x) volume (0 : ℝ) L :=
    (charge_integrand_continuous κ hu n).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun x => conj (conj (u x) * vseq κ u n x)) volume (0 : ℝ) L :=
    (Complex.continuous_conj.comp (charge_integrand_continuous κ hu n)).intervalIntegrable _ _
  have hconj : (∫ x in (0 : ℝ)..L, conj (conj (u x) * vseq κ u n x)) =
      conj (charge L κ u n) := by
    have h := ContinuousLinearMap.intervalIntegral_comp_comm
      (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap hA
    simpa [charge] using h
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hA hB, hconj] at hi
  change Complex.I * (κ : ℂ) * (charge L κ u n - conj (charge L κ u n)) = 0 at hi
  have hn : Complex.I * (κ : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hκ.ne')
  have he := sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hn)
  have him := congrArg Complex.im he
  simp only [Complex.conj_im] at him
  linarith

#print axioms W_equation
#print axioms product_identity
#print axioms charge_real
end QuantumNLS.SmoothScalarMomentsFormal

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SmoothScalarMomentsFormal." ||
        n.toString.startsWith "_private.QuantumNLS.SmoothScalarMomentsFormal." then
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
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
