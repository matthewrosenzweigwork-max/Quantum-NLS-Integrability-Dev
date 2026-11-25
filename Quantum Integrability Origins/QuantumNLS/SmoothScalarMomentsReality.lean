import QuantumNLS.ClassicalCharges

/-! R-275B7656 support: the formal periodic reality argument.
All formal series below have smooth periodic coefficient functions. Derivatives in x act
coefficientwise; no convergence of these series is used. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory PowerSeries
open scoped ComplexConjugate
namespace QuantumNLS.SmoothScalarMomentsReality
open QuantumNLS.ClassicalCharges QuantumNLS.WeakDerivatives

/-- Ring of smooth periodic coefficient functions. -/
def smoothAlgebra (L : ℝ) : Subalgebra ℂ (ℝ → ℂ) where
  carrier := {f | SmoothPeriodic L f}
  zero_mem' := ⟨contDiff_const, fun _ => rfl⟩
  one_mem' := ⟨contDiff_const, fun _ => rfl⟩
  add_mem' := fun hf hg => ⟨hf.smooth.add hg.smooth, hf.periodic.add hg.periodic⟩
  mul_mem' := fun hf hg => ⟨hf.smooth.mul hg.smooth, hf.periodic.mul hg.periodic⟩
  algebraMap_mem' := fun _ => ⟨contDiff_const, fun _ => rfl⟩

abbrev A (L : ℝ) := smoothAlgebra L

/-- Spatial differentiation on the coefficient ring. -/
def spatialD (L : ℝ) : Derivation ℂ (A L) (A L) where
  toFun f := ⟨deriv f.1, (contDiff_infty_iff_deriv.mp f.2.smooth).2,
    fun x => periodic_deriv f.2.periodic x⟩
  map_add' f g := by
    apply Subtype.ext; funext x
    exact deriv_add ((contDiff_infty_iff_deriv.mp f.2.smooth).1 x)
      ((contDiff_infty_iff_deriv.mp g.2.smooth).1 x)
  map_smul' c f := by
    apply Subtype.ext; funext x
    exact deriv_const_mul c ((contDiff_infty_iff_deriv.mp f.2.smooth).1 x)
  map_one_eq_zero' := by
    apply Subtype.ext; funext x
    exact deriv_const x (1 : ℂ)
  leibniz' f g := by
    apply Subtype.ext; funext x
    change deriv (fun x => f.1 x * g.1 x) x = f.1 x * deriv g.1 x + g.1 x * deriv f.1 x
    calc
      _ = deriv f.1 x * g.1 x + f.1 x * deriv g.1 x := by
        simpa only [Pi.mul_def] using deriv_mul
          ((contDiff_infty_iff_deriv.mp f.2.smooth).1 x)
          ((contDiff_infty_iff_deriv.mp g.2.smooth).1 x)
      _ = _ := by ring

/-- Integration over a period annihilates spatial derivatives. -/
lemma integral_spatialD (L : ℝ) (f : A L) :
    ∫ x in (0 : ℝ)..L, (spatialD L f).1 x = 0 := by
  change ∫ x in (0 : ℝ)..L, deriv f.1 x = 0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => ((contDiff_infty_iff_deriv.mp f.2.smooth).1 x).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp f.2.smooth).2.continuous.intervalIntegrable _ _)]
  have h := f.2.periodic 0
  simpa only [zero_add] using sub_eq_zero.mpr h

section CoefficientDifferentiation
variable {B : Type*} [CommRing B] [Algebra ℂ B]

/-- Coefficientwise extension of a derivation to formal power series. -/
def coeffD (D : Derivation ℂ B B) : Derivation ℂ (PowerSeries B) (PowerSeries B) where
  toFun f := PowerSeries.mk (fun n => D (coeff n f))
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp
  map_one_eq_zero' := by
    ext n
    change coeff n (PowerSeries.mk (fun k => D (coeff k (1 : PowerSeries B)))) = coeff n 0
    simp only [coeff_mk, coeff_one, map_zero]
    split_ifs <;> simp
  leibniz' f g := by
    change PowerSeries.mk (fun n => D (coeff n (f * g))) =
      f * PowerSeries.mk (fun n => D (coeff n g)) +
      g * PowerSeries.mk (fun n => D (coeff n f))
    apply PowerSeries.ext
    intro n
    simp only [coeff_mk, coeff_mul, map_sum, Derivation.leibniz,
      map_add, Finset.sum_add_distrib, smul_eq_mul]
    congr 1
    exact Finset.Nat.sum_antidiagonal_swap (f := fun p : ℕ × ℕ => coeff p.1 g * D (coeff p.2 f)) (n := n)

@[simp] lemma coeff_coeffD (D : Derivation ℂ B B) (f : PowerSeries B) (n : ℕ) :
    coeff n (coeffD D f) = D (coeff n f) := by simp [coeffD]

lemma coeffD_derivative (D : Derivation ℂ B B) (f : PowerSeries B) :
    coeffD D (PowerSeries.derivative f) = PowerSeries.derivative (coeffD D f) := by
  ext n
  simp [coeff_derivative, Derivation.leibniz, Derivation.map_natCast, smul_eq_mul, mul_comm]

/-- Formal logarithmic derivative identity, proved using an invertible series.
If Dx P=Q(1-P), then DX Q=Dx((DX P)/(1-P)). This is the finite-coefficient
version of Q=-Dx log(1-P); it avoids any analytic logarithm. -/
theorem formal_logarithmic_identity (D : Derivation ℂ B B)
    (P Q : PowerSeries B) (U : (PowerSeries B)ˣ)
    (hU : (U : PowerSeries B) = 1 - P)
    (heq : coeffD D P = Q * (1 - P)) :
    PowerSeries.derivative Q =
      coeffD D (PowerSeries.derivative P * (↑U⁻¹ : PowerSeries B)) := by
  let E := coeffD D
  let V : PowerSeries B := ↑U⁻¹
  have hV : (1 - P) * V = 1 := by rw [← hU]; simp [V]
  have hEV : E V = V ^ 2 * E P := by
    have h := E.leibniz_of_mul_eq_one (a := V) (b := 1 - P)
      (by rw [mul_comm]; exact hV)
    simpa only [map_sub, Derivation.map_one_eq_zero, zero_sub, smul_eq_mul,
      mul_neg, neg_mul, neg_neg] using h
  have hPV : E P * V = Q := by
    rw [heq, mul_assoc, hV, mul_one]
  have hDX := congrArg PowerSeries.derivative heq
  rw [← coeffD_derivative, Derivation.leibniz, map_sub,
    PowerSeries.derivative_one, zero_sub, smul_eq_mul] at hDX
  have hDXV := congrArg (fun f : PowerSeries B => f * V) hDX
  change PowerSeries.derivative Q = E (PowerSeries.derivative P * V)
  rw [E.leibniz, smul_eq_mul, hEV]
  calc
    PowerSeries.derivative Q =
      E (PowerSeries.derivative P) * V + Q * PowerSeries.derivative P * V := by
        linear_combination -hDXV - (PowerSeries.derivative Q) * hV
    _ = PowerSeries.derivative P * (V ^ 2 * E P) + V * E (PowerSeries.derivative P) := by
      linear_combination -(PowerSeries.derivative P * V) * hPV

end CoefficientDifferentiation

/-- Every coefficient of Q has integral zero if Dx P=Q(1-P), with vanishing
constant terms. This is the periodic formal-log step in positive_moments.tex:22-45. -/
theorem integral_coeff_eq_zero (L : ℝ) (P Q : PowerSeries (A L))
    (hP : constantCoeff P = 0) (hQ : constantCoeff Q = 0)
    (heq : coeffD (spatialD L) P = Q * (1 - P)) (n : ℕ) :
    ∫ x in (0 : ℝ)..L, (coeff n Q).1 x = 0 := by
  have hunit : IsUnit (1 - P) := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [hP])
  obtain ⟨U, hU⟩ := hunit
  have hid := formal_logarithmic_identity (spatialD L) P Q U hU heq
  cases n with
  | zero =>
    have hz : coeff 0 Q = 0 := by simpa only [coeff_zero_eq_constantCoeff] using hQ
    simp [hz]
  | succ n =>
    have h := congrArg (coeff n) hid
    rw [coeff_derivative, coeff_coeffD] at h
    have hint := integral_spatialD L
      (coeff n (PowerSeries.derivative P * (↑U⁻¹ : PowerSeries (A L))))
    rw [← h] at hint
    have hcast : ∀ x : ℝ, ((coeff (n + 1) Q * (n + 1 : A L)).1 x) =
        (n + 1 : ℂ) * (coeff (n + 1) Q).1 x := by intro x; simp; ring
    simp_rw [hcast] at hint
    rw [intervalIntegral.integral_const_mul] at hint
    exact (mul_eq_zero.mp hint).resolve_left (by exact_mod_cast Nat.succ_ne_zero n)

#print axioms formal_logarithmic_identity
#print axioms integral_coeff_eq_zero
end QuantumNLS.SmoothScalarMomentsReality

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SmoothScalarMomentsReality." ||
        n.toString.startsWith "_private.QuantumNLS.SmoothScalarMomentsReality." then
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
