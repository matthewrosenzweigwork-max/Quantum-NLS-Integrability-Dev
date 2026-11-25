import QuantumNLS.Prop018JointCalculus
import QuantumNLS.Prop018Scalar

/-! Charge domains on the event projection and operator-norm lifting of
uniform label inequalities. Full maximal charge domains are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Complex
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.Prop018ChargeCutoff
open BetheLabels BetheCoefficientTransform BetheSpectralCharges
open HaarNonlinearAbstract HaarSpectralTail

section Generic
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma eigen_norm_le (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) (a : ι → ℂ)
    (hA : ∀ i, A (b i) = a i • b i) (i : ι) : ‖a i‖ ≤ ‖A‖ := by
  have h := A.le_opNorm (b i)
  rw [hA, norm_smul, b.orthonormal.norm_eq_one, mul_one, mul_one] at h
  exact h

lemma diagonal_opNorm_le (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H) (a : ι → ℂ)
    (hA : ∀ i, A (b i) = a i • b i) {δ : ℝ} (hδ : 0 ≤ δ) (ha : ∀ i, ‖a i‖ ≤ δ) : ‖A‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound A hδ
  intro ψ
  exact Prop020Vector.diag_apply_le b A a hA Set.univ hδ (fun i _ => ha i) ψ
    (fun i hi => absurd (mem_univ i) hi)
end Generic

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

open Classical in
def eventMask (S : Set (MArr N)) (m : MArr N) : ℂ := if m ∈ S then 1 else 0

/-- Boundedness of a charge symbol on the selected event implies that the
entire range of P lies in its full unbounded maximal domain. -/
theorem restricted_charge (b : BetheBasis L N) (S : Set (MArr N))
    (P : HN L N →L[ℂ] HN L N) (hP : ∀ m, P (b m) = eventMask S m • b m)
    (q : MArr N → ℝ) {C : ℝ} (hC : 0 ≤ C) (hq : ∀ m ∈ S, |q m| ≤ C) :
    ∃ Q : HN L N →L[ℂ] HN L N,
      (∀ m, Q (b m) = ((q m : ℂ) * eventMask S m) • b m) ∧ ‖Q‖ ≤ C ∧
      ∀ ψ : HN L N, ∃ h : P ψ ∈ (multiplier b q).domain,
        multiplier b q ⟨P ψ, h⟩ = Q ψ := by
  classical
  have hbd (m : MArr N) : ‖(q m : ℂ) * eventMask S m‖ ≤ C := by
    by_cases hm : m ∈ S
    · simpa only [eventMask, ite_eq_left hm, mul_one, Complex.norm_real, Real.norm_eq_abs] using hq m hm
    · simp only [eventMask, ite_eq_right hm, mul_zero, norm_zero]
      exact hC
  obtain ⟨Q, hQ, hn⟩ := HilbertDiagOp.diag_exists b _ C hbd hC
  refine ⟨Q, (fun m => (show IsDiagC b Q _ from hQ).apply_basis m), hn, ?_⟩
  intro ψ
  have hcoef (m : MArr N) : ⟪b m, Q ψ⟫_ℂ = (q m : ℂ) * ⟪b m, P ψ⟫_ℂ := by
    rw [hQ, diagC_of_apply hP]
    ring
  have hmem : P ψ ∈ (multiplier b q).domain := (maximal b q (P ψ)).mpr
    ⟨Q ψ, hcoef, fun φ hφ => ext_coeff (b := b) (fun m => (hφ m).trans (hcoef m).symm)⟩
  exact ⟨hmem, ext_coeff (b := b) (fun m => (multiplier_coord b q ⟨P ψ, hmem⟩ m).trans (hcoef m).symm)⟩

/-- The two scalar inequalities become the printed operator norms. In
particular Q is the bounded composition of the actual unbounded charge
with P, as proved by the retained domain clause. -/
theorem operator_bounds (b : BetheBasis L N) (S : Set (MArr N))
    (P C0 C1 : HN L N →L[ℂ] HN L N)
    (hP : ∀ m, P (b m) = eventMask S m • b m)
    (q c0 c1 : MArr N → ℝ)
    (h0 : ∀ m, C0 (b m) = (c0 m : ℂ) • b m)
    (h1 : ∀ m, C1 (b m) = (c1 m : ℂ) • b m)
    {δ0 δ1 c : ℝ} (hδ0 : 0 ≤ δ0) (hδ1 : 0 ≤ δ1)
    (he0 : ∀ m ∈ S, |q m - (N : ℝ) * c0 m - c1 m| ≤ δ0)
    (he1 : ∀ m ∈ S, |c1 m - c| ≤ δ1) :
    ∃ Q : HN L N →L[ℂ] HN L N,
      (∀ ψ : HN L N, ∃ h : P ψ ∈ (multiplier b q).domain,
        multiplier b q ⟨P ψ, h⟩ = Q ψ) ∧
      ‖Q - (((N : ℂ) • C0 + C1) * P)‖ ≤ δ0 ∧
      ‖(C1 - (c : ℂ) • (1 : HN L N →L[ℂ] HN L N)) * P‖ ≤ δ1 := by
  classical
  have hbq (m : MArr N) (hm : m ∈ S) : |q m| ≤ δ0 + N * ‖C0‖ + ‖C1‖ := by
    have hb0 : |c0 m| ≤ ‖C0‖ := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using eigen_norm_le b C0 _ h0 m
    have hb1 : |c1 m| ≤ ‖C1‖ := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using eigen_norm_le b C1 _ h1 m
    have htri : |q m| ≤ |q m - N * c0 m - c1 m| + |N * c0 m| + |c1 m| := by
      calc |q m| = |(q m - N * c0 m - c1 m) + N * c0 m + c1 m| := by congr 1; ring
           _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hn : |(N : ℝ)| = (N : ℝ) := abs_of_nonneg (Nat.cast_nonneg N)
    rw [abs_mul, hn] at htri
    exact htri.trans (add_le_add (add_le_add (he0 m hm)
      (mul_le_mul_of_nonneg_left hb0 (Nat.cast_nonneg N))) hb1)
  obtain ⟨Q, hQ, -, hdom⟩ := restricted_charge b S P hP q (by positivity) hbq
  refine ⟨Q, hdom, ?_, ?_⟩
  · let e : MArr N → ℂ := fun m => ((q m - N * c0 m - c1 m : ℝ) : ℂ) * eventMask S m
    have hd (m : MArr N) :
        (Q - (((N : ℂ) • C0 + C1) * P)) (b m) = e m • b m := by
      simp only [sub_apply, mul_ap, hP, map_smul, add_apply, smul_apply, h0, h1, hQ, smul_smul,
        ← add_smul, ← sub_smul]
      congr 1
      dsimp [e]
      push_cast
      ring
    apply diagonal_opNorm_le b _ e hd hδ0
    intro m
    by_cases hm : m ∈ S
    · simpa only [e, eventMask, ite_eq_left hm, mul_one, Complex.norm_real, Real.norm_eq_abs] using he0 m hm
    · simp only [e, eventMask, ite_eq_right hm, mul_zero, norm_zero]
      exact hδ0
  · let e : MArr N → ℂ := fun m => ((c1 m - c : ℝ) : ℂ) * eventMask S m
    have hd (m : MArr N) :
        ((C1 - (c : ℂ) • (1 : HN L N →L[ℂ] HN L N)) * P) (b m) = e m • b m := by
      simp only [mul_ap, hP, map_smul, sub_apply, h1, smul_apply, one_ap, smul_smul, ← sub_smul]
      congr 1
      dsimp [e]
      push_cast
      ring
    apply diagonal_opNorm_le b _ e hd hδ1
    intro m
    by_cases hm : m ∈ S
    · simpa only [e, eventMask, ite_eq_left hm, mul_one, Complex.norm_real, Real.norm_eq_abs] using he1 m hm
    · simp only [e, eventMask, ite_eq_right hm, mul_zero, norm_zero]
      exact hδ1

/-- The event's actual root window puts ran P in every individual full
charge domain, at all orders. -/
theorem all_charge_domains {κ : ℝ} (hκ : 0 < κ) (hN : 0 < N)
    (E : Set (MArr N)) (P : HN L N →L[ℂ] HN L N)
    (hP : ∀ m, P (HaarSpectralTail.bas L hκ hN m) = eventMask E m • HaarSpectralTail.bas L hκ hN m)
    {R : ℝ} (hR : 0 ≤ R) (hroot : ∀ m ∈ E, ∀ j, |Prop017Quantum.qAct L κ N m j| ≤ R)
    (r : ℕ) (ψ : HN L N) :
    P ψ ∈ (charge (HaarSpectralTail.bas L hκ hN) (κ / N) r).domain := by
  have hb (m : MArr N) (hm : m ∈ E) : |eigenvalue L N (κ / N) r m| ≤ N * R ^ r := by
    rw [Prop018Phase.eigenvalue_eq hκ hN]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      (∑ j : Fin N, |Prop017Quantum.qAct L κ N m j ^ r|) ≤ ∑ _j : Fin N, R ^ r := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hroot m hm j) r
      _ = N * R ^ r := by simp
  obtain ⟨Q, -, -, hdom⟩ := restricted_charge (HaarSpectralTail.bas L hκ hN) E P hP
    (eigenvalue L N (κ / N) r) (mul_nonneg (Nat.cast_nonneg N) (pow_nonneg hR r)) hb
  exact (hdom ψ).choose

/-- On the common domain the maximal polynomial multiplier is exactly the
finite sum of the individual unbounded charge actions. -/
lemma sum_charge_actions (b : BetheBasis L N) (c : ℝ) (p : ℕ → ℝ) (d : ℕ) (ψ : HN L N)
    (hd : ∀ r, ψ ∈ (charge b c r).domain)
    (hq : ψ ∈ (multiplier b (fun m => ∑ r ∈ Finset.range (d + 1), p r * eigenvalue L N c r m)).domain) :
    multiplier b _ ⟨ψ, hq⟩ = ∑ r ∈ Finset.range (d + 1), (p r : ℂ) • charge b c r ⟨ψ, hd r⟩ := by
  apply ext_coeff (b := b)
  intro m
  rw [multiplier_coord]
  simp only [inner_sum, inner_smul_right, charge, multiplier_coord]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Bounded common spectral multipliers preserve every maximal charge
domain and commute there, without extending an unbounded operator. -/
theorem bounded_commutes_multiplier (b : BetheBasis L N) (q : MArr N → ℝ)
    (A : HN L N →L[ℂ] HN L N) (a : MArr N → ℂ)
    (ha : ∀ m, A (b m) = a m • b m) (ψ : (multiplier b q).domain) :
    ∃ h : A ψ.val ∈ (multiplier b q).domain,
      multiplier b q ⟨A ψ.val, h⟩ = A (multiplier b q ψ) := by
  have hd := diagC_of_apply ha
  have hc (m : MArr N) : ⟪b m, A (multiplier b q ψ)⟫_ℂ = (q m : ℂ) * ⟪b m, A ψ.val⟫_ℂ := by
    rw [hd, multiplier_coord, hd]
    ring
  have hm : A ψ.val ∈ (multiplier b q).domain := (maximal b q (A ψ.val)).mpr
    ⟨A (multiplier b q ψ), hc, fun φ hφ => ext_coeff (b := b) (fun m => (hφ m).trans (hc m).symm)⟩
  exact ⟨hm, ext_coeff (b := b) (fun m => (multiplier_coord b q ⟨A ψ.val, hm⟩ m).trans (hc m).symm)⟩

/-- Literal domain commutation with every full actual charge. -/
def CommutesAllCharges (b : BetheBasis L N) (c : ℝ) (A : HN L N →L[ℂ] HN L N) : Prop :=
  ∀ r : ℕ, ∀ ψ : (charge b c r).domain, ∃ h : A ψ.val ∈ (charge b c r).domain,
    charge b c r ⟨A ψ.val, h⟩ = A (charge b c r ψ)

lemma commutes_all_charges (b : BetheBasis L N) (c : ℝ) (A : HN L N →L[ℂ] HN L N)
    (a : MArr N → ℂ) (ha : ∀ m, A (b m) = a m • b m) : CommutesAllCharges b c A :=
  fun r ψ => bounded_commutes_multiplier b (eigenvalue L N c r) A a ha ψ

/-- The event projection is unique, hence the P_N in the operator packet
is independent of the polynomial and of all chart extensions. -/
lemma event_projection_unique (b : BetheBasis L N) (E : Set (MArr N))
    (P Q : HN L N →L[ℂ] HN L N)
    (hP : ∀ m, P (b m) = eventMask E m • b m)
    (hQ : ∀ m, Q (b m) = eventMask E m • b m) : P = Q := by
  apply TransferNormality.ext_of_hilbertBasis b
  intro m
  exact (hP m).trans (hQ m).symm

end QuantumNLS.Prop018ChargeCutoff

#print axioms QuantumNLS.Prop018ChargeCutoff.eigen_norm_le
#print axioms QuantumNLS.Prop018ChargeCutoff.diagonal_opNorm_le
#print axioms QuantumNLS.Prop018ChargeCutoff.eventMask
#print axioms QuantumNLS.Prop018ChargeCutoff.restricted_charge
#print axioms QuantumNLS.Prop018ChargeCutoff.operator_bounds
#print axioms QuantumNLS.Prop018ChargeCutoff.all_charge_domains
#print axioms QuantumNLS.Prop018ChargeCutoff.sum_charge_actions
#print axioms QuantumNLS.Prop018ChargeCutoff.bounded_commutes_multiplier
#print axioms QuantumNLS.Prop018ChargeCutoff.CommutesAllCharges
#print axioms QuantumNLS.Prop018ChargeCutoff.commutes_all_charges
#print axioms QuantumNLS.Prop018ChargeCutoff.event_projection_unique

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop018ChargeCutoff." then
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
