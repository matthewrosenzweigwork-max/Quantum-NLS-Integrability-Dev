import QuantumNLS.Prop021DisplacementR129
import QuantumNLS.Prop021CoefficientR128
import QuantumNLS.Prop022OVacuum
import QuantumNLS.CoherentLowerBound
import QuantumNLS.Prop024WAffine
import QuantumNLS.HighMomentsOps
import QuantumNLS.IntrinsicContact
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Vacuum coefficients of the actual Stone unitary, from the frozen
affine Weyl identities on the common number-moment domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop021CoherentCoreR131
open Occupation Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006QuasifreeWeak
open Ext006ModeDomainR33a Ext006SmoothOperatorsR34a Ext006IdentityCyclicR35a
open Ext006FieldBoundsR42a Ext006StrongFieldR41a Ext006AnalyticFieldR42a
open Ext006EntireFieldR43a Ext006BoundedExponentialR43a Ext006SeriesIdentificationR43a
open Ext006KernelHilbertSchmidt Prop024WAffine Prop024WCoordinates

private lemma vacuum_ann {L : ℝ} [Fact (0 < L)] (g : H) : A g (ketD 0) = 0 := by
  have h := identity_vacuum (physicalBasis L) ((physicalBasis L).repr.symm g)
  simpa only [sourceAnn_identity, LinearIsometryEquiv.apply_symm_apply] using h

/-- Mode-by-mode annihilation recurrence for the actual displaced vacuum. -/
theorem vacuum_recurrence {L : ℝ} [Fact (0 < L)] (h : H) (t : ℝ) (m : Occ) (a : ℤ) :
    (Real.sqrt ((m a : ℝ) + 1) : ℂ) * (unitary h t (ketD 0).val) (m+e a) =
      (Complex.I * (t : ℂ) * h a) * (unitary h t (ketD 0).val) m := by
  have he := ann_affine (lp.single 2 a (1 : ℂ)) h t (ketD 0) m
  rw [annC_single, vacuum_ann (L := L), Submodule.coe_zero, map_zero] at he
  simpa only [xcoord, annCoeff, lp.coeFn_zero, Pi.zero_apply, zero_add,
    lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using he

/-- The differential equation for the vacuum coefficient fixes the phase and
the Gaussian factor, with no selection of a normalized implementer. -/
theorem vacuum_gaussian {L : ℝ} [Fact (0 < L)] (h : H) (t : ℝ) :
    unitary h t (ketD 0).val 0 = Complex.exp (-(t : ℂ)^2 * (‖h‖ : ℂ)^2 / 2) := by
  let v := ketD 0
  let a : ℝ → ℂ := fun r => unitary h r v.val 0
  have hcoeff (r : ℝ) :
      unitary h r (C h v).val 0 = (Complex.I * (r : ℂ) * inner ℂ h h) * a r := by
    have hc := cre_affine h h r v (0 : Occ)
    have hz : creC h 0 (unitary h r v.val) = 0 := by
      rw [creC_apply]
      simp
    rw [hz] at hc
    change 0 = unitary h r (C h v).val 0 +
      (Complex.I * (r : ℂ) * -inner ℂ h h) * a r at hc
    linear_combination -hc
  have ha (r : ℝ) : HasDerivAt a (-(r : ℂ) * (‖h‖ : ℂ)^2 * a r) r := by
    have hg : (v.val, (field h v).val) ∈ Ext006FieldClosureR42a.closedFieldGraph h :=
      subset_closure ⟨v, rfl⟩
    have hd := Ext006StoneGeneratorR44a.graph_hasDerivAt h v.val (field h v).val hg r
    let ev := (lp.evalCLM ℂ (fun _ : Occ => ℂ) 2 (0 : Occ)).restrictScalars ℝ
    have he := ev.hasFDerivAt.comp_hasDerivAt r hd
    change HasDerivAt a (Complex.I * unitary h r (field h v).val 0) r at he
    rw [show field h v = C h v by
      change A h (ketD 0) + C h (ketD 0) = _
      rw [vacuum_ann (L := L), zero_add], hcoeff, inner_self_eq_norm_sq_to_K] at he
    have heq : Complex.I * ((Complex.I * (r : ℂ) * (‖h‖ : ℂ)^2) * a r) =
        -(r : ℂ) * (‖h‖ : ℂ)^2 * a r := by
      calc
        _ = (Complex.I * Complex.I) * ((r : ℂ) * (‖h‖ : ℂ)^2 * a r) := by ring
        _ = _ := by rw [Complex.I_mul_I]; ring
    convert he using 1
    exact heq.symm
  let b : ℝ → ℂ := fun r => Complex.exp ((r : ℂ)^2 * (‖h‖ : ℂ)^2 / 2)
  have hb (r : ℝ) : HasDerivAt b ((r : ℂ) * (‖h‖ : ℂ)^2 * b r) r := by
    have hr := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r (hasDerivAt_id r)
    change HasDerivAt (fun s : ℝ => (s : ℂ)) 1 r at hr
    have he : HasDerivAt (fun s : ℝ => (s : ℂ)^2 * (‖h‖ : ℂ)^2 / 2)
        ((r : ℂ) * (‖h‖ : ℂ)^2) r := by
      convert (((hr.pow 2).mul_const ((‖h‖ : ℂ)^2)).div_const 2) using 1
      ring
    simpa only [b, mul_comm] using he.cexp
  have hz (r : ℝ) : HasDerivAt (fun s => b s * a s) 0 r := by
    convert (hb r).mul (ha r) using 1
    ring
  have hc := is_const_of_deriv_eq_zero (fun r => (hz r).differentiableAt)
    (fun r => (hz r).deriv) t 0
  have h0 : b 0 * a 0 = 1 := by simp [b, a, unitary_zero, v, ketD]
  have ht := congrArg (Complex.exp (-(t : ℂ)^2 * (‖h‖ : ℂ)^2 / 2) * ·) (hc.trans h0)
  change _ * (b t * a t) = _ * 1 at ht
  rw [← mul_assoc, ← Complex.exp_add] at ht
  have he : -(t : ℂ)^2 * (‖h‖ : ℂ)^2 / 2 +
      (t : ℂ)^2 * (‖h‖ : ℂ)^2 / 2 = 0 := by ring
  simpa only [he, Complex.exp_zero, one_mul, mul_one, a] using ht


open PhysicalTensor BetheCoefficientTransform TensorCarrier Ext006PhysFockCoord
open Prop022OVacuum Prop021DisplacementR129 Ext006GlobalCovarianceR43a
open OccupationUnitary CoherentLowerBound Prop021CoefficientR128

variable {L : ℝ} [Fact (0 < L)]

private def gaussian (v : L2T L) : ℂ := (Real.exp (-‖v‖^2/2) : ℝ)

private def expected (v : L2T L) (m : Occ) : ℂ :=
  gaussian v / (Real.sqrt (multiplicityFactorial m : ℝ) : ℂ) *
    m.prod (fun i n => ((physicalBasis L).repr v i)^n)

private lemma expected_step (v : L2T L) (m : Occ) (a : ℤ) :
    (Real.sqrt ((m a : ℝ) + 1) : ℂ) * expected v (m+e a) =
      (physicalBasis L).repr v a * expected v m := by
  unfold expected
  rw [prod_add_e, mult_add_single, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.sqrt_mul (by positivity), Complex.ofReal_mul]
  have hf : (Real.sqrt (multiplicityFactorial m : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast multiplicityFactorial_pos m)).ne'
  have ha : (Real.sqrt ((m a : ℝ) + 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

private lemma printed_vacuum_coords (v : L2T L) :
    Phi (printedWeyl v (vac : Ext025B3PhysicalSectors.Fock L)) =
      unitary ((physicalBasis L).repr ((-Complex.I) • v)) 1 (ketD 0).val := by
  change Phi (displacement v vac) = _
  rw [displacement, Ext006SourceWeylR44a.sourceWeyl_eq,
    physicalExponential_apply, LinearIsometryEquiv.apply_symm_apply, vac, physCore_ket]
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Exact coherent coefficients in the frozen free occupation coordinates. -/
theorem coherent_coordinates (v : L2T L) (m : Occ) :
    Phi (printedWeyl v (vac : Ext025B3PhysicalSectors.Fock L)) m = expected v m := by
  rw [printed_vacuum_coords]
  let h : H := (physicalBasis L).repr ((-Complex.I) • v)
  have hrec (n : Occ) (a : ℤ) :
      (Real.sqrt ((n a : ℝ) + 1) : ℂ) * (unitary h 1 (ketD 0).val) (n+e a) =
      (physicalBasis L).repr v a * (unitary h 1 (ketD 0).val) n := by
    have hr := vacuum_recurrence (L := L) h 1 n a
    have hc : Complex.I * ((1 : ℝ) : ℂ) * h a = (physicalBasis L).repr v a := by
      simp only [h, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_one, mul_one]
      rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
    rwa [hc] at hr
  have hzer : (unitary h 1 (ketD 0).val) 0 = expected v 0 := by
    have hh : ‖h‖ = ‖v‖ := by simp [h, norm_smul]
    rw [vacuum_gaussian (L := L), hh]
    simp [gaussian, expected, multiplicityFactorial, Complex.ofReal_exp]
  suffices ∀ n : ℕ, ∀ m : Occ, total m = n →
      (unitary h 1 (ketD 0).val) m = expected v m from this (total m) m rfl
  intro n
  induction n with
  | zero =>
      intro m hm
      have hz : m = 0 := (Finsupp.degree_eq_zero_iff m).mp hm
      rwa [hz]
  | succ n ih =>
      intro m hm
      obtain ⟨a, ha⟩ : ∃ a, m a ≠ 0 := by
        by_contra! hz
        have he : m = 0 := Finsupp.ext hz
        simp [he, total] at hm
      have ha' : 1 ≤ m a := Nat.one_le_iff_ne_zero.mpr ha
      have htotal := total_sub_e ha'
      have hn : total (m-e a) = n := by omega
      have hr := hrec (m-e a) a
      rw [ih _ hn, ← expected_step, shift_sub_add ha'] at hr
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.mpr (by positivity)).ne') hr

/-- Literal sector of the displaced vacuum, with its Gaussian and factorial
normalization fixed by the source Stone group. -/
theorem coherent_sector (v : L2T L) (n : ℕ) :
    printedWeyl v (vac : Ext025B3PhysicalSectors.Fock L) n =
      (gaussian v / (Real.sqrt (n.factorial : ℝ) : ℂ)) • HighMomentsOps.wvec n v := by
  apply (physicalOccupation L n).injective
  apply lp.ext
  funext m
  have hc := coherent_coordinates v m.val
  change occupationCoefficient (freeBasis L (total m.val))
    (printedWeyl v (vac : Ext025B3PhysicalSectors.Fock L) (total m.val)) ⟨m.val, rfl⟩ =
    expected v m.val at hc
  rcases m with ⟨m,hm⟩
  subst n
  rw [occupationCoefficient_free] at hc
  rw [hc, map_smul]
  change expected v m =
    (gaussian v / (Real.sqrt ((total m).factorial : ℝ) : ℂ)) *
      OccupationUnitary.U4 (total m) (TensorFourier.U3 L (total m) (HighMomentsOps.wvec (total m) v))
        ⟨m,rfl⟩
  rw [HighMomentsOps.wvec, TensorFourier.U3_htpow, OccupationUnitary.U4_htpow]
  change _ = _ * ((normalization _ : ℂ) * m.prod (fun a k => ((physicalBasis L).repr v a)^k))
  have hn : (Real.sqrt ((total m).factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hm : (Real.sqrt (multiplicityFactorial m : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast multiplicityFactorial_pos m)).ne'
  simp only [expected, normalization]
  rw [Real.sqrt_div (Nat.cast_nonneg _), Complex.ofReal_div]
  field_simp

/-- The Poisson coefficient is the one extracted by the literal projection
onto the actual condensate tensor used by PROP-025. -/
theorem coherent_number_sector (N : ℕ) (u : L2T L) (hu : ‖u‖ = 1) :
    printedWeyl ((Real.sqrt N : ℂ) • u) (vac : Ext025B3PhysicalSectors.Fock L) N =
      (coherentCoefficient N : ℂ) • HighMomentsOps.wvec N u := by
  rw [coherent_sector, coefficient_source_formula]
  have hnorm : ‖(Real.sqrt N : ℂ) • u‖ ^ 2 = N := by
    rw [norm_smul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
  have hw : HighMomentsOps.wvec N ((Real.sqrt N : ℂ) • u) =
      ((Real.sqrt N : ℂ)^N) • HighMomentsOps.wvec N u := by
    apply Subtype.ext
    change htpow N ((Real.sqrt N : ℂ) • u) = ((Real.sqrt N : ℂ)^N) • htpow N u
    exact IntrinsicContact.htpow_smul N _ u
  rw [hw, gaussian, hnorm, smul_smul]
  congr 1
  have hsqrt (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x^n) = (Real.sqrt x)^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx n), ih, pow_succ]
  rw [hsqrt _ (Nat.cast_nonneg _) _]
  push_cast
  ring

end QuantumNLS.Prop021CoherentCoreR131

#print axioms QuantumNLS.Prop021CoherentCoreR131.vacuum_recurrence
#print axioms QuantumNLS.Prop021CoherentCoreR131.vacuum_gaussian
#print axioms QuantumNLS.Prop021CoherentCoreR131.coherent_number_sector

set_option maxHeartbeats 12000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if ["Prop021CoherentCoreR131"].any
        (fun m => n.toString.startsWith ("QuantumNLS." ++ m ++ ".") ||
          n.toString.startsWith ("_private.QuantumNLS." ++ m ++ ".")) then
      pending := pending.push n
  let roots := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").contains "HeldGP14Tonelli" ||
          (n.toString.splitOn ".").contains "RegularCut" then
        throwError "Forbidden held dependency: {n}"
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
  Lean.logInfo m!"R131 aggregate audit PASS: {roots} own constants, {seen.size} transitive constants; standard-only."
