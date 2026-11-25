import QuantumNLS.Ext006NumberDomainR32a
import QuantumNLS.Ext006CoreLimit
import QuantumNLS.Ext006QuasifreeWeak

/-! Analytic domains for actual mode creation/annihilation on completed
occupation Fock space. All polynomial number domains are invariant, and the
constructed source-HS vacuum belongs to their intersection. These are domain
lemmas toward implementation; no unitary or Heisenberg relation is an input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ModeDomainR33a
open Occupation Ext006VacuumRecurrence Ext006QuasifreeWeak

/-- The common domain of every polynomial in the particle number. -/
def Smooth (w : Occ → ℂ) : Prop := ∀ p : ℕ,
  Summable (fun m => ((total m : ℝ)+1)^p * ‖w m‖^2)

def annCoeff (a : ℤ) (w : Occ → ℂ) (m : Occ) : ℂ :=
  (Real.sqrt ((m a : ℝ)+1) : ℂ) * w (m+e a)

def creCoeff (a : ℤ) (w : Occ → ℂ) (m : Occ) : ℂ :=
  (Real.sqrt (m a : ℝ) : ℂ) * w (m-e a)

lemma add_e_injective (a : ℤ) : Function.Injective (fun m : Occ => m+e a) :=
  fun _ _ h => add_right_cancel h

lemma creCoeff_add (a : ℤ) (w : Occ → ℂ) (m : Occ) :
    creCoeff a w (m+e a) = (Real.sqrt ((m a : ℝ)+1) : ℂ)*w m := by
  simp [creCoeff]

lemma creCoeff_off (a : ℤ) (w : Occ → ℂ) (m : Occ)
    (hm : m ∉ Set.range (fun n : Occ => n+e a)) : creCoeff a w m = 0 := by
  have ha : m a = 0 := by
    by_contra hz
    have hle : e a ≤ m := single_le_of_donorOK (Nat.one_le_iff_ne_zero.mpr hz)
    exact hm ⟨m-e a, tsub_add_cancel_of_le hle⟩
  simp [creCoeff, ha]

/-- Annihilation preserves every polynomial number domain. -/
theorem Smooth.ann {w : Occ → ℂ} (hw : Smooth w) (a : ℤ) : Smooth (annCoeff a w) := by
  intro p
  have hs := (hw (p+1)).comp_injective (add_e_injective a)
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (pow_nonneg (by positivity) p) (sq_nonneg _)) (fun m => ?_) hs
  simp only [annCoeff, Function.comp_def, total_add_e, Nat.cast_add, Nat.cast_one]
  rw [norm_sq_sqrt_mul _ (by positivity)]
  have ha : (m a : ℝ)+1 ≤ (total m : ℝ)+1+1 := by
    have h := n_le_total m a
    exact_mod_cast (show m a+1 ≤ total m+1+1 by omega)
  have hp : ((total m : ℝ)+1)^p ≤ ((total m : ℝ)+1+1)^p :=
    pow_le_pow_left₀ (by positivity) (by linarith) p
  calc
    _ ≤ ((total m : ℝ)+1+1)^p*(((total m : ℝ)+1+1)*‖w (m+e a)‖^2) :=
      mul_le_mul hp (mul_le_mul_of_nonneg_right ha (sq_nonneg _)) (by positivity) (by positivity)
    _ = _ := by rw [pow_succ (n := p)]; ring

/-- Creation preserves every polynomial number domain; no finite-mode support
assumption is used for the vector. -/
theorem Smooth.cre {w : Occ → ℂ} (hw : Smooth w) (a : ℤ) : Smooth (creCoeff a w) := by
  intro p
  apply (add_e_injective a).summable_iff (fun m hm => by rw [creCoeff_off a w m hm]; simp) |>.mp
  have hs := (hw (p+1)).mul_left ((2 : ℝ)^p)
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (pow_nonneg (by positivity) p) (sq_nonneg _)) (fun m => ?_) hs
  simp only [creCoeff_add, total_add_e, Nat.cast_add, Nat.cast_one]
  rw [norm_sq_sqrt_mul _ (by positivity)]
  have ha : (m a : ℝ)+1 ≤ (total m : ℝ)+1 := by exact_mod_cast Nat.succ_le_succ (n_le_total m a)
  have hp : ((total m : ℝ)+1+1)^p ≤ (2*((total m : ℝ)+1))^p :=
    pow_le_pow_left₀ (by positivity) (by have := Nat.cast_nonneg (α := ℝ) (total m); linarith) p
  rw [mul_pow] at hp
  calc
    _ ≤ ((2 : ℝ)^p*((total m : ℝ)+1)^p)*(((total m : ℝ)+1)*‖w m‖^2) :=
      mul_le_mul hp (mul_le_mul_of_nonneg_right ha (sq_nonneg _)) (by positivity) (by positivity)
    _ = _ := by rw [pow_succ (n := p)]; ring

lemma Smooth.memℓp {w : Occ → ℂ} (hw : Smooth w) : Memℓp w 2 := by
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, pow_zero, one_mul] using hw 0

/-- Strong mode actions on the completed carrier, with proved domains. -/
def ann (a : ℤ) (w : Fock) (hw : Smooth w) : Fock :=
  ⟨annCoeff a w, (hw.ann a).memℓp⟩

def cre (a : ℤ) (w : Fock) (hw : Smooth w) : Fock :=
  ⟨creCoeff a w, (hw.cre a).memℓp⟩

lemma ann_smooth (a : ℤ) (w : Fock) (hw : Smooth w) : Smooth (ann a w hw) := hw.ann a
lemma cre_smooth (a : ℤ) (w : Fock) (hw : Smooth w) : Smooth (cre a w hw) := hw.cre a

/-- Exact mode creation norm, with the usual occupation factor. -/
theorem cre_norm_sq (a : ℤ) (w : Fock) (hw : Smooth w) :
    ‖cre a w hw‖^2 = ∑' m : Occ, ((m a : ℝ)+1)*‖w m‖^2 := by
  have hs := lp.hasSum_norm (p := 2) (by norm_num) (cre a w hw)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  have hs' := ((add_e_injective a).hasSum_iff (fun m hm => by
    change ‖creCoeff a w m‖^2 = 0
    rw [creCoeff_off a w m hm]; simp)).mpr hs
  simp only [Function.comp_def] at hs'
  have he : ∀ m : Occ, ‖cre a w hw (m+e a)‖^2 = ((m a : ℝ)+1)*‖w m‖^2 := by
    intro m
    change ‖creCoeff a w (m+e a)‖^2 = _
    rw [creCoeff_add, norm_sq_sqrt_mul _ (by positivity)]
  simp only [he] at hs'
  exact hs'.tsum_eq.symm

/-- The strong mode operators have the expected adjoint pairing throughout
this invariant domain, justified by summability and an injective reindexing. -/
theorem adjoint_pairing (a : ℤ) (v w : Fock) (hv : Smooth v) (hw : Smooth w) :
    inner ℂ v (ann a w hw) = inner ℂ (cre a v hv) w := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have hs : Function.support (fun m : Occ => inner ℂ (cre a v hv m) (w m)) ⊆
      Set.range (fun n : Occ => n+e a) := by
    intro m hm
    by_contra hn
    apply hm
    change inner ℂ (creCoeff a v m) (w m) = 0
    rw [creCoeff_off a v m hn, inner_zero_left]
  rw [← (add_e_injective a).tsum_eq hs]
  apply tsum_congr
  intro m
  change inner ℂ (v m) (annCoeff a w m) = inner ℂ (creCoeff a v (m+e a)) (w (m+e a))
  rw [creCoeff_add, annCoeff]
  simp [RCLike.inner_apply, mul_comm, mul_left_comm]

/-- R32a's canonical normalized vector is in the actual invariant domain. -/
theorem normalized_smooth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (b : HilbertBasis ℤ ℂ H) (K : H →L[ℂ] H)
    (hSym : ∀ i j, Ext006CompressionR32a.coordinates b K i j = Ext006CompressionR32a.coordinates b K j i)
    (hn : ‖K‖ < 1) (hHS : TraceClass.hsSq b K ≠ ⊤) :
    Smooth (Ext006HSVacuumR32a.normalized b K hSym hn hHS) := by
  obtain ⟨t, ht, hs⟩ := Ext006NumberDomainR32a.normalized_exponential_weight b K hSym hn hHS
  intro p
  have he : Summable (fun m => t^(total m+1) *
      ‖Ext006HSVacuumR32a.normalized b K hSym hn hHS m‖^2) := by
    convert hs.mul_left t using 1
    ext m
    rw [pow_succ]
    ring
  have hp := Ext006NumberDomainR32a.summable_polynomial_of_exponential (fun m => total m+1)
    (fun m => ‖Ext006HSVacuumR32a.normalized b K hSym hn hHS m‖^2)
    (fun _ => sq_nonneg _) t ht he p
  simpa only [Nat.cast_add, Nat.cast_one] using hp

end QuantumNLS.Ext006ModeDomainR33a

#print axioms QuantumNLS.Ext006ModeDomainR33a.Smooth.ann

#print axioms QuantumNLS.Ext006ModeDomainR33a.Smooth.cre

#print axioms QuantumNLS.Ext006ModeDomainR33a.cre_norm_sq

#print axioms QuantumNLS.Ext006ModeDomainR33a.adjoint_pairing

#print axioms QuantumNLS.Ext006ModeDomainR33a.normalized_smooth

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ModeDomainR33a." then
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
  Lean.logInfo m!"Round33a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
