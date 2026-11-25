import QuantumNLS.Ext006CoreLimit

/-! EXT-006, R31a: construct the formal squeezed vacuum without supplying a vacuum.
The coefficients are literal finite-core exponential coefficients. Compatibility
under enlargement of the mode set is proved, so their global weak recurrence
needs only symmetry of K. No analytic convergence or implementer is postulated.
The final equivalence isolates, rather than assumes, the remaining convergence
obligation for constructing a normalized occupation Fock vacuum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.Ext006FormalVacuumR31a
open Occupation OccupationHilbert Ext006VacuumRecurrence Ext006CoreLimit

variable {K : Kernel}

/-- Literal finite-core exponentials agree on occupations in the smaller set. -/
theorem Y_compatible (hK : ∀ a b, K a b = K b a) {S T : Finset ℤ}
    (hST : S ⊆ T) (m : Occ) (hm : m.support ⊆ S) : Y S K m = Y T K m := by
  have hS : LocalVac S K (Y S K) := Y_local S K (fun a _ b _ => hK a b)
  have hT : LocalVac S K (Y T K) := by
    intro a ha n hn
    exact Y_local T K (fun a _ b _ => hK a b) a (hST ha) n (hn.trans hST)
  have hz := local_zero S K (hS.sub hT) (by simp [Y_zero]) m hm
  exact sub_eq_zero.mp hz

/-- The coefficient is computed using only the finite support of its occupation.
This definition does not take a vacuum, HS bound, norm bound or summability. -/
def coefficient (K : Kernel) (m : Occ) : ℂ := Y m.support K m

theorem coefficient_eq_Y (hK : ∀ a b, K a b = K b a)
    (S : Finset ℤ) (m : Occ) (hm : m.support ⊆ S) : coefficient K m = Y S K m :=
  Y_compatible hK hm m (Finset.Subset.refl _)

theorem coefficient_zero (K : Kernel) : coefficient K 0 = 1 := Y_zero _ K

lemma support_sub_e (m : Occ) (a : ℤ) : (m - e a).support ⊆ m.support := by
  intro c hc
  rw [Finsupp.mem_support_iff] at hc ⊢
  intro hz
  apply hc
  simp [Finsupp.tsub_apply, hz]

lemma support_add_e (m : Occ) (a : ℤ) : (m + e a).support ⊆ insert a m.support := by
  classical
  intro c hc
  by_cases hca : c = a
  · simp [hca]
  · have hm : m c ≠ 0 := by
      rw [Finsupp.mem_support_iff] at hc
      simpa [Finsupp.add_apply, e, Finsupp.single_apply, hca] using hc
    exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hm)

/-- Algebraic existence of all coefficients, with the exact minus sign of
exp(-a*(K)/2). This is not an assertion that the coefficients are in Fock space. -/
theorem coefficient_weak (hK : ∀ a b, K a b = K b a) : WeakVacuum K (coefficient K) := by
  classical
  intro a m
  let S := insert a m.support
  have hm : m.support ⊆ S := Finset.subset_insert _ _
  have h := Y_local S K (fun i _ j _ => hK i j) a (Finset.mem_insert_self _ _) m hm
  rw [coefficient_eq_Y hK S (m + e a) (support_add_e m a)]
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [coefficient_eq_Y hK S (m - e b) ((support_sub_e m b).trans hm)]

/-- Every formal weak vacuum is a scalar multiple of the constructed coefficient
function. No Fock membership or existence premise is used. -/
theorem weak_eq_coefficient (hK : ∀ a b, K a b = K b a)
    {x : Occ → ℂ} (hx : WeakVacuum K x) (m : Occ) :
    x m = x 0 * coefficient K m :=
  core_eq m.support K (fun a _ b _ => hK a b) hx m (Finset.Subset.refl _)

theorem coefficient_odd (K : Kernel) {m : Occ} (hm : ¬ Even (total m)) :
    coefficient K m = 0 := Y_of_odd _ K hm

/-- In every degree, these are the literal factorial-normalized finite-core
pair-exponential coefficients, independent of the chosen surrounding modes. -/
theorem coefficient_even (hK : ∀ a b, K a b = K b a)
    (S : Finset ℤ) (m : Occ) (hm : m.support ⊆ S) {n : ℕ} (hn : total m = 2*n) :
    coefficient K m = Ext006PairCoreCommutator.coreTerm S K n m := by
  rw [coefficient_eq_Y hK S m hm, Y_of_even S K hn]

lemma mem_coefficient_iff (K : Kernel) :
    Memℓp (coefficient K) 2 ↔ Summable (fun m => ‖coefficient K m‖^2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (memℓp_gen_iff (p := 2) (by norm_num) (f := coefficient K))

/-- Construct an actual occupation Fock vector when its explicitly constructed
coefficients are square summable. The separate HS-to-summability proof is open. -/
def vector (K : Kernel) (hs : Summable (fun m => ‖coefficient K m‖^2)) : Fock :=
  ⟨coefficient K, (mem_coefficient_iff K).mpr hs⟩

theorem vector_apply (K : Kernel) (hs : Summable (fun m => ‖coefficient K m‖^2)) (m : Occ) :
    vector K hs m = coefficient K m := rfl

theorem vector_ne_zero (K : Kernel) (hs : Summable (fun m => ‖coefficient K m‖^2)) :
    vector K hs ≠ 0 := by
  intro hz
  have h := congrArg (fun x : Fock => x 0) hz
  change coefficient K 0 = 0 at h
  rw [coefficient_zero] at h
  exact one_ne_zero h

theorem vector_weak (hK : ∀ a b, K a b = K b a)
    (hs : Summable (fun m => ‖coefficient K m‖^2)) : WeakVacuum K (vector K hs) :=
  coefficient_weak hK

/-- Exact existence criterion. This is an equivalence, not a replacement for the
source's HS hypothesis: the implication from HS and norm<1 remains to be proved. -/
theorem exists_normalized_iff (hK : ∀ a b, K a b = K b a) :
    (∃ x : Fock, WeakVacuum K x ∧ ‖x‖ = 1) ↔
      Summable (fun m => ‖coefficient K m‖^2) := by
  constructor
  · rintro ⟨x, hx, hn⟩
    have h0 := vacuum_coefficient_ne_zero hx hn
    have he : coefficient K = fun m => (x 0)⁻¹ * x m := by
      funext m
      rw [weak_eq_coefficient hK hx m, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    rw [he]
    have hs : Summable (fun m : Occ => ‖x m‖^2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
        (lp.hasSum_norm (p := 2) (by norm_num) x).summable
    simpa only [norm_mul, mul_pow] using hs.mul_left (‖(x 0)⁻¹‖^2)
  · intro hs
    let x := vector K hs
    have hx : x ≠ 0 := vector_ne_zero K hs
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    refine ⟨(‖x‖⁻¹ : ℂ) • x, (vector_weak hK hs).smul _, ?_⟩
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ hn]

end QuantumNLS.Ext006FormalVacuumR31a

#print axioms QuantumNLS.Ext006FormalVacuumR31a.Y_compatible
#print axioms QuantumNLS.Ext006FormalVacuumR31a.coefficient_weak
#print axioms QuantumNLS.Ext006FormalVacuumR31a.weak_eq_coefficient
#print axioms QuantumNLS.Ext006FormalVacuumR31a.coefficient_even
#print axioms QuantumNLS.Ext006FormalVacuumR31a.exists_normalized_iff

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006FormalVacuumR31a." then
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
  Lean.logInfo m!"Round31a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
