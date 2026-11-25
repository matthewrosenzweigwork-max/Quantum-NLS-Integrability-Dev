import QuantumNLS.Ext006ModeDomainR33a

/-! Arbitrary one-particle smearing on the common number domain. Square
summability of the smearing vector suffices; no finite-support restriction is
added. The estimates use summable nonnegative double series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006SmearedDomainR33a
open Occupation Ext006VacuumRecurrence Ext006QuasifreeWeak Ext006ModeDomainR33a
open Ext006BogoliubovAlg

lemma occupation_tsum (m : Occ) : ∑' a : ℤ, (m a : ℝ) = (total m : ℝ) := by
  rw [tsum_eq_sum (s := m.support) (fun a ha => by
    have hz : m a = 0 := by simpa using ha
    simp [hz])]
  exact_mod_cast (show (∑ a ∈ m.support, m a) = total m from rfl)

/-- Weighted particle-count double series is summable, before any reindexing. -/
lemma count_summable {w : Occ → ℂ} (hw : Smooth w) (p : ℕ) :
    Summable (fun z : Occ × ℤ => ((total z.1 : ℝ)+1)^p * (z.1 z.2 : ℝ)*‖w z.1‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
  constructor
  · intro m
    apply summable_of_ne_finset_zero (s := m.support)
    intro a ha
    have hz : m a = 0 := by simpa using ha
    simp [hz]
  · have he (m : Occ) : (∑' a : ℤ, ((total m : ℝ)+1)^p*(m a : ℝ)*‖w m‖^2) =
        ((total m : ℝ)+1)^p*(total m : ℝ)*‖w m‖^2 := by
      rw [tsum_mul_right, tsum_mul_left, occupation_tsum]
    simp only [he]
    apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) (hw (p+1))
    calc
      _ ≤ ((total m : ℝ)+1)^p*((total m : ℝ)+1)*‖w m‖^2 := by gcongr; linarith
      _ = _ := by rw [pow_succ (n := p)]

lemma shift_pair_injective : Function.Injective (fun z : Occ × ℤ => (z.1+e z.2,z.2)) := by
  intro x y h
  have ha := congrArg (fun z : Occ × ℤ => z.2) h
  have hm := congrArg (fun z : Occ × ℤ => z.1) h
  change x.2 = y.2 at ha
  change x.1+e x.2 = y.1+e y.2 at hm
  exact Prod.ext (add_right_cancel (by simpa only [ha] using hm)) ha

/-- Joint square summability of all annihilation coordinates, with arbitrary
polynomial number weights. -/
lemma ann_double_summable (w : Fock) (hw : Smooth w) (p : ℕ) :
    Summable (fun z : Occ × ℤ => ((total z.1 : ℝ)+1)^p * ‖annCoeff z.2 w z.1‖^2) := by
  have hs := (count_summable hw p).comp_injective shift_pair_injective
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun z => ?_) hs
  rcases z with ⟨m,a⟩
  simp only [Function.comp_def, annCoeff, total_add_e, Nat.cast_add, Nat.cast_one,
    Finsupp.add_apply, Finsupp.single_eq_same]
  rw [norm_sq_sqrt_mul _ (by positivity)]
  have hp := pow_le_pow_left₀ (show 0 ≤ (total m : ℝ)+1 by positivity)
    (show (total m : ℝ)+1 ≤ (total m : ℝ)+1+1 by linarith) p
  calc
    _ ≤ ((total m : ℝ)+1+1)^p*(((m a : ℝ)+1)*‖w (m+e a)‖^2) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by ring

/-- Annihilation smeared by any ℓ² vector, with the usual antilinear convention. -/
def smearedAnnCoeff (h : H) (w : Fock) (m : Occ) : ℂ := inner ℂ h (xvec w m)

theorem smearedAnn_smooth (h : H) (w : Fock) (hw : Smooth w) :
    Smooth (smearedAnnCoeff h w) := by
  intro p
  have hs := ((summable_prod_of_nonneg (fun _ => by positivity)).mp (ann_double_summable w hw p)).2
  have he (m : Occ) : (∑' a : ℤ, ((total m : ℝ)+1)^p*‖annCoeff a w m‖^2) =
      ((total m : ℝ)+1)^p*‖xvec w m‖^2 := by
    rw [tsum_mul_left]
    have hx := lp.hasSum_norm (p := 2) (by norm_num) (xvec w m)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx
    exact congrArg (((total m : ℝ)+1)^p*·) hx.tsum_eq
  simp only [he] at hs
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) (hs.mul_left (‖h‖^2))
  have hb : ‖smearedAnnCoeff h w m‖^2 ≤ ‖h‖^2*‖xvec w m‖^2 := by
    have hb0 : ‖inner ℂ h (xvec w m)‖ ≤ ‖h‖*‖xvec w m‖ := norm_inner_le_norm _ _
    simpa only [smearedAnnCoeff, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb0 2
  calc
    _ ≤ ((total m : ℝ)+1)^p*(‖h‖^2*‖xvec w m‖^2) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Creation's coefficient is a finite sum at each occupation, even for
infinite-support h. -/
def smearedCreCoeff (h : H) (w : Fock) (m : Occ) : ℂ :=
  ∑ a ∈ m.support, h a*creCoeff a w m

lemma cre_coefficient_bound (h : H) (w : Fock) (m : Occ) :
    ‖smearedCreCoeff h w m‖^2 ≤ (total m : ℝ)*
      ∑ a ∈ m.support, ‖h a‖^2*‖w (m-e a)‖^2 := by
  have hn := norm_sum_le m.support (fun a => h a*creCoeff a w m)
  have hn' : ‖smearedCreCoeff h w m‖^2 ≤
      (∑ a ∈ m.support, Real.sqrt (m a : ℝ)*(‖h a‖*‖w (m-e a)‖))^2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa only [smearedCreCoeff, creCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_comm, mul_left_comm, mul_assoc] using hn
  have hc := Finset.sum_mul_sq_le_sq_mul_sq m.support
    (fun a => Real.sqrt (m a : ℝ)) (fun a => ‖h a‖*‖w (m-e a)‖)
  have ht : (∑ a ∈ m.support, (m a : ℝ)) = (total m : ℝ) := by
    exact_mod_cast (show (∑ a ∈ m.support, m a) = total m from rfl)
  simp only [Real.sq_sqrt (Nat.cast_nonneg _), mul_pow, ht] at hc
  exact hn'.trans hc

/-- Summability of the majorant for creation, using the shift separately in
each mode. Empty donor occupations contribute zero. -/
lemma cre_majorant_summable (h : H) (w : Fock) (hw : Smooth w) (p : ℕ) :
    Summable (fun z : ℤ × Occ => if z.2 z.1 = 0 then 0 else
      ((total z.2 : ℝ)+1)^p*(total z.2 : ℝ)*‖h z.1‖^2*‖w (z.2-e z.1)‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => by split_ifs <;> positivity)).mpr
  have shifted (a : ℤ) : Summable (fun m : Occ =>
      ((total (m+e a) : ℝ)+1)^p*(total (m+e a) : ℝ)*‖w m‖^2) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) ((hw (p+1)).mul_left (2^p))
    simp only [total_add_e, Nat.cast_add, Nat.cast_one]
    have hp := pow_le_pow_left₀ (show 0 ≤ (total m : ℝ)+1+1 by positivity)
      (show (total m : ℝ)+1+1 ≤ 2*((total m : ℝ)+1) by have := Nat.cast_nonneg (α := ℝ) (total m); linarith) p
    rw [mul_pow] at hp
    calc
      _ ≤ (2^p*((total m : ℝ)+1)^p)*((total m : ℝ)+1)*‖w m‖^2 := by gcongr
      _ = _ := by rw [pow_succ (n := p)]; ring
  have vanish (a : ℤ) (m : Occ) (hm : m ∉ Set.range (fun n : Occ => n+e a)) : m a = 0 := by
    by_contra hz
    exact hm ⟨m-e a, tsub_add_cancel_of_le (single_le_of_donorOK (Nat.one_le_iff_ne_zero.mpr hz))⟩
  have he (a : ℤ) : (∑' m : Occ, if m a = 0 then (0 : ℝ) else
      ((total m : ℝ)+1)^p*(total m : ℝ)*‖h a‖^2*‖w (m-e a)‖^2) =
      ‖h a‖^2 * ∑' m : Occ, ((total m : ℝ)+1+1)^p*((total m : ℝ)+1)*‖w m‖^2 := by
    rw [← (add_e_injective a).tsum_eq (fun m hm => by
      by_contra hn
      exact hm (by simp [vanish a m hn]))]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, ite_false, add_tsub_cancel_right, total_add_e, Nat.cast_add, Nat.cast_one]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  constructor
  · intro a
    apply (add_e_injective a).summable_iff (fun m hm => by simp [vanish a m hm]) |>.mp
    convert (shifted a).mul_left (‖h a‖^2) using 1
    ext m
    simp only [Function.comp_def, Finsupp.add_apply, Finsupp.single_eq_same,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, add_tsub_cancel_right]
    ring
  · simp only [he]
    have hh := lp.hasSum_norm (p := 2) (by norm_num) h
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hh
    exact hh.summable.mul_right _

theorem smearedCre_smooth (h : H) (w : Fock) (hw : Smooth w) :
    Smooth (smearedCreCoeff h w) := by
  intro p
  have hs := (cre_majorant_summable h w hw p).prod_symm
  have hs' := ((summable_prod_of_nonneg (fun _ => by split_ifs <;> positivity)).mp hs).2
  have he (m : Occ) : (∑' a : ℤ, if m a = 0 then (0 : ℝ) else
      ((total m : ℝ)+1)^p*(total m : ℝ)*‖h a‖^2*‖w (m-e a)‖^2) =
      ((total m : ℝ)+1)^p*(total m : ℝ)*
        ∑ a ∈ m.support, ‖h a‖^2*‖w (m-e a)‖^2 := by
    rw [tsum_eq_sum (s := m.support) (fun a ha => by
      have hz : m a = 0 := by simpa using ha
      simp [hz])]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Finsupp.mem_support_iff.mp ha, ite_false]
    ring
  change Summable (fun m : Occ => ∑' a : ℤ, if m a = 0 then (0 : ℝ) else
    ((total m : ℝ)+1)^p*(total m : ℝ)*‖h a‖^2*‖w (m-e a)‖^2) at hs'
  simp only [he] at hs'
  apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) hs'
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (cre_coefficient_bound h w m)
    (show 0 ≤ ((total m : ℝ)+1)^p by positivity)

/-- Completed smeared operators, with no extra assumption on h. -/
def smearedAnn (h : H) (w : Fock) (hw : Smooth w) : Fock :=
  ⟨smearedAnnCoeff h w, (smearedAnn_smooth h w hw).memℓp⟩

def smearedCre (h : H) (w : Fock) (hw : Smooth w) : Fock :=
  ⟨smearedCreCoeff h w, (smearedCre_smooth h w hw).memℓp⟩

end QuantumNLS.Ext006SmearedDomainR33a

#print axioms QuantumNLS.Ext006SmearedDomainR33a.count_summable

#print axioms QuantumNLS.Ext006SmearedDomainR33a.ann_double_summable

#print axioms QuantumNLS.Ext006SmearedDomainR33a.smearedAnn_smooth

#print axioms QuantumNLS.Ext006SmearedDomainR33a.cre_coefficient_bound

#print axioms QuantumNLS.Ext006SmearedDomainR33a.cre_majorant_summable

#print axioms QuantumNLS.Ext006SmearedDomainR33a.smearedCre_smooth

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006SmearedDomainR33a." then
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
