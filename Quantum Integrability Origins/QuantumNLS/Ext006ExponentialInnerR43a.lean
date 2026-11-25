import QuantumNLS.Ext006EntireFieldR43a
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum

/-! Inner products of the literal entire field exponential sums. Unitarity
is derived from symmetry and absolute double summation, without postulating
an exponential of an unbounded operator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ExponentialInnerR43a
open Ext006BogoliubovAlg Ext006VacuumRecurrence Ext006SmoothOperatorsR34a
open Ext006StrongFieldR41a Ext006FieldBoundsR42a Ext006AnalyticFieldR42a
open Ext006EntireFieldR43a Ext006FieldClosureR42a

/-- Literal norm-convergent exponential sum when v has bounded particles. -/
def exponential (h : H) (t : ℝ) (v : D) : Fock := ∑' n, exponentialTerm h t v n

def coeff (z : ℂ) (n : ℕ) : ℂ := z^n/(n.factorial : ℂ)

lemma coeff_add (z w : ℂ) (n : ℕ) :
    (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, coeff z kl.1 * coeff w kl.2) = coeff (z+w) n := by
  unfold coeff
  rw [(Commute.all z w).add_pow',Finset.sum_div]
  apply Finset.sum_congr rfl
  intro kl hkl
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  rw [← he,nsmul_eq_mul,Nat.cast_add_choose]
  field_simp [Nat.factorial_ne_zero]

lemma inner_powers (h : H) (v w : D) (m n : ℕ) :
    inner ℂ (((field h)^m) v).1 (((field h)^n) w).1 =
      inner ℂ v.1 (((field h)^(m+n)) w).1 := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ' (field h) m]
    change inner ℂ (field h (((field h)^m) v)).1 (((field h)^n) w).1 = _
    rw [← field_symmetric]
    rw [← Module.End.mul_apply,← pow_succ' (field h) n,ih]
    rw [show m+(n+1)=m+1+n by omega]

lemma inner_terms (h : H) (s t : ℝ) (v w : D) (m n : ℕ) :
    inner ℂ (exponentialTerm h s v m) (exponentialTerm h t w n) =
      (coeff (-Complex.I*(s : ℂ)) m * coeff (Complex.I*(t : ℂ)) n) *
        inner ℂ v.1 (((field h)^(m+n)) w).1 := by
  simp only [exponentialTerm,inner_smul_left,inner_smul_right,inner_powers]
  have hc : (starRingEnd ℂ) ((Complex.I*(s : ℂ))^m/(m.factorial : ℂ)) =
      (-Complex.I*(s : ℂ))^m/(m.factorial : ℂ) := by simp
  rw [hc]
  unfold coeff
  ring

lemma sum_inner_antidiagonal (h : H) (s t : ℝ) (v w : D) (n : ℕ) :
    (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      inner ℂ (exponentialTerm h s v kl.1) (exponentialTerm h t w kl.2)) =
        inner ℂ v.1 (exponentialTerm h (t-s) w n) := by
  calc
    _ = (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        coeff (-Complex.I*(s : ℂ)) kl.1 * coeff (Complex.I*(t : ℂ)) kl.2) *
          inner ℂ v.1 (((field h)^n) w).1 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro kl hkl
      rw [inner_terms,Finset.HasAntidiagonal.mem_antidiagonal.mp hkl]
    _ = _ := by
      rw [coeff_add]
      simp only [coeff,exponentialTerm,inner_smul_right,Complex.ofReal_sub]
      congr 2
      ring

/-- A Fubini identity with the absolute convergence hypothesis proved from
actual field estimates, including arbitrary l2 smearings. -/
theorem inner_exponentials {N M : ℕ} (h : H) (s t : ℝ) (v w : D)
    (hv : ParticleBound N v.1) (hw : ParticleBound M w.1) :
    inner ℂ (exponential h s v) (exponential h t w) =
      inner ℂ v.1 (exponential h (t-s) w) := by
  have hs := entire_summable h s v hv
  have ht := entire_summable h t w hw
  have hsn := entire_norm_summable h s v hv
  have htn := entire_norm_summable h t w hw
  have hp : Summable (fun p : ℕ × ℕ =>
      inner ℂ (exponentialTerm h s v p.1) (exponentialTerm h t w p.2)) := by
    apply Summable.of_norm_bounded (hsn.mul_of_nonneg htn
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    intro p
    exact norm_inner_le_norm _ _
  have hleft : inner ℂ (exponential h s v) (exponential h t w) =
      ∑' p : ℕ × ℕ, inner ℂ (exponentialTerm h s v p.1) (exponentialTerm h t w p.2) := by
    rw [exponential,exponential,hp.tsum_prod]
    calc
      _ = ∑' m, inner ℂ (exponentialTerm h s v m) (∑' n, exponentialTerm h t w n) :=
        (innerSLFlip ℂ (∑' n,exponentialTerm h t w n)).map_tsum hs
      _ = _ := tsum_congr (fun m => (innerSL ℂ (exponentialTerm h s v m)).map_tsum ht)
  have he := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq
    (fun p : ℕ × ℕ => inner ℂ (exponentialTerm h s v p.1) (exponentialTerm h t w p.2))
  have hh := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr hp
  rw [hleft,← he]
  change Summable (fun p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n) =>
    inner ℂ (exponentialTerm h s v p.2.val.1) (exponentialTerm h t w p.2.val.2)) at hh
  change (∑' p : Σ n : ℕ, ↥(Finset.HasAntidiagonal.antidiagonal n),
    inner ℂ (exponentialTerm h s v p.2.val.1) (exponentialTerm h t w p.2.val.2)) = _
  rw [hh.tsum_sigma' (fun _ => (hasSum_fintype _).summable)]
  trans ∑' n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
    inner ℂ (exponentialTerm h s v kl.1) (exponentialTerm h t w kl.2)
  · apply tsum_congr
    intro n
    rw [tsum_fintype]
    exact Finset.sum_finset_coe
      (fun kl : ℕ × ℕ => inner ℂ (exponentialTerm h s v kl.1) (exponentialTerm h t w kl.2))
      (Finset.HasAntidiagonal.antidiagonal n)
  · simp_rw [sum_inner_antidiagonal]
    exact ((innerSL ℂ v.1).map_tsum (entire_summable h (t-s) w hw)).symm

lemma exponential_zero (h : H) (v : D) : exponential h 0 v = v.1 := by
  unfold exponential
  rw [tsum_eq_single 0]
  · simp [exponentialTerm]
  · intro n hn
    simp [exponentialTerm,zero_pow hn]

/-- Norm preservation is a consequence of the actual convergent sums. -/
theorem exponential_inner {N M : ℕ} (h : H) (t : ℝ) (v w : D)
    (hv : ParticleBound N v.1) (hw : ParticleBound M w.1) :
    inner ℂ (exponential h t v) (exponential h t w) = inner ℂ v.1 w.1 := by
  rw [inner_exponentials h t t v w hv hw,sub_self,exponential_zero]

theorem exponential_norm {N : ℕ} (h : H) (t : ℝ) (v : D)
    (hv : ParticleBound N v.1) : ‖exponential h t v‖ = ‖v.1‖ := by
  have he := exponential_inner h t v v hv hv
  rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at he
  have hr : ‖exponential h t v‖^2 = ‖v.1‖^2 := by exact_mod_cast he
  nlinarith [norm_nonneg (exponential h t v),norm_nonneg v.1]

end QuantumNLS.Ext006ExponentialInnerR43a
#print axioms QuantumNLS.Ext006ExponentialInnerR43a.inner_exponentials
#print axioms QuantumNLS.Ext006ExponentialInnerR43a.exponential_norm

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ExponentialInnerR43a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn ".").any (fun s => s == "HeldGP14Tonelli" || s == "RegularCut") then
        throwError "Held identifier in dependency closure: {n}"
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
  Lean.logInfo m!"Round43a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
