import QuantumNLS.Ext006PhysQuasifree

/-! EXT-006, round 30a. The isometric one-particle inclusion in occupation
coordinates. This is a carrier lemma for the two-point number calculation in
fluctuations.tex:186-188; it asserts no determinant or implementer existence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace QuantumNLS.Ext006OneParticleR30a
open Occupation Ext006BogoliubovAlg
open scoped ComplexConjugate InnerProductSpace

lemma e_injective : Function.Injective (e : ℤ → Occ) :=
  Finsupp.single_left_injective one_ne_zero

def extendOne (h : ℤ → ℂ) : Occ → ℂ := Function.extend e h 0

@[simp] lemma extendOne_e (h : ℤ → ℂ) (c : ℤ) : extendOne h (e c) = h c :=
  e_injective.extend_apply h 0 c

lemma extendOne_off (h : ℤ → ℂ) (m : Occ) (hm : m ∉ Set.range (e : ℤ → Occ)) :
    extendOne h m = 0 := Function.extend_apply' (f := e) h (0 : Occ → ℂ) m hm

lemma mem_extendOne (h : H) : Memℓp (extendOne h) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  apply (e_injective.summable_iff (fun m hm => ?_)).mp
  · have hs := lp.hasSum_norm (E := fun _ : ℤ => ℂ) (p := 2) (by norm_num) h
    simpa only [Function.comp_def, extendOne_e, ENNReal.toReal_ofNat, Real.rpow_two] using hs.summable
  · rw [extendOne_off _ _ hm]; simp

/-- The one-particle sector inclusion, in the fixed free Fourier coordinates. -/
def oneParticle (h : H) : Ext006VacuumRecurrence.Fock := ⟨extendOne h, mem_extendOne h⟩

@[simp] lemma oneParticle_e (h : H) (c : ℤ) : oneParticle h (e c) = h c := extendOne_e _ _

lemma norm_oneParticle (h : H) : ‖oneParticle h‖ = ‖h‖ := by
  have hf := lp.hasSum_norm (E := fun _ : Occ => ℂ) (p := 2) (by norm_num) (oneParticle h)
  have hh := lp.hasSum_norm (E := fun _ : ℤ => ℂ) (p := 2) (by norm_num) h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hf hh
  have hs : HasSum (fun c : ℤ => ‖oneParticle h (e c)‖ ^ 2) (‖oneParticle h‖ ^ 2) :=
    (e_injective.hasSum_iff (fun m hm => by
      change ‖extendOne h m‖ ^ 2 = 0
      rw [extendOne_off _ _ hm]; simp)).mpr hf
  simp only [oneParticle_e] at hs
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hs.unique hh)

/-- Pairing with a one-particle vector restricts the other vector to unit arrays. -/
lemma inner_oneParticle (h : H) (z : Ext006VacuumRecurrence.Fock) :
    inner ℂ (oneParticle h) z = ∑' c : ℤ, conj (h c) * z (e c) := by
  rw [lp.inner_eq_tsum]
  have hs : Function.support (fun m : Occ => inner ℂ (oneParticle h m) (z m)) ⊆
      Set.range (e : ℤ → Occ) := by
    intro m hm
    by_contra hn
    apply hm
    change inner ℂ (extendOne h m) (z m) = 0
    rw [extendOne_off _ _ hn]; simp
  rw [← e_injective.tsum_eq hs]
  simp only [oneParticle_e, RCLike.inner_apply]
  congr 1; ext c; ring

lemma inner_oneParticle_right (h : H) (z : Ext006VacuumRecurrence.Fock) :
    inner ℂ z (oneParticle h) = ∑' c : ℤ, conj (z (e c)) * h c := by
  rw [lp.inner_eq_tsum]
  have hs : Function.support (fun m : Occ => inner ℂ (z m) (oneParticle h m)) ⊆
      Set.range (e : ℤ → Occ) := by
    intro m hm
    by_contra hn
    apply hm
    change inner ℂ (z m) (extendOne h m) = 0
    rw [extendOne_off _ _ hn]; simp
  rw [← e_injective.tsum_eq hs]
  simp only [oneParticle_e, RCLike.inner_apply]
  congr 1; ext c; ring

end QuantumNLS.Ext006OneParticleR30a
#print axioms QuantumNLS.Ext006OneParticleR30a.norm_oneParticle
#print axioms QuantumNLS.Ext006OneParticleR30a.inner_oneParticle

-- Audit every own declaration, including generated constants, and their full
-- proof dependencies. This is an author check, not independent acceptance.
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006OneParticleR30a." then
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
  Lean.logInfo m!"Round30a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
