import QuantumNLS.Ext025BHaar

/-! GP-15 application maps: literal finite-support integer characters, every
finite-coordinate projection, and coordinate permutations of the full torus.
All measures are the same normalized product Haar measure. The nonlinear
LOCAL-017/R-4C2E4AC7 analytic primitive bindings remain separate obligations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open MeasureTheory
open scoped BigOperators
namespace QuantumNLS.Ext025B6TorusCoordinates
open Ext025BHaar
abbrev Torus := ℤ → Circle

def character (k : ℤ →₀ ℤ) : Torus →* Circle where
  toFun θ := ∏ n ∈ k.support, θ n ^ k n
  map_one' := by simp
  map_mul' θ φ := by simp only [Pi.mul_apply,mul_zpow,Finset.prod_mul_distrib]

theorem character_continuous (k : ℤ →₀ ℤ) : Continuous (character k) :=
  continuous_finsetProd _ fun n _ => (continuous_apply n).zpow (k n)

theorem character_at_single (k : ℤ →₀ ℤ) (n : ℤ) (z : Circle) :
    character k (Pi.mulSingle n z) = z ^ k n := by
  classical
  change (∏ j ∈ k.support, (Pi.mulSingle n z : Torus) j ^ k j) = _
  by_cases hn : n ∈ k.support
  · rw [Finset.prod_eq_single n]
    · simp
    · intro j _ hj
      simp [hj]
    · exact fun h => (h hn).elim
  · have hk : k n = 0 := Finsupp.notMem_support_iff.mp hn
    rw [hk,zpow_zero]
    apply Finset.prod_eq_one
    intro j hj
    have h : j ≠ n := fun he => hn (he ▸ hj)
    simp [h]

theorem character_trivial_iff (k : ℤ →₀ ℤ) : character k = 1 ↔ k = 0 := by
  classical
  constructor
  · intro h
    apply Finsupp.ext
    intro n
    by_contra hn
    have hk : (k n : ℝ) ≠ 0 := by exact_mod_cast hn
    have he := congrArg (fun χ : Torus →* Circle => χ (Pi.mulSingle n (Circle.exp (Real.pi / k n)))) h
    rw [character_at_single] at he
    have hx : Circle.exp (Real.pi / k n) ^ k n = Circle.exp Real.pi := by
      rw [← Circle.exp_intCast_mul]
      congr 1
      field_simp
    rw [hx] at he
    exact Circle.exp_pi_ne_one he
  · rintro rfl
    ext θ
    simp [character]

/-- Orthogonality now has the literal integer-support criterion. -/
theorem character_integral (k : ℤ →₀ ℤ) :
    (∫ θ, (character k θ : ℂ) ∂productCircleHaar) = if k = 0 then 1 else 0 := by
  rw [«FIN-EXT025-GP-15-product»,«FIN-EXT025-GP-15-character»]
  simp only [character_trivial_iff]

def coordinateProjection (F : Finset ℤ) : Torus →* (F → Circle) where
  toFun θ n := θ n.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coordinateProjection_continuous (F : Finset ℤ) : Continuous (coordinateProjection F) :=
  continuous_pi fun n => continuous_apply n.val

theorem coordinateProjection_surjective (F : Finset ℤ) : Function.Surjective (coordinateProjection F) := by
  classical
  intro φ
  refine ⟨fun n => if hn : n ∈ F then φ ⟨n,hn⟩ else 1, ?_⟩
  ext n
  simp [coordinateProjection,n.property]

/-- Every finite-coordinate marginal, with the actual coordinate map. -/
theorem coordinateProjection_haar (F : Finset ℤ) :
    MeasurePreserving (coordinateProjection F) productCircleHaar
      (normalizedHaar : Measure (F → Circle)) := by
  rw [«FIN-EXT025-GP-15-product»]
  exact «FIN-EXT025-GP-15-marginal» (coordinateProjection F)
    (coordinateProjection_continuous F) (coordinateProjection_surjective F)

def coordinatePermutation (σ : ℤ ≃ ℤ) : Torus ≃ₜ* Torus where
  toFun θ n := θ (σ n)
  invFun θ n := θ (σ.symm n)
  left_inv θ := by ext n; simp
  right_inv θ := by ext n; simp
  map_mul' _ _ := rfl
  continuous_toFun := continuous_pi fun n => continuous_apply (σ n)
  continuous_invFun := continuous_pi fun n => continuous_apply (σ.symm n)

theorem coordinatePermutation_haar (σ : ℤ ≃ ℤ) :
    MeasurePreserving (coordinatePermutation σ) productCircleHaar productCircleHaar := by
  rw [«FIN-EXT025-GP-15-product»]
  exact «FIN-EXT025-GP-15-automorphism» (coordinatePermutation σ)

/-- Inversion (angle sign reversal), with the same product normalization. -/
theorem inversion_haar : MeasurePreserving (Inv.inv : Torus → Torus) productCircleHaar productCircleHaar := by
  rw [«FIN-EXT025-GP-15-product»]
  exact «FIN-EXT025-GP-15-inversion»

end QuantumNLS.Ext025B6TorusCoordinates

#print axioms QuantumNLS.Ext025B6TorusCoordinates.character
#print axioms QuantumNLS.Ext025B6TorusCoordinates.character_continuous
#print axioms QuantumNLS.Ext025B6TorusCoordinates.character_at_single
#print axioms QuantumNLS.Ext025B6TorusCoordinates.character_trivial_iff
#print axioms QuantumNLS.Ext025B6TorusCoordinates.character_integral
#print axioms QuantumNLS.Ext025B6TorusCoordinates.coordinateProjection
#print axioms QuantumNLS.Ext025B6TorusCoordinates.coordinateProjection_continuous
#print axioms QuantumNLS.Ext025B6TorusCoordinates.coordinateProjection_surjective
#print axioms QuantumNLS.Ext025B6TorusCoordinates.coordinateProjection_haar
#print axioms QuantumNLS.Ext025B6TorusCoordinates.coordinatePermutation
#print axioms QuantumNLS.Ext025B6TorusCoordinates.coordinatePermutation_haar
#print axioms QuantumNLS.Ext025B6TorusCoordinates.inversion_haar

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B6TorusCoordinates." then
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
  Lean.logInfo m!"Ext025B6TorusCoordinates audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
