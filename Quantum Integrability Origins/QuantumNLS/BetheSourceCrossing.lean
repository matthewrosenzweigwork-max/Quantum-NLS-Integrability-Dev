import QuantumNLS.BetheCrossDegreeFaces

/-! One actual internal spectator crossing, evaluated on the symmetric
source wave at arbitrary particle count. The leftover internal endpoint is
exactly the double primitive dictated by the literal coefficient product.
No eigenrelation is used. Arbitrary-block placement and outer-face results
remain frozen dependencies; global face enumeration is still open. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheSourceCrossing
open BetheWavefunctions BetheInternalFaces BetheCrossDegreeFaces BetheExtension

/-- Moving either of the two coincident coordinates gives the same physical
symmetric configuration, by the actual coordinate transposition. -/
theorem update_swap_face {N : ℕ} (x : Fin N → ℝ) {a b : Fin N}
    (hab : a ≠ b) (hx : x a = x b) (t : ℝ) :
    Function.update x b t = Function.update x a t ∘ Equiv.swap a b := by
  classical
  ext i
  by_cases hia : i = a
  · subst i
    simp only [Function.comp_apply,Equiv.swap_apply_left,
      Function.update_of_ne hab,Function.update_of_ne hab.symm]
    exact hx
  by_cases hib : i = b
  · subst i
    simp
  simp [Function.update_of_ne hia,Function.update_of_ne hib,
    Equiv.swap_apply_of_ne_of_ne hia hib]

theorem source_update_swap_face {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) {a b : Fin N} (hab : a ≠ b) (hx : x a = x b) (t : ℝ) :
    symmetricExtension L c n (Function.update x b t) =
      symmetricExtension L c n (Function.update x a t) := by
  rw [update_swap_face x hab hx t,symmetricExtension_permute]

/-- The literal integral of the actual N-body source across one spectator.
lo <= v <= hi, with the spectator fixed at v=x_a=x_b. The internal endpoint
left by the two chamber evaluations is c times the double primitive.
All other N-2 coordinates and scattering factors are retained. -/
theorem integral_source_crossing {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) {a b : Fin N} (hadj : b.val = a.val+1)
    (hx : Antitone x) (hface : x a = x b) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ))
    (u lo hi : ℝ) (hlo : lo ≤ x a) (hhi : x a ≤ hi)
    (hleft : Antitone (Function.update x b lo))
    (hright : Antitone (Function.update x a hi)) :
    (∫ t in lo..hi, Complex.exp (Complex.I*z*(u-t)) *
      symmetricExtension L c n (Function.update x a t)) =
      Complex.exp (Complex.I*z*(u-hi)) *
          primitive c (BetheSmooth.sourceRoots L n c) (Function.update x a hi) z {a} -
        Complex.exp (Complex.I*z*(u-lo)) *
          primitive c (BetheSmooth.sourceRoots L n c) (Function.update x b lo) z {b} +
        (c : ℂ) * Complex.exp (Complex.I*z*(u-x a)) *
          primitive c (BetheSmooth.sourceRoots L n c) x z {a,b} := by
  classical
  have hab : a ≠ b := by intro h; subst b; omega
  have hua : Function.update x a (x a) = x := Function.update_eq_self a x
  have hub : Function.update x b (x a) = x := by rw [hface]; exact Function.update_eq_self b x
  have hxa : Antitone (Function.update x a (x a)) := by rw [hua]; exact hx
  have hxb : Antitone (Function.update x b (x a)) := by rw [hub]; exact hx
  have hseg1 := integral_source_segment x b n z hz u lo (x a) hlo hleft hxb
  have hseg2 := integral_source_segment x a n z hz u (x a) hi hhi hxa hright
  rw [hub] at hseg1
  rw [hua] at hseg2
  have hphase : Continuous (fun t : ℝ => Complex.exp (Complex.I*z*(u-t))) := by fun_prop
  have hcont : Continuous (fun t : ℝ => Complex.exp (Complex.I*z*(u-t)) *
      symmetricExtension L c n (Function.update x a t)) :=
    hphase.mul ((continuous_symmetricExtension L c n).comp (by fun_prop))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable lo (x a)) (hcont.intervalIntegrable (x a) hi)]
  have he : (∫ t in lo..x a, Complex.exp (Complex.I*z*(u-t)) *
      symmetricExtension L c n (Function.update x a t)) =
      ∫ t in lo..x a, Complex.exp (Complex.I*z*(u-t)) *
        symmetricExtension L c n (Function.update x b t) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [source_update_swap_face L c n x hab hface]
  rw [he,hseg1,hseg2]
  have hf := source_primitive_internal_face hL hc hn x z hz ∅ hadj
    (Finset.notMem_empty a) (Finset.notMem_empty b) hface
  simp only [Finset.insert_empty] at hf
  linear_combination Complex.exp (Complex.I*z*(u-x a)) * hf

/-- The full selected-block displacement along one actual integration
coordinate. Every other selected coordinate and every spectator is fixed. -/
theorem selectedDisplacement_update {N m : ℕ} (ι : Fin m ↪ Fin N)
    (X : Fin m → ℝ) (y : Fin N → ℝ) (j : Fin m) (t : ℝ) :
    BetheHigherCancellation.selectedDisplacement ι X (Function.update y (ι j) t) =
      BetheHigherCancellation.selectedDisplacement ι X y + y (ι j) - t := by
  classical
  have he : (∑ k : Fin m, (Function.update y (ι j) t (ι k) - y (ι k))) = t-y (ι j) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      have hne : ι k ≠ ι j := fun h => hkj (ι.injective h)
      simp [Function.update_of_ne hne]
    · simp
  calc
    _ = BetheHigherCancellation.selectedDisplacement ι X y -
        ∑ k : Fin m, (Function.update y (ι j) t (ι k) - y (ι k)) := by
      simp only [BetheHigherCancellation.selectedDisplacement]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [he]; ring

/-- Actual spectator-crossing integral with the full higher-degree selected
phase, rather than a one-particle phase substituted as an assumption.
This applies to the first acted-on block via castAddEmb and to arbitrary
coordinate placements. The minus branch retains its exp(izL) multiplier
when this equality is multiplied by that scalar. -/
theorem integral_source_selected_crossing {N m : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (ι : Fin m ↪ Fin N) (X : Fin m → ℝ) (y : Fin N → ℝ)
    (j : Fin m) {b : Fin N} (hadj : b.val = (ι j).val+1)
    (hy : Antitone y) (hface : y (ι j) = y b) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ))
    (lo hi : ℝ) (hlo : lo ≤ y (ι j)) (hhi : y (ι j) ≤ hi)
    (hleft : Antitone (Function.update y b lo))
    (hright : Antitone (Function.update y (ι j) hi)) :
    (∫ t in lo..hi,
      Complex.exp (Complex.I*z*BetheHigherCancellation.selectedDisplacement ι X
        (Function.update y (ι j) t)) *
        symmetricExtension L c n (Function.update y (ι j) t)) =
      Complex.exp (Complex.I*z*(BetheHigherCancellation.selectedDisplacement ι X y + y (ι j)-hi)) *
        primitive c (BetheSmooth.sourceRoots L n c) (Function.update y (ι j) hi) z {ι j} -
      Complex.exp (Complex.I*z*(BetheHigherCancellation.selectedDisplacement ι X y + y (ι j)-lo)) *
        primitive c (BetheSmooth.sourceRoots L n c) (Function.update y b lo) z {b} +
      (c : ℂ) * Complex.exp (Complex.I*z*BetheHigherCancellation.selectedDisplacement ι X y) *
        primitive c (BetheSmooth.sourceRoots L n c) y z {ι j,b} := by
  simp_rw [selectedDisplacement_update]
  have h := integral_source_crossing hL hc hn y hadj hy hface z hz
    (BetheHigherCancellation.selectedDisplacement ι X y + y (ι j)) lo hi hlo hhi hleft hright
  simpa only [Complex.ofReal_add,Complex.ofReal_sub,add_sub_cancel_right] using h

/-- The local recurrence with the physical degree-m and degree-(m+1)
coefficients before factorial cancellation. The same total count is m+q+1.
This verifies scalar matching once a global regrouping supplies q+1 lower
faces per higher face; that enumeration remains an explicit open task. -/
theorem source_physical_coefficients_face (r q : ℕ) {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin ((r+1)+(q+1)) → ℤ} (hn : Antitone n)
    (x : Fin ((r+1)+(q+1)) → ℝ) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ))
    (S : Finset (Fin ((r+1)+(q+1)))) {a b : Fin ((r+1)+(q+1))}
    (hadj : b.val = a.val+1) (ha : a ∉ S) (hb : b ∉ S) (hx : x a = x b) :
    (((q+1 : ℕ) : ℂ) *
      (((c^(r+1) * ((r+1)+(q+1)).descFactorial (r+1) : ℝ) : ℂ) * (((r+1)+(q+1)).factorial : ℂ)⁻¹)) *
      (primitive c (BetheSmooth.sourceRoots L n c) x z (insert b S) -
        primitive c (BetheSmooth.sourceRoots L n c) x z (insert a S)) -
      (((c^((r+1)+1) * ((r+1)+(q+1)).descFactorial ((r+1)+1) : ℝ) : ℂ) *
        (((r+1)+(q+1)).factorial : ℂ)⁻¹) *
        primitive c (BetheSmooth.sourceRoots L n c) x z (insert a (insert b S)) = 0 := by
  have he : (r+1)+(q+1) = ((r+1)+1)+q := by omega
  have hlow := BetheHigherPlacement.coefficient_normalization (r+1) (q+1) c
  have hhigh := BetheHigherPlacement.coefficient_normalization ((r+1)+1) q c
  rw [← he] at hhigh
  rw [hlow,hhigh]
  simpa only [mul_assoc] using
    source_neighboring_degree_face hL hc hn x z hz S hadj ha hb hx (r+1) q

end QuantumNLS.BetheSourceCrossing

#print axioms QuantumNLS.BetheSourceCrossing.update_swap_face
#print axioms QuantumNLS.BetheSourceCrossing.source_update_swap_face
#print axioms QuantumNLS.BetheSourceCrossing.integral_source_crossing
#print axioms QuantumNLS.BetheSourceCrossing.selectedDisplacement_update
#print axioms QuantumNLS.BetheSourceCrossing.integral_source_selected_crossing
#print axioms QuantumNLS.BetheSourceCrossing.source_physical_coefficients_face

#check QuantumNLS.BetheInternalFaces.primitive_internal_face
#check QuantumNLS.BetheCrossDegreeFaces.integral_source_segment
#check QuantumNLS.BetheSourceCrossing.integral_source_crossing
#check QuantumNLS.BetheSourceCrossing.integral_source_selected_crossing
#check QuantumNLS.BetheSourceCrossing.source_physical_coefficients_face

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BetheSourceCrossing.integral_source_selected_crossing,
    ``QuantumNLS.BetheSourceCrossing.source_physical_coefficients_face]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[``QuantumNLS.BetheWavefunctions.coefficient,
      ``QuantumNLS.BetheWavefunctions.factor_contact,
      ``QuantumNLS.BetheContact.coefficient_split,
      ``QuantumNLS.BetheContact.spectator_swap,
      ``QuantumNLS.BetheContact.coefficient_contact,
      ``QuantumNLS.BetheContact.planeWave_swap_wall,
      ``QuantumNLS.BetheInternalFaces.denominator_swap,
      ``QuantumNLS.BetheInternalFaces.faceResidual_pair,
      ``QuantumNLS.BetheInternalFaces.sum_faceResidual_eq_zero,
      ``QuantumNLS.BetheInternalFaces.primitive_internal_face,
      ``QuantumNLS.BetheInternalFaces.source_primitive_internal_face,
      ``QuantumNLS.BetheCrossDegreeFaces.planeWave_update,
      ``QuantumNLS.BetheCrossDegreeFaces.integral_planeWave_update,
      ``QuantumNLS.BetheCrossDegreeFaces.integral_primitive_update,
      ``QuantumNLS.BetheCrossDegreeFaces.antitone_update_between,
      ``QuantumNLS.BetheCrossDegreeFaces.integral_source_segment,
      ``QuantumNLS.BetheCrossDegreeFaces.source_neighboring_degree_face,
      ``QuantumNLS.BetheSourceCrossing.update_swap_face,
      ``QuantumNLS.BetheSourceCrossing.source_update_swap_face,
      ``QuantumNLS.BetheSourceCrossing.integral_source_crossing,
      ``QuantumNLS.BetheSourceCrossing.selectedDisplacement_update,
      ``QuantumNLS.BetheHigherCancellation.selectedDisplacement,
      ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
      ``QuantumNLS.BetheExtension.symmetricExtension_eq,
      ``QuantumNLS.BetheExtension.symmetricExtension_permute,
      ``QuantumNLS.BetheExtension.continuous_symmetricExtension,
      ``QuantumNLS.BetheSmooth.sourceRoots_strictAnti,
      ``integral_exp_mul_complex,
      ``intervalIntegral.integral_add_adjacent_intervals] do
    unless seen.contains n do
      throwError "Internal-face route missing literal ingredient: {n}"
  for n in seen do
    if n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" then
      throwError "Internal-face route used special-particle action: {n}"
  Lean.logInfo m!"Internal-face source route PASS: {seen.size} transitive constants; literal coefficient product, spectator swap, paired permutation sum, ordinary interval integrals, actual symmetric source crossing, arbitrary selected displacement, positive neighboring degrees and exact factorial coefficients. Global face enumeration and allN transfer eigenrelation/basis OPEN."
