import QuantumNLS.BetheHigherEndpoints
import QuantumNLS.BetheContact

/-! Internal-face primitive recurrence for the literal N-body Bethe sum.
The primitive denominators are precisely those obtained by integrating
exp(i(q_j-z)t). The adjacent coefficient relation is discharged from the
source product, and the face equality is discharged by the actual plane
waves. No transfer action or cancellation relation is an input.
These are local endpoint identities; global placement regrouping is open. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheInternalFaces
open BetheWavefunctions BetheContact

/-- Literal frequency of the integrated exponential. -/
def frequency (z : ℂ) (q : ℝ) : ℂ := Complex.I * ((q : ℂ) - z)

theorem frequency_ne_zero {z : ℂ} {q : ℝ} (hz : z ≠ (q : ℂ)) :
    frequency z q ≠ 0 := mul_ne_zero Complex.I_ne_zero (sub_ne_zero.mpr hz.symm)

/-- The remaining integrated coordinates, with no degree bound or selected
particle count fixed in advance. -/
def denominator {N : ℕ} (z : ℂ) (q : Fin N → ℝ) (S : Finset (Fin N)) : ℂ :=
  ∏ i ∈ S, (frequency z (q i))⁻¹

theorem denominator_swap {N : ℕ} (z : ℂ) (q : Fin N → ℝ)
    (S : Finset (Fin N)) {a b : Fin N} (ha : a ∉ S) (hb : b ∉ S) :
    denominator z (q ∘ Equiv.swap a b) S = denominator z q S := by
  classical
  apply Finset.prod_congr rfl
  intro i hi
  have hia : i ≠ a := fun h => ha (h ▸ hi)
  have hib : i ≠ b := fun h => hb (h ▸ hi)
  simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hia hib]

/-- An actual partially integrated chamber sum, before endpoint evaluation.
At S=empty it is exactly coordinateAnsatz, with its original coefficients. -/
def primitive {N : ℕ} (c : ℝ) (q x : Fin N → ℝ) (z : ℂ)
    (S : Finset (Fin N)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin N), coefficient c (q ∘ σ) * planeWave (q ∘ σ) x *
    denominator z (q ∘ σ) S

theorem primitive_empty {N : ℕ} (c : ℝ) (q x : Fin N → ℝ) (z : ℂ) :
    primitive c q x z ∅ = coordinateAnsatz c q x := by
  simp [primitive, denominator, coordinateAnsatz]

/-- Two neighboring endpoint choices and their common higher-degree face. -/
def faceResidual {N : ℕ} (c : ℝ) (q x : Fin N → ℝ) (z : ℂ)
    (S : Finset (Fin N)) (a b : Fin N) : ℂ :=
  coefficient c q * planeWave q x * denominator z q S *
    ((frequency z (q b))⁻¹ - (frequency z (q a))⁻¹ -
      (c : ℂ) * (frequency z (q a))⁻¹ * (frequency z (q b))⁻¹)

/-- Exact internal-face cancellation of paired assignments, retaining every
other scattering factor and every remaining primitive denominator. -/
theorem faceResidual_pair {N : ℕ} (c : ℝ) (q x : Fin N → ℝ) (z : ℂ)
    (S : Finset (Fin N)) {a b : Fin N} (hadj : b.val = a.val+1)
    (hq : q a ≠ q b) (hza : z ≠ (q a : ℂ)) (hzb : z ≠ (q b : ℂ))
    (ha : a ∉ S) (hb : b ∉ S) (hx : x a = x b) :
    faceResidual c q x z S a b +
      faceResidual c (q ∘ Equiv.swap a b) x z S a b = 0 := by
  rw [faceResidual, faceResidual, denominator_swap z q S ha hb,
    planeWave_swap_wall a b q x hx]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hc := coefficient_contact c q hadj hq
  have hd : frequency z (q a) - frequency z (q b) =
      Complex.I * ((q a - q b : ℝ) : ℂ) := by
    simp only [frequency, Complex.ofReal_sub]
    ring
  rw [← hd] at hc
  have hda := frequency_ne_zero hza
  have hdb := frequency_ne_zero hzb
  field_simp [hda,hdb]
  linear_combination planeWave q x * denominator z q S * hc

/-- The full permutation sum cancels by its adjacent-position involution,
without choosing orbit representatives or inserting an extra factor two. -/
theorem sum_faceResidual_eq_zero {N : ℕ} (c : ℝ) (q x : Fin N → ℝ) (z : ℂ)
    (hq : Function.Injective q) (hz : ∀ i, z ≠ (q i : ℂ))
    (S : Finset (Fin N)) {a b : Fin N} (hadj : b.val = a.val+1)
    (ha : a ∉ S) (hb : b ∉ S) (hx : x a = x b) :
    (∑ σ : Equiv.Perm (Fin N), faceResidual c (q ∘ σ) x z S a b) = 0 := by
  classical
  let R := fun σ : Equiv.Perm (Fin N) => faceResidual c (q ∘ σ) x z S a b
  have hab : a ≠ b := by intro h; subst b; omega
  have hreindex : (∑ σ, R (swapPermutation a b σ)) = ∑ σ, R σ :=
    (swapPermutation_involutive a b).bijective.sum_comp R
  have hp : (∑ σ, (R σ + R (swapPermutation a b σ))) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    exact faceResidual_pair c (q ∘ σ) x z S hadj
      (fun h => hab (σ.injective (hq h))) (hz (σ a)) (hz (σ b)) ha hb hx
  rw [Finset.sum_add_distrib,hreindex] at hp
  change (∑ σ, R σ) = 0
  linear_combination (1/2 : ℂ) * hp

/-- Central internal-face recurrence. The difference of the two degree-k
endpoint primitives is c times their common degree-(k+1) primitive.
Every coefficient is the literal product defining the Bethe wave. -/
theorem primitive_internal_face {N : ℕ} (c : ℝ) (q x : Fin N → ℝ) (z : ℂ)
    (hq : Function.Injective q) (hz : ∀ i, z ≠ (q i : ℂ))
    (S : Finset (Fin N)) {a b : Fin N} (hadj : b.val = a.val+1)
    (ha : a ∉ S) (hb : b ∉ S) (hx : x a = x b) :
    primitive c q x z (insert b S) - primitive c q x z (insert a S) =
      (c : ℂ) * primitive c q x z (insert a (insert b S)) := by
  classical
  have hab : a ≠ b := by intro h; subst b; omega
  have h := sum_faceResidual_eq_zero c q x z hq hz S hadj ha hb hx
  have hi : a ∉ insert b S := by simp [hab,ha]
  simp only [faceResidual,mul_sub,Finset.sum_sub_distrib] at h
  simp only [primitive,denominator,Finset.prod_insert hb,Finset.prod_insert ha,
    Finset.prod_insert hi, Finset.mul_sum]
  simpa only [denominator,mul_assoc,mul_comm,mul_left_comm] using sub_eq_zero.mp h

/-- Positive-coupling source roots discharge injectivity; the only spectral
restriction is avoidance of the explicit antiderivative denominators. -/
theorem source_primitive_internal_face {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) (z : ℂ)
    (hz : ∀ i, z ≠ (BetheSmooth.sourceRoots L n c i : ℂ))
    (S : Finset (Fin N)) {a b : Fin N} (hadj : b.val = a.val+1)
    (ha : a ∉ S) (hb : b ∉ S) (hx : x a = x b) :
    primitive c (BetheSmooth.sourceRoots L n c) x z (insert b S) -
      primitive c (BetheSmooth.sourceRoots L n c) x z (insert a S) =
      (c : ℂ) * primitive c (BetheSmooth.sourceRoots L n c) x z (insert a (insert b S)) :=
  primitive_internal_face c _ x z (BetheSmooth.sourceRoots_strictAnti hL hc hn).injective
    hz S hadj ha hb hx

end QuantumNLS.BetheInternalFaces

#print axioms QuantumNLS.BetheInternalFaces.frequency
#print axioms QuantumNLS.BetheInternalFaces.frequency_ne_zero
#print axioms QuantumNLS.BetheInternalFaces.denominator
#print axioms QuantumNLS.BetheInternalFaces.denominator_swap
#print axioms QuantumNLS.BetheInternalFaces.primitive
#print axioms QuantumNLS.BetheInternalFaces.primitive_empty
#print axioms QuantumNLS.BetheInternalFaces.faceResidual
#print axioms QuantumNLS.BetheInternalFaces.faceResidual_pair
#print axioms QuantumNLS.BetheInternalFaces.sum_faceResidual_eq_zero
#print axioms QuantumNLS.BetheInternalFaces.primitive_internal_face
#print axioms QuantumNLS.BetheInternalFaces.source_primitive_internal_face
