import QuantumNLS.BetheWavefunctions
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
General-N adjacent contact identities for the literal finite Bethe ansatz.
Source: foundations/periodic_basis.tex:206--226, equations swap and contact.
Frozen input: BetheWavefunctions 105a85c6; no frozen dependency is edited.
The wall identity below concerns the smooth finite chamber formula on real
coordinates. Periodic gluing, a symmetric H1 extension, the operator domain,
orthogonality, completeness, and U5 are separate obligations.
-/

noncomputable section
open scoped BigOperators

namespace QuantumNLS.BetheContact
open BetheWavefunctions

/-- The pairs occurring once in the literal coefficient product. -/
def orderedPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1 < p.2)

theorem coefficient_eq_pairs {N : ℕ} (c : ℝ) (q : Fin N → ℝ) :
    coefficient c q = ∏ p ∈ orderedPairs N, factor c (q p.1) (q p.2) := by
  simp [coefficient, orderedPairs, Finset.prod_filter, Fintype.prod_prod_type]

/-- All factors except the one for the designated wall. -/
def spectator {N : ℕ} (c : ℝ) (q : Fin N → ℝ) (a b : Fin N) : ℂ :=
  ∏ p ∈ (orderedPairs N).erase (a, b), factor c (q p.1) (q p.2)

theorem coefficient_split {N : ℕ} (c : ℝ) (q : Fin N → ℝ)
    {a b : Fin N} (hab : a < b) :
    coefficient c q = spectator c q a b * factor c (q a) (q b) := by
  rw [coefficient_eq_pairs, spectator]
  exact (Finset.prod_erase_mul _ _ (by simp [orderedPairs, hab])).symm

/-- An adjacent position swap preserves the order of every other pair. -/
theorem swap_pair_mem {N : ℕ} {a b : Fin N} (hadj : b.val = a.val + 1)
    (p : Fin N × Fin N) (hp : p ∈ (orderedPairs N).erase (a, b)) :
    (Equiv.swap a b p.1, Equiv.swap a b p.2) ∈ (orderedPairs N).erase (a, b) := by
  rcases p with ⟨i, j⟩
  simp only [Finset.mem_erase, orderedPairs, Finset.mem_filter, Finset.mem_univ,
    true_and] at hp ⊢
  simp only [Equiv.swap_apply_def]
  split_ifs <;> subst_vars <;>
    simp_all [Prod.mk.injEq, Fin.lt_def, Fin.ext_iff, -Fin.val_fin_lt] <;> omega

theorem spectator_swap {N : ℕ} (c : ℝ) (q : Fin N → ℝ)
    {a b : Fin N} (hadj : b.val = a.val + 1) :
    spectator c (q ∘ Equiv.swap a b) a b = spectator c q a b := by
  classical
  unfold spectator
  refine Finset.prod_bij' (fun p _ => (Equiv.swap a b p.1, Equiv.swap a b p.2))
    (fun p _ => (Equiv.swap a b p.1, Equiv.swap a b p.2))
    (fun p hp => swap_pair_mem hadj p hp) (fun p hp => swap_pair_mem hadj p hp)
    (fun p _ => ?_) (fun p _ => ?_) (fun p _ => rfl) <;> simp

/-- Both literal coefficients share precisely the same spectator product. -/
theorem coefficient_swap_split {N : ℕ} (c : ℝ) (q : Fin N → ℝ)
    {a b : Fin N} (hadj : b.val = a.val + 1) :
    coefficient c (q ∘ Equiv.swap a b) = spectator c q a b * factor c (q b) (q a) := by
  have hab : a < b := by simpa only [Fin.lt_def] using (show a.val < b.val by omega)
  rw [coefficient_split c _ hab, spectator_swap c q hadj]
  simp

/-- The general-N form of the source's second adjacent-swap identity. -/
theorem coefficient_contact {N : ℕ} (c : ℝ) (q : Fin N → ℝ)
    {a b : Fin N} (hadj : b.val = a.val + 1) (hq : q a ≠ q b) :
    Complex.I * ((q a - q b : ℝ) : ℂ) *
        (coefficient c q - coefficient c (q ∘ Equiv.swap a b)) =
      (c : ℂ) * (coefficient c q + coefficient c (q ∘ Equiv.swap a b)) := by
  have hab : a < b := by simpa only [Fin.lt_def] using (show a.val < b.val by omega)
  rw [coefficient_swap_split c q hadj, coefficient_split c q hab]
  linear_combination spectator c q a b * factor_contact c (q a) (q b) hq

/-- The source's coefficient ratio, with its literal sign convention. -/
theorem coefficient_swap_ratio {N : ℕ} (c : ℝ) (q : Fin N → ℝ)
    {a b : Fin N} (hadj : b.val = a.val + 1) (hq : q a ≠ q b) :
    coefficient c (q ∘ Equiv.swap a b) / coefficient c q =
      (((q a - q b : ℝ) : ℂ) + Complex.I * (c : ℂ)) /
        (((q a - q b : ℝ) : ℂ) - Complex.I * (c : ℂ)) := by
  have hd : (((q a - q b : ℝ) : ℂ) - Complex.I * (c : ℂ)) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, Complex.zero_re] at hr
    exact hq (sub_eq_zero.mp hr)
  apply (div_eq_div_iff (coefficient_ne_zero c q) hd).mpr
  have h := congrArg (fun z : ℂ => -Complex.I * z) (coefficient_contact c q hadj hq)
  ring_nf at h ⊢
  simp only [Complex.I_sq] at h
  linear_combination -h

/-- The relative-coordinate line has velocity e_a-e_b. Its parameter r
changes x_a-x_b by 2r, hence yields the source partial_a-partial_b. -/
def wallDirection {N : ℕ} (a b : Fin N) (i : Fin N) : ℝ :=
  (if i = a then 1 else 0) - (if i = b then 1 else 0)

def wallLine {N : ℕ} (a b : Fin N) (x : Fin N → ℝ) (r : ℝ) : Fin N → ℝ :=
  fun i => x i + r * wallDirection a b i

theorem wallLine_zero {N : ℕ} (a b : Fin N) (x : Fin N → ℝ) :
    wallLine a b x 0 = x := by
  funext i
  simp [wallLine]

theorem wallLine_left {N : ℕ} {a b : Fin N} (hab : a ≠ b)
    (x : Fin N → ℝ) (r : ℝ) : wallLine a b x r a = x a + r := by
  simp [wallLine, wallDirection, hab]

theorem wallLine_right {N : ℕ} {a b : Fin N} (hab : a ≠ b)
    (x : Fin N → ℝ) (r : ℝ) : wallLine a b x r b = x b - r := by
  simp [wallLine, wallDirection, hab.symm, sub_eq_add_neg]

theorem wallLine_spectator {N : ℕ} {a b i : Fin N} (hia : i ≠ a) (hib : i ≠ b)
    (x : Fin N → ℝ) (r : ℝ) : wallLine a b x r i = x i := by
  simp [wallLine, wallDirection, hia, hib]

theorem frequency_wallDirection {N : ℕ} (a b : Fin N) (q : Fin N → ℝ) :
    (∑ i, q i * wallDirection a b i) = q a - q b := by
  classical
  simp [wallDirection, mul_sub, mul_ite, Finset.sum_sub_distrib]

theorem frequency_wallLine {N : ℕ} (a b : Fin N) (q x : Fin N → ℝ) (r : ℝ) :
    (∑ i, q i * wallLine a b x r i) = (∑ i, q i * x i) + r * (q a - q b) := by
  simp only [wallLine, mul_add, Finset.sum_add_distrib]
  congr 1
  simp_rw [show ∀ i, q i * (r * wallDirection a b i) =
    r * (q i * wallDirection a b i) from fun i => by ring]
  rw [← Finset.mul_sum, frequency_wallDirection]

/-- On a collision wall the paired plane waves agree, including spectators. -/
theorem planeWave_swap_wall {N : ℕ} (a b : Fin N) (q x : Fin N → ℝ)
    (hx : x a = x b) : planeWave (q ∘ Equiv.swap a b) x = planeWave q x := by
  have hs (i : Fin N) : x (Equiv.swap a b i) = x i := by
    by_cases hi : i = a
    · subst i; simpa using hx.symm
    by_cases hj : i = b
    · subst i; simpa using hx
    simp [Equiv.swap_apply_of_ne_of_ne hi hj]
  unfold planeWave
  apply congrArg (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)))
  exact Fintype.sum_equiv (Equiv.swap a b) _ _ (fun i => by simp [hs])

/-- The actual directional derivative of each plane wave. -/
theorem planeWave_wall_hasDerivAt {N : ℕ} (a b : Fin N) (q x : Fin N → ℝ) :
    HasDerivAt (fun r : ℝ => planeWave q (wallLine a b x r))
      (Complex.I * ((q a - q b : ℝ) : ℂ) * planeWave q x) 0 := by
  have hd : HasDerivAt (fun r : ℝ => (∑ i, q i * x i) + r * (q a - q b))
      (q a - q b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (q a - q b)).const_add
      (∑ i, q i * x i)
  have hdc := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hd
  simpa [planeWave, frequency_wallLine, Function.comp_def, mul_comm] using
    (hdc.const_mul Complex.I).cexp

/-- Position pairing on the permutation sum: sigma is followed by swapping
the two adjacent positions, so every spectator rapidity stays in the tuple. -/
def swapPermutation {N : ℕ} (a b : Fin N) (σ : Equiv.Perm (Fin N)) :
    Equiv.Perm (Fin N) := (Equiv.swap a b).trans σ

theorem swapPermutation_involutive {N : ℕ} (a b : Fin N) :
    Function.Involutive (swapPermutation a b) := by
  intro σ
  ext i
  simp [swapPermutation]

theorem swapPermutation_ne {N : ℕ} {a b : Fin N} (hab : a ≠ b)
    (σ : Equiv.Perm (Fin N)) : swapPermutation a b σ ≠ σ := by
  intro h
  have hh : σ b = σ a := by
    simpa [swapPermutation] using congrArg (fun τ : Equiv.Perm (Fin N) => τ a) h
  exact hab (σ.injective hh).symm

/-- One term's directional derivative minus c times its wall value. -/
def contactResidual {N : ℕ} (c : ℝ) (q x : Fin N → ℝ) (a b : Fin N) : ℂ :=
  (coefficient c q * (Complex.I * ((q a - q b : ℝ) : ℂ)) -
    (c : ℂ) * coefficient c q) * planeWave q x

/-- The exact two-term cancellation at an adjacent collision wall. -/
theorem contactResidual_pair {N : ℕ} (c : ℝ) (q x : Fin N → ℝ)
    {a b : Fin N} (hadj : b.val = a.val + 1) (hq : q a ≠ q b)
    (hx : x a = x b) :
    contactResidual c q x a b + contactResidual c (q ∘ Equiv.swap a b) x a b = 0 := by
  unfold contactResidual
  rw [planeWave_swap_wall a b q x hx]
  simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hd : ((q b - q a : ℝ) : ℂ) = -((q a - q b : ℝ) : ℂ) := by push_cast; ring
  rw [hd]
  linear_combination planeWave q x * coefficient_contact c q hadj hq

/-- The finite permutation sum of contact defects vanishes by its explicit
fixed-point-free involution; no boundary equation is assumed as a premise. -/
theorem sum_contactResidual_eq_zero {N : ℕ} (c : ℝ) (q x : Fin N → ℝ)
    (hq : Function.Injective q) {a b : Fin N} (hadj : b.val = a.val + 1)
    (hx : x a = x b) :
    (∑ σ : Equiv.Perm (Fin N), contactResidual c (q ∘ σ) x a b) = 0 := by
  classical
  let R := fun σ : Equiv.Perm (Fin N) => contactResidual c (q ∘ σ) x a b
  have hab : a ≠ b := by intro h; subst b; omega
  have hreindex : (∑ σ, R (swapPermutation a b σ)) = ∑ σ, R σ :=
    (swapPermutation_involutive a b).bijective.sum_comp R
  have hpair : (∑ σ, (R σ + R (swapPermutation a b σ))) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    exact contactResidual_pair c (q ∘ σ) x hadj
      (fun h => hab (σ.injective (hq h))) hx
  rw [Finset.sum_add_distrib, hreindex] at hpair
  change (∑ σ, R σ) = 0
  linear_combination (1 / 2 : ℂ) * hpair

/-- General-N contact-wall identity for the actual finite ansatz. Along
x+r(e_a-e_b), the derivative at a wall is c times the boundary value.
The statement holds at all real wall points, hence on every adjacent face
of the closed source chamber, including intersections of collision walls. -/
theorem coordinateAnsatz_contact_hasDerivAt {N : ℕ} (c : ℝ) (q x : Fin N → ℝ)
    (hq : Function.Injective q) {a b : Fin N} (hadj : b.val = a.val + 1)
    (hx : x a = x b) :
    HasDerivAt (fun r : ℝ => coordinateAnsatz c q (wallLine a b x r))
      ((c : ℂ) * coordinateAnsatz c q x) 0 := by
  classical
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun σ (_ : σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin N)))) =>
      (planeWave_wall_hasDerivAt a b (q ∘ σ) x).const_mul (coefficient c (q ∘ σ)))
  have he : (∑ σ : Equiv.Perm (Fin N), coefficient c (q ∘ σ) *
      (Complex.I * (((q ∘ σ) a - (q ∘ σ) b : ℝ) : ℂ) * planeWave (q ∘ σ) x)) =
      (c : ℂ) * coordinateAnsatz c q x := by
    have hz := sum_contactResidual_eq_zero c q x hq hadj hx
    simp only [contactResidual, sub_mul, Finset.sum_sub_distrib] at hz
    apply sub_eq_zero.mp
    simpa only [coordinateAnsatz, Finset.mul_sum, mul_assoc] using hz
  rw [he] at hd
  exact hd

/-- Specialization to the roots already constructed and proved strictly
decreasing. The caller supplies no contact or regularity assumption. -/
theorem wavefunction_contact_hasDerivAt {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) {a b : Fin N} (hadj : b.val = a.val + 1)
    (hx : x a = x b) :
    HasDerivAt (fun r : ℝ => wavefunction L c n (wallLine a b x r))
      ((c : ℂ) * wavefunction L c n x) 0 := by
  exact coordinateAnsatz_contact_hasDerivAt c (BetheSmooth.sourceRoots L n c) x
    (BetheSmooth.sourceRoots_strictAnti hL hc hn).injective hadj hx

/-- With the actual relative separation as parameter, x_a and x_b move
by r/2 and -r/2, respectively. The source contact coefficient is then c/2. -/
theorem coordinateAnsatz_contact_half_hasDerivAt {N : ℕ} (c : ℝ) (q x : Fin N → ℝ)
    (hq : Function.Injective q) {a b : Fin N} (hadj : b.val = a.val + 1)
    (hx : x a = x b) :
    HasDerivAt (fun r : ℝ => coordinateAnsatz c q (wallLine a b x (r / 2)))
      (((c / 2 : ℝ) : ℂ) * coordinateAnsatz c q x) 0 := by
  have hs : HasDerivAt (fun r : ℝ => r / 2) (1 / 2 : ℝ) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
  have hd := (coordinateAnsatz_contact_hasDerivAt c q x hq hadj hx).scomp_of_eq 0 hs (by norm_num)
  simpa [Function.comp_def, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm,
    div_eq_mul_inv] using hd

theorem wavefunction_contact_half_hasDerivAt {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) {a b : Fin N} (hadj : b.val = a.val + 1)
    (hx : x a = x b) :
    HasDerivAt (fun r : ℝ => wavefunction L c n (wallLine a b x (r / 2)))
      (((c / 2 : ℝ) : ℂ) * wavefunction L c n x) 0 := by
  exact coordinateAnsatz_contact_half_hasDerivAt c (BetheSmooth.sourceRoots L n c) x
    (BetheSmooth.sourceRoots_strictAnti hL hc hn).injective hadj hx

end QuantumNLS.BetheContact

#print axioms QuantumNLS.BetheContact.orderedPairs
#print axioms QuantumNLS.BetheContact.coefficient_eq_pairs
#print axioms QuantumNLS.BetheContact.spectator
#print axioms QuantumNLS.BetheContact.coefficient_split
#print axioms QuantumNLS.BetheContact.swap_pair_mem
#print axioms QuantumNLS.BetheContact.spectator_swap
#print axioms QuantumNLS.BetheContact.coefficient_swap_split
#print axioms QuantumNLS.BetheContact.coefficient_contact
#print axioms QuantumNLS.BetheContact.coefficient_swap_ratio
#print axioms QuantumNLS.BetheContact.wallDirection
#print axioms QuantumNLS.BetheContact.wallLine
#print axioms QuantumNLS.BetheContact.wallLine_zero
#print axioms QuantumNLS.BetheContact.wallLine_left
#print axioms QuantumNLS.BetheContact.wallLine_right
#print axioms QuantumNLS.BetheContact.wallLine_spectator
#print axioms QuantumNLS.BetheContact.frequency_wallDirection
#print axioms QuantumNLS.BetheContact.frequency_wallLine
#print axioms QuantumNLS.BetheContact.planeWave_swap_wall
#print axioms QuantumNLS.BetheContact.planeWave_wall_hasDerivAt
#print axioms QuantumNLS.BetheContact.swapPermutation
#print axioms QuantumNLS.BetheContact.swapPermutation_involutive
#print axioms QuantumNLS.BetheContact.swapPermutation_ne
#print axioms QuantumNLS.BetheContact.contactResidual
#print axioms QuantumNLS.BetheContact.contactResidual_pair
#print axioms QuantumNLS.BetheContact.sum_contactResidual_eq_zero
#print axioms QuantumNLS.BetheContact.coordinateAnsatz_contact_hasDerivAt
#print axioms QuantumNLS.BetheContact.wavefunction_contact_hasDerivAt
#print axioms QuantumNLS.BetheContact.coordinateAnsatz_contact_half_hasDerivAt
#print axioms QuantumNLS.BetheContact.wavefunction_contact_half_hasDerivAt
