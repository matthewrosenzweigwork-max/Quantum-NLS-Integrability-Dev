import QuantumNLS.BethePeriodic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
The symmetric extension of the literal chamber ansatz, followed by periodic
extension using representatives in [0,L). Source: periodic_basis.tex:24--41,
206--259. Frozen inputs: BetheContact 533c6df6, BethePeriodic b88ca2db.
Continuity and face compatibility are constituents of the source H1 argument;
weak integration by parts and H1 membership are separate obligations.
No operator-domain, normalization, completeness or U5 assertion is made.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace QuantumNLS.BetheExtension
open BetheWavefunctions BetheContact BethePeriodic

/-- The decreasing rearrangement retains every coordinate with multiplicity. -/
def decreasing {N : ℕ} (x : Fin N → ℝ) : Fin N → ℝ :=
  x ∘ Tuple.sort (α := ℝᵒᵈ) x

theorem decreasing_antitone {N : ℕ} (x : Fin N → ℝ) : Antitone (decreasing x) :=
  Tuple.monotone_sort (α := ℝᵒᵈ) x

theorem decreasing_eq {N : ℕ} {x : Fin N → ℝ} (hx : Antitone x) :
    decreasing x = x := by
  exact Tuple.unique_antitone (σ := Tuple.sort (α := ℝᵒᵈ) x)
    (τ := Equiv.refl _) (decreasing_antitone x) hx

theorem decreasing_permute {N : ℕ} (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    decreasing (x ∘ σ) = decreasing x :=
  Tuple.comp_perm_comp_sort_eq_comp_sort (α := ℝᵒᵈ)

theorem decreasing_eq_permute {N : ℕ} (x : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) (hσ : Antitone (x ∘ σ)) :
    decreasing x = x ∘ σ :=
  Tuple.unique_antitone (decreasing_antitone x) hσ

/-- Closed ordering regions cover all real tuples, including multiple walls.
On each one rearrangement is a fixed coordinate permutation. Finite closed
pasting proves continuity without assuming an H1 gluing theorem. -/
theorem continuous_decreasing (N : ℕ) : Continuous (decreasing (N := N)) := by
  let S := fun σ : Equiv.Perm (Fin N) => {x : Fin N → ℝ | Antitone (x ∘ σ)}
  apply (locallyFinite_of_finite S).continuous
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨Tuple.sort (α := ℝᵒᵈ) x, decreasing_antitone x⟩
  · intro σ
    exact isClosed_antitone.preimage (by fun_prop)
  · intro σ
    exact (show Continuous (fun x : Fin N → ℝ => x ∘ σ) by fun_prop).continuousOn.congr
      (fun x hx => decreasing_eq_permute x σ hx)

/-- Actual unnormalized chamber formula evaluated on decreasing coordinates. -/
def symmetricExtension {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) (x : Fin N → ℝ) : ℂ :=
  wavefunction L c n (decreasing x)

theorem symmetricExtension_permute {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    symmetricExtension L c n (x ∘ σ) = symmetricExtension L c n x := by
  simp only [symmetricExtension, decreasing_permute]

theorem symmetricExtension_eq {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    {x : Fin N → ℝ} (hx : Antitone x) :
    symmetricExtension L c n x = wavefunction L c n x := by
  rw [symmetricExtension, decreasing_eq hx]

theorem symmetricExtension_chamber {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    {x : Fin N → ℝ} (hx : x ∈ chamber N L) :
    symmetricExtension L c n x = wavefunction L c n x :=
  symmetricExtension_eq L c n hx.1.antitone

/-- Continuity holds across all collision walls and their intersections. -/
theorem continuous_symmetricExtension {N : ℕ} (L c : ℝ) (n : Fin N → ℤ) :
    Continuous (symmetricExtension L c n) :=
  (coordinateAnsatz_contDiff c (BetheSmooth.sourceRoots L n c)).continuous.comp
    (continuous_decreasing N)

/-- Any two closed chamber charts give exactly the same value on overlaps. -/
theorem chamber_charts_agree {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) (σ τ : Equiv.Perm (Fin N))
    (hσ : Antitone (x ∘ σ)) (hτ : Antitone (x ∘ τ)) :
    wavefunction L c n (x ∘ σ) = wavefunction L c n (x ∘ τ) := by
  rw [← decreasing_eq_permute x σ hσ, ← decreasing_eq_permute x τ hτ]

/-- A genuine periodic function on the product torus, constructed from the
actual symmetric formula and the canonical half-open representatives. -/
def torusExtension {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → AddCircle L) : ℂ :=
  symmetricExtension L c n (fun i => (AddCircle.equivIco L 0 (x i) : ℝ))

def periodicExtension {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) : ℂ :=
  torusExtension L c n (fun i => (x i : AddCircle L))

theorem torusExtension_permute {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ)
    (n : Fin N → ℤ) (x : Fin N → AddCircle L) (σ : Equiv.Perm (Fin N)) :
    torusExtension L c n (x ∘ σ) = torusExtension L c n x :=
  symmetricExtension_permute L c n
    (fun i => (AddCircle.equivIco L 0 (x i) : ℝ)) σ

theorem periodicExtension_permute {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ)
    (n : Fin N → ℤ) (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    periodicExtension L c n (x ∘ σ) = periodicExtension L c n x :=
  torusExtension_permute L c n (fun i => (x i : AddCircle L)) σ

theorem periodicExtension_eq {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ)
    (n : Fin N → ℤ) (x : Fin N → ℝ) (hx : ∀ i, x i ∈ Set.Ico 0 L) :
    periodicExtension L c n x = symmetricExtension L c n x := by
  unfold periodicExtension torusExtension
  congr 1
  ext i
  exact AddCircle.equivIco_coe_of_mem (by simpa using hx i)

theorem periodicExtension_chamber {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ)
    (n : Fin N → ℤ) {x : Fin N → ℝ} (hx : x ∈ chamber N L) :
    periodicExtension L c n x = wavefunction L c n x := by
  rw [periodicExtension_eq L c n x (fun i => ⟨(hx.2 i).1.le, (hx.2 i).2⟩),
    symmetricExtension_chamber L c n hx]

/-- Independent integer shifts of every coordinate leave the extension fixed. -/
theorem periodicExtension_zshift {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ)
    (n : Fin N → ℤ) (x : Fin N → ℝ) (m : Fin N → ℤ) :
    periodicExtension L c n (fun i => x i + (m i : ℝ) * L) =
      periodicExtension L c n x := by
  unfold periodicExtension
  congr 1
  ext i
  simp [← zsmul_eq_mul]

/-- A spectator permutation fixes the distinguished first coordinate. -/
def headPermutation {N : ℕ} (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Fin (N+1)) :=
  Equiv.Perm.decomposeFin.symm (0, σ)

theorem cons_permute {N : ℕ} (t : ℝ) (x : Fin N → ℝ)
    (σ : Equiv.Perm (Fin N)) :
    Fin.cons t (x ∘ σ) = Fin.cons t x ∘ headPermutation σ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [headPermutation, Equiv.Perm.decomposeFin_symm_apply_succ]

theorem symmetricExtension_cons_permute {N : ℕ} (L c : ℝ) (n : Fin (N+1) → ℤ)
    (t : ℝ) (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    symmetricExtension L c n (Fin.cons t (x ∘ σ)) =
      symmetricExtension L c n (Fin.cons t x) := by
  rw [cons_permute]
  exact symmetricExtension_permute L c n _ _

theorem symmetricExtension_snoc_permute {N : ℕ} (L c : ℝ) (n : Fin (N+1) → ℤ)
    (t : ℝ) (x : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    symmetricExtension L c n (Fin.snoc (x ∘ σ) t) =
      symmetricExtension L c n (Fin.snoc x t) := by
  rw [Fin.snoc_eq_cons_rotate, Fin.snoc_eq_cons_rotate]
  change symmetricExtension L c n (Fin.cons t (x ∘ σ) ∘ finRotate (N+1)) =
    symmetricExtension L c n (Fin.cons t x ∘ finRotate (N+1))
  rw [symmetricExtension_permute, symmetricExtension_permute,
    symmetricExtension_cons_permute]

theorem antitone_cons {N : ℕ} {x : Fin N → ℝ} (hx : Antitone x)
    {t : ℝ} (ht : ∀ i, x i ≤ t) : Antitone (Fin.cons t x) := by
  intro i j hij
  revert hij
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b _ => ?_) j
    · simp
    · exact ht b
  · refine Fin.cases ?_ (fun b hab => ?_) j
    · simp
    · exact hx (Fin.succ_le_succ_iff.mp hab)

theorem antitone_snoc {N : ℕ} {x : Fin N → ℝ} (hx : Antitone x)
    {t : ℝ} (ht : ∀ i, t ≤ x i) : Antitone (Fin.snoc x t) := by
  intro i j hij
  revert hij
  refine Fin.lastCases ?_ (fun a => ?_) i
  · refine Fin.lastCases ?_ (fun b hb => ?_) j
    · simp
    · exact (not_le_of_gt (Fin.castSucc_lt_last b) hb).elim
  · refine Fin.lastCases ?_ (fun b hab => ?_) j
    · intro _; simpa using ht a
    · simpa using hx (Fin.castSucc_le_castSucc_iff.mp hab)

/-- The symmetric cube extension identifies the first coordinate's two
boundary values for arbitrary spectators in the closed cube. Sorting the
spectators reduces this to the PROVED source outer-face identity. -/
theorem symmetricExtension_outer_faces {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 L) :
    symmetricExtension L c n (Fin.cons L x) =
      symmetricExtension L c n (Fin.cons 0 x) := by
  have hu : Antitone (Fin.cons L (decreasing x)) :=
    antitone_cons (decreasing_antitone x) (fun i => (hx _).2)
  have hl : Antitone (Fin.snoc (decreasing x) 0) :=
    antitone_snoc (decreasing_antitone x) (fun i => (hx _).1)
  calc
    symmetricExtension L c n (Fin.cons L x) =
        symmetricExtension L c n (Fin.cons L (decreasing x)) :=
      (symmetricExtension_cons_permute L c n L x (Tuple.sort (α := ℝᵒᵈ) x)).symm
    _ = wavefunction L c n (Fin.cons L (decreasing x)) := symmetricExtension_eq L c n hu
    _ = wavefunction L c n (Fin.snoc (decreasing x) 0) :=
      wavefunction_outer_faces hL hc hn _
    _ = symmetricExtension L c n (Fin.snoc (decreasing x) 0) :=
      (symmetricExtension_eq L c n hl).symm
    _ = symmetricExtension L c n (Fin.snoc x 0) :=
      symmetricExtension_snoc_permute L c n 0 x (Tuple.sort (α := ℝᵒᵈ) x)
    _ = symmetricExtension L c n (Fin.cons 0 x) := by
      rw [Fin.snoc_eq_cons_rotate]
      exact symmetricExtension_permute L c n _ _

/-- Every pair of opposite cube faces agrees, including their intersections. -/
theorem symmetricExtension_update_faces {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (x : Fin (N+1) → ℝ) (hx : ∀ j, x j ∈ Set.Icc 0 L) (i : Fin (N+1)) :
    symmetricExtension L c n (Function.update x i L) =
      symmetricExtension L c n (Function.update x i 0) := by
  classical
  let σ := Equiv.swap (0 : Fin (N+1)) i
  let y := fun j : Fin N => x (σ j.succ)
  have he (t : ℝ) : Function.update x i t ∘ σ = Fin.cons t y := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [σ]
    · have hne : σ k.succ ≠ i := by
        have hzero : σ 0 = i := Equiv.swap_apply_left _ _
        rw [← hzero]
        exact fun h => Fin.succ_ne_zero k (σ.injective h)
      simp [Function.update_of_ne hne, y]
  calc
    symmetricExtension L c n (Function.update x i L) =
        symmetricExtension L c n (Function.update x i L ∘ σ) :=
      (symmetricExtension_permute L c n _ σ).symm
    _ = symmetricExtension L c n (Fin.cons L y) := by rw [he]
    _ = symmetricExtension L c n (Fin.cons 0 y) :=
      symmetricExtension_outer_faces hL hc hn y (fun j => hx _)
    _ = symmetricExtension L c n (Function.update x i 0 ∘ σ) := by rw [he]
    _ = symmetricExtension L c n (Function.update x i 0) :=
      symmetricExtension_permute L c n _ σ

/-- Replacing any selected L-valued coordinates by zero preserves the cube
extension. This proves compatibility even at multiple outer-face corners. -/
theorem symmetricExtension_zero_endpoints {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (x : Fin (N+1) → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 L)
    (s : Finset (Fin (N+1))) :
    symmetricExtension L c n (fun i => if i ∈ s ∧ x i = L then 0 else x i) =
      symmetricExtension L c n x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    let y := fun i => if i ∈ s ∧ x i = L then 0 else x i
    have hy : ∀ i, y i ∈ Set.Icc 0 L := by
      intro i
      dsimp [y]
      split_ifs
      · exact ⟨le_rfl, hL.le⟩
      · exact hx i
    by_cases hxa : x a = L
    · have hya : y a = L := by simp [y, ha, hxa]
      have he : (fun i => if i ∈ insert a s ∧ x i = L then 0 else x i) =
          Function.update y a 0 := by
        ext i
        by_cases hi : i = a
        · subst i; simp [hxa]
        · simp [hi, y]
      rw [he, ← symmetricExtension_update_faces hL hc hn y hy a,
        Function.update_eq_self_iff.mpr hya.symm]
      exact ih
    · have he : (fun i => if i ∈ insert a s ∧ x i = L then 0 else x i) = y := by
        ext i
        by_cases hi : i = a
        · subst i; simp [hxa, y]
        · simp [hi, y]
      rw [he]
      exact ih

/-- The torus function pulls back to the symmetric ansatz on the entire
CLOSED cube, so its definition at the periodic seam is compatible. -/
theorem torusExtension_closed_cube {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n)
    (x : Fin (N+1) → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 L) :
    torusExtension L c n (fun i => (x i : AddCircle L)) =
      symmetricExtension L c n x := by
  classical
  have hL : 0 < L := Fact.out
  have he (i : Fin (N+1)) : (AddCircle.equivIco L 0 (x i : AddCircle L) : ℝ) =
      if x i = L then 0 else x i := by
    by_cases hi : x i = L
    · rw [hi, AddCircle.coe_period]
      simp only [ite_true]
      exact AddCircle.equivIco_coe_of_mem (by simp [hL])
    · rw [ite_eq_right_iff.mpr (fun h => (hi h).elim)]
      exact AddCircle.equivIco_coe_of_mem (by
        simpa using (show x i ∈ Set.Ico 0 L from ⟨(hx i).1, lt_of_le_of_ne (hx i).2 hi⟩))
  unfold torusExtension
  simp_rw [he]
  simpa using symmetricExtension_zero_endpoints hL hc hn x hx Finset.univ

/-- Compact closed cube -> product torus is a continuous surjection. Pulling
back the constructed function gives the already proved continuous symmetric
formula, proving continuity across periodic seams and all collision walls. -/
theorem continuous_torusExtension {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    Continuous (torusExtension L c n) := by
  let P := fun x : Fin (N+1) → Set.Icc (0 : ℝ) L =>
    fun i => ((x i : ℝ) : AddCircle L)
  have hp : Continuous P := by fun_prop
  have hs : Function.Surjective P := by
    intro x
    refine ⟨fun i => ⟨(AddCircle.equivIco L 0 (x i) : ℝ), ?_⟩, ?_⟩
    · exact Set.Ico_subset_Icc_self (by simpa using (AddCircle.equivIco L 0 (x i)).property)
    · funext i
      exact AddCircle.coe_equivIco
  apply (Topology.IsQuotientMap.of_surjective_continuous hs hp).continuous_iff.mpr
  have he : torusExtension L c n ∘ P =
      fun x : Fin (N+1) → Set.Icc (0 : ℝ) L =>
        symmetricExtension L c n (fun i => (x i : ℝ)) := by
    funext x
    exact torusExtension_closed_cube hc hn _ (fun i => (x i).property)
  rw [he]
  exact (continuous_symmetricExtension L c n).comp (by fun_prop)

theorem continuous_periodicExtension {N : ℕ} {L : ℝ} [Fact (0 < L)] {c : ℝ}
    (hc : 0 < c) {n : Fin (N+1) → ℤ} (hn : Antitone n) :
    Continuous (periodicExtension L c n) :=
  (continuous_torusExtension hc hn).comp (by fun_prop)

/-- The two adjacent chamber charts on a normal line are related by actual
coordinate reflection, with all spectator coordinates fixed. -/
theorem wallLine_swap {N : ℕ} (x : Fin N → ℝ) {a b : Fin N}
    (hab : a ≠ b) (hx : x a = x b) (r : ℝ) :
    wallLine a b x r ∘ Equiv.swap a b = wallLine a b x (-r) := by
  ext i
  by_cases hia : i = a
  · subst i
    simp [wallLine, wallDirection, hab, hab.symm, hx]
  by_cases hib : i = b
  · subst i
    simp [wallLine, wallDirection, hab, hab.symm, hx]
  simp [Equiv.swap_apply_of_ne_of_ne hia hib, wallLine_spectator hia hib]

theorem symmetricExtension_wallLine_even {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) {a b : Fin N} (hab : a ≠ b) (hx : x a = x b) (r : ℝ) :
    symmetricExtension L c n (wallLine a b x (-r)) =
      symmetricExtension L c n (wallLine a b x r) := by
  rw [← wallLine_swap x hab hx r]
  exact symmetricExtension_permute L c n _ _

/-- Local symmetric normal continuation in the actual relative separation
r=x_a-x_b. Its right derivative is c/2 times the common trace. -/
def reflectedContact {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) (a b : Fin N) (r : ℝ) : ℂ :=
  wavefunction L c n (wallLine a b x (|r| / 2))

theorem continuous_reflectedContact {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) (a b : Fin N) :
    Continuous (reflectedContact L c n x a b) :=
  (coordinateAnsatz_contDiff c (BetheSmooth.sourceRoots L n c)).continuous.comp
    (by unfold wallLine; fun_prop)

theorem reflectedContact_right {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) (x : Fin N → ℝ)
    {a b : Fin N} (hadj : b.val = a.val + 1) (hx : x a = x b) :
    HasDerivWithinAt (reflectedContact L c n x a b)
      (((c / 2 : ℝ) : ℂ) * wavefunction L c n x) (Set.Ici 0) 0 := by
  apply (wavefunction_contact_half_hasDerivAt hL hc hn x hadj hx).hasDerivWithinAt.congr
  · intro r hr
    simp [reflectedContact, abs_of_nonneg (show 0 ≤ r from hr)]
  · simp [reflectedContact]

theorem reflectedContact_left {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) (x : Fin N → ℝ)
    {a b : Fin N} (hadj : b.val = a.val + 1) (hx : x a = x b) :
    HasDerivWithinAt (reflectedContact L c n x a b)
      (-(((c / 2 : ℝ) : ℂ) * wavefunction L c n x)) (Set.Iic 0) 0 := by
  have hd := (wavefunction_contact_half_hasDerivAt hL hc hn x hadj hx).scomp_of_eq 0
    (hasDerivAt_id (0 : ℝ)).neg (by simp)
  simp only [Function.comp_def, neg_smul, one_smul] at hd
  apply hd.hasDerivWithinAt.congr
  · intro r hr
    simp [reflectedContact, abs_of_nonpos (show r ≤ 0 from hr)]
  · simp [reflectedContact]

/-- The contact jump has the source factor c: the kinetic operator in the
relative coordinate is -2 d²/dr², and the delta coupling is 2c. This theorem
only computes one-sided derivatives; it does not assert a weak equation. -/
theorem reflectedContact_jump {N : ℕ} {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    {n : Fin N → ℤ} (hn : Antitone n) (x : Fin N → ℝ)
    {a b : Fin N} (hadj : b.val = a.val + 1) (hx : x a = x b) :
    derivWithin (reflectedContact L c n x a b) (Set.Ici 0) 0 -
      derivWithin (reflectedContact L c n x a b) (Set.Iic 0) 0 =
      (c : ℂ) * wavefunction L c n x := by
  rw [(reflectedContact_right hL hc hn x hadj hx).derivWithin (uniqueDiffWithinAt_Ici 0),
    (reflectedContact_left hL hc hn x hadj hx).derivWithin (uniqueDiffWithinAt_Iic 0)]
  push_cast
  ring

/-- Wherever the positive normal coordinate is in the closed ordered
chamber, the constructed symmetric extension is exactly the reflected
contact profile. This explicitly connects the local contact calculation
to the extension, rather than positing a global wavefunction. -/
theorem symmetricExtension_eq_reflectedContact {N : ℕ} (L c : ℝ)
    (n : Fin N → ℤ) (x : Fin N → ℝ) {a b : Fin N} (hab : a ≠ b)
    (hx : x a = x b) (r : ℝ) (hr : Antitone (wallLine a b x (|r| / 2))) :
    symmetricExtension L c n (wallLine a b x (r / 2)) =
      reflectedContact L c n x a b r := by
  by_cases h : 0 ≤ r
  · simpa [reflectedContact, abs_of_nonneg h] using symmetricExtension_eq L c n hr
  · have he : r / 2 = -(|r| / 2) := by rw [abs_of_neg (lt_of_not_ge h)]; ring
    rw [he, symmetricExtension_wallLine_even L c n x hab hx]
    exact symmetricExtension_eq L c n hr

/-- On each closed ordering region the extension is the restriction of an
explicit smooth finite ansatz after a fixed coordinate permutation. -/
theorem contDiffOn_symmetricExtension {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (σ : Equiv.Perm (Fin N)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (symmetricExtension L c n)
      {x | Antitone (x ∘ σ)} := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin N → ℝ => wavefunction L c n (x ∘ σ)) :=
    (coordinateAnsatz_contDiff c (BetheSmooth.sourceRoots L n c)).comp (by fun_prop)
  exact h.contDiffOn.congr (fun x hx =>
    congrArg (wavefunction L c n) (decreasing_eq_permute x σ hx))

/-- At a single collision face, the strict spectator gaps ensure that the
positive normal ray stays ordered near zero. This geometric obligation is
proved from finitely many strict inequalities, rather than assumed gluing. -/
theorem eventually_antitone_wallLine {N : ℕ} (x : Fin N → ℝ) {a b : Fin N}
    (hab : a ≠ b) (hx : x a = x b)
    (hsep : ∀ i j, i < j → ¬(i = a ∧ j = b) → x j < x i) :
    ∀ᶠ r : ℝ in 𝓝 0, 0 ≤ r → Antitone (wallLine a b x (r / 2)) := by
  have hrest : ∀ᶠ r : ℝ in 𝓝 0, ∀ i j : Fin N,
      i < j → ¬(i = a ∧ j = b) →
        wallLine a b x (r / 2) j < wallLine a b x (r / 2) i := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hp : i < j ∧ ¬(i = a ∧ j = b)
    · have hopen : IsOpen {r : ℝ | wallLine a b x (r / 2) j <
          wallLine a b x (r / 2) i} := isOpen_lt (by unfold wallLine; fun_prop)
            (by unfold wallLine; fun_prop)
      have hm : (0 : ℝ) ∈ {r : ℝ | wallLine a b x (r / 2) j <
          wallLine a b x (r / 2) i} := by
        simpa only [Set.mem_ofPred_eq, zero_div, wallLine_zero] using hsep i j hp.1 hp.2
      filter_upwards [hopen.mem_nhds hm] with r hr
      exact fun _ _ => hr
    · exact Filter.Eventually.of_forall (fun _ hij hne => (hp ⟨hij, hne⟩).elim)
  filter_upwards [hrest] with r hr hpos
  apply antitone_iff_forall_lt.mpr
  intro i j hij
  by_cases hp : i = a ∧ j = b
  · rcases hp with ⟨rfl, rfl⟩
    rw [wallLine_left hab, wallLine_right hab, hx]
    linarith
  · exact (hr i j hij hp).le

/-- The actual symmetric extension and the reflected contact profile agree
on a full neighborhood of each single collision face. -/
theorem symmetricExtension_contact_germ {N : ℕ} (L c : ℝ) (n : Fin N → ℤ)
    (x : Fin N → ℝ) {a b : Fin N} (hab : a ≠ b) (hx : x a = x b)
    (hsep : ∀ i j, i < j → ¬(i = a ∧ j = b) → x j < x i) :
    (fun r => symmetricExtension L c n (wallLine a b x (r / 2))) =ᶠ[𝓝 0]
      reflectedContact L c n x a b := by
  have habs : Filter.Tendsto (fun r : ℝ => |r|) (𝓝 0) (𝓝 0) := by
    simpa using continuous_abs.tendsto (0 : ℝ)
  filter_upwards [habs.eventually (eventually_antitone_wallLine x hab hx hsep)] with r hr
  exact symmetricExtension_eq_reflectedContact L c n x hab hx r (hr (abs_nonneg r))

/-- The extension itself has the source right and left contact derivatives
at a single adjacent collision face. Multiple-wall continuity is covered
globally above; no first-derivative agreement across a contact wall is claimed. -/
theorem symmetricExtension_contact_derivatives {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) {a b : Fin N} (hadj : b.val = a.val + 1)
    (hx : x a = x b) (hsep : ∀ i j, i < j → ¬(i = a ∧ j = b) → x j < x i) :
    let F := fun r => symmetricExtension L c n (wallLine a b x (r / 2))
    HasDerivWithinAt F (((c / 2 : ℝ) : ℂ) * wavefunction L c n x) (Set.Ici 0) 0 ∧
      HasDerivWithinAt F (-(((c / 2 : ℝ) : ℂ) * wavefunction L c n x)) (Set.Iic 0) 0 := by
  have hab : a ≠ b := by intro h; subst b; omega
  have he := symmetricExtension_contact_germ L c n x hab hx hsep
  exact ⟨(reflectedContact_right hL hc hn x hadj hx).congr_of_eventuallyEq
      (he.filter_mono nhdsWithin_le_nhds) he.eq_of_nhds,
    (reflectedContact_left hL hc hn x hadj hx).congr_of_eventuallyEq
      (he.filter_mono nhdsWithin_le_nhds) he.eq_of_nhds⟩

/-- Source contact jump for the constructed symmetric extension, at every
single adjacent collision face. -/
theorem symmetricExtension_contact_jump {N : ℕ} {L c : ℝ}
    (hL : 0 < L) (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) {a b : Fin N} (hadj : b.val = a.val + 1)
    (hx : x a = x b) (hsep : ∀ i j, i < j → ¬(i = a ∧ j = b) → x j < x i) :
    let F := fun r => symmetricExtension L c n (wallLine a b x (r / 2))
    derivWithin F (Set.Ici 0) 0 - derivWithin F (Set.Iic 0) 0 =
      (c : ℂ) * wavefunction L c n x := by
  obtain ⟨hr, hl⟩ := symmetricExtension_contact_derivatives hL hc hn x hadj hx hsep
  dsimp only
  rw [hr.derivWithin (uniqueDiffWithinAt_Ici 0), hl.derivWithin (uniqueDiffWithinAt_Iic 0)]
  push_cast
  ring

/-- Inside the cube, periodization agrees locally with the symmetric formula. -/
theorem periodicExtension_eq_near {N : ℕ} (L : ℝ) [Fact (0 < L)] (c : ℝ)
    (n : Fin N → ℤ) (x : Fin N → ℝ) (hx : ∀ i, x i ∈ Set.Ioo 0 L) :
    periodicExtension L c n =ᶠ[𝓝 x] symmetricExtension L c n := by
  have hbox : ∀ᶠ y : Fin N → ℝ in 𝓝 x, ∀ i, y i ∈ Set.Ioo 0 L := by
    apply Filter.eventually_all.mpr
    intro i
    exact (isOpen_Ioo.preimage (continuous_apply i)).mem_nhds (hx i)
  filter_upwards [hbox] with y hy
  exact periodicExtension_eq L c n y (fun i => ⟨(hy i).1.le, (hy i).2⟩)

/-- The periodic extension inherits the actual one-sided contact derivatives
at every single collision face in the interior cube. -/
theorem periodicExtension_contact_derivatives {N : ℕ} {L : ℝ} [Fact (0 < L)]
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (x : Fin N → ℝ) (hxbox : ∀ i, x i ∈ Set.Ioo 0 L)
    {a b : Fin N} (hadj : b.val = a.val + 1) (hx : x a = x b)
    (hsep : ∀ i j, i < j → ¬(i = a ∧ j = b) → x j < x i) :
    let F := fun r => periodicExtension L c n (wallLine a b x (r / 2))
    HasDerivWithinAt F (((c / 2 : ℝ) : ℂ) * wavefunction L c n x) (Set.Ici 0) 0 ∧
      HasDerivWithinAt F (-(((c / 2 : ℝ) : ℂ) * wavefunction L c n x)) (Set.Iic 0) 0 := by
  have ht : Tendsto (fun r : ℝ => wallLine a b x (r / 2)) (𝓝 0) (𝓝 x) := by
    have hh : Continuous (fun r : ℝ => wallLine a b x (r / 2)) := by
      unfold wallLine
      fun_prop
    simpa only [zero_div, wallLine_zero] using hh.tendsto 0
  have he : (fun r => periodicExtension L c n (wallLine a b x (r / 2))) =ᶠ[𝓝 0]
      (fun r => symmetricExtension L c n (wallLine a b x (r / 2))) :=
    ht.eventually (periodicExtension_eq_near L c n x hxbox)
  obtain ⟨hr, hl⟩ := symmetricExtension_contact_derivatives (show 0 < L from Fact.out) hc hn x hadj hx hsep
  exact ⟨hr.congr_of_eventuallyEq (he.filter_mono nhdsWithin_le_nhds) he.eq_of_nhds,
    hl.congr_of_eventuallyEq (he.filter_mono nhdsWithin_le_nhds) he.eq_of_nhds⟩

end QuantumNLS.BetheExtension

#print axioms QuantumNLS.BetheExtension.decreasing
#print axioms QuantumNLS.BetheExtension.decreasing_antitone
#print axioms QuantumNLS.BetheExtension.decreasing_eq
#print axioms QuantumNLS.BetheExtension.decreasing_permute
#print axioms QuantumNLS.BetheExtension.decreasing_eq_permute
#print axioms QuantumNLS.BetheExtension.continuous_decreasing
#print axioms QuantumNLS.BetheExtension.symmetricExtension
#print axioms QuantumNLS.BetheExtension.symmetricExtension_permute
#print axioms QuantumNLS.BetheExtension.symmetricExtension_eq
#print axioms QuantumNLS.BetheExtension.symmetricExtension_chamber
#print axioms QuantumNLS.BetheExtension.continuous_symmetricExtension
#print axioms QuantumNLS.BetheExtension.chamber_charts_agree
#print axioms QuantumNLS.BetheExtension.torusExtension
#print axioms QuantumNLS.BetheExtension.periodicExtension
#print axioms QuantumNLS.BetheExtension.torusExtension_permute
#print axioms QuantumNLS.BetheExtension.periodicExtension_permute
#print axioms QuantumNLS.BetheExtension.periodicExtension_eq
#print axioms QuantumNLS.BetheExtension.periodicExtension_chamber
#print axioms QuantumNLS.BetheExtension.periodicExtension_zshift
#print axioms QuantumNLS.BetheExtension.headPermutation
#print axioms QuantumNLS.BetheExtension.cons_permute
#print axioms QuantumNLS.BetheExtension.symmetricExtension_cons_permute
#print axioms QuantumNLS.BetheExtension.symmetricExtension_snoc_permute
#print axioms QuantumNLS.BetheExtension.antitone_cons
#print axioms QuantumNLS.BetheExtension.antitone_snoc
#print axioms QuantumNLS.BetheExtension.symmetricExtension_outer_faces
#print axioms QuantumNLS.BetheExtension.symmetricExtension_update_faces
#print axioms QuantumNLS.BetheExtension.symmetricExtension_zero_endpoints
#print axioms QuantumNLS.BetheExtension.torusExtension_closed_cube
#print axioms QuantumNLS.BetheExtension.continuous_torusExtension
#print axioms QuantumNLS.BetheExtension.continuous_periodicExtension
#print axioms QuantumNLS.BetheExtension.wallLine_swap
#print axioms QuantumNLS.BetheExtension.symmetricExtension_wallLine_even
#print axioms QuantumNLS.BetheExtension.reflectedContact
#print axioms QuantumNLS.BetheExtension.continuous_reflectedContact
#print axioms QuantumNLS.BetheExtension.reflectedContact_right
#print axioms QuantumNLS.BetheExtension.reflectedContact_left
#print axioms QuantumNLS.BetheExtension.reflectedContact_jump
#print axioms QuantumNLS.BetheExtension.symmetricExtension_eq_reflectedContact
#print axioms QuantumNLS.BetheExtension.contDiffOn_symmetricExtension
#print axioms QuantumNLS.BetheExtension.eventually_antitone_wallLine
#print axioms QuantumNLS.BetheExtension.symmetricExtension_contact_germ
#print axioms QuantumNLS.BetheExtension.symmetricExtension_contact_derivatives
#print axioms QuantumNLS.BetheExtension.symmetricExtension_contact_jump
#print axioms QuantumNLS.BetheExtension.periodicExtension_eq_near
#print axioms QuantumNLS.BetheExtension.periodicExtension_contact_derivatives
