import QuantumNLS.BetheConvexity
import QuantumNLS.BetheSmooth
import QuantumNLS.BetheRoots

/-!
# DEF-006: Bethe labels, rapidity equation, corrected integers, multiplicity arrays

Source (PR11 `3b1f701a`): `chapters/definitions.tex:37-41` (DEF-006) and
`chapters/foundations/periodic_basis.tex` (`basis:eq:logbethe`, `basis:lem:roots`).

DEF-006 (verbatim): "The logarithmic labels are strictly increasing `I_j ∈ ℤ + (N-1)/2`. The real
rapidities solve `L q_j + 2 Σ_{k≠j} arctan((q_j-q_k)/c) = 2π I_j`. The corrected integers
`n_j = I_j - j + (N+1)/2` are nondecreasing. Their multiplicities `m_n` form a finitely supported
array of nonnegative integers with `Σ_n m_n = N`. The set of all such arrays is `M_N`."

**Indexing.** Lean indices are `j : Fin N`, zero based; the source's `j` is `j.val + 1`.

**Convention comparison with `periodic_basis.tex`.** There `𝔑_N = {n : n_1 ≥ … ≥ n_N}` (nonincreasing),
`ρ_j = (N+1-2j)/2`, `I_j = n_j + ρ_j` and `q` strictly *decreasing*. DEF-006 has `I` increasing and
`n_j = I_j - j + (N+1)/2 = I_j + ρ_j` nondecreasing. The two are related by reversing the
enumeration `j ↦ N+1-j` (no rapidity or label is negated): `n^{src}_i = n_{rev i}` and
`I^{src}_i = I_{rev i}`, because `ρ_{N+1-j} = -ρ_j`. The bridge theorems below prove this
identification against the accepted `BetheSmooth.sourceRoots`/`BetheAdmission.quantumNumbers`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace QuantumNLS.BetheLabels

open QuantumNLS.BetheAdmission QuantumNLS.BetheRoots QuantumNLS.BetheSmooth

section Labels
variable {N : ℕ}

/-- **Logarithmic labels**: strictly increasing `I_j ∈ ℤ + (N-1)/2`. -/
structure LogLabels (N : ℕ) where
  I : Fin N → ℝ
  strictMono : StrictMono I
  mem : ∀ j, ∃ z : ℤ, I j = (z : ℝ) + ((N : ℝ) - 1) / 2

@[ext] theorem LogLabels.ext' {ℓ ℓ' : LogLabels N} (h : ℓ.I = ℓ'.I) : ℓ = ℓ' := by
  cases ℓ; cases ℓ'; cases h; rfl

/-- **The rapidity equation** `L q_j + 2 Σ_{k≠j} arctan((q_j-q_k)/c) = 2π I_j` (literal, over `k ≠ j`). -/
def RapidityEq (L c : ℝ) (I : Fin N → ℝ) (q : Fin N → ℝ) : Prop :=
  ∀ j : Fin N, L * q j + 2 * ∑ k ∈ Finset.univ.erase j, Real.arctan ((q j - q k) / c) =
    2 * Real.pi * I j

theorem rapidityEq_iff_logMap (L c : ℝ) (I : Fin N → ℝ) (q : Fin N → ℝ) :
    RapidityEq L c I q ↔ logMap L c q = fun j => 2 * Real.pi * I j := by
  unfold RapidityEq
  constructor
  · intro h; funext j; rw [logMap_erase]; exact h j
  · intro h j; rw [← logMap_erase]; exact congrFun h j

/-- The integer `z_j` with `I_j = z_j + (N-1)/2`. -/
def lat (ℓ : LogLabels N) (j : Fin N) : ℤ := Classical.choose (ℓ.mem j)

theorem lat_spec (ℓ : LogLabels N) (j : Fin N) :
    ℓ.I j = (lat ℓ j : ℝ) + ((N : ℝ) - 1) / 2 := Classical.choose_spec (ℓ.mem j)

/-- **Corrected integers** `n_j = I_j - j + (N+1)/2` (source index `j = j.val + 1`), as integers. -/
def correctedInt (ℓ : LogLabels N) (j : Fin N) : ℤ := lat ℓ j + N - 1 - (j.val : ℤ)

/-- The corrected integers are the literal formula of DEF-006; in particular they are integers. -/
theorem correctedInt_spec (ℓ : LogLabels N) (j : Fin N) :
    (correctedInt ℓ j : ℝ) = ℓ.I j - ((j.val : ℝ) + 1) + ((N : ℝ) + 1) / 2 := by
  rw [lat_spec ℓ j]
  simp only [correctedInt, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
  ring

theorem quantumNumbers_correctedInt (ℓ : LogLabels N) :
    quantumNumbers (correctedInt ℓ) = ℓ.I := by
  funext j
  have h := correctedInt_spec ℓ j
  unfold quantumNumbers
  linarith

/-- **The corrected integers are nondecreasing.** -/
theorem correctedInt_monotone (ℓ : LogLabels N) : Monotone (correctedInt ℓ) := by
  rw [← quantumNumbers_strictMono_iff, quantumNumbers_correctedInt]
  exact ℓ.strictMono

/-- Nondecreasing corrected integers (`CorrectedLabels` of the accepted `BetheAdmission`). -/
abbrev Corrected (N : ℕ) := {n : Fin N → ℤ // Monotone n}

/-- The labels of a nondecreasing corrected-integer array. -/
def labelsOf (n : Corrected N) : LogLabels N where
  I := quantumNumbers n.1
  strictMono := quantumNumbers_strictMono n
  mem := quantumNumbers_lattice n.1

/-- **Bijection: strictly increasing labels ↔ nondecreasing corrected integers.** -/
def labelsEquivCorrected : LogLabels N ≃ Corrected N where
  toFun ℓ := ⟨correctedInt ℓ, correctedInt_monotone ℓ⟩
  invFun n := labelsOf n
  left_inv ℓ := LogLabels.ext' (quantumNumbers_correctedInt ℓ)
  right_inv n := by
    apply Subtype.ext
    funext j
    have h := correctedInt_spec (labelsOf n) j
    have h2 := corrected_recovery n.1 j
    have h3 : ((correctedInt (labelsOf n) j : ℤ) : ℝ) = (n.1 j : ℝ) := by
      rw [h]; simpa [labelsOf] using h2
    exact_mod_cast h3

end Labels


section Mult
variable {N : ℕ}

/-- **The set `M_N`**: finitely supported arrays `m : ℤ →₀ ℕ` (`m_n ≥ 0`) with `Σ_n m_n = N`. -/
def MArr (N : ℕ) : Type := {m : ℤ →₀ ℕ // (m.sum fun _ k => k) = N}

/-- The multiset of values of a corrected-integer vector. -/
def msOf (n : Fin N → ℤ) : Multiset ℤ := Multiset.map n Finset.univ.val

theorem card_msOf (n : Fin N → ℤ) : Multiset.card (msOf n) = N := by simp [msOf]

theorem msOf_eq_ofFn (n : Fin N → ℤ) : msOf n = ((List.ofFn n : List ℤ) : Multiset ℤ) := by
  unfold msOf
  rw [Fin.univ_val_map]

/-- Multisets of size `N` ≃ arrays in `M_N` (multiplicities). -/
def msEquivArr : {s : Multiset ℤ // Multiset.card s = N} ≃ MArr N where
  toFun s := ⟨Multiset.toFinsupp s.1, by
    have h := Finsupp.card_toMultiset (Multiset.toFinsupp s.1)
    rw [Multiset.toFinsupp_toMultiset] at h
    exact h.symm.trans s.2⟩
  invFun m := ⟨Finsupp.toMultiset m.1, by rw [Finsupp.card_toMultiset]; exact m.2⟩
  left_inv s := Subtype.ext (Multiset.toFinsupp_toMultiset s.1)
  right_inv m := Subtype.ext (Multiset.toFinsupp.apply_symm_apply m.1)

/-- The sorted (nondecreasing) vector of a multiset of size `N`. -/
def sortSeq (s : {s : Multiset ℤ // Multiset.card s = N}) : Fin N → ℤ :=
  fun j => (s.1.sort)[j.val]'(by rw [Multiset.length_sort, s.2]; exact j.2)

theorem sortSeq_monotone (s : {s : Multiset ℤ // Multiset.card s = N}) : Monotone (sortSeq s) := by
  have hl : (s.1.sort).SortedLE := List.sortedLE_iff_pairwise.2 (Multiset.pairwise_sort _ _)
  intro a b hab
  exact hl (show (⟨a.val, by rw [Multiset.length_sort, s.2]; exact a.2⟩ : Fin (s.1.sort).length) ≤
    ⟨b.val, by rw [Multiset.length_sort, s.2]; exact b.2⟩ from hab)

/-- **Bijection: nondecreasing corrected integers ↔ multisets of size `N`.** -/
def corrEquivMS : Corrected N ≃ {s : Multiset ℤ // Multiset.card s = N} where
  toFun n := ⟨msOf n.1, card_msOf n.1⟩
  invFun s := ⟨sortSeq s, sortSeq_monotone s⟩
  left_inv n := by
    apply Subtype.ext
    have hpw : (List.ofFn n.1).Pairwise (· ≤ ·) :=
      List.sortedLE_iff_pairwise.1 (n.2.sortedLE_ofFn)
    have hperm : (msOf n.1).sort = List.ofFn n.1 := by
      refine (Multiset.coe_eq_coe.1 ?_).eq_of_pairwise' (Multiset.pairwise_sort _ _) hpw
      rw [Multiset.sort_eq, msOf_eq_ofFn]
    funext j
    show ((msOf n.1).sort)[j.val]'_ = n.1 j
    simp only [hperm, List.getElem_ofFn]
  right_inv s := by
    apply Subtype.ext
    show msOf (sortSeq s) = s.1
    rw [msOf_eq_ofFn]
    have : List.ofFn (sortSeq s) = s.1.sort := by
      refine List.ext_getElem (by simp [Multiset.length_sort, s.2]) (fun i h1 h2 => ?_)
      simp [sortSeq]
    rw [this, Multiset.sort_eq]

/-- **Bijection: nondecreasing corrected integers ↔ arrays in `M_N`**
(`m_n = #{j : n_j = n}`). -/
def correctedEquivArr : Corrected N ≃ MArr N := corrEquivMS.trans msEquivArr

theorem correctedEquivArr_apply (n : Corrected N) (k : ℤ) :
    (correctedEquivArr n).1 k = (Finset.univ.filter fun j => n.1 j = k).card := by
  show Multiset.count k (msOf n.1) = _
  unfold msOf
  rw [Multiset.count_map]
  simp only [eq_comm (a := k)]
  rfl

/-- **The full bijection of DEF-006**: strictly increasing labels `I` ↔ nondecreasing corrected
integers `n` ↔ arrays `m ∈ M_N`. -/
def labelsEquivArr : LogLabels N ≃ MArr N := labelsEquivCorrected.trans correctedEquivArr

theorem labelsEquivArr_apply (ℓ : LogLabels N) (k : ℤ) :
    (labelsEquivArr ℓ).1 k = (Finset.univ.filter fun j => correctedInt ℓ j = k).card :=
  correctedEquivArr_apply _ k

/-- The multiplicity array of any label set sums to `N`. -/
theorem labelsEquivArr_sum (ℓ : LogLabels N) : ((labelsEquivArr ℓ).1.sum fun _ k => k) = N :=
  (labelsEquivArr ℓ).2

end Mult


section Bridge
variable {N : ℕ} {L c : ℝ}

open QuantumNLS.BetheConvexity

theorem logMap_rev (q : Fin N → ℝ) (i : Fin N) :
    logMap L c (fun k => q (Fin.rev k)) i = logMap L c q (Fin.rev i) := by
  unfold logMap
  have h : ∑ j, Real.arctan ((q (Fin.rev i) - q (Fin.rev j)) / c) =
      ∑ j, Real.arctan ((q (Fin.rev i) - q j) / c) :=
    Equiv.sum_comp Fin.revPerm (fun j => Real.arctan ((q (Fin.rev i) - q j) / c))
  simp only [h]

theorem rapidityEq_iff_solves (ℓ : LogLabels N) (q : Fin N → ℝ) :
    RapidityEq L c ℓ.I q ↔ Solves L c (correctedInt ℓ) q := by
  rw [rapidityEq_iff_logMap]
  unfold Solves
  rw [quantumNumbers_correctedInt]
  constructor
  · intro h i; exact congrFun h i
  · intro h; funext i; exact h i

/-- **Existence and uniqueness of the real rapidities** for logarithmic labels `I` (`c > 0`). -/
theorem existsUnique_rapidity (hL : 0 < L) (hc : 0 < c) (ℓ : LogLabels N) :
    ∃! q : Fin N → ℝ, RapidityEq L c ℓ.I q := by
  obtain ⟨q, hq, hu⟩ := existsUnique_solution hL hc (fun i => 2 * Real.pi * ℓ.I i)
  exact ⟨q, (rapidityEq_iff_logMap L c ℓ.I q).2 hq,
    fun r hr => hu r ((rapidityEq_iff_logMap L c ℓ.I r).1 hr)⟩

/-- **Identification with the accepted root theorem (R-4C8D7C9E):** the unique real solution of the
rapidity equation for the labels `I` is the accepted root vector `roots L n c` of the corrected
integers `n = correctedInt ℓ` (increasing convention of `BetheAdmission`). -/
theorem rapidityEq_iff_roots (hL : 0 < L) (hc : 0 < c) (ℓ : LogLabels N) (q : Fin N → ℝ) :
    RapidityEq L c ℓ.I q ↔ q = roots L (correctedInt ℓ) c := by
  constructor
  · intro h
    have hq : logMap L c q = fun i => 2 * Real.pi * quantumNumbers (correctedInt ℓ) i := by
      rw [quantumNumbers_correctedInt]; exact (rapidityEq_iff_logMap L c ℓ.I q).1 h
    exact BetheConvexity.eq_root hL hc hq
  · rintro rfl
    exact (rapidityEq_iff_solves ℓ _).2 (roots_solves hL hc _)

theorem roots_strictMono_labels (hL : 0 < L) (hc : 0 < c) (ℓ : LogLabels N) :
    StrictMono (roots L (correctedInt ℓ) c) :=
  roots_strictMono hL hc ⟨correctedInt ℓ, correctedInt_monotone ℓ⟩ (roots_solves hL hc _)

/-- The root vector of the labels of an array `m ∈ M_N`. -/
def arrRoots (L c : ℝ) (m : MArr N) : Fin N → ℝ :=
  roots L (correctedInt (labelsEquivArr.symm m)) c

theorem rapidityEq_iff_arrRoots (hL : 0 < L) (hc : 0 < c) (m : MArr N) (q : Fin N → ℝ) :
    RapidityEq L c (labelsEquivArr.symm m).I q ↔ q = arrRoots L c m :=
  rapidityEq_iff_roots hL hc _ q

/-! ### Comparison with the printed (decreasing) convention of `periodic_basis.tex` -/

/-- The source's nonincreasing integers `n^{src}_i = n_{rev i}`. -/
def srcOf (n : Fin N → ℤ) : Fin N → ℤ := fun i => n (Fin.rev i)

theorem srcOf_antitone {n : Fin N → ℤ} (hn : Monotone n) : Antitone (srcOf n) :=
  fun _ _ hij => hn (Fin.rev_le_rev.2 hij)

theorem srcOf_srcOf (n : Fin N → ℤ) : srcOf (srcOf n) = n := by
  funext i; simp [srcOf]

/-- Source labels `I^{src}_i = n^{src}_i + ρ_i` (`ρ_j = (N+1-2j)/2`, zero-based
`ρ_i = (N-1)/2 - i`) are the DEF-006 labels in reversed enumeration; nothing is negated. -/
theorem sourceNumbers_srcOf (n : Fin N → ℤ) (i : Fin N) :
    sourceNumbers (srcOf n) i = quantumNumbers n (Fin.rev i) := by
  have h := quantumNumbers_reverse n i
  simp only [sourceNumbers, srcOf]
  rw [h]; ring

theorem sourceNumbers_labels (ℓ : LogLabels N) (i : Fin N) :
    sourceNumbers (srcOf (correctedInt ℓ)) i = ℓ.I (Fin.rev i) := by
  rw [sourceNumbers_srcOf, quantumNumbers_correctedInt]

/-- **The accepted source root vector is the reversed DEF-006 root vector**:
`sourceRoots L n^{src} c = (roots L n c) ∘ rev`, equivalently `q^{src}_i = q_{N+1-i}`. -/
theorem sourceRoots_eq_roots_rev (hL : 0 < L) (hc : 0 < c) (n : Fin N → ℤ) (i : Fin N) :
    sourceRoots L (srcOf n) c i = roots L n c (Fin.rev i) := by
  have hq : logMap L c (fun k => roots L n c (Fin.rev k)) =
      fun i => 2 * Real.pi * sourceNumbers (srcOf n) i := by
    funext i
    rw [logMap_rev, roots_solves hL hc n (Fin.rev i), sourceNumbers_srcOf]
  exact (congrFun (BetheConvexity.eq_root hL hc hq) i).symm

/-- **DEF-006 labels ↔ the accepted source theorem (R-4C8D7C9E / `basis:lem:roots`)**, for `c > 0`:
the unique real solution of the rapidity equation exists and equals the accepted root vector; it is
strictly increasing; its reversal is the accepted source root vector `sourceRoots` of the
nonincreasing integers `n^{src}` (source labels `I^{src}_i = I_{rev i}`), which satisfies the printed
equation `basis:eq:logbethe` with `I_j = n_j + ρ_j`, is strictly decreasing, and is unique. -/
theorem bethe_labels_roots (hL : 0 < L) (hc : 0 < c) (ℓ : LogLabels N) :
    (∃! q : Fin N → ℝ, RapidityEq L c ℓ.I q) ∧
    (∀ q, RapidityEq L c ℓ.I q ↔ q = roots L (correctedInt ℓ) c) ∧
    StrictMono (roots L (correctedInt ℓ) c) ∧
    (∀ i, sourceRoots L (srcOf (correctedInt ℓ)) c i = roots L (correctedInt ℓ) c (Fin.rev i)) ∧
    Antitone (srcOf (correctedInt ℓ)) ∧
    (∀ i, sourceNumbers (srcOf (correctedInt ℓ)) i = ℓ.I (Fin.rev i)) ∧
    StrictAnti (sourceRoots L (srcOf (correctedInt ℓ)) c) ∧
    (∀ i, L * sourceRoots L (srcOf (correctedInt ℓ)) c i +
        2 * ∑ j ∈ Finset.univ.erase i, Real.arctan
          ((sourceRoots L (srcOf (correctedInt ℓ)) c i -
            sourceRoots L (srcOf (correctedInt ℓ)) c j) / c) =
        2 * Real.pi * ((srcOf (correctedInt ℓ) i : ℝ) + ((N : ℝ) - 1) / 2 - (i.val : ℝ))) := by
  have hanti := srcOf_antitone (correctedInt_monotone ℓ)
  refine ⟨existsUnique_rapidity hL hc ℓ, rapidityEq_iff_roots hL hc ℓ,
    roots_strictMono_labels hL hc ℓ, sourceRoots_eq_roots_rev hL hc _, hanti,
    sourceNumbers_labels ℓ, sourceRoots_strictAnti hL hc hanti, ?_⟩
  intro i
  have h := sourceRoots_solves hL hc (srcOf (correctedInt ℓ))
  have h2 := congrFun h i
  rw [logMap_erase] at h2
  simpa only [sourceNumbers] using h2

end Bridge


/-- **DEF-006, assembled** (`c`-independent part): corrected integers are the literal integers
`n_j = I_j - j + (N+1)/2`, nondecreasing; their multiplicity array lies in `M_N` with
`m_n = #{j : n_j = n}`, `Σ_n m_n = N`; and labels ↔ corrected integers ↔ `M_N` are bijections. -/
theorem def006 (N : ℕ) :
    (∀ (ℓ : LogLabels N) (j : Fin N), (correctedInt ℓ j : ℝ) =
        ℓ.I j - ((j.val : ℝ) + 1) + ((N : ℝ) + 1) / 2) ∧
    (∀ ℓ : LogLabels N, Monotone (correctedInt ℓ)) ∧
    (∀ (ℓ : LogLabels N) (k : ℤ), (labelsEquivArr ℓ).1 k =
        (Finset.univ.filter fun j => correctedInt ℓ j = k).card) ∧
    (∀ ℓ : LogLabels N, ((labelsEquivArr ℓ).1.sum fun _ k => k) = N) ∧
    Function.Bijective (labelsEquivCorrected (N := N)) ∧
    Function.Bijective (correctedEquivArr (N := N)) ∧
    Function.Bijective (labelsEquivArr (N := N)) :=
  ⟨correctedInt_spec, correctedInt_monotone, labelsEquivArr_apply, labelsEquivArr_sum,
    labelsEquivCorrected.bijective, correctedEquivArr.bijective, labelsEquivArr.bijective⟩

end QuantumNLS.BetheLabels
