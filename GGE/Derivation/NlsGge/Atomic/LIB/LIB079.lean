import Mathlib
import NlsGge.Atomic.LIB.LIB015

/- LIB-079 PRODUCTION (dedup of proof development/LIB079_ALL_A04.lean.txt by proof development: the 17 declarations already landed in NlsGge.Atomic.LIB.LIB015
   (CONTOUR_DEFS_GK38 block, 79.05 circle adapter, 79.18) are deleted and NlsGge.Atomic.LIB.LIB015 is imported; all other text identical).
   LIB-079 assembled (proof development; authors: proof development for the pasted blocks, proof development for C07/C08/C12, 79.04, 79.06, 79.12, 79.13, 79.16, 79.17; no self-review).
   One file, namespace NlsGge.GK38.Lib.SlitContours.  Main signatures of the design (root/gpt6pro_design/NLS_GGE_FIVE_PACKET_DESIGN_20261027T134300Z.md section LIB-079):
   gap_cycle_period (79.13), endpoint_path_integral_tendsto (79.17); all leaves 79.01-79.18 and C01-C12 are declared with the design names.
   Added helper definitions beyond the design: ellipseDeriv, ellipseCoordinates_* lemmas, cutDisc_mono, DiscWithSegment.swap, curveIntegral_subpath_eq', scale_integral. -/

open Set Metric MeasureTheory Filter
open scoped Topology unitInterval Interval

namespace NlsGge.GK38.Lib.SlitContours
noncomputable section
-- BEGIN PASTED H3 BASE: contour library C00-C06, C09-C11, 79.07-79.10 (proof development/*_GK38 files; compiled project_8; `segment_contDiffOn` moved ahead)

theorem subpath_extend_eq {a b : ℂ} (γ : Path a b) (s t : I) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    (γ.subpath s t).extend u = γ.extend ((s : ℝ) + u * ((t : ℝ) - (s : ℝ))) := by
  have hA : (γ.subpath s t).extend u = γ (Icc.convexComb s t ⟨u, hu⟩) :=
    Path.extend_extends' _ ⟨u, hu⟩
  have hw : ((Icc.convexComb s t ⟨u, hu⟩ : I) : ℝ) = (s : ℝ) + u * ((t : ℝ) - (s : ℝ)) := by
    rw [Icc.coe_convexComb]
    ring
  have hB : γ.extend ((s : ℝ) + u * ((t : ℝ) - (s : ℝ))) = γ (Icc.convexComb s t ⟨u, hu⟩) := by
    rw [← hw]
    exact Path.extend_extends' γ _
  rw [hA, hB]

theorem cells_cover (P : TimePartition) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin P.n, (P.cut i.castSucc : ℝ) ≤ t ∧ t ≤ (P.cut i.succ : ℝ) := by
  classical
  set S : Finset (Fin (P.n + 1)) := Finset.univ.filter (fun j => (P.cut j : ℝ) ≤ t) with hS
  have h0 : (0 : Fin (P.n + 1)) ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [P.first]
    simpa using ht.1
  set m := S.max' ⟨0, h0⟩ with hmdef
  have hm : (P.cut m : ℝ) ≤ t := (Finset.mem_filter.1 (Finset.max'_mem S _)).2
  have hmax : ∀ j, (P.cut j : ℝ) ≤ t → j ≤ m := fun j hj =>
    Finset.le_max' S j (by simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hj)
  by_cases hml : m = Fin.last P.n
  · have hn : 0 < P.n := by
      rcases Nat.eq_zero_or_pos P.n with h | h
      · exfalso
        have h2 : Fin.last P.n = 0 := Fin.ext (by simp [h])
        have hl := P.last
        rw [h2, P.first] at hl
        simp at hl
      · exact h
    have ht1 : t = 1 := by
      rw [hml, P.last] at hm
      have : (1 : ℝ) ≤ t := by simpa using hm
      exact le_antisymm ht.2 this
    refine ⟨⟨P.n - 1, by omega⟩, ?_, ?_⟩
    · have hle : (P.cut (Fin.castSucc (⟨P.n - 1, by omega⟩ : Fin P.n)) : ℝ) ≤ 1 := (P.cut _).2.2
      linarith
    · have hfin : (⟨P.n - 1, by omega⟩ : Fin P.n).succ = Fin.last P.n := Fin.ext (by simp; omega)
      rw [hfin, P.last]
      simp
      linarith [ht.2]
  · have hmlt : m.val < P.n := by
      have hne : m.val ≠ P.n := fun h => hml (Fin.ext h)
      have hle : m.val ≤ P.n := Nat.lt_succ_iff.mp m.isLt
      omega
    refine ⟨⟨m.val, hmlt⟩, ?_, ?_⟩
    · have : (⟨m.val, hmlt⟩ : Fin P.n).castSucc = m := by ext; simp
      rw [this]; exact hm
    · by_contra hcon
      push_neg at hcon
      have hsucc : (⟨m.val, hmlt⟩ : Fin P.n).succ ≤ m := hmax _ (le_of_lt hcon)
      have hgt : m < (⟨m.val, hmlt⟩ : Fin P.n).succ := by
        rw [Fin.lt_def]
        simp
      exact absurd hsucc (not_le.mpr hgt)

/-- Leaf C02b-refine: each new cell lies inside one old cell (order theory). -/
theorem refine_cell (P : TimePartition) (S T' : ℝ) (hST : S < T') (hS0 : 0 ≤ S) (hT1 : T' ≤ 1)
    (Tset : Set (Icc (0 : ℝ) 1))
    (hPT : ∀ i : Fin (P.n + 1),
      Set.projIcc (0 : ℝ) 1 zero_le_one (((P.cut i : ℝ) - S) / (T' - S)) ∈ Tset)
    (Q : TimePartition) (hmem : ∀ j, Q.cut j ∈ Tset)
    (hsurj : ∀ x ∈ Tset, ∃ j, Q.cut j = x)
    (j : Fin Q.n) :
    ∃ i : Fin P.n, (P.cut i.castSucc : ℝ) ≤ S + (Q.cut j.castSucc : ℝ) * (T' - S) ∧
      S + (Q.cut j.succ : ℝ) * (T' - S) ≤ (P.cut i.succ : ℝ) := by
  have hd : (0 : ℝ) < T' - S := by linarith
  have hQlt : (Q.cut j.castSucc : ℝ) < (Q.cut j.succ : ℝ) :=
    Subtype.coe_lt_coe.mpr (Q.strict (Fin.castSucc_lt_succ (i := j)))
  have hQ0 : (0 : ℝ) ≤ (Q.cut j.castSucc : ℝ) := (Q.cut j.castSucc).2.1
  have hQ1 : (Q.cut j.succ : ℝ) ≤ 1 := (Q.cut j.succ).2.2
  have hxlt : S + (Q.cut j.castSucc : ℝ) * (T' - S) < S + (Q.cut j.succ : ℝ) * (T' - S) := by
    have := mul_lt_mul_of_pos_right hQlt hd
    linarith
  have hxS : S ≤ S + (Q.cut j.castSucc : ℝ) * (T' - S) := by
    have := mul_nonneg hQ0 hd.le
    linarith
  have hxT : S + (Q.cut j.succ : ℝ) * (T' - S) ≤ T' := by
    have := mul_le_mul_of_nonneg_right hQ1 hd.le
    linarith
  have hnob : ∀ k : Fin (P.n + 1), S + (Q.cut j.castSucc : ℝ) * (T' - S) < (P.cut k : ℝ) →
      (P.cut k : ℝ) < S + (Q.cut j.succ : ℝ) * (T' - S) → False := by
    intro k hk1 hk2
    obtain ⟨m, hm⟩ := hsurj _ (hPT k)
    have hmem01 : ((P.cut k : ℝ) - S) / (T' - S) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · apply div_nonneg _ hd.le
        linarith
      · rw [div_le_one hd]
        linarith
    have hvalm : (Q.cut m : ℝ) = ((P.cut k : ℝ) - S) / (T' - S) := by
      rw [hm, Set.projIcc_of_mem zero_le_one hmem01]
    have h1 : (Q.cut j.castSucc : ℝ) < (Q.cut m : ℝ) := by
      rw [hvalm, lt_div_iff₀ hd]
      linarith
    have h2 : (Q.cut m : ℝ) < (Q.cut j.succ : ℝ) := by
      rw [hvalm, div_lt_iff₀ hd]
      linarith
    have h1' : j.castSucc < m := Q.strict.lt_iff_lt.mp (Subtype.coe_lt_coe.mp h1)
    have h2' : m < j.succ := Q.strict.lt_iff_lt.mp (Subtype.coe_lt_coe.mp h2)
    rw [Fin.lt_def, Fin.coe_castSucc] at h1'
    rw [Fin.lt_def, Fin.val_succ] at h2'
    omega
  obtain ⟨i, hi1, hi2⟩ := cells_cover P (((S + (Q.cut j.castSucc : ℝ) * (T' - S)) +
      (S + (Q.cut j.succ : ℝ) * (T' - S))) / 2)
    ⟨by linarith, by linarith⟩
  refine ⟨i, ?_, ?_⟩
  · by_contra hcon
    push_neg at hcon
    exact hnob i.castSucc hcon (by linarith)
  · by_contra hcon
    push_neg at hcon
    exact hnob i.succ (by linarith) hcon

/-- Leaf C02b-cellC1: a cell of a subpath lying inside one old C¹ cell is C¹ (double reparametrization). -/
theorem cell_subpath_c1 {a b : ℂ} (γ : Path a b) (P : TimePartition) (i : Fin P.n)
    (hold : ContDiffOn ℝ 1 (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend (Icc (0 : ℝ) 1))
    (s t : I) (hst : (s : ℝ) < (t : ℝ))
    (ua ub : I) (hab : ua < ub)
    (hx : (P.cut i.castSucc : ℝ) ≤ (s : ℝ) + (ua : ℝ) * ((t : ℝ) - (s : ℝ)))
    (hx2 : (s : ℝ) + (ub : ℝ) * ((t : ℝ) - (s : ℝ)) ≤ (P.cut i.succ : ℝ)) :
    ContDiffOn ℝ 1 ((γ.subpath s t).subpath ua ub).extend (Icc (0 : ℝ) 1) := by
  have hcd : (P.cut i.castSucc : ℝ) < (P.cut i.succ : ℝ) :=
    Subtype.coe_lt_coe.mpr (P.strict (Fin.castSucc_lt_succ (i := i)))
  set ca : ℝ := (P.cut i.castSucc : ℝ) with hca
  set cb : ℝ := (P.cut i.succ : ℝ) with hcb
  have hts : 0 < (t : ℝ) - (s : ℝ) := by linarith
  have hab' : (ua : ℝ) < (ub : ℝ) := Subtype.coe_lt_coe.mpr hab
  have hcbd : 0 < cb - ca := by linarith
  -- the affine parameter of the old cell
  have hAsm : ContDiffOn ℝ 1 (fun w : ℝ => ((s : ℝ) + ((ua : ℝ) + w * ((ub : ℝ) - (ua : ℝ))) *
      ((t : ℝ) - (s : ℝ)) - ca) / (cb - ca)) (Icc (0 : ℝ) 1) := by
    apply ContDiff.contDiffOn
    fun_prop
  have hAmaps : MapsTo (fun w : ℝ => ((s : ℝ) + ((ua : ℝ) + w * ((ub : ℝ) - (ua : ℝ))) *
      ((t : ℝ) - (s : ℝ)) - ca) / (cb - ca)) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro w hw
    have hw1 : 0 ≤ w * (((ub : ℝ) - (ua : ℝ)) * ((t : ℝ) - (s : ℝ))) :=
      mul_nonneg hw.1 (mul_nonneg (by linarith) hts.le)
    have hw2 : w * (((ub : ℝ) - (ua : ℝ)) * ((t : ℝ) - (s : ℝ))) ≤
        ((ub : ℝ) - (ua : ℝ)) * ((t : ℝ) - (s : ℝ)) :=
      mul_le_of_le_one_left (mul_nonneg (by linarith) hts.le) hw.2
    constructor
    · apply div_nonneg _ hcbd.le
      nlinarith
    · rw [div_le_one hcbd]
      nlinarith
  -- the cell parameter lies in [0,1]
  have hUmem : ∀ w ∈ Icc (0 : ℝ) 1, ((ua : ℝ) + w * ((ub : ℝ) - (ua : ℝ))) ∈ Icc (0 : ℝ) 1 := by
    intro w hw
    constructor
    · nlinarith [ua.2.1, ub.2.1, hw.1, hw.2, mul_nonneg hw.1 ub.2.1,
        mul_nonneg (sub_nonneg.2 hw.2) ua.2.1]
    · nlinarith [ua.2.2, ub.2.2, hw.1, hw.2, mul_nonneg hw.1 (sub_nonneg.2 ub.2.2),
        mul_nonneg (sub_nonneg.2 hw.2) (sub_nonneg.2 ua.2.2)]
  have hcongr : ∀ w ∈ Icc (0 : ℝ) 1,
      ((γ.subpath s t).subpath ua ub).extend w =
        (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend
          (((s : ℝ) + ((ua : ℝ) + w * ((ub : ℝ) - (ua : ℝ))) * ((t : ℝ) - (s : ℝ)) - ca) / (cb - ca)) := by
    intro w hw
    rw [subpath_extend_eq (γ.subpath s t) ua ub w hw,
      subpath_extend_eq γ s t _ (hUmem w hw)]
    rw [subpath_extend_eq γ (P.cut i.castSucc) (P.cut i.succ) _ (hAmaps hw)]
    congr 1
    rw [div_mul_cancel₀ _ hcbd.ne']
    ring
  have hcomp := hold.comp hAsm hAmaps
  exact hcomp.congr (fun w hw => hcongr w hw)

/-- Leaf C02a: a finite set of parameters containing 0 and 1 is the cut set of a time partition. -/
theorem exists_partition_of_finset (T : Finset I) (h0 : (0 : I) ∈ T) (h1 : (1 : I) ∈ T) :
    ∃ P : TimePartition, (∀ j, P.cut j ∈ T) ∧ (∀ x ∈ T, ∃ j, P.cut j = x) := by
  have hcard : 1 < T.card := Finset.one_lt_card.mpr ⟨0, h0, 1, h1, zero_ne_one⟩
  have hc : (T.card - 1) + 1 = T.card := by omega
  set e := T.orderEmbOfFin rfl with he
  have hpos : 0 < T.card := by omega
  refine ⟨⟨T.card - 1, fun j => e (Fin.cast hc j), ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- first
    have h : Fin.cast hc (0 : Fin (T.card - 1 + 1)) = ⟨0, hpos⟩ := Fin.ext rfl
    simp only [h, he]
    rw [Finset.orderEmbOfFin_zero rfl hpos]
    apply le_antisymm
    · exact Finset.min'_le _ _ h0
    · exact Finset.le_min' _ _ _ (fun y _ => unitInterval.nonneg' (t := y))
  · -- last
    have h : Fin.cast hc (Fin.last (T.card - 1)) = ⟨T.card - 1, by omega⟩ := Fin.ext rfl
    simp only [h, he]
    rw [Finset.orderEmbOfFin_last rfl hpos]
    apply le_antisymm
    · exact Finset.max'_le _ _ _ (fun y _ => unitInterval.le_one' (t := y))
    · exact Finset.le_max' _ _ h1
  · -- strictly monotone
    intro a b hab
    apply e.strictMono
    rw [Fin.lt_def] at hab ⊢
    simpa using hab
  · intro j
    exact Finset.orderEmbOfFin_mem T rfl _
  · intro x hx
    have hr : x ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]
      exact hx
    obtain ⟨i, hi⟩ := hr
    refine ⟨Fin.cast hc.symm i, ?_⟩
    simp only
    have : Fin.cast hc (Fin.cast hc.symm i) = i := Fin.ext rfl
    rw [this]
    exact hi


/-- Leaf C02c: the subpath of a piecewise C¹ path on [s,t] (s < t) is piecewise C¹. -/
theorem piecewiseC1_subpath_lt {a b : ℂ} (γ : Path a b) (hγ : PiecewiseC1 γ) (s t : I)
    (hst : s < t) : PiecewiseC1 (γ.subpath s t) := by
  obtain ⟨P, hP⟩ := hγ
  have hst' : (s : ℝ) < (t : ℝ) := Subtype.coe_lt_coe.mpr hst
  set f : Fin (P.n + 1) → Icc (0 : ℝ) 1 := fun i =>
    Set.projIcc (0 : ℝ) 1 zero_le_one (((P.cut i : ℝ) - (s : ℝ)) / ((t : ℝ) - (s : ℝ))) with hf
  set T : Finset (Icc (0 : ℝ) 1) := insert 0 (insert 1 (Finset.univ.image f)) with hT
  have hTmem : ∀ i, f i ∈ T := fun i => by
    simp only [hT, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨i, rfl⟩)
  have h0T : (0 : Icc (0 : ℝ) 1) ∈ T := by simp [hT]
  have h1T : (1 : Icc (0 : ℝ) 1) ∈ T := by simp [hT]
  obtain ⟨Q, hQmem, hQsurj⟩ := exists_partition_of_finset T h0T h1T
  refine ⟨Q, fun j => ?_⟩
  obtain ⟨i, hi1, hi2⟩ := refine_cell P (s : ℝ) (t : ℝ) hst' s.2.1 t.2.2 (↑T)
    (fun i => Finset.mem_coe.mpr (hTmem i)) Q
    (fun j => Finset.mem_coe.mpr (hQmem j)) (fun x hx => hQsurj x (Finset.mem_coe.mp hx)) j
  have hab : Q.cut j.castSucc < Q.cut j.succ := Q.strict (Fin.castSucc_lt_succ (i := j))
  exact cell_subpath_c1 γ P i (hP i) s t hst' (Q.cut j.castSucc) (Q.cut j.succ) hab hi1 hi2

-- CONTOUR_HELPERS BEGIN (leaf-local helper definitions; merge as one block)
/-- Leaf C02d-revpart: reversal of a time partition. -/
def revPartition (R : TimePartition) : TimePartition where
  n := R.n
  cut := fun i => unitInterval.symm (R.cut (Fin.rev i))
  first := by
    show unitInterval.symm (R.cut (Fin.rev 0)) = 0
    have h : Fin.rev (0 : Fin (R.n + 1)) = Fin.last R.n := by
      apply Fin.ext
      simp [Fin.val_rev]
    rw [h, R.last, unitInterval.symm_one]
  last := by
    show unitInterval.symm (R.cut (Fin.rev (Fin.last R.n))) = 1
    have h : Fin.rev (Fin.last R.n) = (0 : Fin (R.n + 1)) := by
      apply Fin.ext
      simp [Fin.val_rev]
    rw [h, R.first, unitInterval.symm_zero]
  strict := by
    intro i j hij
    show unitInterval.symm (R.cut (Fin.rev i)) < unitInterval.symm (R.cut (Fin.rev j))
    rw [unitInterval.symm_lt_symm]
    apply R.strict
    have hij' : (i : ℕ) < (j : ℕ) := hij
    have hi := i.2
    have hj := j.2
    rw [Fin.lt_def, Fin.val_rev, Fin.val_rev]
    omega

/-- Leaf C02d-single: the one-cell partition of [0,1]. -/
def singlePartition : TimePartition where
  n := 1
  cut := ![0, 1]
  first := rfl
  last := rfl
  strict := by
    apply Fin.strictMono_iff_lt_succ.2
    intro i
    fin_cases i
    exact zero_lt_one
-- CONTOUR_HELPERS END

/-- Leaf C02d-aux: affine interpolation between two points of [0,1] stays in [0,1]. -/
theorem affine_mem_Icc_contour (x y : I) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (x : ℝ) + u * ((y : ℝ) - (x : ℝ)) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨hu0, hu1⟩ := hu
  have hx0 := x.2.1
  have hx1 := x.2.2
  have hy0 := y.2.1
  have hy1 := y.2.2
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hu1) hx0, mul_nonneg hu0 hy0]
  · nlinarith [mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hx1), mul_nonneg hu0 (sub_nonneg.2 hy1)]

/-- Leaf C02d-rev-identity: a subpath of a subpath, read backwards. -/
theorem subpath_subpath_rev_extend {a b : ℂ} (γ : Path a b) (s t x y : I) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    ((γ.subpath s t).subpath x y).extend u =
      ((γ.subpath t s).subpath (unitInterval.symm y) (unitInterval.symm x)).extend (1 - u) := by
  have hu' : (1 - u) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  rw [subpath_extend_eq (γ.subpath s t) x y u hu,
    subpath_extend_eq γ s t _ (affine_mem_Icc_contour x y hu),
    subpath_extend_eq (γ.subpath t s) (unitInterval.symm y) (unitInterval.symm x) (1 - u) hu',
    subpath_extend_eq γ t s _
      (affine_mem_Icc_contour (unitInterval.symm y) (unitInterval.symm x) hu')]
  congr 1
  simp only [unitInterval.coe_symm_eq]
  ring

/-- Leaf C02d-revcells: cells of the reversed partition are reversed cells. -/
theorem revPartition_cell_eq (R : TimePartition) (i : Fin (revPartition R).n) :
    (revPartition R).cut i.castSucc = unitInterval.symm (R.cut (Fin.rev i).succ) ∧
    (revPartition R).cut i.succ = unitInterval.symm (R.cut (Fin.rev i).castSucc) := by
  have h1 : Fin.rev i.castSucc = (Fin.rev i).succ := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
    have := i.2
    omega
  have h2 : Fin.rev i.succ = (Fin.rev i).castSucc := by
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
    have := i.2
    omega
  exact ⟨congrArg (fun k : Fin (R.n + 1) => unitInterval.symm (R.cut k)) h1,
    congrArg (fun k : Fin (R.n + 1) => unitInterval.symm (R.cut k)) h2⟩

/-- Leaf C02d-gt: the subpath from s down to t (t < s) is piecewise C¹. -/
theorem piecewiseC1_subpath_gt {a b : ℂ} (γ : Path a b) (hγ : PiecewiseC1 γ) (s t : I)
    (hts : t < s) : PiecewiseC1 (γ.subpath s t) := by
  obtain ⟨R, hR⟩ := piecewiseC1_subpath_lt γ hγ t s hts
  refine ⟨revPartition R, fun i => ?_⟩
  obtain ⟨h1, h2⟩ := revPartition_cell_eq R i
  rw [h1, h2]
  have hcomp : ContDiffOn ℝ 1
      (((γ.subpath t s).subpath (R.cut (Fin.rev i).castSucc) (R.cut (Fin.rev i).succ)).extend
        ∘ fun u : ℝ => 1 - u) (Icc (0 : ℝ) 1) := by
    refine (hR (Fin.rev i)).comp ?_ ?_
    · exact (contDiff_const.sub contDiff_id).contDiffOn
    · intro u hu
      obtain ⟨hu0, hu1⟩ := hu
      exact ⟨by dsimp only; linarith, by dsimp only; linarith⟩
  refine hcomp.congr (fun u hu => ?_)
  simp only [Function.comp]
  rw [subpath_subpath_rev_extend γ s t _ _ u hu, unitInterval.symm_symm, unitInterval.symm_symm]

/-- Leaf C02d-const-extend: every subpath of the constant subpath s→s is constant. -/
theorem subpath_self_extend {a b : ℂ} (γ : Path a b) (s : I) (x y : I) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    ((γ.subpath s s).subpath x y).extend u = γ.extend s := by
  rw [subpath_extend_eq (γ.subpath s s) x y u hu,
    subpath_extend_eq γ s s _ (affine_mem_Icc_contour x y hu)]
  simp

/-- Leaf C02d-const: the constant subpath s→s is piecewise C¹. -/
theorem piecewiseC1_subpath_self {a b : ℂ} (γ : Path a b) (s : I) :
    PiecewiseC1 (γ.subpath s s) := by
  refine ⟨singlePartition, fun i => ?_⟩
  exact contDiffOn_const (c := γ.extend s) |>.congr
    (fun u hu => subpath_self_extend γ s _ _ u hu)

/-- Leaf C02d: every subpath of a piecewise C¹ path is piecewise C¹. -/
theorem piecewiseC1_subpath {a b : ℂ} (γ : Path a b)
    (hγ : PiecewiseC1 γ) (s t : I) :
    PiecewiseC1 (γ.subpath s t) := by
  rcases lt_trichotomy s t with h | h | h
  · exact piecewiseC1_subpath_lt γ hγ s t h
  · rw [h]
    exact piecewiseC1_subpath_self γ t
  · exact piecewiseC1_subpath_gt γ hγ s t h

/-- Leaf C03-chain: derivative of an affine reparametrisation, valid without differentiability. -/
theorem deriv_affine_chain (g : ℝ → ℂ) (c d u : ℝ) :
    deriv (fun u' : ℝ => g (c * u' + d)) u = c • deriv g (c * u + d) := by
  have h := deriv_comp_mul_left c (fun v : ℝ => g (v + d)) u
  rw [deriv_comp_add_const] at h
  exact h

/-- Leaf C03-affine: subpath extension as an affine reparametrisation of the parent path. -/
theorem subpath_extend_eq_affine {a b : ℂ} (γ : Path a b) (s t : I) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    (γ.subpath s t).extend u = γ.extend (((t : ℝ) - (s : ℝ)) * u + (s : ℝ)) := by
  rw [subpath_extend_eq γ s t u hu]
  congr 1
  ring

/-- Leaf C03-deriv: the derivative of a subpath extension on the open unit interval. -/
theorem deriv_subpath_extend_Ioo {a b : ℂ} (γ : Path a b) (s t : I) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    deriv (γ.subpath s t).extend u =
      ((t : ℝ) - (s : ℝ)) • deriv γ.extend (((t : ℝ) - (s : ℝ)) * u + (s : ℝ)) := by
  have hev : (γ.subpath s t).extend =ᶠ[𝓝 u]
      fun u' : ℝ => γ.extend (((t : ℝ) - (s : ℝ)) * u' + (s : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with u' hu'
    exact subpath_extend_eq_affine γ s t u' (Ioo_subset_Icc_self hu')
  rw [hev.deriv_eq]
  exact deriv_affine_chain γ.extend _ _ u

/-- Leaf C03-cov: change of variables for an affine reparametrisation of an interval integral. -/
theorem integral_affine_complex (H : ℝ → ℂ) (s t : ℝ) (hst : s ≠ t) :
    ∫ u in (0 : ℝ)..1, (((t - s : ℝ)) : ℂ) * H ((t - s) * u + s) = ∫ x in s..t, H x := by
  have hc : t - s ≠ 0 := sub_ne_zero.2 (Ne.symm hst)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_add _ hc]
  rw [show (t - s) * 0 + s = s by ring, show (t - s) * 1 + s = t by ring, Complex.real_smul]
  have hc' : ((t - s : ℝ) : ℂ) * (((t - s)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hc, Complex.ofReal_one]
  linear_combination (∫ x in s..t, H x) * hc'

/-- Leaf C03: the subpath integral is the restricted parameter integral. -/
theorem curveIntegral_subpath_eq {a b : ℂ} (γ : Path a b)
    (hγ : PiecewiseC1 γ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (range γ)) (s t : I) :
    curveIntegral (complexForm f) (γ.subpath s t) =
      ∫ u : ℝ in (s : ℝ)..(t : ℝ), f (γ.extend u) * deriv γ.extend u := by
  have hx1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp only [complexForm, ContinuousLinearMap.mul_apply']
  by_cases hst : s = t
  · subst hst
    rw [intervalIntegral.integral_same]
    have key : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) 1 →
        f ((γ.subpath s s).extend x) * deriv (γ.subpath s s).extend x = 0 := by
      filter_upwards [hx1] with x hx1' hx
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1'⟩
      rw [deriv_subpath_extend_Ioo γ s s hxI]
      simp
    rw [intervalIntegral.integral_congr_ae key]
    simp
  · have key : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) 1 →
        f ((γ.subpath s t).extend x) * deriv (γ.subpath s t).extend x =
          (((t : ℝ) - (s : ℝ) : ℝ) : ℂ) *
            (f (γ.extend (((t : ℝ) - (s : ℝ)) * x + (s : ℝ))) *
              deriv γ.extend (((t : ℝ) - (s : ℝ)) * x + (s : ℝ))) := by
      filter_upwards [hx1] with x hx1' hx
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1'⟩
      rw [subpath_extend_eq_affine γ s t x (Ioo_subset_Icc_self hxI),
        deriv_subpath_extend_Ioo γ s t hxI]
      simp only [Complex.real_smul]
      ring
    rw [intervalIntegral.integral_congr_ae key]
    exact integral_affine_complex (fun v => f (γ.extend v) * deriv γ.extend v) (s : ℝ) (t : ℝ)
      (fun h => hst (Subtype.ext h))

/-- Calculus core: derivative of a function composed with an affine change of variable. -/
theorem cell_deriv_affine (g : ℝ → ℂ) (s d t : ℝ) (hsd : s < d) (ht : t ∈ Ioo s d)
    (hg : DifferentiableAt ℝ g ((t - s) / (d - s))) (F : ℝ → ℂ)
    (hF : F =ᶠ[𝓝 t] fun t' => g ((t' - s) / (d - s))) :
    deriv F t = (d - s)⁻¹ • deriv g ((t - s) / (d - s)) := by
  have hdpos : 0 < d - s := by linarith
  have haff : HasDerivAt (fun t' : ℝ => (t' - s) / (d - s)) (1 / (d - s)) t := by
    have := ((hasDerivAt_id t).sub_const s).div_const (d - s)
    simpa using this
  have hgd : HasDerivAt g (deriv g ((t - s) / (d - s))) ((t - s) / (d - s)) := hg.hasDerivAt
  have hc := hgd.scomp t haff
  rw [hF.deriv_eq]
  have hc' : deriv (fun t' : ℝ => g ((t' - s) / (d - s))) t = (1 / (d - s)) • deriv g ((t - s) / (d - s)) :=
    hc.deriv
  rw [hc', one_div]

/-- Leaf C01b: on an open cell the derivWithin of the global extension is the affine rescaling
of the derivWithin of the cell subpath. -/
theorem cell_derivWithin_transfer {a b : ℂ} (γ : Path a b) (P : TimePartition) (i : Fin P.n)
    (hsub : ContDiffOn ℝ 1 (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend (Icc (0 : ℝ) 1))
    (hlt : (P.cut i.castSucc : ℝ) < (P.cut i.succ : ℝ))
    (t : ℝ) (ht : t ∈ Ioo (P.cut i.castSucc : ℝ) (P.cut i.succ : ℝ)) :
    derivWithin γ.extend (Icc (0 : ℝ) 1) t =
      ((P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ))⁻¹ •
        derivWithin (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend (Icc (0 : ℝ) 1)
          ((t - (P.cut i.castSucc : ℝ)) / ((P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ))) := by
  have hdpos : (0 : ℝ) < (P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ) := by linarith
  have hev' : ∀ t' ∈ Ioo (P.cut i.castSucc : ℝ) (P.cut i.succ : ℝ),
      γ.extend t' = (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend
        ((t' - (P.cut i.castSucc : ℝ)) / ((P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ))) := by
    intro t' ht'
    have hu' : ((t' - (P.cut i.castSucc : ℝ)) / ((P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ)))
        ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith [ht'.1]) hdpos.le, by rw [div_le_one hdpos]; linarith [ht'.2]⟩
    rw [subpath_extend_eq γ _ _ _ hu']
    congr 1
    rw [div_mul_cancel₀ _ hdpos.ne']
    ring
  have htI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith [ht.1, (P.cut i.castSucc).2.1], by linarith [ht.2, (P.cut i.succ).2.2]⟩
  have hu : ((t - (P.cut i.castSucc : ℝ)) / ((P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ))) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (by linarith [ht.1]) hdpos
    · rw [div_lt_one hdpos]; linarith [ht.2]
  have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds htI.1 htI.2
  have hIccu : Icc (0 : ℝ) 1 ∈ 𝓝 ((t - (P.cut i.castSucc : ℝ)) / ((P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ))) :=
    Icc_mem_nhds hu.1 hu.2
  have hev2 : γ.extend =ᶠ[𝓝 t] fun t' => (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend
      ((t' - (P.cut i.castSucc : ℝ)) / ((P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ))) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t' ht'
    exact hev' t' ht'
  have hgdiff : DifferentiableAt ℝ (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend
      ((t - (P.cut i.castSucc : ℝ)) / ((P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ))) :=
    (hsub.differentiableOn (by norm_num)).differentiableAt hIccu
  rw [derivWithin_of_mem_nhds hIcc, cell_deriv_affine _ _ _ _ hlt ht hgdiff _ hev2,
    derivWithin_of_mem_nhds hIccu]


/-- Leaf C01c: the integrand on one cell of a piecewise C¹ path is interval integrable. -/
theorem cell_integrable {a b : ℂ} (γ : Path a b) (P : TimePartition) (i : Fin P.n)
    (hsub : ContDiffOn ℝ 1 (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend (Icc (0 : ℝ) 1))
    (hlt : (P.cut i.castSucc : ℝ) < (P.cut i.succ : ℝ))
    (f : ℂ → ℂ) (hf : ContinuousOn f (range γ)) :
    IntervalIntegrable (fun t => f (γ.extend t) * derivWithin γ.extend (Icc (0 : ℝ) 1) t) volume
      (P.cut i.castSucc : ℝ) (P.cut i.succ : ℝ) := by
  set s : ℝ := (P.cut i.castSucc : ℝ) with hsdef
  set d : ℝ := (P.cut i.succ : ℝ) with hddef
  have hs0 : 0 ≤ s := (P.cut i.castSucc).2.1
  have hd1 : d ≤ 1 := (P.cut i.succ).2.2
  have hsd : s ≤ d := hlt.le
  have hdpos : 0 < d - s := by linarith
  have hsub_c : ContinuousOn (derivWithin (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend
      (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) :=
    hsub.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  have hγc : ContinuousOn γ.extend (Icc s d) := γ.continuous_extend.continuousOn
  have hmaps : MapsTo γ.extend (Icc s d) (range γ) := by
    intro t ht
    have hI : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans hs0 ht.1, le_trans ht.2 hd1⟩
    have h := Path.extend_extends' γ ⟨t, hI⟩
    exact ⟨⟨t, hI⟩, h.symm⟩
  have hfγ : ContinuousOn (fun t => f (γ.extend t)) (Icc s d) :=
    ContinuousOn.comp hf hγc hmaps
  have haff : ContinuousOn (fun t : ℝ => (t - s) / (d - s)) (Icc s d) :=
    (((continuous_id.sub continuous_const).div_const _)).continuousOn
  have haffmaps : MapsTo (fun t : ℝ => (t - s) / (d - s)) (Icc s d) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ⟨div_nonneg (by linarith [ht.1]) hdpos.le, by rw [div_le_one hdpos]; linarith [ht.2]⟩
  have hder : ContinuousOn (fun t : ℝ => (d - s)⁻¹ •
      derivWithin (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend (Icc (0 : ℝ) 1)
        ((t - s) / (d - s))) (Icc s d) :=
    (ContinuousOn.comp hsub_c haff haffmaps).const_smul ((d - s)⁻¹)
  have hH : ContinuousOn (fun t : ℝ => f (γ.extend t) * ((d - s)⁻¹ •
      derivWithin (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend (Icc (0 : ℝ) 1)
        ((t - s) / (d - s)))) (uIcc s d) := by
    rw [uIcc_of_le hsd]
    exact hfγ.mul hder
  have hint := hH.intervalIntegrable (μ := (volume : Measure ℝ))
  apply IntervalIntegrable.congr_uIoo hint
  intro t ht
  have ht' : t ∈ Ioo s d := by
    rw [uIoo_of_le hsd] at ht
    exact ht
  simp only
  rw [cell_derivWithin_transfer γ P i hsub hlt t ht']


/-- Leaf C01: a piecewise C¹ path makes the complex 1-form curve integrable. -/
theorem piecewise_curveIntegrable {a b : ℂ} (γ : Path a b)
    (hγ : PiecewiseC1 γ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (range γ)) :
    CurveIntegrable (complexForm f) γ := by
  obtain ⟨P, hP⟩ := hγ
  have hcell : ∀ i : Fin P.n, IntervalIntegrable
      (fun t => f (γ.extend t) * derivWithin γ.extend (Icc (0 : ℝ) 1) t) volume
      (P.cut i.castSucc : ℝ) (P.cut i.succ : ℝ) := by
    intro i
    have hlt : (P.cut i.castSucc : ℝ) < (P.cut i.succ : ℝ) :=
      Subtype.coe_lt_coe.mpr (P.strict (Fin.castSucc_lt_succ (i := i)))
    exact cell_integrable γ P i (hP i) hlt f hf
  have hpre : ∀ k : ℕ, (hk : k < P.n + 1) → IntervalIntegrable
      (fun t => f (γ.extend t) * derivWithin γ.extend (Icc (0 : ℝ) 1) t) volume 0
      ((P.cut ⟨k, hk⟩ : unitInterval) : ℝ) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 : P.cut ⟨0, hk⟩ = 0 := by
        have : (⟨0, hk⟩ : Fin (P.n + 1)) = 0 := Fin.ext rfl
        rw [this, P.first]
      rw [h0]
      simp
    | succ k ih =>
      intro hk
      have hk' : k < P.n + 1 := by omega
      have hkn : k < P.n := by omega
      have h1 := ih hk'
      have h2 := hcell ⟨k, hkn⟩
      have e1 : (⟨k, hkn⟩ : Fin P.n).castSucc = ⟨k, hk'⟩ := rfl
      have e2 : (⟨k, hkn⟩ : Fin P.n).succ = ⟨k + 1, hk⟩ := rfl
      rw [e1, e2] at h2
      exact h1.trans h2
  have hlast : ((P.cut ⟨P.n, by omega⟩ : unitInterval) : ℝ) = 1 := by
    have : (⟨P.n, by omega⟩ : Fin (P.n + 1)) = Fin.last P.n := rfl
    rw [this, P.last]
    simp
  have hfin := hpre P.n (by omega)
  rw [hlast] at hfin
  unfold CurveIntegrable
  have heq : curveIntegralFun (complexForm f) γ =
      fun t => f (γ.extend t) * derivWithin γ.extend (Icc (0 : ℝ) 1) t := by
    funext t
    rw [curveIntegralFun_def]
    rfl
  rw [heq]
  exact hfin

/-- Leaf C05: primitive theorem for a C¹ path. -/
theorem primitive_curveIntegral_c1 {a b : ℂ} (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc (0 : ℝ) 1))
    (U : Set ℂ) (f P : ℂ → ℂ)
    (hU : IsOpen U) (hγU : range γ ⊆ U)
    (hf : ContinuousOn f U)
    (hP : ∀ z ∈ U, HasDerivAt P (f z) z) :
    curveIntegral (complexForm f) γ = P b - P a := by
  have hmemU : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ U := by
    intro t ht
    have h : γ.extend t = γ ⟨t, ht⟩ := Path.extend_extends' γ ⟨t, ht⟩
    rw [h]
    exact hγU (mem_range_self _)
  have hγcont : ContinuousOn (fun t => γ.extend t) (Icc (0 : ℝ) 1) :=
    hγ.continuousOn
  have hPcont : ContinuousOn (fun t => P (γ.extend t)) (Icc (0 : ℝ) 1) := by
    intro t ht
    have hd : DifferentiableAt ℂ P (γ.extend t) := (hP _ (hmemU t ht)).differentiableAt
    exact (hd.continuousAt.comp_continuousWithinAt (hγcont t ht))
  have hdiffγ : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ.extend x := by
    intro x hx
    have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    exact (hγ.differentiableOn (by norm_num) x (Ioo_subset_Icc_self hx)).differentiableAt hIcc
  have hderivD : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun t => P (γ.extend t)) (f (γ.extend x) * derivWithin γ.extend (Icc (0 : ℝ) 1) x) x := by
    intro x hx
    have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
    have hγd : HasDerivAt γ.extend (deriv γ.extend x) x := (hdiffγ x hx).hasDerivAt
    have hPd : HasDerivAt P (f (γ.extend x)) (γ.extend x) := hP _ (hmemU x (Ioo_subset_Icc_self hx))
    have hsc := hPd.scomp x hγd
    have hw : derivWithin γ.extend (Icc (0 : ℝ) 1) x = deriv γ.extend x :=
      derivWithin_of_mem_nhds hIcc
    rw [hw]
    have hmc : deriv γ.extend x * f (γ.extend x) = f (γ.extend x) * deriv γ.extend x := mul_comm _ _
    rw [← hmc]
    exact hsc
  have hh : ContinuousOn (fun t => f (γ.extend t) * derivWithin γ.extend (Icc (0 : ℝ) 1) t)
      (Icc (0 : ℝ) 1) := by
    apply ContinuousOn.mul
    · intro t ht
      exact ContinuousWithinAt.comp (hf _ (hmemU t ht)) (hγcont t ht) (fun u hu => hmemU u hu)
    · exact hγ.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [ae_iff]
    simp [measure_singleton]
  have heq : (∫ t in (0 : ℝ)..1, f (γ.extend t) * deriv γ.extend t) =
      ∫ t in (0 : ℝ)..1, f (γ.extend t) * derivWithin γ.extend (Icc (0 : ℝ) 1) t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with x hx hxI
    rw [Set.uIoc_of_le zero_le_one] at hxI
    have hxo : x ∈ Ioo (0 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx⟩
    have hIcc : Icc (0 : ℝ) 1 ∈ 𝓝 x := Icc_mem_nhds hxo.1 hxo.2
    simp only [derivWithin_of_mem_nhds hIcc]
  rw [curveIntegral_eq_intervalIntegral_deriv]
  show ∫ t in (0 : ℝ)..1, f (γ.extend t) * deriv γ.extend t = P b - P a
  rw [heq]
  have hint : IntervalIntegrable (fun t => f (γ.extend t) * derivWithin γ.extend (Icc (0 : ℝ) 1) t)
      (volume : Measure ℝ) 0 1 := hh.intervalIntegrable_of_Icc zero_le_one
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hPcont hderivD hint]
  have hb : γ.extend 1 = b := by
    have h := Path.extend_extends' γ ⟨1, by simp⟩
    simpa using h
  have ha : γ.extend 0 = a := by
    have h := Path.extend_extends' γ ⟨0, by simp⟩
    simpa using h
  rw [hb, ha]

/-- Telescoping over `Fin`: the alternating sum of consecutive differences. -/
theorem fin_telescope {M : Type*} [AddCommGroup M] :
    ∀ (n : ℕ) (g : Fin (n + 1) → M),
      ∑ j : Fin n, (g j.castSucc - g j.succ) = g 0 - g (Fin.last n)
  | 0, g => by simp
  | n + 1, g => by
    rw [Fin.sum_univ_castSucc]
    have ih := fin_telescope n (fun j : Fin (n + 1) => g j.castSucc)
    simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero] at ih ⊢
    rw [ih]
    abel

/-- Leaf C04-int: the curve integrand is interval integrable on [0,1] (derivative version). -/
theorem integrable_H {a b : ℂ} (γ : Path a b) (hγ : PiecewiseC1 γ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (range γ)) :
    IntervalIntegrable (fun u : ℝ => f (γ.extend u) * deriv γ.extend u) volume 0 1 := by
  have hC : IntervalIntegrable (curveIntegralFun (complexForm f) γ) volume 0 1 :=
    piecewise_curveIntegrable γ hγ f hf
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hC ⊢
  have hx1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  refine hC.congr_fun_ae ?_
  filter_upwards [ae_restrict_of_ae hx1,
    ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))] with x hx1' hx
  have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1'⟩
  rw [curveIntegralFun_def, derivWithin_of_mem_nhds (Icc_mem_nhds hxI.1 hxI.2)]
  rfl

/-- Leaf C04-telescope: a finite sum of cell integrals is the total integral. -/
theorem sum_cells_integral (H : ℝ → ℂ) (hH : IntervalIntegrable H volume 0 1) (P : TimePartition) :
    ∑ i : Fin P.n, ∫ u in (P.cut i.castSucc : ℝ)..(P.cut i.succ : ℝ), H u =
      ∫ u in (0 : ℝ)..1, H u := by
  let tt : ℕ → ℝ := fun k => if h : k < P.n + 1 then (P.cut ⟨k, h⟩ : ℝ) else 1
  have ha_mem : ∀ k, tt k ∈ Icc (0 : ℝ) 1 := by
    intro k
    simp only [tt]
    split_ifs
    · exact (P.cut _).2
    · norm_num
  have ha_cast : ∀ i : Fin P.n, tt i = (P.cut i.castSucc : ℝ) := by
    intro i
    simp only [tt]
    rw [dif_pos (by omega)]
    rfl
  have ha_succ : ∀ i : Fin P.n, tt ((i : ℕ) + 1) = (P.cut i.succ : ℝ) := by
    intro i
    simp only [tt]
    rw [dif_pos (by have := i.2; omega)]
    rfl
  have ha0 : tt 0 = 0 := by
    have h0 : (P.cut 0 : ℝ) = 0 := by
      rw [P.first]
      rfl
    simp only [tt]
    rw [dif_pos (Nat.succ_pos _)]
    exact h0
  have han : tt P.n = 1 := by
    have h1 : (P.cut (Fin.last P.n) : ℝ) = 1 := by
      rw [P.last]
      rfl
    simp only [tt]
    rw [dif_pos (Nat.lt_succ_self _)]
    exact h1
  have hint : ∀ k < P.n, IntervalIntegrable H volume (tt k) (tt (k + 1)) := by
    intro k _
    apply hH.mono_set
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le zero_le_one]
      exact ha_mem k
    · rw [Set.uIcc_of_le zero_le_one]
      exact ha_mem (k + 1)
  have key := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) hint
  calc ∑ i : Fin P.n, ∫ u in (P.cut i.castSucc : ℝ)..(P.cut i.succ : ℝ), H u
      = ∑ i : Fin P.n, ∫ x in tt i..tt ((i : ℕ) + 1), H x :=
        Finset.sum_congr rfl (fun i _ => by rw [ha_cast i, ha_succ i])
    _ = ∑ k ∈ Finset.range P.n, ∫ x in tt k..tt (k + 1), H x :=
        Fin.sum_univ_eq_sum_range (fun k => ∫ x in tt k..tt (k + 1), H x) P.n
    _ = ∫ x in tt 0..tt P.n, H x := key
    _ = ∫ u in (0 : ℝ)..1, H u := by rw [ha0, han]

/-- Leaf C04: finite partition additivity of the curve integral. -/
theorem curveIntegral_partition {a b : ℂ} (γ : Path a b)
    (hγ : PiecewiseC1 γ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (range γ)) (P : TimePartition) :
    curveIntegral (complexForm f) γ =
      ∑ i : Fin P.n, curveIntegral (complexForm f)
        (γ.subpath (P.cut i.castSucc) (P.cut i.succ)) := by
  simp only [curveIntegral_subpath_eq γ hγ f hf]
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp only [complexForm, ContinuousLinearMap.mul_apply']
  exact (sum_cells_integral (fun u => f (γ.extend u) * deriv γ.extend u)
    (integrable_H γ hγ f hf) P).symm

/-- Leaf C06: primitive theorem for a piecewise C¹ path. -/
theorem primitive_curveIntegral {a b : ℂ} (γ : Path a b)
    (hγ : PiecewiseC1 γ) (U : Set ℂ) (f P : ℂ → ℂ)
    (hU : IsOpen U) (hγU : range γ ⊆ U)
    (hf : ContinuousOn f U)
    (hP : ∀ z ∈ U, HasDerivAt P (f z) z) :
    curveIntegral (complexForm f) γ = P b - P a := by
  obtain ⟨Q, hQ⟩ := hγ
  rw [curveIntegral_partition γ ⟨Q, hQ⟩ f (hf.mono hγU) Q]
  have hpiece : ∀ i : Fin Q.n,
      curveIntegral (complexForm f) (γ.subpath (Q.cut i.castSucc) (Q.cut i.succ)) =
        P (γ (Q.cut i.succ)) - P (γ (Q.cut i.castSucc)) := by
    intro i
    have hsub : range (γ.subpath (Q.cut i.castSucc) (Q.cut i.succ)) ⊆ U := by
      rintro _ ⟨u, rfl⟩
      exact hγU ⟨Icc.convexComb (Q.cut i.castSucc) (Q.cut i.succ) u, rfl⟩
    exact primitive_curveIntegral_c1 _ (hQ i) U f P hU hsub hf hP
  simp only [hpiece]
  have h2 : ∀ i : Fin Q.n, (P (γ (Q.cut i.succ)) - P (γ (Q.cut i.castSucc))) =
      -(P (γ (Q.cut i.castSucc)) - P (γ (Q.cut i.succ))) := fun i => by ring
  simp only [h2, Finset.sum_neg_distrib]
  rw [fin_telescope Q.n (fun k => P (γ (Q.cut k)))]
  have hl : Q.cut (Fin.last Q.n) = 1 := Q.last
  have h0' : Q.cut 0 = 0 := Q.first
  simp only [hl, h0', Path.target, Path.source]
  ring

/-- Leaf 79.08 aux: local logarithm branch. -/
theorem log_branch_local (h g : ℝ → ℂ) {S : Set ℝ} {u0 : ℝ} (hu0 : u0 ∈ S)
    (hhc : Continuous h) (hgc : Continuous g)
    (hexp : ∀ u ∈ S, Complex.exp (h u) = g u) :
    ∀ᶠ u in 𝓝[S] u0, h u = h u0 + Complex.log (g u / g u0) := by
  have hg0 : g u0 ≠ 0 := by
    rw [← hexp u0 hu0]
    exact Complex.exp_ne_zero _
  set w : ℝ → ℂ := fun u => h u - h u0 - Complex.log (g u / g u0) with hwdef
  have hwc : ContinuousAt w u0 := by
    have hc : ContinuousAt (fun u => g u / g u0) u0 :=
      (hgc.div_const _).continuousAt
    have hmem : g u0 / g u0 ∈ Complex.slitPlane := by
      rw [div_self hg0]
      exact Complex.one_mem_slitPlane
    have hl : ContinuousAt (fun u => Complex.log (g u / g u0)) u0 :=
      hc.clog hmem
    exact (hhc.continuousAt.sub continuousAt_const).sub hl
  have hw0 : w u0 = 0 := by
    simp [hwdef, hg0]
  have hball : ∀ᶠ u in 𝓝 u0, w u ∈ Metric.ball (0 : ℂ) (2 * Real.pi) := by
    have ht : Filter.Tendsto w (𝓝 u0) (𝓝 (w u0)) := hwc
    rw [hw0] at ht
    exact ht (Metric.ball_mem_nhds 0 (by positivity))
  have hexpw : ∀ u ∈ S, Complex.exp (w u) = 1 := by
    intro u hu
    have hgu : g u ≠ 0 := by
      rw [← hexp u hu]
      exact Complex.exp_ne_zero _
    have hx0 : g u / g u0 ≠ 0 := div_ne_zero hgu hg0
    simp only [hwdef]
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log hx0, hexp u hu, hexp u0 hu0,
      div_self hx0]
  have hint : ∀ u ∈ S, w u ∈ Metric.ball (0 : ℂ) (2 * Real.pi) → w u = 0 := by
    intro u hu hb
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hexpw u hu)
    have hnorm : ‖w u‖ < 2 * Real.pi := by
      have hb' := hb
      rw [Metric.mem_ball, dist_zero_right] at hb'
      exact hb'
    rw [hn] at hnorm ⊢
    have hn0 : n = 0 := by
      by_contra hne
      have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
      have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast h1
      have h3 : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
        simp [norm_mul, abs_of_pos Real.pi_pos]
      rw [h3] at hnorm
      nlinarith [Real.pi_pos]
    simp [hn0]
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with u hbu hu
  have h0 := hint u hu hbu
  simp only [hwdef] at h0
  linear_combination h0

/-- Leaf 79.08 aux: the local logarithm branch is C¹ within a set. -/
theorem log_branch_contDiffWithinAt (h g : ℝ → ℂ) {S : Set ℝ} {u0 : ℝ}
    (hg0 : g u0 ≠ 0) (hgd : ContDiffWithinAt ℝ 1 g S u0) :
    ContDiffWithinAt ℝ 1 (fun u => h u0 + Complex.log (g u / g u0)) S u0 := by
  have hF : ContDiffWithinAt ℝ 1 (fun u => g u / g u0) S u0 := hgd.div_const _
  have hl : ContDiffAt ℝ 1 Complex.log (g u0 / g u0) := by
    rw [div_self hg0]
    have hl0 : ContDiffAt ℂ 1 Complex.log 1 := Complex.contDiffAt_log Complex.one_mem_slitPlane
    exact ContDiffAt.restrict_scalars (𝕜 := ℝ) hl0
  have hcomp : ContDiffWithinAt ℝ 1 (Complex.log ∘ fun u => g u / g u0) S u0 :=
    ContDiffAt.comp_contDiffWithinAt u0 hl hF
  exact contDiffWithinAt_const.add hcomp

/-- Leaf 79.08: a logarithm lift of a piecewise C¹ path is piecewise C¹. -/
theorem piecewiseC1_log_lift {a b p q : ℂ}
    (γ : Path a b) (L : Path p q)
    (hγ : PiecewiseC1 γ)
    (hL : ∀ t : I, Complex.exp (L t) = γ t) :
    PiecewiseC1 L := by
  obtain ⟨P, hP⟩ := hγ
  refine ⟨P, fun i => ?_⟩
  have hL' : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Complex.exp (L.extend t) = γ.extend t := by
    intro t ht
    have e1 : L.extend t = L ⟨t, ht⟩ := Path.extend_extends' L ⟨t, ht⟩
    have e2 : γ.extend t = γ ⟨t, ht⟩ := Path.extend_extends' γ ⟨t, ht⟩
    rw [e1, e2]
    exact hL ⟨t, ht⟩
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1,
      (P.cut i.castSucc : ℝ) + u * ((P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ)) ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    obtain ⟨hu0, hu1⟩ := hu
    have hc0 := (P.cut i.castSucc).2.1
    have hc1 := (P.cut i.castSucc).2.2
    have hd0 := (P.cut i.succ).2.1
    have hd1 := (P.cut i.succ).2.2
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 hu1) hc0, mul_nonneg hu0 hd0]
    · nlinarith [mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 hc1), mul_nonneg hu0 (sub_nonneg.2 hd1)]
  have hexpS : ∀ u ∈ Icc (0 : ℝ) 1,
      Complex.exp ((L.subpath (P.cut i.castSucc) (P.cut i.succ)).extend u) =
        (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend u := by
    intro u hu
    rw [subpath_extend_eq L _ _ u hu, subpath_extend_eq γ _ _ u hu]
    exact hL' _ (hmem u hu)
  intro u0 hu0
  have hgd : ContDiffWithinAt ℝ 1 (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend
      (Icc (0 : ℝ) 1) u0 := hP i u0 hu0
  have hloc := log_branch_local
    (L.subpath (P.cut i.castSucc) (P.cut i.succ)).extend
    (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend
    (S := Icc (0 : ℝ) 1) hu0
    (L.subpath (P.cut i.castSucc) (P.cut i.succ)).continuous_extend
    (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).continuous_extend hexpS
  have hg0 : (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend u0 ≠ 0 := by
    rw [← hexpS u0 hu0]
    exact Complex.exp_ne_zero _
  have hk := log_branch_contDiffWithinAt
    (L.subpath (P.cut i.castSucc) (P.cut i.succ)).extend
    (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend hg0 hgd
  exact hk.congr_of_eventuallyEq hloc (by simp [div_self hg0])

/-- Leaf 79.09 aux: on one cell the reciprocal integrand is the derivative of the logarithm lift. -/
theorem cell_reciprocal_eq {a b p q : ℂ} (γ : Path a b) (L : Path p q)
    (hL : ∀ t : I, Complex.exp (L t) = γ t)
    (c d : I) (hcd : c < d)
    (hLc : ContDiffOn ℝ 1 (L.subpath c d).extend (Icc (0 : ℝ) 1))
    (hH : IntervalIntegrable (fun u : ℝ => (γ.extend u)⁻¹ * deriv γ.extend u) volume
      (c : ℝ) (d : ℝ)) :
    ∫ u in (c : ℝ)..(d : ℝ), (γ.extend u)⁻¹ * deriv γ.extend u =
      L.extend (d : ℝ) - L.extend (c : ℝ) := by
  have hL' : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Complex.exp (L.extend t) = γ.extend t := by
    intro t ht
    have e1 : L.extend t = L ⟨t, ht⟩ := Path.extend_extends' L ⟨t, ht⟩
    have e2 : γ.extend t = γ ⟨t, ht⟩ := Path.extend_extends' γ ⟨t, ht⟩
    rw [e1, e2]
    exact hL ⟨t, ht⟩
  have hcd' : (c : ℝ) < (d : ℝ) := Subtype.coe_lt_coe.mpr hcd
  have hne : (d : ℝ) - (c : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (d : ℝ) - (c : ℝ) := by linarith
    exact ne_of_gt this
  have hLf_eq : ∀ t ∈ Ioo (c : ℝ) (d : ℝ),
      L.extend t = (L.subpath c d).extend ((t - (c : ℝ)) / ((d : ℝ) - (c : ℝ))) := by
    intro t ht
    have hu : (t - (c : ℝ)) / ((d : ℝ) - (c : ℝ)) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (by linarith [ht.1]) (by linarith)
      · rw [div_le_one (by linarith)]
        linarith [ht.2]
    rw [subpath_extend_eq L c d _ hu]
    congr 1
    rw [div_mul_cancel₀ _ hne]
    ring
  have hdiff : ∀ t ∈ Ioo (c : ℝ) (d : ℝ), DifferentiableAt ℝ L.extend t := by
    intro t ht
    have hu : (t - (c : ℝ)) / ((d : ℝ) - (c : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos (by linarith [ht.1]) (by linarith)
      · rw [div_lt_one (by linarith)]
        linarith [ht.2]
    have hdu : DifferentiableAt ℝ (L.subpath c d).extend
        ((t - (c : ℝ)) / ((d : ℝ) - (c : ℝ))) :=
      (hLc.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hu.1 hu.2)
    have haff : DifferentiableAt ℝ (fun s : ℝ => (s - (c : ℝ)) / ((d : ℝ) - (c : ℝ))) t :=
      ((differentiableAt_id.sub_const _).div_const _)
    have hcomp : DifferentiableAt ℝ
        ((L.subpath c d).extend ∘ fun s : ℝ => (s - (c : ℝ)) / ((d : ℝ) - (c : ℝ))) t :=
      DifferentiableAt.comp t hdu haff
    have hev : L.extend =ᶠ[𝓝 t]
        fun s : ℝ => (L.subpath c d).extend ((s - (c : ℝ)) / ((d : ℝ) - (c : ℝ))) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hLf_eq s hs
    exact hev.differentiableAt_iff.2 hcomp
  have hgf_eq : ∀ t ∈ Ioo (c : ℝ) (d : ℝ),
      deriv γ.extend t = Complex.exp (L.extend t) * deriv L.extend t := by
    intro t ht
    have hev : γ.extend =ᶠ[𝓝 t] fun s => Complex.exp (L.extend s) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (hL' s ⟨by linarith [hs.1, (c : I).2.1], by linarith [hs.2, (d : I).2.2]⟩).symm
    rw [hev.deriv_eq]
    exact ((hdiff t ht).hasDerivAt.cexp).deriv
  have hint_eq : ∀ t ∈ Ioo (c : ℝ) (d : ℝ),
      (γ.extend t)⁻¹ * deriv γ.extend t = deriv L.extend t := by
    intro t ht
    have hγt : γ.extend t = Complex.exp (L.extend t) :=
      (hL' t ⟨by linarith [ht.1, (c : I).2.1], by linarith [ht.2, (d : I).2.2]⟩).symm
    rw [hgf_eq t ht, hγt, inv_mul_cancel_left₀ (Complex.exp_ne_zero _)]
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (d : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  have hint_congr : ∫ u in (c : ℝ)..(d : ℝ), (γ.extend u)⁻¹ * deriv γ.extend u =
      ∫ u in (c : ℝ)..(d : ℝ), deriv L.extend u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with x hxd hx
    rw [Set.uIoc_of_le hcd'.le] at hx
    exact hint_eq x ⟨hx.1, lt_of_le_of_ne hx.2 hxd⟩
  have hint_deriv : IntervalIntegrable (fun u => deriv L.extend u) volume (c : ℝ) (d : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcd'.le]
    have hH' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd'.le).1 hH
    refine hH'.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae hae,
      ae_restrict_mem (measurableSet_Ioc : MeasurableSet (Ioc (c : ℝ) (d : ℝ)))] with x hxd hx
    exact hint_eq x ⟨hx.1, lt_of_le_of_ne hx.2 hxd⟩
  rw [hint_congr]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcd'.le
    L.continuous_extend.continuousOn
    (fun x hx => (hdiff x hx).hasDerivAt) hint_deriv

/-- Leaf 79.09: the reciprocal integral of a piecewise C¹ path is the logarithm increment. -/
theorem reciprocal_integral_eq_log_increment {a b p q : ℂ}
    (γ : Path a b) (L : Path p q)
    (hγ : PiecewiseC1 γ)
    (hL : ∀ t : I, Complex.exp (L t) = γ t) :
    CurveIntegrable (complexForm (fun z : ℂ => z⁻¹)) γ ∧
    curveIntegral (complexForm (fun z : ℂ => z⁻¹)) γ = q - p := by
  have hnz : ∀ t : I, γ t ≠ 0 := fun t => by
    rw [← hL t]
    exact Complex.exp_ne_zero _
  have hf : ContinuousOn (fun z : ℂ => z⁻¹) (range γ) := by
    refine ContinuousOn.inv₀ continuousOn_id ?_
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    exact hnz t
  have hCI := piecewise_curveIntegrable γ hγ _ hf
  obtain ⟨Q, hQ⟩ := piecewiseC1_log_lift γ L hγ hL
  refine ⟨hCI, ?_⟩
  rw [curveIntegral_partition γ hγ _ hf Q]
  have hcell : ∀ i : Fin Q.n,
      curveIntegral (complexForm (fun z : ℂ => z⁻¹))
          (γ.subpath (Q.cut i.castSucc) (Q.cut i.succ)) =
        L.extend (Q.cut i.succ : ℝ) - L.extend (Q.cut i.castSucc : ℝ) := by
    intro i
    rw [curveIntegral_subpath_eq γ hγ _ hf]
    have hlt : Q.cut i.castSucc < Q.cut i.succ := Q.strict (Fin.castSucc_lt_succ (i := i))
    have hH : IntervalIntegrable (fun u : ℝ => (γ.extend u)⁻¹ * deriv γ.extend u) volume
        (Q.cut i.castSucc : ℝ) (Q.cut i.succ : ℝ) := by
      apply (integrable_H γ hγ _ hf).mono_set
      apply Set.uIcc_subset_uIcc
      · rw [Set.uIcc_of_le zero_le_one]
        exact (Q.cut i.castSucc).2
      · rw [Set.uIcc_of_le zero_le_one]
        exact (Q.cut i.succ).2
    exact cell_reciprocal_eq γ L hL _ _ hlt (hQ i) hH
  rw [Finset.sum_congr rfl (fun i _ => hcell i)]
  have h2 : ∀ i : Fin Q.n,
      (L.extend (Q.cut i.succ : ℝ) - L.extend (Q.cut i.castSucc : ℝ)) =
        -(L.extend (Q.cut i.castSucc : ℝ) - L.extend (Q.cut i.succ : ℝ)) :=
    fun i => by ring
  simp only [h2, Finset.sum_neg_distrib]
  have htel : ∑ j : Fin Q.n, (L.extend (Q.cut j.castSucc : ℝ) - L.extend (Q.cut j.succ : ℝ)) =
      L.extend (Q.cut 0 : ℝ) - L.extend (Q.cut (Fin.last Q.n) : ℝ) :=
    fin_telescope Q.n (fun k => L.extend (Q.cut k : ℝ))
  rw [htel]
  have h0' : (Q.cut 0 : ℝ) = 0 := by
    rw [Q.first]
    rfl
  have hl' : (Q.cut (Fin.last Q.n) : ℝ) = 1 := by
    rw [Q.last]
    rfl
  rw [h0', hl', Path.extend_zero, Path.extend_one]
  ring

/-- Leaf 79.07: a nonvanishing path in ℂ has a continuous logarithm lift (covering-map lifting). -/
theorem exists_log_lift {a b : ℂ} (γ : Path a b) (hγ : ∀ t : I, γ t ≠ 0) :
    ∃ q : ℂ, ∃ L : Path (Complex.log a) q,
      ∀ t : I, Complex.exp (L t) = γ t := by
  have ha : a ≠ 0 := by
    have h := hγ 0
    rwa [γ.source] at h
  let γ' : C(I, {z : ℂ // z ≠ 0}) :=
    ⟨fun t => ⟨γ t, hγ t⟩, γ.continuous.subtype_mk _⟩
  have h0 : γ' 0 = (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
      (Complex.log a) := by
    apply Subtype.ext
    show γ 0 = Complex.exp (Complex.log a)
    rw [Complex.exp_log ha, γ.source]
  let L : C(I, ℂ) := Complex.isCoveringMap_exp.liftPath γ' (Complex.log a) h0
  have hsrc : L 0 = Complex.log a := Complex.isCoveringMap_exp.liftPath_zero γ' _ h0
  have hlift := Complex.isCoveringMap_exp.liftPath_lifts γ' (Complex.log a) h0
  refine ⟨L 1, { toContinuousMap := L, source' := hsrc, target' := rfl }, fun t => ?_⟩
  have h := congrFun hlift t
  exact congrArg Subtype.val h

/-- Leaf 79.10: the normalized index about a point off the loop is an integer. -/
theorem indexIntegral_int {a p : ℂ} (γ : Path a a)
    (hγ : PiecewiseC1 γ) (hp : p ∉ range γ) :
    CurveIntegrable (complexForm (fun z => (z - p)⁻¹)) γ ∧
    indexIntegral γ p = (windingNumber γ p : ℂ) := by
  have hnz : ∀ t : I, γ t - p ≠ 0 := fun t h => hp ⟨t, sub_eq_zero.1 h⟩
  have hf : ContinuousOn (fun z : ℂ => (z - p)⁻¹) (range γ) := by
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    exact hnz t
  have hCI := piecewise_curveIntegrable γ hγ _ hf
  refine ⟨hCI, ?_⟩
  let δ : Path (a - p) (a - p) := γ.map (continuous_sub_right p)
  have hδ : ∀ t : I, δ t = γ t - p := fun t => rfl
  have hext : δ.extend = fun s => γ.extend s - p := funext fun s => rfl
  have hδnz : ∀ t : I, δ t ≠ 0 := fun t => by
    rw [hδ]
    exact hnz t
  have hδPC : PiecewiseC1 δ := by
    obtain ⟨P, hP⟩ := hγ
    refine ⟨P, fun i => ?_⟩
    refine ContDiffOn.congr (f := fun u => (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend u - p)
      ((hP i).sub contDiffOn_const) (fun u hu => ?_)
    rw [subpath_extend_eq δ _ _ u hu, subpath_extend_eq γ _ _ u hu, hext]
  obtain ⟨q, L, hL⟩ := exists_log_lift δ hδnz
  have key := (reciprocal_integral_eq_log_increment δ L hδPC hL).2
  have hval : curveIntegral (complexForm (fun z => (z - p)⁻¹)) γ =
      curveIntegral (complexForm (fun z => z⁻¹)) δ := by
    rw [curveIntegral_eq_intervalIntegral_deriv, curveIntegral_eq_intervalIntegral_deriv, hext]
    congr 1
    funext t
    simp only [complexForm, ContinuousLinearMap.mul_apply', deriv_sub_const]
  have hap : a - p ≠ 0 := by
    have h := hnz 0
    rwa [γ.source] at h
  have hexpq : Complex.exp q = a - p := by
    have h := hL 1
    rw [L.target, hδ, γ.target] at h
    exact h
  have hlog : Complex.exp (Complex.log (a - p)) = a - p := Complex.exp_log hap
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (hexpq.trans hlog.symm)
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hmain : (2 * Real.pi * Complex.I : ℂ)⁻¹ * (q - Complex.log (a - p)) = (n : ℂ) := by
    rw [hn, add_sub_cancel_left, mul_comm (n : ℂ) (2 * Real.pi * Complex.I), ← mul_assoc,
      inv_mul_cancel₀ hne, one_mul]
  have hidx : indexIntegral γ p = (n : ℂ) := by
    unfold indexIntegral
    rw [hval, key]
    exact hmain
  rw [hidx]
  unfold windingNumber
  rw [hidx, Complex.intCast_re, Int.floor_intCast]


theorem segment_contDiffOn (x y : ℂ) :
    ContDiffOn ℝ 1 (Path.segment x y).extend (Icc (0 : ℝ) 1) := by
  have h : ContDiffOn ℝ 1 (fun t : ℝ => (1 - t) • x + t • y) (Icc (0 : ℝ) 1) := by
    apply ContDiff.contDiffOn
    fun_prop
  refine h.congr ?_
  intro t ht
  have := Path.extend_extends' (Path.segment x y) ⟨t, ht⟩
  simpa [AffineMap.lineMap_apply_module] using this


/-- Leaf C09: four chords of a cell inside a disc have zero integral. -/
theorem four_chords_eq_zero (f : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hf : DifferentiableOn ℂ f (ball c r))
    (a b d e : ℂ)
    (ha : a ∈ ball c r) (hb : b ∈ ball c r)
    (hd : d ∈ ball c r) (he : e ∈ ball c r) :
    edgeIntegral f a b + edgeIntegral f b e -
      edgeIntegral f d e - edgeIntegral f a d = 0 := by
  obtain ⟨P, hP⟩ := hf.isExactOn_ball
  have hseg : ∀ u v : ℂ, u ∈ ball c r → v ∈ ball c r → edgeIntegral f u v = P v - P u := by
    intro u v hu hv
    unfold edgeIntegral
    apply primitive_curveIntegral_c1 (Path.segment u v) (segment_contDiffOn u v) (ball c r) f P
      isOpen_ball _ hf.continuousOn hP
    rw [Path.range_segment]
    exact (convex_ball c r).segment_subset hu hv
  rw [hseg a b ha hb, hseg b e hb he, hseg d e hd he, hseg a d ha hd]
  ring


theorem sum_cellBoundary (f : ℂ → ℂ) (H : C(I × I, ℂ))
    (P Q : TimePartition) :
    (∑ i : Fin P.n, ∑ j : Fin Q.n, cellBoundary f H P Q i j) =
      gridBoundary f H P Q := by
  -- horizontal rows: RA j = sum over columns of the bottom edge at height Q.cut j
  set RA : Fin (Q.n + 1) → ℂ := fun j =>
    ∑ i : Fin P.n, edgeIntegral f (H (P.cut i.castSucc, Q.cut j)) (H (P.cut i.succ, Q.cut j)) with hRA
  -- vertical columns: VA i = sum over rows of the left edge at abscissa P.cut i
  set VA : Fin (P.n + 1) → ℂ := fun i =>
    ∑ j : Fin Q.n, edgeIntegral f (H (P.cut i, Q.cut j.castSucc)) (H (P.cut i, Q.cut j.succ)) with hVA
  have hA : (∑ i : Fin P.n, ∑ j : Fin Q.n, edgeIntegral f
      (H (P.cut i.castSucc, Q.cut j.castSucc)) (H (P.cut i.succ, Q.cut j.castSucc))) =
      ∑ j : Fin Q.n, RA j.castSucc := by
    rw [Finset.sum_comm]
  have hC : (∑ i : Fin P.n, ∑ j : Fin Q.n, edgeIntegral f
      (H (P.cut i.castSucc, Q.cut j.succ)) (H (P.cut i.succ, Q.cut j.succ))) =
      ∑ j : Fin Q.n, RA j.succ := by
    rw [Finset.sum_comm]
  have hB : (∑ i : Fin P.n, ∑ j : Fin Q.n, edgeIntegral f
      (H (P.cut i.succ, Q.cut j.castSucc)) (H (P.cut i.succ, Q.cut j.succ))) =
      ∑ i : Fin P.n, (VA i.succ) := by
    rfl
  have hD : (∑ i : Fin P.n, ∑ j : Fin Q.n, edgeIntegral f
      (H (P.cut i.castSucc, Q.cut j.castSucc)) (H (P.cut i.castSucc, Q.cut j.succ))) =
      ∑ i : Fin P.n, (VA i.castSucc) := by
    rfl
  have htel1 := fin_telescope Q.n RA
  have htel2 := fin_telescope P.n VA
  simp only [cellBoundary, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hA, hC, hB, hD]
  simp only [gridBoundary]
  have hR0 : RA 0 = ∑ i : Fin P.n, edgeIntegral f (H (P.cut i.castSucc, 0)) (H (P.cut i.succ, 0)) := by
    simp only [hRA, Q.first]
  have hRQ : RA (Fin.last Q.n) = ∑ i : Fin P.n, edgeIntegral f (H (P.cut i.castSucc, 1)) (H (P.cut i.succ, 1)) := by
    simp only [hRA, Q.last]
  have hV0 : VA 0 = ∑ j : Fin Q.n, edgeIntegral f (H (0, Q.cut j.castSucc)) (H (0, Q.cut j.succ)) := by
    simp only [hVA, P.first]
  have hVP : VA (Fin.last P.n) = ∑ j : Fin Q.n, edgeIntegral f (H (1, Q.cut j.castSucc)) (H (1, Q.cut j.succ)) := by
    simp only [hVA, P.last]
  rw [hR0, hRQ] at htel1
  rw [hV0, hVP] at htel2
  rw [Finset.sum_sub_distrib] at htel1 htel2
  linear_combination htel1 - htel2

/-- Leaf C11: the zero boundary integral for the grid. -/
theorem gridBoundary_eq_zero (U : Set ℂ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (H : C(I × I, ℂ)) (P Q : TimePartition)
    (hballs : ∀ i : Fin P.n, ∀ j : Fin Q.n,
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
        cellImage H P Q i j ⊆ ball c r ∧ ball c r ⊆ U) :
    gridBoundary f H P Q = 0 := by
  rw [← sum_cellBoundary f H P Q]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  obtain ⟨c, r, hr, hsub, hball⟩ := hballs i j
  have hmem : ∀ p ∈ Icc (P.cut i.castSucc) (P.cut i.succ) ×ˢ Icc (Q.cut j.castSucc) (Q.cut j.succ),
      H p ∈ ball c r := fun p hp => hsub ⟨p, hp, rfl⟩
  have hP1 : P.cut i.castSucc ≤ P.cut i.succ := P.strict.monotone (Fin.castSucc_lt_succ (i := i)).le
  have hQ1 : Q.cut j.castSucc ≤ Q.cut j.succ := Q.strict.monotone (Fin.castSucc_lt_succ (i := j)).le
  have ha : H (P.cut i.castSucc, Q.cut j.castSucc) ∈ ball c r :=
    hmem _ ⟨⟨le_refl _, hP1⟩, ⟨le_refl _, hQ1⟩⟩
  have hb : H (P.cut i.succ, Q.cut j.castSucc) ∈ ball c r :=
    hmem _ ⟨⟨hP1, le_refl _⟩, ⟨le_refl _, hQ1⟩⟩
  have hd : H (P.cut i.castSucc, Q.cut j.succ) ∈ ball c r :=
    hmem _ ⟨⟨le_refl _, hP1⟩, ⟨hQ1, le_refl _⟩⟩
  have he : H (P.cut i.succ, Q.cut j.succ) ∈ ball c r :=
    hmem _ ⟨⟨hP1, le_refl _⟩, ⟨hQ1, le_refl _⟩⟩
  unfold cellBoundary
  exact four_chords_eq_zero f c r (hf.mono hball) _ _ _ _ ha hb hd he






-- END PASTED H3 BASE (C00-C06, C09-C11, 79.07-79.10)
-- BEGIN proof development: C07, C08, C12
theorem mem_range_subpath {a b : ℂ} (γ : Path a b) (s t' x : I) (hsx : s ≤ x) (hxt : x ≤ t') :
    γ x ∈ range (γ.subpath s t') := by
  rcases (hsx.trans hxt).eq_or_lt with h | h
  · have h' : t' = s := h.symm
    subst h'
    have hxs : x = t' := le_antisymm hxt hsx
    subst hxs
    refine ⟨0, ?_⟩
    exact Path.source _
  · have hne : ((t' : ℝ) - s) ≠ 0 := by
      have : (s : ℝ) < t' := h
      linarith
    have hpos : 0 < (t' : ℝ) - s := by
      have : (s : ℝ) < t' := h
      linarith
    set u : ℝ := ((x : ℝ) - s) / ((t' : ℝ) - s) with hu
    have hu0 : 0 ≤ u := div_nonneg (by have : (s : ℝ) ≤ x := hsx; linarith) hpos.le
    have hu1 : u ≤ 1 := by
      rw [hu, div_le_one hpos]
      have : (x : ℝ) ≤ t' := hxt
      linarith
    refine ⟨⟨u, ⟨hu0, hu1⟩⟩, ?_⟩
    have h1 := subpath_extend_eq γ s t' u ⟨hu0, hu1⟩
    have h2 : (γ.subpath s t').extend u = (γ.subpath s t') ⟨u, ⟨hu0, hu1⟩⟩ :=
      Path.extend_extends' (γ.subpath s t') ⟨u, ⟨hu0, hu1⟩⟩
    have h3 : (s : ℝ) + u * ((t' : ℝ) - s) = x := by
      rw [hu]; field_simp; ring
    rw [← h2, h1, h3]
    exact Path.extend_extends' γ x

/-- Leaf C07: replace short path pieces by chords. -/
theorem curveIntegral_eq_chord_sum {a b : ℂ} (γ : Path a b)
    (hγ : PiecewiseC1 γ) (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (P : TimePartition)
    (hballs : ∀ i : Fin P.n, ∃ c : ℂ, ∃ r : ℝ,
      0 < r ∧ range (γ.subpath (P.cut i.castSucc) (P.cut i.succ))
        ⊆ ball c r ∧ ball c r ⊆ U) :
    curveIntegral (complexForm f) γ =
      ∑ i : Fin P.n, edgeIntegral f
        (γ (P.cut i.castSucc)) (γ (P.cut i.succ)) := by
  have hrange : range γ ⊆ U := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨i, hi1, hi2⟩ := cells_cover P x x.2
    obtain ⟨c, r, hr, hsub, hball⟩ := hballs i
    exact hball (hsub (mem_range_subpath γ _ _ x (by exact_mod_cast hi1) (by exact_mod_cast hi2)))
  rw [curveIntegral_partition γ hγ f (hf.continuousOn.mono hrange) P]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨c, r, hr, hsub, hball⟩ := hballs i
  obtain ⟨Pr, hPr⟩ := (hf.mono hball).isExactOn_ball
  have hs := hsub (mem_range_subpath γ (P.cut i.castSucc) (P.cut i.succ) (P.cut i.castSucc) le_rfl
    (P.strict.monotone (Fin.castSucc_lt_succ (i := i)).le))
  have ht := hsub (mem_range_subpath γ (P.cut i.castSucc) (P.cut i.succ) (P.cut i.succ)
    (P.strict.monotone (Fin.castSucc_lt_succ (i := i)).le) le_rfl)
  rw [primitive_curveIntegral (γ.subpath (P.cut i.castSucc) (P.cut i.succ))
    (piecewiseC1_subpath γ hγ _ _) (ball c r) f Pr isOpen_ball hsub (hf.mono hball).continuousOn hPr]
  unfold edgeIntegral
  rw [primitive_curveIntegral_c1 (Path.segment (γ (P.cut i.castSucc)) (γ (P.cut i.succ)))
    (segment_contDiffOn _ _) (ball c r) f Pr isOpen_ball _ (hf.mono hball).continuousOn hPr]
  rw [Path.range_segment]
  exact (convex_ball c r).segment_subset hs ht

/-- uniform partition of `I` into `N` equal pieces. -/
def uniformPartition (N : ℕ) (hN : 0 < N) : TimePartition where
  n := N
  cut := fun k => ⟨(k : ℕ) / (N : ℝ), by
    constructor
    · positivity
    · rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast Nat.lt_succ_iff.mp k.2⟩
  first := by
    apply Subtype.ext
    simp
  last := by
    apply Subtype.ext
    show (((Fin.last N : Fin (N + 1)) : ℕ) : ℝ) / (N : ℝ) = 1
    rw [Fin.val_last]
    exact div_self (Nat.cast_ne_zero.mpr hN.ne')
  strict := by
    intro k l hkl
    show ((k : ℕ) : ℝ) / N < ((l : ℕ) : ℝ) / N
    exact div_lt_div_of_pos_right (by exact_mod_cast hkl) (by exact_mod_cast hN)

theorem uniformPartition_cut_sub (N : ℕ) (hN : 0 < N) (k : Fin N) :
    ((uniformPartition N hN).cut k.succ : ℝ) - (uniformPartition N hN).cut k.castSucc = 1 / N := by
  show (((k.succ : Fin (N + 1)) : ℕ) : ℝ) / N - (((k.castSucc : Fin (N + 1)) : ℕ) : ℝ) / N = 1 / N
  simp only [Fin.val_succ, Fin.coe_castSucc]
  push_cast
  ring

/-- Leaf C08: a finite grid subordinate to local balls. -/
theorem exists_grid_local_balls (U : Set ℂ) (hU : IsOpen U)
    (H : C(I × I, ℂ)) (hHU : range H ⊆ U) :
    ∃ P Q : TimePartition, ∀ i : Fin P.n, ∀ j : Fin Q.n,
      ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
        cellImage H P Q i j ⊆ ball c r ∧ ball c r ⊆ U := by
  have hK : IsCompact (range H) := isCompact_range H.continuous
  obtain ⟨ε, hε, hth⟩ := hK.exists_thickening_subset_open hU hHU
  have huc : UniformContinuous H := CompactSpace.uniformContinuous_of_continuous H.continuous
  obtain ⟨δ, hδ, hH⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  have hN : 0 < m + 1 := Nat.succ_pos m
  refine ⟨uniformPartition (m + 1) hN, uniformPartition (m + 1) hN, fun i j => ?_⟩
  set p0 : I × I := ((uniformPartition (m + 1) hN).cut i.castSucc,
    (uniformPartition (m + 1) hN).cut j.castSucc) with hp0
  refine ⟨H p0, ε, hε, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    have hd : dist p p0 < δ := by
      have h1 : dist p.1 p0.1 ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
        · have := uniformPartition_cut_sub (m + 1) hN i
          have hp1 : (p.1 : ℝ) ≤ (uniformPartition (m + 1) hN).cut i.succ := hp.1.2
          have e : (p0.1 : ℝ) = ((uniformPartition (m + 1) hN).cut i.castSucc : ℝ) := rfl
          have key : (p.1 : ℝ) - p0.1 ≤ ((uniformPartition (m + 1) hN).cut i.succ : ℝ) -
              ((uniformPartition (m + 1) hN).cut i.castSucc : ℝ) := by rw [e]; linarith
          exact key.trans (le_of_eq this)
        · have : ((uniformPartition (m + 1) hN).cut i.castSucc : ℝ) ≤ p.1 := hp.1.1
          simp only [hp0]; linarith
      have h2 : dist p.2 p0.2 ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg]
        · have := uniformPartition_cut_sub (m + 1) hN j
          have hp1 : (p.2 : ℝ) ≤ (uniformPartition (m + 1) hN).cut j.succ := hp.2.2
          have e : (p0.2 : ℝ) = ((uniformPartition (m + 1) hN).cut j.castSucc : ℝ) := rfl
          have key : (p.2 : ℝ) - p0.2 ≤ ((uniformPartition (m + 1) hN).cut j.succ : ℝ) -
              ((uniformPartition (m + 1) hN).cut j.castSucc : ℝ) := by rw [e]; linarith
          exact key.trans (le_of_eq this)
        · have : ((uniformPartition (m + 1) hN).cut j.castSucc : ℝ) ≤ p.2 := hp.2.1
          simp only [hp0]; linarith
      have h3 : 1 / ((m + 1 : ℕ) : ℝ) < δ := by simpa using hm
      rw [Prod.dist_eq]
      exact lt_of_le_of_lt (max_le h1 h2) h3
    have := hH hd
    rw [mem_ball]
    linarith
  · intro z hz
    apply hth
    rw [mem_thickening_iff]
    exact ⟨H p0, ⟨p0, rfl⟩, hz⟩

theorem partition_n_pos (P : TimePartition) : 0 < P.n := by
  rcases Nat.eq_zero_or_pos P.n with h | h
  · exfalso
    have h1 := P.first
    have h2 := P.last
    have : (Fin.last P.n : Fin (P.n + 1)) = 0 := by
      apply Fin.ext; simp [h]
    rw [this, h1] at h2
    exact zero_ne_one h2
  · exact h

theorem subpath_range_mem {a b : ℂ} (γ : Path a b) (s t' : I) (hst : s ≤ t') {y : ℂ}
    (hy : y ∈ range (γ.subpath s t')) : ∃ x : I, s ≤ x ∧ x ≤ t' ∧ γ x = y := by
  obtain ⟨u, rfl⟩ := hy
  have hw : ((Icc.convexComb s t' u : I) : ℝ) = (s : ℝ) + (u : ℝ) * ((t' : ℝ) - s) := by
    rw [Icc.coe_convexComb]; ring
  have hu0 : (0 : ℝ) ≤ u := u.2.1
  have hu1 : (u : ℝ) ≤ 1 := u.2.2
  refine ⟨Icc.convexComb s t' u, ?_, ?_, rfl⟩
  · show (s : ℝ) ≤ ((Icc.convexComb s t' u : I) : ℝ)
    rw [hw]
    have : (s : ℝ) ≤ t' := hst
    nlinarith [mul_nonneg hu0 (sub_nonneg.2 this)]
  · show ((Icc.convexComb s t' u : I) : ℝ) ≤ t'
    rw [hw]
    have : (s : ℝ) ≤ t' := hst
    nlinarith [mul_nonneg (sub_nonneg.2 hu1) (sub_nonneg.2 this)]

/-- Leaf C12: exact continuous free-homotopy bridge. -/
theorem curveIntegral_eq_of_free_homotopy
    {a b : ℂ} (γ : Path a a) (η : Path b b)
    (hγ : PiecewiseC1 γ) (hη : PiecewiseC1 η)
    (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (H : C(I × I, ℂ)) (hHU : range H ⊆ U)
    (hzero : ∀ t : I, H (0, t) = γ t)
    (hone : ∀ t : I, H (1, t) = η t)
    (hclosed : ∀ s : I, H (s, 0) = H (s, 1)) :
    curveIntegral (complexForm f) γ =
      curveIntegral (complexForm f) η := by
  obtain ⟨P, Q, hballs⟩ := exists_grid_local_balls U hU H hHU
  have hgrid := gridBoundary_eq_zero U f hf H P Q hballs
  have hPn := partition_n_pos P
  set i0 : Fin P.n := ⟨0, hPn⟩ with hi0
  set i1 : Fin P.n := ⟨P.n - 1, by omega⟩ with hi1
  have hc0 : P.cut i0.castSucc = 0 := by
    have : i0.castSucc = (0 : Fin (P.n + 1)) := Fin.ext (by simp [hi0])
    rw [this]; exact P.first
  have hc1 : P.cut i1.succ = 1 := by
    have : i1.succ = Fin.last P.n := Fin.ext (by simp [hi1]; omega)
    rw [this]; exact P.last
  have hQmono : ∀ j : Fin Q.n, (Q.cut j.castSucc : I) ≤ Q.cut j.succ :=
    fun j => Q.strict.monotone (Fin.castSucc_lt_succ (i := j)).le
  have hγs := curveIntegral_eq_chord_sum γ hγ U hU f hf Q (fun j => by
    obtain ⟨c, r, hr, hsub, hball⟩ := hballs i0 j
    refine ⟨c, r, hr, ?_, hball⟩
    intro y hy
    obtain ⟨x, hx1, hx2, rfl⟩ := subpath_range_mem γ _ _ (hQmono j) hy
    apply hsub
    refine ⟨(0, x), ⟨⟨?_, ?_⟩, ⟨hx1, hx2⟩⟩, hzero x⟩
    · rw [hc0]
    · exact (P.cut i0.succ).2.1)
  have hηs := curveIntegral_eq_chord_sum η hη U hU f hf Q (fun j => by
    obtain ⟨c, r, hr, hsub, hball⟩ := hballs i1 j
    refine ⟨c, r, hr, ?_, hball⟩
    intro y hy
    obtain ⟨x, hx1, hx2, rfl⟩ := subpath_range_mem η _ _ (hQmono j) hy
    apply hsub
    refine ⟨(1, x), ⟨⟨?_, ?_⟩, ⟨hx1, hx2⟩⟩, hone x⟩
    · exact (P.cut i1.castSucc).2.2
    · rw [hc1])
  simp only [← hzero] at hγs
  simp only [← hone] at hηs
  have hbd : (∑ i : Fin P.n, edgeIntegral f (H (P.cut i.castSucc, 0)) (H (P.cut i.succ, 0))) =
      ∑ i : Fin P.n, edgeIntegral f (H (P.cut i.castSucc, 1)) (H (P.cut i.succ, 1)) :=
    Finset.sum_congr rfl fun i _ => by rw [hclosed, hclosed]
  unfold gridBoundary at hgrid
  rw [hbd] at hgrid
  rw [hγs, hηs]
  linear_combination -hgrid

/-- The isolating disc with a complex straight segment (design LIB-079 definitions). -/
-- END proof development: C07, C08, C12
-- BEGIN PASTED H3: 79.01/79.02 (proof development/LIB079_79_02_V7_GK38)
structure DiscWithSegment where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius
  a : ℂ
  b : ℂ
  contained : segment ℝ (a : ℂ) (b : ℂ) ⊆ Metric.ball center radius

def DiscWithSegment.midpoint (D : DiscWithSegment) : ℂ :=
  (D.a + D.b) / 2

def DiscWithSegment.halfLength (D : DiscWithSegment) : ℝ :=
  ‖D.b - D.a‖ / 2

def DiscWithSegment.axis (D : DiscWithSegment) : ℂ :=
  if D.a = D.b then 1 else (D.b - D.a) / (‖D.b - D.a‖ : ℂ)

def DiscWithSegment.width (D : DiscWithSegment) : ℝ :=
  (D.radius - max (dist D.a D.center) (dist D.b D.center)) / 2

/-- Leaf 79.01: segment coordinates and positive clearance. -/
theorem disc_segment_coordinates (D : DiscWithSegment) :
    0 < D.width ∧ 0 < D.halfLength + D.width ∧
    ‖D.axis‖ = 1 ∧
    segment ℝ D.a D.b =
      (fun t : ℝ => D.midpoint + D.axis * (t : ℂ)) ''
        Icc (-D.halfLength) D.halfLength := by
  have ha : dist D.a D.center < D.radius :=
    Metric.mem_ball.1 (D.contained (left_mem_segment ℝ D.a D.b))
  have hb : dist D.b D.center < D.radius :=
    Metric.mem_ball.1 (D.contained (right_mem_segment ℝ D.a D.b))
  have hw : 0 < D.width := by
    unfold DiscWithSegment.width
    exact div_pos (sub_pos.2 (max_lt ha hb)) two_pos
  have hL : 0 ≤ D.halfLength := by
    unfold DiscWithSegment.halfLength
    positivity
  refine ⟨hw, add_pos_of_nonneg_of_pos hL hw, ?_, ?_⟩
  · unfold DiscWithSegment.axis
    split_ifs with h
    · simp
    · have hne : ‖D.b - D.a‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm h))
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self hne]
  · by_cases h : D.a = D.b
    · have hL0 : D.halfLength = 0 := by
        unfold DiscWithSegment.halfLength
        rw [h, sub_self, norm_zero, zero_div]
      have hax : D.axis = 1 := by
        unfold DiscWithSegment.axis
        rw [if_pos h]
      have hmid : D.midpoint = D.a := by
        unfold DiscWithSegment.midpoint
        rw [← h]
        ring
      rw [hL0, hax, hmid, neg_zero, Icc_self, h, segment_same]
      simp
    · have hLpos : 0 < ‖D.b - D.a‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm h))
      have hLc : ((‖D.b - D.a‖ : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hLpos.ne'
      have hax : D.axis = (D.b - D.a) / (‖D.b - D.a‖ : ℂ) := by
        unfold DiscWithSegment.axis
        rw [if_neg h]
      have hmid : D.midpoint = (D.a + D.b) / 2 := rfl
      have hhl : D.halfLength = ‖D.b - D.a‖ / 2 := rfl
      rw [segment_eq_image, hhl, hax, hmid]
      ext z
      constructor
      · rintro ⟨θ, hθ, rfl⟩
        obtain ⟨h0, h1⟩ := hθ
        refine ⟨‖D.b - D.a‖ * (θ - 1 / 2), ⟨by nlinarith, by nlinarith⟩, ?_⟩
        simp only [Complex.real_smul]
        push_cast
        field_simp
        ring
      · rintro ⟨t, ht, rfl⟩
        obtain ⟨ht0, ht1⟩ := ht
        have hq0 : -(1 / 2 : ℝ) ≤ t / ‖D.b - D.a‖ := by
          rw [le_div_iff₀ hLpos]
          linarith
        have hq1 : t / ‖D.b - D.a‖ ≤ 1 / 2 := by
          rw [div_le_iff₀ hLpos]
          linarith
        refine ⟨t / ‖D.b - D.a‖ + 1 / 2, ⟨by linarith, by linarith⟩, ?_⟩
        simp only [Complex.real_smul]
        push_cast
        field_simp
        ring

def DiscWithSegment.domain (D : DiscWithSegment) : Set ℂ :=
  Metric.ball D.center D.radius \ segment ℝ D.a D.b

/-- The ellipse parametrization of the gap cycle (design LIB-079). -/
def ellipseParam (D : DiscWithSegment) (θ : ℝ) : ℂ :=
  D.midpoint + D.axis *
    (((D.halfLength + D.width) * Real.cos θ : ℝ) +
      Complex.I * (D.width * Real.sin θ : ℝ))

def gapCycle (D : DiscWithSegment) :
    Path (ellipseParam D 0) (ellipseParam D 0) where
  toFun t := ellipseParam D (2 * Real.pi * (t : ℝ))
  continuous_toFun := by
    unfold ellipseParam
    fun_prop
  source' := by simp
  target' := by simp [ellipseParam]

theorem affMem (s t : unitInterval) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (s : ℝ) + u * ((t : ℝ) - (s : ℝ)) ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hu
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) s.2.1, mul_nonneg h0 t.2.1]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 s.2.2), mul_nonneg h0 (sub_nonneg.2 t.2.2)]

theorem gapCycle_subpath_extend (D : DiscWithSegment) (s t : unitInterval) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    ((gapCycle D).subpath s t).extend u =
      ellipseParam D (2 * Real.pi * ((s : ℝ) + u * ((t : ℝ) - (s : ℝ)))) := by
  rw [subpath_extend_eq (gapCycle D) s t u hu]
  have e : (gapCycle D).extend ((s : ℝ) + u * ((t : ℝ) - (s : ℝ))) =
      gapCycle D ⟨_, affMem s t hu⟩ :=
    Path.extend_extends' _ ⟨_, affMem s t hu⟩
  rw [e]
  rfl

/-- The reparametrized ellipse is smooth. -/
theorem ellipse_contDiff (D : DiscWithSegment) (s t : ℝ) :
    ContDiff ℝ 1 (fun u : ℝ => ellipseParam D (2 * Real.pi * (s + u * (t - s)))) := by
  unfold ellipseParam
  have hA : ContDiff ℝ 1 (fun u : ℝ =>
      (D.halfLength + D.width) * Real.cos (2 * Real.pi * (s + u * (t - s)))) := by
    fun_prop
  have hB : ContDiff ℝ 1 (fun u : ℝ =>
      D.width * Real.sin (2 * Real.pi * (s + u * (t - s)))) := by
    fun_prop
  have hAc : ContDiff ℝ 1 (fun u : ℝ =>
      (((D.halfLength + D.width) * Real.cos (2 * Real.pi * (s + u * (t - s))) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hA
  have hBc : ContDiff ℝ 1 (fun u : ℝ =>
      ((D.width * Real.sin (2 * Real.pi * (s + u * (t - s))) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hB
  exact contDiff_const.add (contDiff_const.mul (hAc.add (contDiff_const.mul hBc)))

/-- Leaf 79.02a: the gap cycle is piecewise C¹. -/
theorem gapCycle_piecewise (D : DiscWithSegment) : PiecewiseC1 (gapCycle D) := by
  refine ⟨singlePartition, fun i => ?_⟩
  have hsm := ellipse_contDiff D ((singlePartition.cut i.castSucc : unitInterval) : ℝ)
    ((singlePartition.cut i.succ : unitInterval) : ℝ)
  exact hsm.contDiffOn.congr (fun u hu => gapCycle_subpath_extend D _ _ u hu)

/-- Real inequality: the clamped point of the segment is within `w` of the ellipse point. -/
theorem clamp_bound (h w co si : ℝ) (hh : 0 ≤ h) (hw : 0 < w)
    (hcs : si ^ 2 + co ^ 2 = 1) (hc1 : co ≤ 1) (hc2 : -1 ≤ co) :
    ((h + w) * co - max (-h) (min ((h + w) * co) h)) ^ 2 + (w * si) ^ 2 ≤ w ^ 2 := by
  have f1 : (h + w) * co - h ≤ w * co := by nlinarith
  have f2 : w * co ≤ (h + w) * co + h := by nlinarith [mul_nonneg hh (by linarith : (0:ℝ) ≤ co + 1)]
  have f3 : (w * co) ^ 2 + (w * si) ^ 2 = w ^ 2 := by
    calc (w * co) ^ 2 + (w * si) ^ 2 = w ^ 2 * (si ^ 2 + co ^ 2) := by ring
      _ = w ^ 2 := by rw [hcs, mul_one]
  rcases le_total ((h + w) * co) h with h1 | h1
  · rcases le_total (-h) ((h + w) * co) with h2 | h2
    · rw [min_eq_left h1, max_eq_right h2, sub_self]
      nlinarith [sq_nonneg (w * co)]
    · rw [min_eq_left h1, max_eq_left h2]
      have g1 : (h + w) * co + h ≤ 0 := by linarith
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ -((h + w) * co + h))
        (by linarith : (0:ℝ) ≤ -(w * co) + (h + w) * co + h)]
  · rw [min_eq_right h1, max_eq_right (by linarith : -h ≤ h)]
    have g1 : 0 ≤ (h + w) * co - h := by linarith
    have g2 : (h + w) * co - h ≤ w * co := f1
    nlinarith [mul_nonneg g1 (sub_nonneg.2 g2),
      mul_nonneg (sub_nonneg.2 g2) (by linarith : (0:ℝ) ≤ w * co + ((h + w) * co - h))]

/-- Generic-parameter form of 79.02b: every ellipse point lies in the domain. -/
theorem ellipseParam_mem_domain (D : DiscWithSegment) (θ : ℝ) :
    ellipseParam D θ ∈ D.domain := by
  obtain ⟨hw, _, hu1, hseg⟩ := disc_segment_coordinates D
  have hh : 0 ≤ D.halfLength := by
    unfold DiscWithSegment.halfLength
    positivity
  have hM : 2 * D.width = D.radius - max (dist D.a D.center) (dist D.b D.center) := by
    unfold DiscWithSegment.width
    ring
  have hu0 : D.axis ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hu1
    norm_num at hu1
  have hcs : Real.sin (θ) ^ 2 + Real.cos (θ) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have hc1 : Real.cos (θ) ≤ 1 := Real.cos_le_one _
  have hc2 : -1 ≤ Real.cos (θ) := Real.neg_one_le_cos _
  set co := Real.cos (θ) with hco
  set si := Real.sin (θ) with hsi
  have hp : ellipseParam D (θ) = D.midpoint + D.axis *
      ((((D.halfLength + D.width) * co : ℝ) : ℂ) + Complex.I * ((D.width * si : ℝ) : ℂ)) := rfl
  set T : ℝ := max (-D.halfLength) (min ((D.halfLength + D.width) * co) D.halfLength) with hT
  have hT1 : -D.halfLength ≤ T := le_max_left _ _
  have hT2 : T ≤ D.halfLength := max_le (by linarith) (min_le_right _ _)
  have hs_seg : D.midpoint + D.axis * (T : ℂ) ∈ segment ℝ D.a D.b := by
    rw [hseg]
    exact ⟨T, ⟨hT1, hT2⟩, rfl⟩
  have hdistsp : dist (ellipseParam D (θ))
      (D.midpoint + D.axis * (T : ℂ)) ≤ D.width := by
    rw [dist_eq_norm, hp]
    have e : D.midpoint + D.axis * ((((D.halfLength + D.width) * co : ℝ) : ℂ) +
        Complex.I * ((D.width * si : ℝ) : ℂ)) - (D.midpoint + D.axis * (T : ℂ)) =
        D.axis * ((((D.halfLength + D.width) * co - T : ℝ) : ℂ) +
          ((D.width * si : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [e, norm_mul, hu1, one_mul, Complex.norm_add_mul_I]
    apply Real.sqrt_le_iff.2
    refine ⟨hw.le, ?_⟩
    have key := clamp_bound D.halfLength D.width co si hh hw hcs hc1 hc2
    exact key
  have ha : D.a ∈ Metric.closedBall D.center
      (max (dist D.a D.center) (dist D.b D.center)) :=
    Metric.mem_closedBall.2 (le_max_left _ _)
  have hb : D.b ∈ Metric.closedBall D.center
      (max (dist D.a D.center) (dist D.b D.center)) :=
    Metric.mem_closedBall.2 (le_max_right _ _)
  have hsc := (convex_closedBall D.center
      (max (dist D.a D.center) (dist D.b D.center))).segment_subset ha hb hs_seg
  have hdsc := Metric.mem_closedBall.1 hsc
  have hball : ellipseParam D (θ) ∈ Metric.ball D.center D.radius := by
    rw [Metric.mem_ball]
    calc dist (ellipseParam D (θ)) D.center
        ≤ dist (ellipseParam D (θ)) (D.midpoint + D.axis * (T : ℂ)) +
            dist (D.midpoint + D.axis * (T : ℂ)) D.center := dist_triangle _ _ _
      _ < D.radius := by linarith [hdistsp, hdsc, hM, hw]
  have hnot : ellipseParam D (θ) ∉ segment ℝ D.a D.b := by
    intro hmem
    rw [hseg] at hmem
    obtain ⟨τ, ⟨hτ1, hτ2⟩, hτ⟩ := hmem
    have hτ' : D.midpoint + D.axis * (τ : ℂ) = ellipseParam D (θ) := hτ
    rw [hp] at hτ'
    have h2 : (τ : ℂ) = (((D.halfLength + D.width) * co : ℝ) : ℂ) +
        Complex.I * ((D.width * si : ℝ) : ℂ) := by
      apply mul_left_cancel₀ hu0
      linear_combination hτ'
    have hre := congrArg Complex.re h2
    have him := congrArg Complex.im h2
    simp at hre him
    have hsi0 : si = 0 := by
      rcases him with h0 | h0
      · exact absurd h0 hw.ne'
      · exact h0
    have hco2 : co ^ 2 = 1 := by nlinarith [hcs, hsi0]
    have hτsq : τ ^ 2 = (D.halfLength + D.width) ^ 2 := by
      rw [hre]
      nlinarith [hco2]
    nlinarith [hτ1, hτ2, hw, hh, mul_nonneg hh hw.le]
  exact ⟨hball, hnot⟩

/-- Leaf 79.02b: the gap cycle lies in the disc and avoids the segment. -/
theorem gapCycle_range (D : DiscWithSegment) : range (gapCycle D) ⊆ D.domain := by
  rintro _ ⟨t, rfl⟩
  show ellipseParam D (2 * Real.pi * (t : ℝ)) ∈ D.domain
  exact ellipseParam_mem_domain D _

theorem gapCycle_admissible (D : DiscWithSegment) : Admissible D.domain (gapCycle D) :=
  ⟨gapCycle_piecewise D, gapCycle_range D⟩


-- END PASTED H3: 79.01/79.02
-- BEGIN proof development: 79.06 reciprocal gap cycle
theorem piecewiseC1_of_smooth {a b : ℂ} (γ : Path a b) (G : ℝ → ℂ) (hG : ContDiff ℝ 1 G)
    (hγ : ∀ t : I, γ t = G t) : PiecewiseC1 γ := by
  refine ⟨singlePartition, fun i => ?_⟩
  have hsm : ContDiff ℝ 1 (fun u : ℝ =>
      G ((singlePartition.cut i.castSucc : I) + u * ((singlePartition.cut i.succ : I) -
        (singlePartition.cut i.castSucc : I)))) := hG.comp (by fun_prop)
  refine hsm.contDiffOn.congr (fun u hu => ?_)
  rw [subpath_extend_eq γ _ _ u hu]
  have e : γ.extend ((singlePartition.cut i.castSucc : I) + u * ((singlePartition.cut i.succ : I) -
      (singlePartition.cut i.castSucc : I))) = γ ⟨_, affMem _ _ hu⟩ :=
    Path.extend_extends' _ ⟨_, affMem _ _ hu⟩
  rw [e, hγ]

/-- the circle variant (equal semiaxes `width`, rotated by `axis`) used as the end of the interpolation. -/
def circleGen (D : DiscWithSegment) (u : ℝ) : ℂ :=
  D.midpoint + D.axis * (D.width : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (u : ℂ))

def interpLoop (D : DiscWithSegment) :
    Path (D.midpoint + D.axis * (D.width : ℂ)) (D.midpoint + D.axis * (D.width : ℂ)) where
  toFun t := circleGen D (t : ℝ)
  continuous_toFun := by
    unfold circleGen
    fun_prop
  source' := by simp [circleGen]
  target' := by
    simp only [circleGen, Set.Icc.coe_one, Complex.ofReal_one, mul_one, Complex.exp_two_pi_mul_I]

def interpH (D : DiscWithSegment) (p : I × I) : ℂ :=
  D.midpoint + D.axis *
    ((((D.width + (1 - (p.1 : ℝ)) * D.halfLength) * Real.cos (2 * Real.pi * (p.2 : ℝ)) : ℝ) : ℂ) +
      Complex.I * ((D.width * Real.sin (2 * Real.pi * (p.2 : ℝ)) : ℝ) : ℂ))

theorem continuous_interpH (D : DiscWithSegment) : Continuous (interpH D) := by
  unfold interpH
  fun_prop

theorem exp_two_pi_mul_I_mul (u : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) =
      ((Real.cos (2 * Real.pi * u) : ℝ) : ℂ) + Complex.I * ((Real.sin (2 * Real.pi * u) : ℝ) : ℂ) := by
  have : (2 * Real.pi * Complex.I * (u : ℂ)) = (((2 * Real.pi * u : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_mul_I]
  push_cast
  rw [mul_comm Complex.I]

theorem interpH_zero (D : DiscWithSegment) (t : I) :
    interpH D (0, t) = ellipseParam D (2 * Real.pi * (t : ℝ)) := by
  unfold interpH ellipseParam
  simp only [Set.Icc.coe_zero]
  congr 3
  · ring

theorem interpH_one (D : DiscWithSegment) (t : I) :
    interpH D (1, t) = circleGen D (t : ℝ) := by
  unfold interpH circleGen
  rw [exp_two_pi_mul_I_mul]
  simp only [Set.Icc.coe_one]
  push_cast
  ring

theorem interpH_closed (D : DiscWithSegment) (s : I) : interpH D (s, 0) = interpH D (s, 1) := by
  unfold interpH
  simp [Real.cos_two_pi, Real.sin_two_pi]

theorem re_im_zero (x y : ℝ) (h : (x : ℂ) + Complex.I * (y : ℂ) = 0) : x = 0 ∧ y = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero, add_zero, Complex.zero_re] at h1
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, zero_add, Complex.zero_im] at h2
  exact ⟨h1, h2⟩

theorem interpH_ne (D : DiscWithSegment) (p : I × I) : interpH D p ≠ D.midpoint := by
  obtain ⟨hw, -, hax, -⟩ := disc_segment_coordinates D
  have hh : 0 ≤ D.halfLength := by unfold DiscWithSegment.halfLength; positivity
  intro h
  unfold interpH at h
  have h0 : D.axis *
      ((((D.width + (1 - (p.1 : ℝ)) * D.halfLength) * Real.cos (2 * Real.pi * (p.2 : ℝ)) : ℝ) : ℂ) +
        Complex.I * ((D.width * Real.sin (2 * Real.pi * (p.2 : ℝ)) : ℝ) : ℂ)) = 0 := by
    linear_combination h
  have hax0 : D.axis ≠ 0 := by
    intro h0; rw [h0] at hax; simp at hax
  have h1 := (mul_eq_zero.mp h0).resolve_left hax0
  obtain ⟨hre, him⟩ := re_im_zero _ _ h1
  have hA : 0 < D.width + (1 - (p.1 : ℝ)) * D.halfLength := by
    have : (p.1 : ℝ) ≤ 1 := p.1.2.2
    nlinarith
  have hc : Real.cos (2 * Real.pi * (p.2 : ℝ)) = 0 := by
    rcases mul_eq_zero.mp hre with h | h
    · exact absurd h hA.ne'
    · exact h
  have hs : Real.sin (2 * Real.pi * (p.2 : ℝ)) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd h hw.ne'
    · exact h
  have := Real.cos_sq_add_sin_sq (2 * Real.pi * (p.2 : ℝ))
  rw [hc, hs] at this
  norm_num at this

theorem reciprocal_integral_circle (D : DiscWithSegment) :
    curveIntegral (complexForm (fun z => (z - D.midpoint)⁻¹)) (interpLoop D) =
      2 * Real.pi * Complex.I := by
  obtain ⟨hw, -, hax, -⟩ := disc_segment_coordinates D
  have hax0 : D.axis ≠ 0 := by
    intro h0; rw [h0] at hax; simp at hax
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp only [complexForm, ContinuousLinearMap.mul_apply']
  have hK : ∀ u ∈ Ioo (0 : ℝ) 1,
      ((interpLoop D).extend u - D.midpoint)⁻¹ * deriv (interpLoop D).extend u =
        2 * Real.pi * Complex.I := by
    intro u hu
    have hext : (interpLoop D).extend =ᶠ[nhds u] (fun v : ℝ => circleGen D v) := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
      have := Path.extend_extends' (interpLoop D) ⟨v, ⟨hv.1.le, hv.2.le⟩⟩
      exact this
    have hder : HasDerivAt (fun v : ℝ => circleGen D v)
        (D.axis * (D.width : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) *
          (2 * Real.pi * Complex.I))) u := by
      unfold circleGen
      have h1 : HasDerivAt (fun v : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * (v : ℂ))
          (2 * (Real.pi : ℂ) * Complex.I) u := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (2 * (Real.pi : ℂ) * Complex.I)
      have h2 := h1.cexp
      exact (h2.const_mul (D.axis * (D.width : ℂ))).const_add D.midpoint
    rw [hext.deriv_eq, hder.deriv, hext.self_of_nhds]
    unfold circleGen
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (u : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hwc : (D.width : ℂ) ≠ 0 := by exact_mod_cast hw.ne'
    field_simp
    ring
  have : ∫ u in (0 : ℝ)..1, ((interpLoop D).extend u - D.midpoint)⁻¹ * deriv (interpLoop D).extend u =
      ∫ u in (0 : ℝ)..1, (2 * Real.pi * Complex.I : ℂ) := by
    rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hK
  rw [this]
  simp

/-- Leaf 79.06: the reciprocal integral of the positive gap cycle. -/
theorem reciprocal_gapCycle (D : DiscWithSegment) :
    CurveIntegrable
      (complexForm (fun z => (z - D.midpoint)⁻¹)) (gapCycle D) ∧
    curveIntegral (complexForm (fun z => (z - D.midpoint)⁻¹))
      (gapCycle D) = 2 * Real.pi * Complex.I := by
  set U : Set ℂ := {z | z ≠ D.midpoint} with hUdef
  have hU : IsOpen U := isOpen_ne
  set f : ℂ → ℂ := fun z => (z - D.midpoint)⁻¹ with hfdef
  have hf : DifferentiableOn ℂ f U := by
    intro z hz
    exact ((differentiableAt_id.sub_const D.midpoint).inv (sub_ne_zero.2 hz)).differentiableWithinAt
  let H : C(I × I, ℂ) := ⟨interpH D, continuous_interpH D⟩
  have hHU : range H ⊆ U := by
    rintro _ ⟨p, rfl⟩
    exact interpH_ne D p
  have hγ := gapCycle_piecewise D
  have hη : PiecewiseC1 (interpLoop D) := by
    apply piecewiseC1_of_smooth (interpLoop D) (circleGen D)
    · unfold circleGen
      apply ContDiff.add contDiff_const
      apply ContDiff.mul contDiff_const
      apply ContDiff.cexp
      exact contDiff_const.mul Complex.ofRealCLM.contDiff
    · intro t; rfl
  have hmain := curveIntegral_eq_of_free_homotopy (gapCycle D) (interpLoop D) hγ hη U hU f hf H hHU
    (fun t => by
      show interpH D (0, t) = ellipseParam D (2 * Real.pi * (t : ℝ))
      exact interpH_zero D t)
    (fun t => interpH_one D t) (fun s => interpH_closed D s)
  refine ⟨?_, ?_⟩
  · apply piecewise_curveIntegrable (gapCycle D) hγ f
    apply hf.continuousOn.mono
    rintro _ ⟨t, rfl⟩
    show ellipseParam D (2 * Real.pi * (t : ℝ)) ≠ D.midpoint
    rw [← interpH_zero D t]
    exact interpH_ne D (0, t)
  · rw [hmain]
    exact reciprocal_integral_circle D


/-- Leaf 79.14-a: a holomorphic function bounded by `C` on a convex open set has a
`C`-Lipschitz primitive there (real mean value theorem along affine segments). -/
-- END proof development: 79.06
-- BEGIN PASTED H3: 79.14, 79.15, 79.18 (proof development/LIB079_79_14_V3_GK38, 79_15_V1_GK38, 79_18_V3_GK38)
theorem primitive_lipschitz_convex (V : Set ℂ) (hVo : IsOpen V) (hVc : Convex ℝ V)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f V) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z ∈ V, ‖f z‖ ≤ C) :
    ∃ P0 : ℂ → ℂ, (∀ z ∈ V, HasDerivAt P0 (f z) z) ∧
      ∀ x ∈ V, ∀ y ∈ V, ‖P0 y - P0 x‖ ≤ C * ‖y - x‖ := by
  obtain ⟨P0, hP0⟩ := Convex.exists_forall_hasDerivWithinAt hVc hf
  have hd : ∀ z ∈ V, HasDerivAt P0 (f z) z := fun z hz =>
    (hP0 z hz).hasDerivAt (hVo.mem_nhds hz)
  refine ⟨P0, hd, fun x hx y hy => ?_⟩
  set g : ℝ → ℂ := fun s => P0 (x + (s : ℂ) * (y - x)) with hg
  have hmemI : ∀ s ∈ Icc (0 : ℝ) 1, x + (s : ℂ) * (y - x) ∈ V := by
    intro s hs
    have := hVc.add_smul_sub_mem hx hy hs
    simpa [Complex.real_smul] using this
  have hgd : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt g ((y - x) • f (x + (s : ℂ) * (y - x))) (Icc (0 : ℝ) 1) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
    have hinner : HasDerivAt (fun s : ℝ => x + (s : ℂ) * (y - x)) (y - x) s := by
      have h := (h1.mul_const (y - x)).const_add x
      simpa using h
    have hc := (hd _ (hmemI s hs)).scomp s hinner
    exact hc.hasDerivWithinAt
  have hbnd : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖(y - x) • f (x + (s : ℂ) * (y - x))‖ ≤ C * ‖y - x‖ := by
    intro s hs
    rw [smul_eq_mul, norm_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbound _ (hmemI s hs)) (norm_nonneg _)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g)
    (f' := fun s : ℝ => (y - x) • f (x + (s : ℂ) * (y - x))) (C := C * ‖y - x‖)
    hgd hbnd (convex_Icc (0 : ℝ) 1) (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  have e1 : g 1 = P0 y := by simp [hg]
  have e0 : g 0 = P0 x := by simp [hg]
  rw [e1, e0] at key
  simpa using key

/-- Leaf 79.14: a bounded holomorphic function on a convex open set has a continuous extension
of a primitive to the closure, with the same Lipschitz constant. -/
theorem convex_bounded_primitive_extension (V : Set ℂ)
    (hVo : IsOpen V) (hVc : Convex ℝ V) (hV : V.Nonempty)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f V)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z ∈ V, ‖f z‖ ≤ C) :
    ∃ P : ℂ → ℂ, ContinuousOn P (closure V) ∧
      (∀ z ∈ V, HasDerivAt P (f z) z) ∧
      (∀ z ∈ closure V, ∀ w ∈ closure V, ‖P z - P w‖ ≤ C * dist z w) := by
  obtain ⟨P0, hd, hlip⟩ := primitive_lipschitz_convex V hVo hVc f hf C hC hbound
  have hlim : ∀ x ∈ closure V, ∃ y, Tendsto P0 (𝓝[V] x) (𝓝 y) := by
    intro x hx
    haveI : NeBot (𝓝[V] x) := mem_closure_iff_nhdsWithin_neBot.1 hx
    have hcau : Cauchy (map P0 (𝓝[V] x)) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      set δ : ℝ := ε / (2 * (C + 1)) with hδdef
      have hδpos : 0 < δ := by
        rw [hδdef]
        positivity
      have h2 : 2 * δ * (C + 1) = ε := by
        rw [hδdef]
        field_simp
      refine ⟨P0 '' (V ∩ ball x δ), mem_map.2 (mem_of_superset
        (inter_mem_nhdsWithin V (ball_mem_nhds x hδpos))
        (fun z hz => mem_image_of_mem P0 hz)), ?_⟩
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      have hdist : dist a b < 2 * δ := by
        have h1 : dist a x < δ := mem_ball.1 ha.2
        have h2' : dist b x < δ := mem_ball.1 hb.2
        have := dist_triangle a x b
        rw [dist_comm x b] at this
        linarith
      rw [dist_eq_norm]
      calc ‖P0 a - P0 b‖ = dist (P0 a) (P0 b) := (dist_eq_norm _ _).symm
        _ ≤ C * dist a b := by
          rw [dist_eq_norm (P0 a) (P0 b), dist_eq_norm a b]
          exact hlip b hb.1 a ha.1
        _ ≤ C * (2 * δ) := mul_le_mul_of_nonneg_left hdist.le hC
        _ < ε := by nlinarith [h2, hδpos]
    exact cauchy_iff_exists_le_nhds.1 hcau
  have hcont : ContinuousOn P0 V := fun z hz => (hd z hz).continuousAt.continuousWithinAt
  have hPV : ∀ z ∈ V, extendFrom V P0 z = P0 z := fun z hz => extendFrom_extends hcont z hz
  have hPc : ContinuousOn (extendFrom V P0) (closure V) :=
    continuousOn_extendFrom subset_rfl hlim
  refine ⟨extendFrom V P0, hPc, fun z hz => ?_, fun z hz w hw => ?_⟩
  · exact (hd z hz).congr_of_eventuallyEq (by
      filter_upwards [hVo.mem_nhds hz] with u hu
      exact hPV u hu)
  · have hle := le_on_closure (s := V ×ˢ V)
      (f := fun p : ℂ × ℂ => ‖extendFrom V P0 p.1 - extendFrom V P0 p.2‖)
      (g := fun p : ℂ × ℂ => C * dist p.1 p.2)
      (by
        rintro ⟨a, b⟩ ⟨ha, hb⟩
        simp only
        rw [hPV a ha, hPV b hb, dist_eq_norm]
        exact hlip b hb a ha)
      (by
        rw [closure_prod_eq]
        exact ((hPc.comp continuousOn_fst (fun p hp => hp.1)).sub
          (hPc.comp continuousOn_snd (fun p hp => hp.2))).norm)
      ((continuous_const.mul continuous_dist).continuousOn)
      (x := (z, w)) (by rw [closure_prod_eq]; exact ⟨hz, hw⟩)
    simpa using hle


/-- The half-disc `{w : Re w > 0, |w| < r}` used by the square-root chart. -/
def halfDisc (r : ℝ) : Set ℂ :=
  {w : ℂ | 0 < w.re ∧ ‖w‖ < r}

/-- The square-root chart `w ↦ a - u w²` at an endpoint `a`. -/
def squareChart (a u w : ℂ) : ℂ := a - u * w ^ 2

/-- Leaf 79.15: the square-root chart makes the endpoint differential bounded. -/
theorem squareChart_pullback_bound (f : ℂ → ℂ) (a u : ℂ)
    (hu : ‖u‖ = 1) (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hbound : ∀ w ∈ halfDisc r,
      ‖f (squareChart a u w)‖ ≤
        C / Real.sqrt (dist (squareChart a u w) a)) :
    ∀ w ∈ halfDisc r,
      ‖(-2 * u * w) * f (squareChart a u w)‖ ≤ 2 * C := by
  intro w hw
  obtain ⟨hre, hnorm⟩ := hw
  have hwpos : 0 < ‖w‖ := by
    rw [norm_pos_iff]
    intro h0
    rw [h0] at hre
    simp at hre
  have hd : dist (squareChart a u w) a = ‖w‖ ^ 2 := by
    rw [dist_eq_norm, squareChart]
    have h : a - u * w ^ 2 - a = -(u * w ^ 2) := by ring
    rw [h, norm_neg, norm_mul, norm_pow, hu, one_mul]
  have hsq : Real.sqrt (dist (squareChart a u w) a) = ‖w‖ := by
    rw [hd, Real.sqrt_sq (norm_nonneg w)]
  have hf := hbound w ⟨hre, hnorm⟩
  rw [hsq] at hf
  have key : ‖f (squareChart a u w)‖ * ‖w‖ ≤ C := (le_div_iff₀ hwpos).1 hf
  have hfac : ‖(-2 * u * w : ℂ)‖ = 2 * ‖w‖ := by
    simp [norm_mul, hu]
  rw [norm_mul, hfac]
  linarith [key, mul_comm ‖w‖ ‖f (squareChart a u w)‖]


-- END PASTED H3: 79.14, 79.15, 79.18
-- BEGIN proof development: 79.16 endpoint continuous primitive and chart helpers
def cutDisc (a u : ℂ) (r : ℝ) : Set ℂ :=
  ball a r \ (fun t : ℝ => a + u * (t : ℂ)) '' Ici 0

def squareChartInv (a u z : ℂ) : ℂ :=
  Complex.sqrt (-star u * (z - a))

theorem sqrt_re_pos {z : ℂ} (hz : z ∈ Complex.slitPlane) : 0 < (Complex.sqrt z).re := by
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  have hse : Complex.sqrt z = Complex.exp (Complex.log z / 2) := by
    simp [Complex.sqrt, Complex.cpow_def, hz0, div_eq_mul_inv]
  rw [hse, Complex.exp_re]
  refine mul_pos (Real.exp_pos _) ?_
  have h1 : (Complex.log z / 2).im = Complex.arg z / 2 := by
    rw [Complex.div_ofNat_im, Complex.log_im]
  rw [h1]
  have hπ : Complex.arg z ≠ Real.pi := (Complex.mem_slitPlane_iff_arg.1 hz).1
  have hlt : Complex.arg z < Real.pi := lt_of_le_of_ne (Complex.arg_le_pi z) hπ
  have hgt : -Real.pi < Complex.arg z := Complex.neg_pi_lt_arg z
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith

theorem sq_mem_slit {w : ℂ} (hw : 0 < w.re) : w ^ 2 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : w.im = 0
  · left
    have : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [pow_two]
    rw [this, him]
    nlinarith
  · right
    have : (w ^ 2).im = 2 * w.re * w.im := by simp [pow_two]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hw.ne') him

theorem sqrt_sq_of_re_pos {w : ℂ} (hw : 0 < w.re) : Complex.sqrt (w ^ 2) = w := by
  have hs := sq_mem_slit hw
  have hre := sqrt_re_pos hs
  have hsq : (Complex.sqrt (w ^ 2)) ^ 2 = w ^ 2 := by
    unfold Complex.sqrt
    exact Complex.cpow_nat_inv_pow (w ^ 2) (n := 2) (by norm_num) |>.trans rfl
  have h2 : (Complex.sqrt (w ^ 2) - w) * (Complex.sqrt (w ^ 2) + w) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have : (Complex.sqrt (w ^ 2) + w).re = 0 := by rw [h]; simp
    simp only [Complex.add_re] at this
    linarith

theorem star_mul_self_of_norm {u : ℂ} (hu : ‖u‖ = 1) : star u * u = 1 := by
  have h : star u * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [h, hu]; simp

theorem neg_star_mul_mem_slit {a u z : ℂ} (hu : ‖u‖ = 1) {r : ℝ} (hz : z ∈ cutDisc a u r) :
    -star u * (z - a) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push_neg at hcon
  obtain ⟨hre, him⟩ := hcon
  have hreal : (-star u * (z - a)) = (((-star u * (z - a)).re : ℝ) : ℂ) := by
    exact Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact him)
  set s : ℝ := (-star u * (z - a)).re with hs
  apply hz.2
  refine ⟨-s, by simpa using hre, ?_⟩
  have h1 : z - a = u * ((-s : ℝ) : ℂ) := by
    have e : (z - a) = u * (-star u * (z - a)) * (-1) := by
      have := star_mul_self_of_norm hu
      linear_combination (-(z - a)) * this
    rw [e, hreal]; push_cast; ring
  show a + u * ((-s : ℝ) : ℂ) = z
  linear_combination -h1

theorem squareChart_inverse (a u : ℂ) (hu : ‖u‖ = 1)
    (r : ℝ) (hr : 0 < r) :
    (∀ w ∈ halfDisc r,
      squareChart a u w ∈ cutDisc a u (r ^ 2) ∧
      squareChartInv a u (squareChart a u w) = w) ∧
    (∀ z ∈ cutDisc a u (r ^ 2),
      squareChartInv a u z ∈ halfDisc r ∧
      squareChart a u (squareChartInv a u z) = z) := by
  have hmul := star_mul_self_of_norm hu
  have hu0 : u ≠ 0 := by intro h0; rw [h0] at hu; simp at hu
  refine ⟨fun w hw => ⟨⟨?_, ?_⟩, ?_⟩, fun z hz => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rw [mem_ball, dist_eq_norm]
    unfold squareChart
    have h : a - u * w ^ 2 - a = -(u * w ^ 2) := by ring
    rw [h, norm_neg, norm_mul, norm_pow, hu, one_mul]
    nlinarith [hw.2, norm_nonneg w]
  · rintro ⟨t, ht, hteq⟩
    simp only [squareChart] at hteq
    have h1 : u * ((t : ℂ) + w ^ 2) = 0 := by linear_combination hteq
    have h2 : (t : ℂ) + w ^ 2 = 0 := (mul_eq_zero.mp h1).resolve_left hu0
    have h3 : w ^ 2 = -(t : ℂ) := by linear_combination h2
    have hs := sq_mem_slit hw.1
    rw [h3, Complex.mem_slitPlane_iff] at hs
    rcases hs with hs | hs
    · simp at hs; exact absurd (mem_Ici.mp ht) (not_le.mpr hs)
    · simp at hs
  · unfold squareChartInv squareChart
    have e : -star u * (a - u * w ^ 2 - a) = w ^ 2 := by
      linear_combination (w ^ 2) * hmul
    rw [e]; exact sqrt_sq_of_re_pos hw.1
  · exact sqrt_re_pos (neg_star_mul_mem_slit (r := r ^ 2) hu hz)
  · have hsq : (Complex.sqrt (-star u * (z - a))) ^ 2 = -star u * (z - a) := by
      unfold Complex.sqrt
      exact Complex.cpow_nat_inv_pow _ (n := 2) (by norm_num)
    have hn : ‖squareChartInv a u z‖ ^ 2 = ‖z - a‖ := by
      unfold squareChartInv
      rw [← norm_pow, hsq, norm_mul, norm_neg, norm_star, hu, one_mul]
    have hzr : ‖z - a‖ < r ^ 2 := by
      have := hz.1
      rwa [mem_ball, dist_eq_norm] at this
    rw [← hn] at hzr
    exact lt_of_pow_lt_pow_left₀ 2 hr.le hzr
  · have hsq : (Complex.sqrt (-star u * (z - a))) ^ 2 = -star u * (z - a) := by
      unfold Complex.sqrt
      exact Complex.cpow_nat_inv_pow _ (n := 2) (by norm_num)
    unfold squareChart squareChartInv
    rw [hsq]
    linear_combination (z - a) * hmul

theorem cutDisc_eq_slit (a u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) :
    cutDisc a u r = ball a r ∩ (fun z : ℂ => -star u * (z - a)) ⁻¹' Complex.slitPlane := by
  have hmul := star_mul_self_of_norm hu
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, neg_star_mul_mem_slit hu hz⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro ⟨t, ht, hteq⟩
    simp only at hteq
    have : -star u * (z - a) = -(t : ℂ) := by
      rw [← hteq]
      linear_combination (-(t : ℂ)) * hmul
    simp only [Set.mem_preimage] at h2
    rw [this, Complex.mem_slitPlane_iff] at h2
    rcases h2 with h2 | h2
    · simp at h2; exact absurd (mem_Ici.mp ht) (not_le.mpr h2)
    · simp at h2

theorem isOpen_cutDisc (a u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) : IsOpen (cutDisc a u r) := by
  rw [cutDisc_eq_slit a u hu r]
  exact isOpen_ball.inter (Complex.isOpen_slitPlane.preimage (by fun_prop))

theorem squareChartInv_differentiableAt (a u : ℂ) (hu : ‖u‖ = 1) {r : ℝ} {z : ℂ}
    (hz : z ∈ cutDisc a u r) : DifferentiableAt ℂ (squareChartInv a u) z := by
  have hs := neg_star_mul_mem_slit hu hz
  have h1 : DifferentiableAt ℂ (fun y : ℂ => -star u * (y - a)) z := by fun_prop
  exact (Complex.differentiableAt_sqrt hs).comp z h1

theorem squareChartInv_regular (a u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) :
    DifferentiableOn ℂ (squareChartInv a u) (cutDisc a u r) ∧
    ContinuousAt (squareChartInv a u) a ∧
    squareChartInv a u a = 0 := by
  refine ⟨fun z hz => (squareChartInv_differentiableAt a u hu hz).differentiableWithinAt, ?_, ?_⟩
  · unfold squareChartInv
    have h1 : ContinuousAt (fun y : ℂ => -star u * (y - a)) a := by fun_prop
    have h2 : ContinuousAt Complex.sqrt (-star u * (a - a)) := by
      apply Complex.continuousAt_sqrt
      simp
    exact h2.comp_of_eq h1 rfl
  · simp [squareChartInv]

theorem squareChart_hasDerivAt (a u w : ℂ) :
    HasDerivAt (squareChart a u) (-2 * u * w) w := by
  unfold squareChart
  have h := (hasDerivAt_pow 2 w).const_mul u
  have h2 := h.const_sub a
  convert h2 using 1
  simp <;> ring

theorem squareChartInv_hasDerivAt (a u : ℂ) (hu : ‖u‖ = 1) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ cutDisc a u (r ^ 2)) :
    HasDerivAt (squareChartInv a u) ((-2 * u * squareChartInv a u z)⁻¹) z := by
  obtain ⟨-, hback⟩ := (squareChart_inverse a u hu r hr).2 z hz
  set w := squareChartInv a u z with hw
  have hd := squareChartInv_differentiableAt a u hu hz
  have hcomp := (squareChart_hasDerivAt a u w).comp z hd.hasDerivAt
  have hev : (squareChart a u ∘ squareChartInv a u) =ᶠ[nhds z] id := by
    filter_upwards [(isOpen_cutDisc a u hu (r ^ 2)).mem_nhds hz] with y hy
    exact ((squareChart_inverse a u hu r hr).2 y hy).2
  have hcomp' := hcomp.congr_of_eventuallyEq hev.symm
  have huniq := (hasDerivAt_id z).unique hcomp'
  have hw0 : (-2 * u * w) ≠ 0 := by
    have hre : 0 < w.re := ((squareChart_inverse a u hu r hr).2 z hz).1.1
    have hw1 : w ≠ 0 := by intro h0; rw [h0] at hre; simp at hre
    have hu0 : u ≠ 0 := by intro h0; rw [h0] at hu; simp at hu
    exact mul_ne_zero (mul_ne_zero (by norm_num) hu0) hw1
  have h1 : (-2 * u * w) * deriv (squareChartInv a u) z = 1 := by
    have h2 := hcomp'.unique (hasDerivAt_id z)
    exact h2
  have h3 : deriv (squareChartInv a u) z = (-2 * u * w)⁻¹ :=
    (eq_inv_of_mul_eq_one_right h1)
  have h4 := hd.hasDerivAt
  rw [h3] at h4
  exact h4


theorem cutDisc_mono (a u : ℂ) {r r' : ℝ} (h : r ≤ r') : cutDisc a u r ⊆ cutDisc a u r' :=
  diff_subset_diff_left (ball_subset_ball h)

theorem halfDisc_isOpen (ρ : ℝ) : IsOpen (halfDisc ρ) := by
  have : halfDisc ρ = (fun w : ℂ => w.re) ⁻¹' Ioi 0 ∩ ball 0 ρ := by
    ext w; simp [halfDisc]
  rw [this]
  exact (isOpen_Ioi.preimage Complex.continuous_re).inter isOpen_ball

theorem halfDisc_convex (ρ : ℝ) : Convex ℝ (halfDisc ρ) := by
  have : halfDisc ρ = {w : ℂ | 0 < w.re} ∩ ball 0 ρ := by
    ext w; simp [halfDisc]
  rw [this]
  exact (convex_halfSpace_re_gt 0).inter (convex_ball 0 ρ)

theorem halfDisc_small {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ m : ℝ, 0 < m ∧ m < ε ∧ m < ρ ∧ ((m : ℝ) : ℂ) ∈ halfDisc ρ := by
  refine ⟨min (ε / 2) (ρ / 2), lt_min (by linarith) (by linarith),
    lt_of_le_of_lt (min_le_left _ _) (by linarith),
    lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_, ?_⟩
  · simp only [Complex.ofReal_re]
    exact lt_min (by linarith) (by linarith)
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_min (by linarith) (by linarith))]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

theorem zero_mem_closure_halfDisc {ρ : ℝ} (hρ : 0 < ρ) : (0 : ℂ) ∈ closure (halfDisc ρ) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨m, hm0, hmε, -, hmem⟩ := halfDisc_small hρ hε
  refine ⟨(m : ℂ), hmem, ?_⟩
  rw [dist_eq_norm, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
  exact hmε

theorem endpoint_primitive_core (a u : ℂ) (hu : ‖u‖ = 1) (f : ℂ → ℂ) (r0 : ℝ) (hr0 : 0 < r0)
    (hf : DifferentiableOn ℂ f (cutDisc a u r0)) (C δ0 : ℝ) (hC : 0 ≤ C) (hδ0 : 0 < δ0)
    (hB : ∀ z ∈ cutDisc a u r0, 0 < dist z a → dist z a < δ0 →
      ‖f z‖ ≤ C / Real.sqrt (dist z a)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r0 ∧ ∃ P : ℂ → ℂ,
      ContinuousOn P (cutDisc a u δ ∪ {a}) ∧
      ∀ z ∈ cutDisc a u δ, HasDerivAt P (f z) z := by
  have hu0 : u ≠ 0 := by intro h0; rw [h0] at hu; simp at hu
  set r := min r0 δ0 with hr
  have hrpos : 0 < r := lt_min hr0 hδ0
  set ρ := Real.sqrt r with hρ
  have hρpos : 0 < ρ := Real.sqrt_pos.2 hrpos
  have hρsq : ρ ^ 2 = r := Real.sq_sqrt hrpos.le
  have hinv := squareChart_inverse a u hu ρ hρpos
  rw [hρsq] at hinv
  have hsub : cutDisc a u r ⊆ cutDisc a u r0 := cutDisc_mono a u (min_le_left _ _)
  have hchart : ∀ w ∈ halfDisc ρ, squareChart a u w ∈ cutDisc a u r0 :=
    fun w hw => hsub (hinv.1 w hw).1
  set g : ℂ → ℂ := fun w => (-2 * u * w) * f (squareChart a u w) with hg
  have hgd : DifferentiableOn ℂ g (halfDisc ρ) := by
    intro w hw
    have hfd : DifferentiableAt ℂ f (squareChart a u w) :=
      hf.differentiableAt ((isOpen_cutDisc a u hu r0).mem_nhds (hchart w hw))
    have hc : DifferentiableAt ℂ (squareChart a u) w :=
      (squareChart_hasDerivAt a u w).differentiableAt
    have h1 : DifferentiableAt ℂ (fun w : ℂ => -2 * u * w) w := by fun_prop
    exact (h1.mul (hfd.comp w hc)).differentiableWithinAt
  have hbdw : ∀ w ∈ halfDisc ρ,
      ‖f (squareChart a u w)‖ ≤ C / Real.sqrt (dist (squareChart a u w) a) := by
    intro w hw
    have hd : dist (squareChart a u w) a = ‖w‖ ^ 2 := by
      rw [dist_eq_norm]; unfold squareChart
      have h : a - u * w ^ 2 - a = -(u * w ^ 2) := by ring
      rw [h, norm_neg, norm_mul, norm_pow, hu, one_mul]
    have hw0 : w ≠ 0 := by
      intro h0; have := hw.1; rw [h0] at this; simp at this
    have hpos : 0 < dist (squareChart a u w) a := by
      rw [hd]; exact pow_pos (norm_pos_iff.2 hw0) 2
    have hlt : dist (squareChart a u w) a < δ0 := by
      rw [hd]
      have h2 : ‖w‖ ^ 2 < ρ ^ 2 := pow_lt_pow_left₀ hw.2 (norm_nonneg w) two_ne_zero
      rw [hρsq] at h2
      exact lt_of_lt_of_le h2 (min_le_right _ _)
    exact hB _ (hchart w hw) hpos hlt
  have hgb : ∀ w ∈ halfDisc ρ, ‖g w‖ ≤ 2 * C :=
    squareChart_pullback_bound f a u hu ρ C hρpos hC hbdw
  obtain ⟨m, -, -, -, hmem⟩ := halfDisc_small hρpos hρpos
  obtain ⟨Pw, hPc, hPd, -⟩ := convex_bounded_primitive_extension (halfDisc ρ)
    (halfDisc_isOpen ρ) (halfDisc_convex ρ) ⟨_, hmem⟩ g hgd (2 * C) (by linarith) hgb
  have hder : ∀ z ∈ cutDisc a u r,
      HasDerivAt (fun z => Pw (squareChartInv a u z)) (f z) z := by
    intro z hz
    have hz' : z ∈ cutDisc a u (ρ ^ 2) := by rw [hρsq]; exact hz
    obtain ⟨hwmem, hback⟩ := hinv.2 z hz
    have h1 : HasDerivAt Pw (g (squareChartInv a u z)) (squareChartInv a u z) :=
      hPd _ hwmem
    have h2 := squareChartInv_hasDerivAt a u hu hρpos hz'
    have h3 := h1.comp z h2
    have hw0 : (-2 * u * squareChartInv a u z) ≠ 0 := by
      have hre : 0 < (squareChartInv a u z).re := hwmem.1
      have hw1 : squareChartInv a u z ≠ 0 := by
        intro h0; rw [h0] at hre; simp at hre
      exact mul_ne_zero (mul_ne_zero (by norm_num) hu0) hw1
    have hgw : g (squareChartInv a u z) = (-2 * u * squareChartInv a u z) * f z := by
      simp only [hg, hback]
    refine h3.congr_deriv ?_
    rw [hgw]
    linear_combination (f z) * mul_inv_cancel₀ hw0
  refine ⟨r, hrpos, min_le_left _ _, fun z => Pw (squareChartInv a u z), ?_, hder⟩
  intro z hz
  rcases hz with hz | hz
  · exact (hder z hz).continuousAt.continuousWithinAt
  · rw [Set.mem_singleton_iff] at hz
    rw [hz]
    obtain ⟨-, hca, h0⟩ := squareChartInv_regular a u hu r
    have hmaps : MapsTo (squareChartInv a u) (cutDisc a u r ∪ {a}) (closure (halfDisc ρ)) := by
      intro y hy
      rcases hy with hy | hy
      · have hy' : y ∈ cutDisc a u (ρ ^ 2) := by rw [hρsq]; exact hy
        exact subset_closure (hinv.2 y hy).1
      · rw [Set.mem_singleton_iff] at hy
        rw [hy, h0]
        exact zero_mem_closure_halfDisc hρpos
    have hPw : ContinuousWithinAt Pw (closure (halfDisc ρ)) (squareChartInv a u a) := by
      rw [h0]; exact hPc 0 (zero_mem_closure_halfDisc hρpos)
    exact hPw.comp hca.continuousWithinAt hmaps

theorem endpoint_cutDisc_eq (D : DiscWithSegment)
    (hgap : D.a ≠ D.b) (r : ℝ) (hr : 0 < r)
    (hlen : r < ‖D.b - D.a‖)
    (hclear : r ≤ D.radius - dist D.a D.center) :
    D.domain ∩ ball D.a r = cutDisc D.a D.axis r := by
  have hL : 0 < ‖D.b - D.a‖ := norm_pos_iff.2 (sub_ne_zero.2 hgap.symm)
  obtain ⟨-, -, hu, -⟩ := disc_segment_coordinates D
  have haxis : D.axis = (D.b - D.a) / ((‖D.b - D.a‖ : ℝ) : ℂ) := by
    simp [DiscWithSegment.axis, hgap]
  have hLc : ((‖D.b - D.a‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hballsub : ball D.a r ⊆ ball D.center D.radius := by
    intro z hz
    rw [mem_ball] at hz ⊢
    have := dist_triangle z D.a D.center
    linarith
  have hrayeq : ∀ θ : ℝ, D.a + θ • (D.b - D.a) =
      D.a + D.axis * ((θ * ‖D.b - D.a‖ : ℝ) : ℂ) := by
    intro θ
    rw [haxis, Complex.real_smul]
    push_cast
    field_simp
  ext z
  constructor
  · rintro ⟨⟨hzc, hzseg⟩, hzb⟩
    refine ⟨hzb, ?_⟩
    rintro ⟨t, ht, hteq⟩
    apply hzseg
    have hnorm : ‖z - D.a‖ = t := by
      rw [← hteq]
      have ht' : 0 ≤ t := ht
      simp only [add_sub_cancel_left, norm_mul, hu, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht']
    have htr : t < r := by
      have := hzb; rw [mem_ball, dist_eq_norm, hnorm] at this; exact this
    rw [segment_eq_image']
    refine ⟨t / ‖D.b - D.a‖, ⟨div_nonneg ht hL.le, ?_⟩, ?_⟩
    · rw [div_le_one hL]; linarith
    · show D.a + (t / ‖D.b - D.a‖) • (D.b - D.a) = z
      rw [hrayeq, div_mul_cancel₀ _ hL.ne']
      exact hteq
  · rintro ⟨hzb, hzray⟩
    refine ⟨⟨hballsub hzb, ?_⟩, hzb⟩
    intro hzseg
    apply hzray
    rw [segment_eq_image'] at hzseg
    obtain ⟨θ, ⟨hθ0, hθ1⟩, hθeq⟩ := hzseg
    refine ⟨θ * ‖D.b - D.a‖, mul_nonneg hθ0 hL.le, ?_⟩
    show D.a + D.axis * ((θ * ‖D.b - D.a‖ : ℝ) : ℂ) = z
    rw [← hrayeq]
    exact hθeq

theorem endpoint_primitive_left (D : DiscWithSegment) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f D.domain)
    (hbound : HasEndpointBound f D.domain D.a) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℂ → ℂ,
      ContinuousOn P ((D.domain ∩ ball D.a δ) ∪ {D.a}) ∧
      ∀ z ∈ D.domain ∩ ball D.a δ, HasDerivAt P (f z) z := by
  obtain ⟨C, δ0, hC, hδ0, hB⟩ := hbound
  have hclearpos : 0 < D.radius - dist D.a D.center := by
    have := D.contained (left_mem_segment ℝ D.a D.b)
    rw [mem_ball] at this; linarith
  by_cases hgap : D.a = D.b
  · set r := D.radius - dist D.a D.center with hr
    have hballsub : ball D.a r ⊆ ball D.center D.radius := by
      intro z hz
      rw [mem_ball] at hz ⊢
      have := dist_triangle z D.a D.center
      linarith
    have hdomsub : ball D.a r \ {D.a} ⊆ D.domain := by
      rintro z ⟨hz, hza⟩
      refine ⟨hballsub hz, ?_⟩
      rw [← hgap, segment_same]
      exact hza
    have hfd : DifferentiableOn ℂ f (ball D.a r \ {D.a}) := hf.mono hdomsub
    have hbd : HasEndpointBound f (ball D.a r \ {D.a}) D.a :=
      ⟨C, δ0, hC, hδ0, fun z hz => hB z (hdomsub hz)⟩
    obtain ⟨F, hFd, hFeq⟩ := square_root_bound_removable f D.a r hclearpos hfd hbd
    obtain ⟨P0, hP0⟩ := Convex.exists_forall_hasDerivWithinAt (convex_ball D.a r) hFd
    have hd : ∀ z ∈ ball D.a r, HasDerivAt P0 (F z) z := fun z hz =>
      (hP0 z hz).hasDerivAt (isOpen_ball.mem_nhds hz)
    have hsubset : (D.domain ∩ ball D.a r) ∪ {D.a} ⊆ ball D.a r := by
      rintro z (hz | hz)
      · exact hz.2
      · rw [mem_singleton_iff] at hz; rw [hz]; exact mem_ball_self hclearpos
    refine ⟨r, hclearpos, P0, ?_, ?_⟩
    · intro z hz
      exact (hd z (hsubset hz)).continuousAt.continuousWithinAt
    · intro z hz
      have hza : z ≠ D.a := by
        intro h; apply hz.1.2; rw [h]; exact left_mem_segment ℝ D.a D.b
      have := hd z hz.2
      rwa [hFeq ⟨hz.2, hza⟩] at this
  · have hL : 0 < ‖D.b - D.a‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hgap))
    obtain ⟨-, -, hu, -⟩ := disc_segment_coordinates D
    set r0 := min (‖D.b - D.a‖ / 2) (D.radius - dist D.a D.center) with hr0
    have hr0pos : 0 < r0 := lt_min (by linarith) hclearpos
    have hr0L : r0 < ‖D.b - D.a‖ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hr0c : r0 ≤ D.radius - dist D.a D.center := min_le_right _ _
    have heq0 := endpoint_cutDisc_eq D hgap r0 hr0pos hr0L hr0c
    have hsub0 : cutDisc D.a D.axis r0 ⊆ D.domain := by
      rw [← heq0]; exact inter_subset_left
    have hfd : DifferentiableOn ℂ f (cutDisc D.a D.axis r0) := hf.mono hsub0
    have hB' : ∀ z ∈ cutDisc D.a D.axis r0, 0 < dist z D.a → dist z D.a < δ0 →
        ‖f z‖ ≤ C / Real.sqrt (dist z D.a) := fun z hz h1 h2 => hB z (hsub0 hz) h1 h2
    obtain ⟨δ, hδ, hδr0, P, hPc, hPd⟩ :=
      endpoint_primitive_core D.a D.axis hu f r0 hr0pos hfd C δ0 hC hδ0 hB'
    have heq := endpoint_cutDisc_eq D hgap δ hδ (lt_of_le_of_lt hδr0 hr0L) (hδr0.trans hr0c)
    refine ⟨δ, hδ, P, ?_, ?_⟩
    · rw [heq]; exact hPc
    · rw [heq]; exact hPd

def DiscWithSegment.swap (D : DiscWithSegment) : DiscWithSegment where
  center := D.center
  radius := D.radius
  radius_pos := D.radius_pos
  a := D.b
  b := D.a
  contained := by rw [segment_symm]; exact D.contained

theorem DiscWithSegment.swap_domain (D : DiscWithSegment) : D.swap.domain = D.domain := by
  unfold DiscWithSegment.domain
  show Metric.ball D.center D.radius \ segment ℝ D.b D.a = Metric.ball D.center D.radius \ segment ℝ D.a D.b
  rw [segment_symm]

theorem endpoint_continuous_primitive (D : DiscWithSegment)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f D.domain)
    (a : ℂ) (ha : a = D.a ∨ a = D.b)
    (hbound : HasEndpointBound f D.domain a) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℂ → ℂ,
      ContinuousOn P ((D.domain ∩ ball a δ) ∪ {a}) ∧
      ∀ z ∈ D.domain ∩ ball a δ, HasDerivAt P (f z) z := by
  rcases ha with rfl | rfl
  · exact endpoint_primitive_left D f hf hbound
  · have hdom := D.swap_domain
    have := endpoint_primitive_left D.swap f (by rw [hdom]; exact hf) (by rw [hdom]; exact hbound)
    rw [hdom] at this
    exact this


-- END proof development: 79.16
-- BEGIN PASTED H3: 79.03 tail (proof development/LIB079_79_03_V5_GK38)
-- 79.03 (H3 LIB079_79_03_V5_GK38 tail)
theorem axis_mul_star (D : DiscWithSegment) : D.axis * star D.axis = 1 := by
  have hu1 := (disc_segment_coordinates D).2.2.1
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu1]
  norm_num

theorem star_axis_mul (D : DiscWithSegment) : star D.axis * D.axis = 1 := by
  rw [mul_comm]
  exact axis_mul_star D

theorem mid_mem_seg (D : DiscWithSegment) : D.midpoint ∈ segment ℝ D.a D.b := by
  have hh : 0 ≤ D.halfLength := by
    unfold DiscWithSegment.halfLength
    positivity
  rw [(disc_segment_coordinates D).2.2.2]
  exact ⟨0, ⟨by linarith, by linarith⟩, by simp⟩

/-- The coordinate map of the ellipse (design LIB-079). -/
def ellipseCoordinates (D : DiscWithSegment) (z : ℂ) : ℂ :=
  ((star D.axis * (z - D.midpoint)).re /
      (D.halfLength + D.width) : ℝ) +
    Complex.I * ((star D.axis * (z - D.midpoint)).im / D.width : ℝ)

/-- The radial projection onto the ellipse (design LIB-079). -/
def ellipseProjection (D : DiscWithSegment) (z : ℂ) : ℂ :=
  D.midpoint + (‖ellipseCoordinates D z‖⁻¹ : ℝ) • (z - D.midpoint)

/-- The radial deformation (design LIB-079). -/
def radialDeformation (D : DiscWithSegment) (s : ℝ) (z : ℂ) : ℂ :=
  (1 - s) • z + s • ellipseProjection D z

theorem ellipseCoordinates_re (D : DiscWithSegment) (z : ℂ) :
    (ellipseCoordinates D z).re = (star D.axis * (z - D.midpoint)).re / (D.halfLength + D.width) := by
  unfold ellipseCoordinates
  generalize star D.axis * (z - D.midpoint) = q
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem ellipseCoordinates_im (D : DiscWithSegment) (z : ℂ) :
    (ellipseCoordinates D z).im = (star D.axis * (z - D.midpoint)).im / D.width := by
  unfold ellipseCoordinates
  generalize star D.axis * (z - D.midpoint) = q
  rw [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.ofReal_re]
  ring

theorem ellipseCoordinates_ne_zero (D : DiscWithSegment) {z : ℂ} (hz : z ∈ D.domain) :
    ellipseCoordinates D z ≠ 0 := by
  intro h0
  apply hz.2
  have hα : D.halfLength + D.width ≠ 0 := ((disc_segment_coordinates D).2.1).ne'
  have hβ : D.width ≠ 0 := (disc_segment_coordinates D).1.ne'
  have hre0 := ellipseCoordinates_re D z
  have him0 := ellipseCoordinates_im D z
  rw [h0, Complex.zero_re] at hre0
  rw [h0, Complex.zero_im] at him0
  have hq1 : (star D.axis * (z - D.midpoint)).re = 0 :=
    (div_eq_zero_iff.1 hre0.symm).resolve_right hα
  have hq2 : (star D.axis * (z - D.midpoint)).im = 0 :=
    (div_eq_zero_iff.1 him0.symm).resolve_right hβ
  have hq : star D.axis * (z - D.midpoint) = 0 :=
    Complex.ext (by simpa using hq1) (by simpa using hq2)
  have h3 : D.axis * (star D.axis * (z - D.midpoint)) = 0 := by
    rw [hq, mul_zero]
  rw [← mul_assoc, axis_mul_star, one_mul] at h3
  have hzm' : z = D.midpoint := sub_eq_zero.1 h3
  rw [hzm']
  exact mid_mem_seg D

theorem ellipseProjection_eq_ellipseParam (D : DiscWithSegment) {z : ℂ} (hz : z ∈ D.domain) :
    ∃ θ : ℝ, ellipseProjection D z = ellipseParam D θ := by
  have hc0 := ellipseCoordinates_ne_zero D hz
  have hα : D.halfLength + D.width ≠ 0 := ((disc_segment_coordinates D).2.1).ne'
  have hβ : D.width ≠ 0 := (disc_segment_coordinates D).1.ne'
  have hρ : ‖ellipseCoordinates D z‖ ≠ 0 := norm_ne_zero_iff.2 hc0
  have hu := axis_mul_star D
  have hdecomp : z - D.midpoint = D.axis * (star D.axis * (z - D.midpoint)) := by
    rw [← mul_assoc, hu, one_mul]
  obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = ((‖ellipseCoordinates D z‖⁻¹ : ℝ) : ℂ) *
      ellipseCoordinates D z := ⟨_, rfl⟩
  have hwn : ‖w‖ = 1 := by
    rw [hwdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
    exact inv_mul_cancel₀ hρ
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hwn
    norm_num at hwn
  refine ⟨Complex.arg w, ?_⟩
  unfold ellipseProjection ellipseParam
  rw [Complex.cos_arg hw0, Complex.sin_arg, hwn, div_one, div_one]
  have hre : (D.halfLength + D.width) * w.re =
      ‖ellipseCoordinates D z‖⁻¹ * (star D.axis * (z - D.midpoint)).re := by
    rw [hwdef, Complex.re_ofReal_mul, ellipseCoordinates_re]
    field_simp
  have him : D.width * w.im =
      ‖ellipseCoordinates D z‖⁻¹ * (star D.axis * (z - D.midpoint)).im := by
    rw [hwdef, Complex.im_ofReal_mul, ellipseCoordinates_im]
    field_simp
  have hmain : ((‖ellipseCoordinates D z‖⁻¹ * (star D.axis * (z - D.midpoint)).re : ℝ) : ℂ) +
      Complex.I * ((‖ellipseCoordinates D z‖⁻¹ * (star D.axis * (z - D.midpoint)).im : ℝ) : ℂ) =
      ((‖ellipseCoordinates D z‖⁻¹ : ℝ) : ℂ) * (star D.axis * (z - D.midpoint)) := by
    apply Complex.ext <;> simp
  rw [hre, him]
  rw [Complex.real_smul]
  calc D.midpoint + ((‖ellipseCoordinates D z‖⁻¹ : ℝ) : ℂ) * (z - D.midpoint)
      = D.midpoint + ((‖ellipseCoordinates D z‖⁻¹ : ℝ) : ℂ) * (D.axis * (star D.axis * (z - D.midpoint))) := by
        rw [← hdecomp]
    _ = D.midpoint + D.axis * (((‖ellipseCoordinates D z‖⁻¹ : ℝ) : ℂ) * (star D.axis * (z - D.midpoint))) := by
        ring
    _ = D.midpoint + D.axis * (((‖ellipseCoordinates D z‖⁻¹ * (star D.axis * (z - D.midpoint)).re : ℝ) : ℂ) +
          Complex.I * ((‖ellipseCoordinates D z‖⁻¹ * (star D.axis * (z - D.midpoint)).im : ℝ) : ℂ)) := by
        rw [hmain]

theorem ellipseProjection_contDiffOn (D : DiscWithSegment) :
    ContDiffOn ℝ 1 (ellipseProjection D) D.domain := by
  have hgC : ContDiff ℂ 1 (fun y : ℂ => star D.axis * (y - D.midpoint)) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  have hgR : ContDiff ℝ 1 (fun y : ℂ => star D.axis * (y - D.midpoint)) :=
    hgC.restrict_scalars ℝ
  have hre_s : ContDiff ℝ 1 (fun y : ℂ => (star D.axis * (y - D.midpoint)).re) :=
    Complex.reCLM.contDiff.comp hgR
  have him_s : ContDiff ℝ 1 (fun y : ℂ => (star D.axis * (y - D.midpoint)).im) :=
    Complex.imCLM.contDiff.comp hgR
  have hcoord : ContDiff ℝ 1 (ellipseCoordinates D) := by
    unfold ellipseCoordinates
    exact (Complex.ofRealCLM.contDiff.comp (hre_s.div_const _)).add
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (him_s.div_const _)))
  intro z hz
  have hne := ellipseCoordinates_ne_zero D hz
  have hn : ContDiffAt ℝ 1 (fun y => ‖ellipseCoordinates D y‖) z :=
    hcoord.contDiffAt.norm ℝ hne
  have hinv : ContDiffAt ℝ 1 (fun y => ‖ellipseCoordinates D y‖⁻¹) z :=
    hn.inv (norm_ne_zero_iff.2 hne)
  have hsm : ContDiffAt ℝ 1
      (fun y => D.midpoint + (‖ellipseCoordinates D y‖⁻¹ : ℝ) • (y - D.midpoint)) z :=
    contDiffAt_const.add (hinv.smul (contDiffAt_id.sub contDiffAt_const))
  exact hsm.contDiffWithinAt

theorem radialDeformation_mem (D : DiscWithSegment) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {z : ℂ} (hz : z ∈ D.domain) : radialDeformation D s z ∈ D.domain := by
  obtain ⟨θ, hθ⟩ := ellipseProjection_eq_ellipseParam D hz
  have hp : ellipseProjection D z ∈ D.domain := by
    rw [hθ]
    exact ellipseParam_mem_domain D θ
  refine ⟨?_, ?_⟩
  · exact (convex_ball D.center D.radius) hz.1 hp.1 (by linarith [hs.2]) hs.1 (by ring)
  · intro hq
    rw [(disc_segment_coordinates D).2.2.2] at hq
    obtain ⟨t, ⟨ht1, ht2⟩, ht⟩ := hq
    have hc0 := ellipseCoordinates_ne_zero D hz
    have hρ : 0 < ‖ellipseCoordinates D z‖ := norm_pos_iff.2 hc0
    have hK : 0 < ‖ellipseCoordinates D z‖⁻¹ := inv_pos.2 hρ
    obtain ⟨lam, hlamdef⟩ : ∃ l : ℝ, l = (1 - s) + s * ‖ellipseCoordinates D z‖⁻¹ := ⟨_, rfl⟩
    have hlpos : 0 < lam := by
      rw [hlamdef]
      rcases le_total ‖ellipseCoordinates D z‖⁻¹ 1 with hK1 | hK1
      · nlinarith [mul_nonneg hs.1 hK.le, hs.2]
      · nlinarith [mul_nonneg hs.1 (sub_nonneg.2 hK1), hs.2]
    have hrad : radialDeformation D s z = D.midpoint + lam • (z - D.midpoint) := by
      rw [hlamdef]
      unfold radialDeformation ellipseProjection
      module
    have ht' : D.midpoint + D.axis * (t : ℂ) = D.midpoint + lam • (z - D.midpoint) := by
      rw [← hrad]
      exact ht
    have h2 : D.axis * (t : ℂ) = lam • (z - D.midpoint) := add_left_cancel ht'
    have hvτ : z - D.midpoint = D.axis * (((lam⁻¹ * t : ℝ)) : ℂ) := by
      have hid : lam⁻¹ • (lam • (z - D.midpoint)) = z - D.midpoint := by
        rw [smul_smul, inv_mul_cancel₀ hlpos.ne', one_smul]
      calc z - D.midpoint = lam⁻¹ • (lam • (z - D.midpoint)) := hid.symm
        _ = lam⁻¹ • (D.axis * (t : ℂ)) := by rw [← h2]
        _ = D.axis * (((lam⁻¹ * t : ℝ)) : ℂ) := by
          rw [Complex.real_smul]
          push_cast
          ring
    obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = lam⁻¹ * t := ⟨_, rfl⟩
    rw [← hτ] at hvτ
    have hτt : (t : ℝ) = lam * τ := by
      rw [hτ, ← mul_assoc, mul_inv_cancel₀ hlpos.ne', one_mul]
    have hα : 0 < D.halfLength + D.width := (disc_segment_coordinates D).2.1
    have hw : 0 < D.width := (disc_segment_coordinates D).1
    have hh : 0 ≤ D.halfLength := by
      unfold DiscWithSegment.halfLength
      positivity
    have hτbig : D.halfLength < |τ| := by
      by_contra hle
      push_neg at hle
      apply hz.2
      rw [(disc_segment_coordinates D).2.2.2]
      obtain ⟨h1, h2'⟩ := abs_le.1 hle
      refine ⟨τ, ⟨h1, h2'⟩, ?_⟩
      simp only
      linear_combination (-1 : ℂ) * hvτ
    have hq : star D.axis * (z - D.midpoint) = (τ : ℂ) := by
      rw [hvτ, ← mul_assoc, star_axis_mul, one_mul]
    have hcoord : ellipseCoordinates D z = ((τ / (D.halfLength + D.width) : ℝ) : ℂ) := by
      unfold ellipseCoordinates
      rw [hq]
      simp
    have hnorm : ‖ellipseCoordinates D z‖ = |τ| / (D.halfLength + D.width) := by
      rw [hcoord, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hα]
    have hτpos : 0 < |τ| := by linarith
    have hτne : |τ| ≠ 0 := hτpos.ne'
    have habs : |(t : ℝ)| = (1 - s) * |τ| + s * (D.halfLength + D.width) := by
      rw [hτt, abs_mul, abs_of_pos hlpos, hlamdef, hnorm, inv_div]
      field_simp
    have hthh : |(t : ℝ)| ≤ D.halfLength := abs_le.2 ⟨ht1, ht2⟩
    have key1 := mul_le_mul_of_nonneg_left (min_le_left (|τ| - D.halfLength) D.width)
      (sub_nonneg.2 hs.2)
    have key2 := mul_le_mul_of_nonneg_left (min_le_right (|τ| - D.halfLength) D.width) hs.1
    have hm : 0 < min (|τ| - D.halfLength) D.width := lt_min (by linarith) hw
    nlinarith [key1, key2, hm, habs, hthh]

theorem ellipseProjection_geometry (D : DiscWithSegment) :
    ContDiffOn ℝ 1 (ellipseProjection D) D.domain ∧
    (∀ z ∈ D.domain, ‖ellipseCoordinates D z‖ ≠ 0) ∧
    (∀ z ∈ D.domain, ∃ θ : ℝ,
      ellipseProjection D z = ellipseParam D θ) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ D.domain,
      radialDeformation D s z ∈ D.domain) :=
  ⟨ellipseProjection_contDiffOn D,
    fun z hz => norm_ne_zero_iff.2 (ellipseCoordinates_ne_zero D hz),
    fun z hz => ellipseProjection_eq_ellipseParam D hz,
    fun s hs z hz => radialDeformation_mem D hs hz⟩


-- END PASTED H3: 79.03
-- BEGIN proof development: 79.11 (H3 LIB079_79_11_V1_GK38 adapter), 79.12, 79.04, 79.13, 79.17
-- 79.11/79.12
/-- Leaf 79.11: integration over integer periods (routine adapter). -/
theorem integral_integer_period (g : ℝ → ℂ) (hg : Continuous g)
    (T : ℝ) (hT : 0 < T) (hper : Function.Periodic g T)
    (x : ℝ) (k : ℤ) :
    (∫ t : ℝ in x..(x + (k : ℝ) * T), g t) =
      (k : ℂ) * (∫ t : ℝ in 0..T, g t) := by
  have hI : ∀ t₁ t₂ : ℝ, IntervalIntegrable g MeasureSpace.volume t₁ t₂ :=
    fun t₁ t₂ => hg.intervalIntegrable t₁ t₂
  rw [← zsmul_eq_mul, hper.intervalIntegral_add_zsmul_eq k x hI,
    hper.intervalIntegral_add_eq x 0, zero_add, zsmul_eq_mul]

/-- derivative of the ellipse parametrisation -/
def ellipseDeriv (D : DiscWithSegment) (s : ℝ) : ℂ :=
  D.axis * ((((D.halfLength + D.width) * -Real.sin s : ℝ) : ℂ) +
    Complex.I * ((D.width * Real.cos s : ℝ) : ℂ))

theorem ellipseParam_hasDerivAt (D : DiscWithSegment) (s : ℝ) :
    HasDerivAt (ellipseParam D) (ellipseDeriv D s) s := by
  have h1 := ((Real.hasDerivAt_cos s).const_mul (D.halfLength + D.width)).ofReal_comp
  have h2 := ((Real.hasDerivAt_sin s).const_mul D.width).ofReal_comp
  have h3 := ((h1.add (h2.const_mul Complex.I)).const_mul D.axis).const_add D.midpoint
  exact h3

theorem ellipseParam_periodic (D : DiscWithSegment) :
    Function.Periodic (ellipseParam D) (2 * Real.pi) := by
  intro x
  unfold ellipseParam
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem ellipseDeriv_periodic (D : DiscWithSegment) :
    Function.Periodic (ellipseDeriv D) (2 * Real.pi) := by
  intro x
  unfold ellipseDeriv
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem ellipse_mem_range (D : DiscWithSegment) (s : ℝ) :
    ellipseParam D s ∈ range (gapCycle D) := by
  refine ⟨⟨Int.fract (s / (2 * Real.pi)), Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩
  show ellipseParam D (2 * Real.pi * Int.fract (s / (2 * Real.pi))) = ellipseParam D s
  have h := (ellipseParam_periodic D).int_mul ⌊s / (2 * Real.pi)⌋
    (2 * Real.pi * Int.fract (s / (2 * Real.pi)))
  have e : 2 * Real.pi * Int.fract (s / (2 * Real.pi)) +
      (⌊s / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi) = s := by
    rw [Int.fract]
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp
    ring
  rw [e] at h
  exact h.symm

theorem ellipse_g_continuous (D : DiscWithSegment) (f : ℂ → ℂ)
    (hf : ContinuousOn f (range (gapCycle D))) :
    Continuous (fun s : ℝ => f (ellipseParam D s) * ellipseDeriv D s) := by
  have hE : Continuous (ellipseParam D) :=
    continuous_iff_continuousAt.2 fun s => (ellipseParam_hasDerivAt D s).continuousAt
  have hf' : Continuous fun s : ℝ => f (ellipseParam D s) :=
    hf.comp_continuous hE (fun s => ellipse_mem_range D s)
  have hd : Continuous (ellipseDeriv D) := by
    unfold ellipseDeriv
    fun_prop
  exact hf'.mul hd

theorem cos_add_sin_eq_exp (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I]
  push_cast
  rw [mul_comm Complex.I]

theorem ellipseCoordinates_ellipseParam (D : DiscWithSegment) (θ : ℝ) :
    ellipseCoordinates D (ellipseParam D θ) =
      ((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ) := by
  obtain ⟨hw, hA, hu, -⟩ := disc_segment_coordinates D
  have hmul := star_mul_self_of_norm hu
  have hX : star D.axis * (ellipseParam D θ - D.midpoint) =
      (((D.halfLength + D.width) * Real.cos θ : ℝ) : ℂ) +
        Complex.I * ((D.width * Real.sin θ : ℝ) : ℂ) := by
    unfold ellipseParam
    rw [add_sub_cancel_left, ← mul_assoc, hmul, one_mul]
  unfold ellipseCoordinates
  rw [hX]
  have hre : ((((D.halfLength + D.width) * Real.cos θ : ℝ) : ℂ) +
        Complex.I * ((D.width * Real.sin θ : ℝ) : ℂ)).re =
      (D.halfLength + D.width) * Real.cos θ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, zero_mul, one_mul, mul_zero, sub_zero, add_zero, zero_add] <;> ring
  have him : ((((D.halfLength + D.width) * Real.cos θ : ℝ) : ℂ) +
        Complex.I * ((D.width * Real.sin θ : ℝ) : ℂ)).im = D.width * Real.sin θ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.mul_im, zero_mul, one_mul, mul_zero, sub_zero, add_zero, zero_add] <;> ring
  rw [hre, him, mul_div_cancel_left₀ _ hA.ne', mul_div_cancel_left₀ _ hw.ne']

theorem ellipseCoordinates_contDiff (D : DiscWithSegment) : ContDiff ℝ 1 (ellipseCoordinates D) := by
  have h1 : ContDiff ℝ 1 (fun z : ℂ => star D.axis * (z - D.midpoint)) :=
    contDiff_const.mul (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ 1 (fun z : ℂ =>
      (star D.axis * (z - D.midpoint)).re / (D.halfLength + D.width)) :=
    (Complex.reCLM.contDiff.comp h1).div_const _
  have h3 : ContDiff ℝ 1 (fun z : ℂ =>
      (star D.axis * (z - D.midpoint)).im / D.width) :=
    (Complex.imCLM.contDiff.comp h1).div_const _
  unfold ellipseCoordinates
  exact (Complex.ofRealCLM.contDiff.comp h2).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h3))

theorem ellipse_angle_lift (D : DiscWithSegment)
    {p : ℂ} (η : Path p p) (hη : PiecewiseC1 η)
    (himage : ∀ t : I, ∃ θ : ℝ, η t = ellipseParam D θ) :
    ∃ k : ℤ, ∃ θ : ℝ → ℝ,
      ContinuousOn θ (Icc (0 : ℝ) 1) ∧
      (∃ P : TimePartition, ∀ i : Fin P.n,
        ContDiffOn ℝ 1 θ
          (Icc (P.cut i.castSucc : ℝ) (P.cut i.succ : ℝ))) ∧
      (∀ t : I, η t = ellipseParam D (θ t)) ∧
      θ 1 - θ 0 = (k : ℝ) * (2 * Real.pi) := by
  have hcont : Continuous (ellipseCoordinates D) := (ellipseCoordinates_contDiff D).continuous
  let c : Path (ellipseCoordinates D (η 0)) (ellipseCoordinates D (η 1)) :=
    { toFun := fun t => ellipseCoordinates D (η t)
      continuous_toFun := hcont.comp η.continuous
      source' := rfl
      target' := rfl }
  have hct : ∀ (t : I) (θ0 : ℝ), η t = ellipseParam D θ0 →
      c t = Complex.exp ((θ0 : ℂ) * Complex.I) := by
    intro t θ0 hθ0
    show ellipseCoordinates D (η t) = _
    rw [hθ0, ellipseCoordinates_ellipseParam, cos_add_sin_eq_exp]
  have hne : ∀ t : I, c t ≠ 0 := by
    intro t
    obtain ⟨θ0, hθ0⟩ := himage t
    rw [hct t θ0 hθ0]
    exact Complex.exp_ne_zero _
  obtain ⟨q, L, hL⟩ := exists_log_lift c hne
  have hcpc : PiecewiseC1 c := by
    obtain ⟨P, hP⟩ := hη
    refine ⟨P, fun i => ?_⟩
    have h1 := (ellipseCoordinates_contDiff D).comp_contDiffOn (hP i)
    refine h1.congr (fun u hu => ?_)
    show (c.subpath _ _).extend u = ellipseCoordinates D ((η.subpath _ _).extend u)
    rw [subpath_extend_eq c _ _ u hu, subpath_extend_eq η _ _ u hu]
    rfl
  have hLpc := piecewiseC1_log_lift c L hcpc hL
  have hre : ∀ t : I, (L t).re = 0 := by
    intro t
    have h1 : ‖Complex.exp (L t)‖ = 1 := by
      rw [hL t]
      obtain ⟨θ0, hθ0⟩ := himage t
      rw [hct t θ0 hθ0]
      exact Complex.norm_exp_ofReal_mul_I θ0
    rw [Complex.norm_exp] at h1
    exact Real.exp_eq_one_iff _ |>.1 h1
  set θ : ℝ → ℝ := fun v => (L.extend v).im with hθdef
  have hθt : ∀ t : I, θ t = (L t).im := by
    intro t
    show (L.extend t).im = _
    rw [Path.extend_extends' L t]
  have hLt : ∀ t : I, L t = ((θ t : ℝ) : ℂ) * Complex.I := by
    intro t
    rw [hθt t]
    apply Complex.ext <;> simp [hre t]
  have hparam : ∀ t : I, η t = ellipseParam D (θ t) := by
    intro t
    obtain ⟨θ0, hθ0⟩ := himage t
    have heq : ((Real.cos (θ t) : ℝ) : ℂ) + Complex.I * ((Real.sin (θ t) : ℝ) : ℂ) =
        ((Real.cos θ0 : ℝ) : ℂ) + Complex.I * ((Real.sin θ0 : ℝ) : ℂ) := by
      rw [cos_add_sin_eq_exp, cos_add_sin_eq_exp, ← hLt t, hL t, hct t θ0 hθ0]
    have hc1 := congrArg Complex.re heq
    have hs1 := congrArg Complex.im heq
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add] at hc1 hs1
    rw [hθ0]
    unfold ellipseParam
    rw [hc1, hs1]
  have hk : Complex.exp (L 1) = Complex.exp (L 0) := by
    rw [hL 1, hL 0]
    show ellipseCoordinates D (η 1) = ellipseCoordinates D (η 0)
    rw [η.source, η.target]
  obtain ⟨k, hk'⟩ := Complex.exp_eq_exp_iff_exists_int.1 hk
  refine ⟨k, θ, ?_, ?_, hparam, ?_⟩
  · exact (Complex.continuous_im.comp L.continuous_extend).continuousOn
  · obtain ⟨P, hP⟩ := hLpc
    refine ⟨P, fun i => ?_⟩
    have hlt : (P.cut i.castSucc : ℝ) < (P.cut i.succ : ℝ) :=
      Subtype.coe_lt_coe.mpr (P.strict (Fin.castSucc_lt_succ (i := i)))
    set s : ℝ := (P.cut i.castSucc : ℝ) with hs
    set d : ℝ := (P.cut i.succ : ℝ) with hd
    have hdpos : 0 < d - s := by linarith
    have hmaps : MapsTo (fun v : ℝ => (v - s) / (d - s)) (Icc s d) (Icc (0 : ℝ) 1) := by
      intro v hv
      exact ⟨div_nonneg (by linarith [hv.1]) hdpos.le,
        (div_le_one hdpos).2 (by linarith [hv.2])⟩
    have haff : ContDiff ℝ 1 (fun v : ℝ => (v - s) / (d - s)) :=
      (contDiff_id.sub contDiff_const).div_const _
    have h1 := (hP i).comp haff.contDiffOn hmaps
    have h2 := Complex.imCLM.contDiff.comp_contDiffOn h1
    refine h2.congr (fun v hv => ?_)
    have hu := hmaps hv
    show (L.extend v).im = (((L.subpath _ _).extend ((v - s) / (d - s))).im)
    rw [subpath_extend_eq_affine L _ _ _ hu]
    have e : (d - s) * ((v - s) / (d - s)) + s = v := by
      field_simp <;> ring
    rw [e]
  · have e1 : L.extend 1 = L 1 := Path.extend_extends' L (1 : I)
    have e0 : L.extend 0 = L 0 := Path.extend_extends' L (0 : I)
    have him := congrArg Complex.im hk'
    simp only [Complex.add_im, Complex.mul_im, Complex.natCast_im, Complex.intCast_re,
      Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im] at him
    show (L.extend 1).im - (L.extend 0).im = _
    rw [e1, e0]
    linarith

theorem curveIntegral_of_angle_lift (D : DiscWithSegment) (f : ℂ → ℂ)
    (hf : ContinuousOn f (range (gapCycle D))) {p : ℂ} (η : Path p p) (hη : PiecewiseC1 η)
    (θ : ℝ → ℝ) (P : TimePartition)
    (hθ : ∀ i : Fin P.n, ContDiffOn ℝ 1 θ
      (Icc (P.cut i.castSucc : ℝ) (P.cut i.succ : ℝ)))
    (hparam : ∀ t : I, η t = ellipseParam D (θ t)) :
    curveIntegral (complexForm f) η =
      ∫ s in (θ 0)..(θ 1), f (ellipseParam D s) * ellipseDeriv D s := by
  set g : ℝ → ℂ := fun s => f (ellipseParam D s) * ellipseDeriv D s with hg
  have hgc : Continuous g := ellipse_g_continuous D f hf
  set G : ℝ → ℂ := fun x => ∫ s in (θ 0)..x, g s with hG
  have hGd : ∀ x, HasDerivAt G (g x) x := fun x =>
    (hgc.integral_hasStrictDerivAt (θ 0) x).hasDerivAt
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun x => (hGd x).continuousAt
  have hrange : range η ⊆ range (gapCycle D) := by
    rintro _ ⟨t, rfl⟩
    rw [hparam t]
    exact ellipse_mem_range D _
  have hHint := integrable_H η hη f (hf.mono hrange)
  have hcell : ∀ i : Fin P.n,
      ∫ u in (P.cut i.castSucc : ℝ)..(P.cut i.succ : ℝ), f (η.extend u) * deriv η.extend u =
        G (θ (P.cut i.succ)) - G (θ (P.cut i.castSucc)) := by
    intro i
    have hlt : (P.cut i.castSucc : ℝ) < (P.cut i.succ : ℝ) :=
      Subtype.coe_lt_coe.mpr (P.strict (Fin.castSucc_lt_succ (i := i)))
    set s : ℝ := (P.cut i.castSucc : ℝ) with hs
    set d : ℝ := (P.cut i.succ : ℝ) with hd
    have hs0 : 0 ≤ s := (P.cut i.castSucc).2.1
    have hd1 : d ≤ 1 := (P.cut i.succ).2.2
    have hθcont : ContinuousOn θ (Icc s d) := (hθ i).continuousOn
    have hext : ∀ y ∈ Icc s d, η.extend y = ellipseParam D (θ y) := by
      intro y hy
      have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨le_trans hs0 hy.1, le_trans hy.2 hd1⟩
      have e : η.extend y = η ⟨y, hy01⟩ := Path.extend_extends' η ⟨y, hy01⟩
      rw [e, hparam ⟨y, hy01⟩]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := fun u => G (θ u)) hlt.le ?_ ?_ ?_
    · exact hGc.comp_continuousOn hθcont
    · intro x hx
      have hxI : x ∈ Icc s d := Ioo_subset_Icc_self hx
      have hθd : HasDerivAt θ (deriv θ x) x :=
        (((hθ i).differentiableOn one_ne_zero).differentiableAt
          (Icc_mem_nhds hx.1 hx.2)).hasDerivAt
      have h1 : HasDerivAt (fun u => G (θ u)) (deriv θ x • g (θ x)) x :=
        (hGd (θ x)).scomp x hθd
      have h2 : HasDerivAt (fun u => ellipseParam D (θ u))
          (deriv θ x • ellipseDeriv D (θ x)) x :=
        (ellipseParam_hasDerivAt D (θ x)).scomp x hθd
      have hev : η.extend =ᶠ[𝓝 x] fun u => ellipseParam D (θ u) := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
        exact hext y (Ioo_subset_Icc_self hy)
      have h3 : deriv η.extend x = deriv θ x • ellipseDeriv D (θ x) :=
        (h2.congr_of_eventuallyEq hev).deriv
      refine h1.congr_deriv ?_
      rw [h3, hext x hxI]
      simp only [hg, Complex.real_smul]
      ring
    · refine hHint.mono_set ?_
      rw [Set.uIcc_of_le hlt.le, Set.uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hs0 hd1
  have hc : curveIntegral (complexForm f) η =
      ∫ u in (0 : ℝ)..1, f (η.extend u) * deriv η.extend u := by
    rw [curveIntegral_eq_intervalIntegral_deriv]
    simp only [complexForm, ContinuousLinearMap.mul_apply']
  rw [hc, ← sum_cells_integral _ hHint P]
  rw [Finset.sum_congr rfl (fun i _ => hcell i)]
  have ht : ∑ j : Fin P.n, (G (θ (P.cut j.castSucc)) - G (θ (P.cut j.succ))) =
      G (θ (P.cut 0)) - G (θ (P.cut (Fin.last P.n))) :=
    fin_telescope P.n (fun j => G (θ (P.cut j)))
  have hsum : ∑ i : Fin P.n, (G (θ (P.cut i.succ)) - G (θ (P.cut i.castSucc))) =
      G (θ (P.cut (Fin.last P.n))) - G (θ (P.cut 0)) := by
    rw [← neg_sub (G (θ (P.cut 0))), ← ht, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [neg_sub])
  rw [hsum, P.first, P.last]
  show (∫ s in (θ 0)..(θ 1), g s) - ∫ s in (θ 0)..(θ 0), g s = _
  rw [intervalIntegral.integral_same, sub_zero]

theorem ellipse_integral_of_angle_lift (D : DiscWithSegment)
    (f : ℂ → ℂ) (hf : ContinuousOn f (range (gapCycle D)))
    {p : ℂ} (η : Path p p) (hη : PiecewiseC1 η)
    (k : ℤ) (θ : ℝ → ℝ)
    (hθc : ContinuousOn θ (Icc (0 : ℝ) 1))
    (P : TimePartition)
    (hθ : ∀ i : Fin P.n, ContDiffOn ℝ 1 θ
      (Icc (P.cut i.castSucc : ℝ) (P.cut i.succ : ℝ)))
    (hparam : ∀ t : I, η t = ellipseParam D (θ t))
    (hends : θ 1 - θ 0 = (k : ℝ) * (2 * Real.pi)) :
    curveIntegral (complexForm f) η =
      (k : ℂ) * curveIntegral (complexForm f) (gapCycle D) := by
  rw [curveIntegral_of_angle_lift D f hf η hη θ P hθ hparam]
  have hgam := curveIntegral_of_angle_lift D f hf (gapCycle D) (gapCycle_piecewise D)
    (fun t : ℝ => 2 * Real.pi * t) singlePartition
    (fun i => (contDiff_const.mul contDiff_id : ContDiff ℝ 1 (fun t : ℝ => 2 * Real.pi * t)).contDiffOn)
    (fun t => rfl)
  rw [hgam]
  simp only [mul_zero, mul_one]
  have hgc := ellipse_g_continuous D f hf
  have hper : Function.Periodic (fun s : ℝ => f (ellipseParam D s) * ellipseDeriv D s)
      (2 * Real.pi) := by
    intro x
    simp only []
    rw [ellipseParam_periodic D x, ellipseDeriv_periodic D x]
  have h := integral_integer_period _ hgc (2 * Real.pi) (by positivity) hper (θ 0) k
  have e : θ 1 = θ 0 + (k : ℝ) * (2 * Real.pi) := by linarith
  rw [e]
  exact h

theorem ellipse_loop_period (D : DiscWithSegment)
    (f : ℂ → ℂ) (hf : ContinuousOn f (range (gapCycle D)))
    {p : ℂ} (η : Path p p) (hη : PiecewiseC1 η)
    (himage : ∀ t : I, ∃ θ : ℝ, η t = ellipseParam D θ) :
    ∃ k : ℤ,
      curveIntegral (complexForm f) η =
        (k : ℂ) * curveIntegral (complexForm f) (gapCycle D) ∧
      curveIntegral (complexForm (fun z => (z - D.midpoint)⁻¹)) η =
        (k : ℂ) * (2 * Real.pi * Complex.I) := by
  obtain ⟨k, θ, hθc, ⟨P, hP⟩, hparam, hends⟩ := ellipse_angle_lift D η hη himage
  refine ⟨k, ellipse_integral_of_angle_lift D f hf η hη k θ hθc P hP hparam hends, ?_⟩
  have hne : ContinuousOn (fun z : ℂ => (z - D.midpoint)⁻¹) (range (gapCycle D)) := by
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    rintro _ ⟨t, rfl⟩
    show ellipseParam D (2 * Real.pi * (t : ℝ)) - D.midpoint ≠ 0
    rw [← interpH_zero D t]
    exact sub_ne_zero.2 (interpH_ne D (0, t))
  rw [ellipse_integral_of_angle_lift D _ hne η hη k θ hθc P hP hparam hends,
    (reciprocal_gapCycle D).2]

-- 79.04/79.13
theorem isOpen_domain (D : DiscWithSegment) : IsOpen D.domain := by
  unfold DiscWithSegment.domain
  have hcl : IsClosed (segment ℝ D.a D.b) := by
    rw [segment_eq_image]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  exact isOpen_ball.sdiff hcl

theorem mid_notMem_domain (D : DiscWithSegment) : D.midpoint ∉ D.domain := fun h => h.2 (mid_mem_seg D)

theorem recip_differentiableOn (D : DiscWithSegment) :
    DifferentiableOn ℂ (fun z : ℂ => (z - D.midpoint)⁻¹) D.domain := by
  intro z hz
  have hne : z - D.midpoint ≠ 0 := sub_ne_zero.2 (fun h => mid_notMem_domain D (h ▸ hz))
  exact ((differentiableAt_id.sub_const D.midpoint).inv hne).differentiableWithinAt

/-- Leaf 79.04: any admissible loop in the punctured disc reduces to a loop on the ellipse. -/
theorem reduce_loop_to_ellipse (D : DiscWithSegment)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f D.domain)
    {p : ℂ} (γ : Path p p) (hγ : Admissible D.domain γ) :
    ∃ q : ℂ, ∃ η : Path q q, Admissible D.domain η ∧
      (∀ t : I, η t = ellipseProjection D (γ t)) ∧
      curveIntegral (complexForm f) γ =
        curveIntegral (complexForm f) η ∧
      curveIntegral (complexForm (fun z => (z - D.midpoint)⁻¹)) γ =
        curveIntegral (complexForm (fun z => (z - D.midpoint)⁻¹)) η := by
  obtain ⟨hpc, hrange⟩ := hγ
  obtain ⟨hC1, -, hell, hdef⟩ := ellipseProjection_geometry D
  have hγmem : ∀ t : I, γ t ∈ D.domain := fun t => hrange ⟨t, rfl⟩
  have hEPc : ContinuousOn (ellipseProjection D) D.domain := hC1.continuousOn
  have hEPγ : Continuous fun t : I => ellipseProjection D (γ t) :=
    hEPc.comp_continuous γ.continuous hγmem
  let η : Path (ellipseProjection D p) (ellipseProjection D p) :=
    { toFun := fun t => ellipseProjection D (γ t)
      continuous_toFun := hEPγ
      source' := by simp
      target' := by simp }
  have hηe : ∀ v : ℝ, η.extend v = ellipseProjection D (γ.extend v) := fun v => rfl
  have hηpc : PiecewiseC1 η := by
    obtain ⟨P, hP⟩ := hpc
    refine ⟨P, fun i => ?_⟩
    have hmaps : MapsTo (γ.subpath (P.cut i.castSucc) (P.cut i.succ)).extend (Icc (0 : ℝ) 1)
        D.domain := by
      intro u hu
      rw [subpath_extend_eq γ _ _ u hu]
      have e : γ.extend ((P.cut i.castSucc : ℝ) + u * ((P.cut i.succ : ℝ) - (P.cut i.castSucc : ℝ))) =
          γ ⟨_, affMem _ _ hu⟩ := Path.extend_extends' _ ⟨_, affMem _ _ hu⟩
      rw [e]
      exact hγmem _
    have h1 := hC1.comp (hP i) hmaps
    refine h1.congr (fun u hu => ?_)
    show (η.subpath _ _).extend u = ellipseProjection D ((γ.subpath _ _).extend u)
    rw [subpath_extend_eq η _ _ u hu, subpath_extend_eq γ _ _ u hu, hηe]
  have hηrange : range η ⊆ D.domain := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨θ, hθ⟩ := hell _ (hγmem t)
    show ellipseProjection D (γ t) ∈ D.domain
    rw [hθ]
    exact ellipseParam_mem_domain D θ
  let H : C(I × I, ℂ) :=
    ⟨fun q => radialDeformation D (q.1 : ℝ) (γ q.2), by
      have h2 : Continuous fun q : I × I => ellipseProjection D (γ q.2) :=
        hEPγ.comp continuous_snd
      unfold radialDeformation
      have h3 : Continuous fun q : I × I => (1 - (q.1 : ℝ)) • γ q.2 :=
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst))).smul
          (γ.continuous.comp continuous_snd)
      have h4 : Continuous fun q : I × I => (q.1 : ℝ) • ellipseProjection D (γ q.2) :=
        (continuous_subtype_val.comp continuous_fst).smul h2
      exact h3.add h4⟩
  have hHU : range H ⊆ D.domain := by
    rintro _ ⟨q, rfl⟩
    exact hdef (q.1 : ℝ) q.1.2 (γ q.2) (hγmem q.2)
  have hzero : ∀ t : I, H (0, t) = γ t := by
    intro t
    show radialDeformation D ((0 : I) : ℝ) (γ t) = γ t
    simp [radialDeformation]
  have hone : ∀ t : I, H (1, t) = η t := by
    intro t
    show radialDeformation D ((1 : I) : ℝ) (γ t) = ellipseProjection D (γ t)
    simp [radialDeformation]
  have hclosed : ∀ s : I, H (s, 0) = H (s, 1) := by
    intro s
    show radialDeformation D (s : ℝ) (γ 0) = radialDeformation D (s : ℝ) (γ 1)
    rw [γ.source, γ.target]
  refine ⟨ellipseProjection D p, η, ⟨hηpc, hηrange⟩, fun t => rfl, ?_, ?_⟩
  · exact curveIntegral_eq_of_free_homotopy γ η hpc hηpc D.domain (isOpen_domain D) f hf H hHU
      hzero hone hclosed
  · exact curveIntegral_eq_of_free_homotopy γ η hpc hηpc D.domain (isOpen_domain D) _
      (recip_differentiableOn D) H hHU hzero hone hclosed

/-- Leaf 79.13: assemble the packet. -/
theorem gap_cycle_period (D : DiscWithSegment) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f D.domain)
    {p : ℂ} (γ : Path p p) (hγ : Admissible D.domain γ) :
    CurveIntegrable (complexForm f) γ ∧
    CurveIntegrable (complexForm f) (gapCycle D) ∧
    CurveIntegrable (complexForm (fun z => (z - D.midpoint)⁻¹)) γ ∧
    indexIntegral γ D.midpoint =
      (windingNumber γ D.midpoint : ℂ) ∧
    curveIntegral (complexForm f) γ =
      (windingNumber γ D.midpoint : ℂ) *
        curveIntegral (complexForm f) (gapCycle D) := by
  have hmid : D.midpoint ∉ range γ := fun h => mid_notMem_domain D (hγ.2 h)
  obtain ⟨hrec, hidx⟩ := indexIntegral_int γ hγ.1 hmid
  refine ⟨piecewise_curveIntegrable γ hγ.1 f (hf.continuousOn.mono hγ.2),
    piecewise_curveIntegrable (gapCycle D) (gapCycle_piecewise D) f
      (hf.continuousOn.mono (gapCycle_range D)),
    hrec, hidx, ?_⟩
  obtain ⟨q, η, hη, hηeq, hfeq, hreq⟩ := reduce_loop_to_ellipse D f hf γ hγ
  have himage : ∀ t : I, ∃ θ : ℝ, η t = ellipseParam D θ := by
    intro t
    rw [hηeq t]
    exact (ellipseProjection_geometry D).2.2.1 _ (hγ.2 ⟨t, rfl⟩)
  obtain ⟨k, hk1, hk2⟩ := ellipse_loop_period D f (hf.continuousOn.mono (gapCycle_range D))
    η hη.1 himage
  have hidx2 : indexIntegral γ D.midpoint = (k : ℂ) := by
    unfold indexIntegral
    rw [hreq, hk2]
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp
  have hw : windingNumber γ D.midpoint = k := by
    have : ((windingNumber γ D.midpoint : ℤ) : ℂ) = (k : ℂ) := hidx ▸ hidx2
    exact_mod_cast this
  rw [hfeq, hk1, hw]

-- 79.17
/-- hypothesis-free form of `curveIntegral_subpath_eq` (its proof never used the regularity hypotheses). -/
theorem curveIntegral_subpath_eq' {a b : ℂ} (γ : Path a b) (f : ℂ → ℂ) (s t : I) :
    curveIntegral (complexForm f) (γ.subpath s t) =
      ∫ u : ℝ in (s : ℝ)..(t : ℝ), f (γ.extend u) * deriv γ.extend u := by
  have hx1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  rw [curveIntegral_eq_intervalIntegral_deriv]
  simp only [complexForm, ContinuousLinearMap.mul_apply']
  by_cases hst : s = t
  · subst hst
    rw [intervalIntegral.integral_same]
    have key : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) 1 →
        f ((γ.subpath s s).extend x) * deriv (γ.subpath s s).extend x = 0 := by
      filter_upwards [hx1] with x hx1' hx
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1'⟩
      rw [deriv_subpath_extend_Ioo γ s s hxI]
      simp
    rw [intervalIntegral.integral_congr_ae key]
    simp
  · have key : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) 1 →
        f ((γ.subpath s t).extend x) * deriv (γ.subpath s t).extend x =
          (((t : ℝ) - (s : ℝ) : ℝ) : ℂ) *
            (f (γ.extend (((t : ℝ) - (s : ℝ)) * x + (s : ℝ))) *
              deriv γ.extend (((t : ℝ) - (s : ℝ)) * x + (s : ℝ))) := by
      filter_upwards [hx1] with x hx1' hx
      rw [Set.uIoc_of_le zero_le_one] at hx
      have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_ne hx.2 hx1'⟩
      rw [subpath_extend_eq_affine γ s t x (Ioo_subset_Icc_self hxI),
        deriv_subpath_extend_Ioo γ s t hxI]
      simp only [Complex.real_smul]
      ring
    rw [intervalIntegral.integral_congr_ae key]
    exact integral_affine_complex (fun v => f (γ.extend v) * deriv γ.extend v) (s : ℝ) (t : ℝ)
      (fun h => hst (Subtype.ext h))

/-- Scaling of the integrand under truncation `γ ↦ γ.subpath 0 T`. -/
theorem scale_integral {a b : ℂ} (γ : Path a b) (f : ℂ → ℂ) (T : I) (hT : 0 < (T : ℝ))
    (s' t' : ℝ) (hs : s' ∈ Icc (0 : ℝ) 1) (ht : t' ∈ Icc (0 : ℝ) 1) :
    ∫ v : ℝ in s'..t', f ((γ.subpath 0 T).extend v) * deriv (γ.subpath 0 T).extend v =
      ∫ u : ℝ in ((T : ℝ) * s')..((T : ℝ) * t'), f (γ.extend u) * deriv γ.extend u := by
  have hx1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  have key : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι s' t' →
      f ((γ.subpath 0 T).extend x) * deriv (γ.subpath 0 T).extend x =
        (T : ℂ) * (f (γ.extend ((T : ℝ) * x)) * deriv γ.extend ((T : ℝ) * x)) := by
    filter_upwards [hx1] with x hx1' hx
    rw [Set.mem_uIoc] at hx
    have hx01 : 0 < x ∧ x ≤ 1 := by
      rcases hx with hx | hx
      · exact ⟨lt_of_le_of_lt hs.1 hx.1, le_trans hx.2 ht.2⟩
      · exact ⟨lt_of_le_of_lt ht.1 hx.1, le_trans hx.2 hs.2⟩
    have hxI : x ∈ Ioo (0 : ℝ) 1 := ⟨hx01.1, lt_of_le_of_ne hx01.2 hx1'⟩
    rw [subpath_extend_eq_affine γ 0 T x (Ioo_subset_Icc_self hxI),
      deriv_subpath_extend_Ioo γ 0 T hxI]
    simp only [Complex.real_smul, Set.Icc.coe_zero, sub_zero, add_zero]
    push_cast
    ring
  rw [intervalIntegral.integral_congr_ae key, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left
      (fun u : ℝ => f (γ.extend u) * deriv γ.extend u) hT.ne']
  rw [Complex.real_smul]
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  field_simp

theorem curveIntegral_trunc_step (D : DiscWithSegment)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f D.domain) (a : ℂ)
    {p : ℂ} (γ : Path p a)
    (hγU : ∀ t : I, t < 1 → γ t ∈ D.domain)
    (hγ : ∀ t : I, t < 1 → PiecewiseC1 (γ.subpath 0 t))
    (δ : ℝ) (P : ℂ → ℂ)
    (hPd : ∀ z ∈ D.domain ∩ ball a δ, HasDerivAt P (f z) z)
    (t0 t : I) (ht0 : 0 < (t0 : ℝ)) (ht0t : t0 < t) (htl : t < 1)
    (hball : ∀ τ : ℝ, (t0 : ℝ) ≤ τ → τ < 1 → γ.extend τ ∈ ball a δ) :
    curveIntegral (complexForm f) (γ.subpath 0 t) =
      curveIntegral (complexForm f) (γ.subpath 0 t0) + (P (γ t) - P (γ t0)) := by
  have hT : 0 < (t : ℝ) := lt_trans ht0 ht0t
  have ht0t' : (t0 : ℝ) < (t : ℝ) := ht0t
  have htl' : (t : ℝ) < 1 := htl
  have hdom : ∀ τ : ℝ, 0 ≤ τ → τ < 1 → γ.extend τ ∈ D.domain := by
    intro τ h0 h1
    have h : γ.extend τ = γ ⟨τ, h0, h1.le⟩ := Path.extend_extends' γ ⟨τ, h0, h1.le⟩
    rw [h]
    exact hγU _ h1
  set γ' : Path (γ 0) (γ t) := γ.subpath 0 t with hγ'def
  have hγ' : PiecewiseC1 γ' := hγ t htl
  have hextγ' : ∀ x : ℝ, x ∈ Icc (0 : ℝ) 1 → γ'.extend x = γ.extend ((t : ℝ) * x) := by
    intro x hx
    rw [hγ'def, subpath_extend_eq_affine γ 0 t x hx]
    simp
  have hγ'pt : ∀ x : I, γ' x = γ.extend ((t : ℝ) * x) := by
    intro x
    have h := Path.extend_extends' γ' x
    rw [← h]
    exact hextγ' x x.2
  have hrangeγ' : range γ' ⊆ D.domain := by
    rintro _ ⟨x, rfl⟩
    rw [hγ'pt x]
    exact hdom _ (mul_nonneg hT.le x.2.1)
      (lt_of_le_of_lt (mul_le_of_le_one_right hT.le x.2.2) htl')
  have hcont : ContinuousOn f (range γ') := hf.continuousOn.mono hrangeγ'
  have hs1a : 0 ≤ (t0 : ℝ) / t := div_nonneg ht0.le hT.le
  have hs1b : (t0 : ℝ) / t ≤ 1 := (div_le_one hT).2 ht0t'.le
  have hs1_le : (⟨(t0 : ℝ) / t, hs1a, hs1b⟩ : I) ≤ 1 := hs1b
  let s1 : I := ⟨(t0 : ℝ) / t, hs1a, hs1b⟩
  have hts1 : (t : ℝ) * (s1 : ℝ) = t0 := by
    show (t : ℝ) * ((t0 : ℝ) / t) = t0
    field_simp
  have hc : curveIntegral (complexForm f) γ' =
      ∫ u in (0 : ℝ)..1, f (γ'.extend u) * deriv γ'.extend u := by
    rw [curveIntegral_eq_intervalIntegral_deriv]
    simp only [complexForm, ContinuousLinearMap.mul_apply']
  have hint := integrable_H γ' hγ' f hcont
  have hint1 : IntervalIntegrable (fun u : ℝ => f (γ'.extend u) * deriv γ'.extend u)
      volume 0 (s1 : ℝ) :=
    hint.mono_set (by
      rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hs1a]
      exact Icc_subset_Icc le_rfl hs1b)
  have hint2 : IntervalIntegrable (fun u : ℝ => f (γ'.extend u) * deriv γ'.extend u)
      volume (s1 : ℝ) 1 :=
    hint.mono_set (by
      rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hs1b]
      exact Icc_subset_Icc hs1a le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
  have h3 : curveIntegral (complexForm f) (γ'.subpath s1 1) =
      ∫ u : ℝ in (s1 : ℝ)..1, f (γ'.extend u) * deriv γ'.extend u :=
    curveIntegral_subpath_eq γ' hγ' f hcont s1 1
  have hUo : IsOpen (D.domain ∩ ball a δ) := (isOpen_domain D).inter isOpen_ball
  have hrU : range (γ'.subpath s1 1) ⊆ D.domain ∩ ball a δ := by
    intro y hy
    obtain ⟨x, hx1, hx2, rfl⟩ := subpath_range_mem γ' s1 1 hs1_le hy
    rw [hγ'pt x]
    have hxs : (s1 : ℝ) ≤ x := hx1
    have hτ0 : (t0 : ℝ) ≤ (t : ℝ) * x := by
      calc (t0 : ℝ) = (t : ℝ) * s1 := hts1.symm
        _ ≤ (t : ℝ) * x := mul_le_mul_of_nonneg_left hxs hT.le
    have hτ1 : (t : ℝ) * x < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right hT.le x.2.2) htl'
    exact ⟨hdom _ (le_trans ht0.le hτ0) hτ1, hball _ hτ0 hτ1⟩
  have h4 : curveIntegral (complexForm f) (γ'.subpath s1 1) = P (γ' 1) - P (γ' s1) :=
    primitive_curveIntegral (γ'.subpath s1 1) (piecewiseC1_subpath γ' hγ' s1 1)
      (D.domain ∩ ball a δ) f P hUo hrU (hf.continuousOn.mono inter_subset_left) hPd
  have h1v : γ' 1 = γ t := γ'.target
  have hs1v : γ' s1 = γ t0 := by
    rw [hγ'pt s1, hts1]
    exact Path.extend_extends' γ t0
  have h5 : ∫ v : ℝ in (0 : ℝ)..(s1 : ℝ), f (γ'.extend v) * deriv γ'.extend v =
      ∫ u : ℝ in ((t : ℝ) * 0)..((t : ℝ) * s1), f (γ.extend u) * deriv γ.extend u :=
    scale_integral γ f t hT 0 s1 ⟨le_rfl, zero_le_one⟩ ⟨hs1a, hs1b⟩
  rw [mul_zero, hts1] at h5
  have h6 := curveIntegral_subpath_eq' γ f 0 t0
  simp only [Set.Icc.coe_zero] at h6
  have h7 : curveIntegral (complexForm f) (γ.subpath 0 t) =
      curveIntegral (complexForm f) γ' := rfl
  rw [h7, hc, ← hsplit, h5, ← h6, ← h3, h4, h1v, hs1v]

theorem endpoint_path_integral_tendsto (D : DiscWithSegment)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f D.domain)
    (a : ℂ) (ha : a = D.a ∨ a = D.b)
    (hbound : HasEndpointBound f D.domain a)
    {p : ℂ} (γ : Path p a)
    (hγU : ∀ t : I, t < 1 → γ t ∈ D.domain)
    (hγ : ∀ t : I, t < 1 → PiecewiseC1 (γ.subpath 0 t)) :
    (∀ t : I, t < 1 →
      CurveIntegrable (complexForm f) (γ.subpath 0 t)) ∧
    ∃ L : ℂ, Tendsto
      (fun t : I => curveIntegral (complexForm f) (γ.subpath 0 t))
      (𝓝[<] (1 : I)) (𝓝 L) := by
  have hdomc : ∀ t : I, t < 1 → ContinuousOn f (range (γ.subpath 0 t)) := by
    intro t ht
    refine hf.continuousOn.mono ?_
    intro y hy
    obtain ⟨x, -, hxt, rfl⟩ := subpath_range_mem γ 0 t (show (0 : I) ≤ t from t.2.1) hy
    exact hγU x (lt_of_le_of_lt hxt ht)
  refine ⟨fun t ht => piecewise_curveIntegrable _ (hγ t ht) f (hdomc t ht), ?_⟩
  obtain ⟨δ, hδ, P, hPc, hPd⟩ := endpoint_continuous_primitive D f hf a ha hbound
  have hev : ∀ᶠ τ in 𝓝 (1 : ℝ), γ.extend τ ∈ ball a δ := by
    have hc : ContinuousAt γ.extend 1 := γ.continuous_extend.continuousAt
    have h1 : γ.extend 1 = a := by
      have := Path.extend_extends' γ (1 : I)
      rw [γ.target] at this
      exact this
    exact hc.eventually (by rw [h1]; exact ball_mem_nhds a hδ)
  obtain ⟨η, hη, hηb⟩ := Metric.eventually_nhds_iff.1 hev
  set r : ℝ := min (1 / 2) (η / 2) with hrdef
  have hr : 0 < r := lt_min (by norm_num) (by linarith)
  have hr1 : r ≤ 1 / 2 := min_le_left _ _
  have hrη : r < η := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let t0 : I := ⟨1 - r, by linarith, by linarith⟩
  have ht0pos : 0 < (t0 : ℝ) := by show 0 < 1 - r; linarith
  have ht01 : t0 < 1 := by
    show (t0 : ℝ) < 1
    show 1 - r < 1
    linarith
  have hball : ∀ τ : ℝ, (t0 : ℝ) ≤ τ → τ < 1 → γ.extend τ ∈ ball a δ := by
    intro τ h1 h2
    apply hηb
    rw [Real.dist_eq, abs_lt]
    have : (t0 : ℝ) = 1 - r := rfl
    constructor <;> linarith
  have hγt : Tendsto (fun t : I => γ t) (𝓝[<] (1 : I))
      (𝓝[(D.domain ∩ ball a δ) ∪ {a}] a) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h := γ.continuous.tendsto (1 : I)
      rw [γ.target] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT ht01] with t ht
      left
      refine ⟨hγU t ht.2, ?_⟩
      have h := hball t ht.1.le ht.2
      rwa [Path.extend_extends' γ t] at h
  have hLim : Tendsto (fun t : I => P (γ t)) (𝓝[<] (1 : I)) (𝓝 (P a)) :=
    (hPc a (Or.inr rfl)).tendsto.comp hγt
  refine ⟨curveIntegral (complexForm f) (γ.subpath 0 t0) +
    (P a - P (γ t0)), ?_⟩
  have hlim2 := (hLim.sub_const (P (γ t0))).const_add (curveIntegral (complexForm f) (γ.subpath 0 t0))
  refine Tendsto.congr' ?_ hlim2
  filter_upwards [Ioo_mem_nhdsLT ht01] with t ht
  exact (curveIntegral_trunc_step D f hf a γ hγU hγ δ P hPd t0 t ht0pos ht.1 ht.2 hball).symm

-- BEGIN PASTED H3: 79.05 circle adapter (proof development/LIB079_79_05_V2_GK38)
-- END PASTED H3: 79.05

end
end NlsGge.GK38.Lib.SlitContours
