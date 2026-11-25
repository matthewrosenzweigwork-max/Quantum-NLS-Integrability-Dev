import Mathlib
import NlsGge.Atomic.LIB.LIB024
import NlsGge.Atomic.LIB.LIB025
import NlsGge.Atomic.G6.G6020
import NlsGge.Atomic.G1.G1081Host
import NlsGge.Atomic.G1.G1081Sup1
import NlsGge.Atomic.G1.G1081Sup2
import NlsGge.Atomic.G1.G1080

/- G1-081 SUP3 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/G1081Sup3.lean.
   S3: global existence and uniqueness for x' = singleGapField n x. Generic part (any locally Lipschitz V on a Banach space with a
   compact trapping set for forward solutions): uniqueness via LocallyLipschitzOn.exists_lipschitzOnWith_of_compact + ODE_solution_unique_of_mem_Icc_right;
   forward existence via LIB-024 (local), gluing, S2 + G1_080 compactness, LIB-025 continuation; backward time by applying it to -V. -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
namespace NlsGge.Atomic.G1081Sup3
noncomputable section

section Generic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hasDerivWithinAt_Ici_of_Ico {f : ℝ → E} {f' : E} {T r : ℝ}
    (h : HasDerivWithinAt f f' (Ico 0 T) r) (hr : r ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt f f' (Ici r) r :=
  h.mono_of_mem_nhdsWithin
    (mem_of_superset (Ico_mem_nhdsGE hr.2) (fun s hs => ⟨hr.1.trans hs.1, hs.2⟩))

/-- Uniqueness on `[0,T)` for a locally Lipschitz field. -/
theorem solution_unique_Ico {V : E → E} (hV : LocallyLipschitzOn univ V) {T : ℝ}
    {x y : ℝ → E} (h0 : x 0 = y 0)
    (hx : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt x (V (x t)) (Ico 0 T) t)
    (hy : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt y (V (y t)) (Ico 0 T) t) :
    EqOn x y (Ico 0 T) := by
  intro t ht
  set b : ℝ := (t + T) / 2 with hbdef
  have hb1 : t < b := by rw [hbdef]; linarith [ht.2]
  have hb2 : b < T := by rw [hbdef]; linarith [ht.2]
  have hsub : Icc (0 : ℝ) b ⊆ Ico 0 T := fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 hb2⟩
  have hxc0 : ContinuousOn x (Ico 0 T) := fun r hr => (hx r hr).continuousWithinAt
  have hyc0 : ContinuousOn y (Ico 0 T) := fun r hr => (hy r hr).continuousWithinAt
  have hxc : ContinuousOn x (Icc 0 b) := hxc0.mono hsub
  have hyc : ContinuousOn y (Icc 0 b) := hyc0.mono hsub
  have hK : IsCompact (x '' Icc 0 b ∪ y '' Icc 0 b) :=
    (isCompact_Icc.image_of_continuousOn hxc).union (isCompact_Icc.image_of_continuousOn hyc)
  obtain ⟨L, hL⟩ := (hV.mono (subset_univ _)).exists_lipschitzOnWith_of_compact hK
  have := ODE_solution_unique_of_mem_Icc_right (v := fun _ => V)
    (s := fun _ => x '' Icc 0 b ∪ y '' Icc 0 b) (K := L) (a := 0) (b := b)
    (fun _ _ => hL) hxc
    (fun r hr => hasDerivWithinAt_Ici_of_Ico (hx r (hsub ⟨hr.1, hr.2.le⟩))
      ⟨hr.1, lt_trans hr.2 hb2⟩)
    (fun r hr => Or.inl ⟨r, ⟨hr.1, hr.2.le⟩, rfl⟩) hyc
    (fun r hr => hasDerivWithinAt_Ici_of_Ico (hy r (hsub ⟨hr.1, hr.2.le⟩))
      ⟨hr.1, lt_trans hr.2 hb2⟩)
    (fun r hr => Or.inr ⟨r, ⟨hr.1, hr.2.le⟩, rfl⟩) h0
  exact this ⟨ht.1, hb1.le⟩

theorem solution_agree_Ico {V : E → E} (hV : LocallyLipschitzOn univ V) {a b : ℝ}
    {x y : ℝ → E} (h0 : x 0 = y 0)
    (hx : ∀ t ∈ Ico (0 : ℝ) a, HasDerivWithinAt x (V (x t)) (Ico 0 a) t)
    (hy : ∀ t ∈ Ico (0 : ℝ) b, HasDerivWithinAt y (V (y t)) (Ico 0 b) t) :
    EqOn x y (Ico 0 (min a b)) := by
  refine solution_unique_Ico hV h0 (fun t ht => ?_) (fun t ht => ?_)
  · exact (hx t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩).mono
      (Ico_subset_Ico_right (min_le_left _ _))
  · exact (hy t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩).mono
      (Ico_subset_Ico_right (min_le_right _ _))

/-- Gluing local solutions on `[0,T)` into a solution on a subset `I` of `[0,∞)`. -/
theorem glue_solutions {V : E → E} (hV : LocallyLipschitzOn univ V) {u : E} {I : Set ℝ}
    (hI : I ⊆ Ici 0) (h0 : (0 : ℝ) ∈ I)
    (hP : ∀ t ∈ I, ∃ T : ℝ, t < T ∧ ∃ x : ℝ → E, x 0 = u ∧
      ∀ s ∈ Ico (0 : ℝ) T, HasDerivWithinAt x (V (x s)) (Ico 0 T) s) :
    ∃ x : ℝ → E, x 0 = u ∧ ∀ t ∈ I, HasDerivWithinAt x (V (x t)) I t := by
  choose Tf hTt hPf using hP
  choose X hX0 hXd using hPf
  classical
  let x : ℝ → E := fun t => if ht : t ∈ I then X t ht t else u
  have hxX : ∀ t (ht : t ∈ I) r (hr : r ∈ I), r < Tf t ht → x r = X t ht r := by
    intro t ht r hr hrt
    have hxr : x r = X r hr r := by simp only [x, dif_pos hr]
    rw [hxr]
    have := solution_agree_Ico hV (a := Tf r hr) (b := Tf t ht) (x := X r hr) (y := X t ht)
      ((hX0 r hr).trans (hX0 t ht).symm) (hXd r hr) (hXd t ht)
      ⟨hI hr, lt_min (hTt r hr) hrt⟩
    exact this
  refine ⟨x, ?_, fun t ht => ?_⟩
  · have : x 0 = X 0 h0 0 := by simp only [x, dif_pos h0]
    rw [this, hX0 0 h0]
  · have hnh : Ico 0 (Tf t ht) ∈ 𝓝[I] t :=
      mem_nhdsWithin.2 ⟨Iio (Tf t ht), isOpen_Iio, hTt t ht,
        fun r hr => ⟨hI hr.2, hr.1⟩⟩
    have hd := (hXd t ht t ⟨hI ht, hTt t ht⟩).mono_of_mem_nhdsWithin hnh
    have heq : x =ᶠ[𝓝[I] t] X t ht := by
      have hnh2 : Iio (Tf t ht) ∩ I ∈ 𝓝[I] t :=
        mem_nhdsWithin.2 ⟨Iio (Tf t ht), isOpen_Iio, hTt t ht, fun r hr => hr⟩
      filter_upwards [hnh2] with r hr using hxX t ht r hr.2 hr.1
    have hxt : x t = X t ht t := hxX t ht t ht (hTt t ht)
    rw [hxt]
    exact hd.congr_of_eventuallyEq heq hxt

/-- Forward existence on every `[0,T)` given a compact trapping set. -/
theorem forward_exists {V : E → E} (hV : LocallyLipschitzOn univ V)
    (hinv : ∀ u : E, ∃ K : Set E, IsCompact K ∧ ∀ T : ℝ, 0 < T → ∀ x : ℝ → E, x 0 = u →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt x (V (x t)) (Ico 0 T) t) →
      ∀ t ∈ Ico (0 : ℝ) T, x t ∈ K) (u : E) :
    ∀ T : ℝ, 0 < T → ∃ x : ℝ → E, x 0 = u ∧
      ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt x (V (x t)) (Ico 0 T) t := by
  let P : ℝ → Prop := fun T => ∃ x : ℝ → E, x 0 = u ∧
    ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt x (V (x t)) (Ico 0 T) t
  suffices hgoal : ∀ T, 0 < T → P T from hgoal
  by_contra hcon
  obtain ⟨T0, hT0, hno⟩ : ∃ T0, 0 < T0 ∧ ¬ P T0 := by
    by_contra h
    exact hcon fun T hT => by_contra fun hn => h ⟨T, hT, hn⟩
  have hmono : ∀ T T', 0 < T' → T' ≤ T → P T → P T' := by
    rintro T T' hT' hle ⟨x, hx0, hx⟩
    exact ⟨x, hx0, fun t ht => (hx t ⟨ht.1, lt_of_lt_of_le ht.2 hle⟩).mono
      (Ico_subset_Ico_right hle)⟩
  -- local existence
  have hloc : ∃ ε : ℝ, 0 < ε ∧ P ε := by
    obtain ⟨r, hr, K, -, -, ε, hε, x, hx0, hxd, -⟩ :=
      NlsGge.Atomic.LIB024.localFlow_exists_unique (U := univ) isOpen_univ hV (mem_univ u)
    refine ⟨ε, hε, x, hx0, fun t ht => ?_⟩
    exact (hxd t ⟨by linarith [ht.1], ht.2⟩).1.hasDerivWithinAt
  let S : Set ℝ := {T | 0 < T ∧ P T}
  obtain ⟨ε0, hε0, hPε0⟩ := hloc
  have hSne : S.Nonempty := ⟨ε0, hε0, hPε0⟩
  have hSbdd : BddAbove S := ⟨T0, fun T hT => by
    by_contra hlt
    exact hno (hmono T T0 hT0 (not_le.1 hlt).le hT.2)⟩
  set Ts := sSup S with hTs
  have hTspos : 0 < Ts := lt_of_lt_of_le hε0 (le_csSup hSbdd ⟨hε0, hPε0⟩)
  have hPlt : ∀ T, 0 < T → T < Ts → P T := by
    intro T hT hTl
    obtain ⟨s, hs, hTs'⟩ := exists_lt_of_lt_csSup hSne hTl
    exact hmono s T hT hTs'.le hs.2
  obtain ⟨x, hx0, hxd⟩ := glue_solutions (u := u) (I := Ico 0 Ts) hV
    (fun t ht => ht.1) ⟨le_rfl, hTspos⟩
    (fun t ht => ⟨(t + Ts) / 2, by linarith [ht.2], hPlt _ (by linarith [ht.1, ht.2])
      (by linarith [ht.2])⟩)
  obtain ⟨K, hKc, hKi⟩ := hinv u
  obtain ⟨ε, hε, y, hyd, hyx, -⟩ := NlsGge.Atomic.LIB.extend_solution_of_compact_range
    isOpen_univ hV hKc (subset_univ K) hTspos x hxd (hKi Ts hTspos x hx0 hxd)
  have hy0 : y 0 = u := by rw [hyx ⟨le_rfl, hTspos⟩]; exact hx0
  have hPnew : P (Ts + ε) := ⟨y, hy0, hyd⟩
  have := le_csSup hSbdd (show Ts + ε ∈ S from ⟨by linarith, hPnew⟩)
  linarith

theorem forward_global {V : E → E} (hV : LocallyLipschitzOn univ V)
    (hinv : ∀ u : E, ∃ K : Set E, IsCompact K ∧ ∀ T : ℝ, 0 < T → ∀ x : ℝ → E, x 0 = u →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt x (V (x t)) (Ico 0 T) t) →
      ∀ t ∈ Ico (0 : ℝ) T, x t ∈ K) (u : E) :
    ∃ x : ℝ → E, x 0 = u ∧ ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (V (x t)) (Ici 0) t :=
  glue_solutions hV (subset_refl _) (mem_Ici.2 le_rfl) (fun t ht =>
    ⟨t + 1, by linarith, forward_exists hV hinv u (t + 1) (by linarith [mem_Ici.1 ht])⟩)

theorem reflect_hasDerivAt {V : E → E} {x : ℝ → E} (hx : ∀ t, HasDerivAt x (V (x t)) t) (s : ℝ) :
    HasDerivAt (fun r => x (-r)) ((fun y => -V y) (x (-s))) s := by
  have := (hx (-s)).scomp s (hasDerivAt_neg s)
  simpa [Function.comp_def] using this

/-- S3 (generic): global existence on `ℝ` from forward trapping for `V` and `-V`. -/
theorem global_exists {V : E → E} (hV : LocallyLipschitzOn univ V)
    (hVn : LocallyLipschitzOn univ (fun y => -V y))
    (hinv : ∀ u : E, ∃ K : Set E, IsCompact K ∧ ∀ T : ℝ, 0 < T → ∀ x : ℝ → E, x 0 = u →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt x (V (x t)) (Ico 0 T) t) →
      ∀ t ∈ Ico (0 : ℝ) T, x t ∈ K)
    (hinvn : ∀ u : E, ∃ K : Set E, IsCompact K ∧ ∀ T : ℝ, 0 < T → ∀ x : ℝ → E, x 0 = u →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt x ((fun y => -V y) (x t)) (Ico 0 T) t) →
      ∀ t ∈ Ico (0 : ℝ) T, x t ∈ K) (u : E) :
    ∃ x : ℝ → E, x 0 = u ∧ ∀ t, HasDerivAt x (V (x t)) t := by
  obtain ⟨xf, hf0, hf⟩ := forward_global hV hinv u
  obtain ⟨xb, hb0, hb⟩ := forward_global hVn hinvn u
  classical
  let x : ℝ → E := fun t => if 0 ≤ t then xf t else xb (-t)
  have hxpos : ∀ t, 0 ≤ t → x t = xf t := fun t ht => by simp only [x, if_pos ht]
  have hxneg : ∀ t, t ≤ 0 → x t = xb (-t) := fun t ht => by
    rcases ht.lt_or_eq with h | h
    · simp only [x, if_neg (not_le.2 h)]
    · subst h; simp only [x, if_pos le_rfl, neg_zero, hf0, hb0]
  have hR : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt x (V (x t)) (Ici 0) t := by
    intro t ht
    rw [hxpos t ht]
    exact (hf t ht).congr (fun s hs => hxpos s hs) (hxpos t ht)
  have hL : ∀ t ∈ Iic (0 : ℝ), HasDerivWithinAt x (V (x t)) (Iic 0) t := by
    intro t ht
    have h1 := (hb (-t) (by simpa using ht)).scomp t (hasDerivAt_neg t).hasDerivWithinAt
      (fun s (hs : s ∈ Iic (0 : ℝ)) => (by simpa using hs : -s ∈ Ici (0 : ℝ)))
    rw [hxneg t ht]
    have h2 : (-1 : ℝ) • (fun y => -V y) (xb (-t)) = V (xb (-t)) := by simp
    rw [h2] at h1
    exact h1.congr (fun s hs => hxneg s hs) (hxneg t ht)
  refine ⟨x, by rw [hxpos 0 le_rfl, hf0], fun t => ?_⟩
  rcases lt_trichotomy t 0 with h | h | h
  · exact (hL t h.le).hasDerivAt (Iic_mem_nhds h)
  · subst h
    have := (hL 0 (mem_Iic.2 le_rfl)).union (hR 0 (mem_Ici.2 le_rfl))
    rw [Iic_union_Ici] at this
    exact hasDerivWithinAt_univ.1 this
  · exact (hR t h.le).hasDerivAt (Ici_mem_nhds h)

/-- S3 (generic): global uniqueness on `ℝ`. -/
theorem global_unique {V : E → E} (hV : LocallyLipschitzOn univ V)
    (hVn : LocallyLipschitzOn univ (fun y => -V y)) {x y : ℝ → E}
    (hx : ∀ t, HasDerivAt x (V (x t)) t) (hy : ∀ t, HasDerivAt y (V (y t)) t)
    (h0 : x 0 = y 0) : x = y := by
  funext t
  rcases le_total 0 t with ht | ht
  · exact solution_unique_Ico hV (T := t + 1) h0 (fun s _ => (hx s).hasDerivWithinAt)
      (fun s _ => (hy s).hasDerivWithinAt) ⟨ht, by linarith⟩
  · have this := solution_unique_Ico hVn (T := -t + 1) (x := fun r => x (-r)) (y := fun r => y (-r))
      (by simpa using h0) (fun s _ => (reflect_hasDerivAt hx s).hasDerivWithinAt)
      (fun s _ => (reflect_hasDerivAt hy s).hasDerivWithinAt)
    have h := this (show -t ∈ Ico (0 : ℝ) (-t + 1) from ⟨by linarith, by linarith⟩)
    simpa using h

end Generic

section Specific
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

theorem locallyLipschitzOn_neg_singleGapField (n : ℤ) :
    LocallyLipschitzOn (univ : Set PhysicalL2) (fun u => -singleGapField n u) := by
  intro u hu
  obtain ⟨K, s, hs, hK⟩ := NlsGge.Atomic.G1081Sup1.locallyLipschitzOn_singleGapField n hu
  refine ⟨K, s, hs, ?_⟩
  intro a ha b hb
  have := hK ha hb
  simpa [edist_neg_neg] using this

theorem singleGapField_trapping_of_compact (hcpt : ∀ u : PhysicalL2, IsCompact (isospectralSet u))
    (n : ℤ) (u : PhysicalL2) :
    ∃ K : Set PhysicalL2, IsCompact K ∧ ∀ T : ℝ, 0 < T → ∀ x : ℝ → PhysicalL2, x 0 = u →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt x (singleGapField n (x t)) (Ico 0 T) t) →
      ∀ t ∈ Ico (0 : ℝ) T, x t ∈ K := by
  refine ⟨isospectralSet u, hcpt u, fun T _ x hx0 hd t ht => ?_⟩
  have h := NlsGge.Atomic.G1081Sup2.isospectral_of_solution_Ico n (γ := x) (T := T) 1
    (fun t ht => by simpa only [one_smul] using hd t ht) t ht
  rw [hx0] at h
  exact h

theorem singleGapField_trapping_neg_of_compact
    (hcpt : ∀ u : PhysicalL2, IsCompact (isospectralSet u)) (n : ℤ) (u : PhysicalL2) :
    ∃ K : Set PhysicalL2, IsCompact K ∧ ∀ T : ℝ, 0 < T → ∀ x : ℝ → PhysicalL2, x 0 = u →
      (∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt x ((fun y => -singleGapField n y) (x t))
        (Ico 0 T) t) →
      ∀ t ∈ Ico (0 : ℝ) T, x t ∈ K := by
  refine ⟨isospectralSet u, hcpt u, fun T _ x hx0 hd t ht => ?_⟩
  have h := NlsGge.Atomic.G1081Sup2.isospectral_of_solution_Ico n (γ := x) (T := T) (-1)
    (fun t ht => by simpa only [neg_one_smul] using hd t ht) t ht
  rw [hx0] at h
  exact h

/-- S3 conditional on the compactness of isospectral sets (realized by `G1_080`). -/
theorem singleGapField_global_exists_of_compact
    (hcpt : ∀ u : PhysicalL2, IsCompact (isospectralSet u)) (n : ℤ) (u : PhysicalL2) :
    ∃ x : ℝ → PhysicalL2, x 0 = u ∧ ∀ t, HasDerivAt x (singleGapField n (x t)) t :=
  global_exists (NlsGge.Atomic.G1081Sup1.locallyLipschitzOn_singleGapField n)
    (locallyLipschitzOn_neg_singleGapField n)
    (singleGapField_trapping_of_compact hcpt n) (singleGapField_trapping_neg_of_compact hcpt n) u

theorem singleGapField_global_unique (n : ℤ) {x y : ℝ → PhysicalL2}
    (hx : ∀ t, HasDerivAt x (singleGapField n (x t)) t)
    (hy : ∀ t, HasDerivAt y (singleGapField n (y t)) t) (h0 : x 0 = y 0) : x = y :=
  global_unique (NlsGge.Atomic.G1081Sup1.locallyLipschitzOn_singleGapField n)
    (locallyLipschitzOn_neg_singleGapField n) hx hy h0

-- BEGIN G1080-DEPENDENT
/-- S3: global existence for every initial datum (compactness from `G1_080`). -/
theorem singleGapField_global_exists (n : ℤ) (u : PhysicalL2) :
    ∃ x : ℝ → PhysicalL2, x 0 = u ∧ ∀ t, HasDerivAt x (singleGapField n (x t)) t :=
  singleGapField_global_exists_of_compact (fun v => (G1_080 v).1) n u

/-- S3: global existence and uniqueness. -/
theorem singleGapField_global_exists_unique (n : ℤ) (u : PhysicalL2) :
    ∃ x : ℝ → PhysicalL2, (x 0 = u ∧ ∀ t, HasDerivAt x (singleGapField n (x t)) t) ∧
      ∀ y : ℝ → PhysicalL2, (y 0 = u ∧ ∀ t, HasDerivAt y (singleGapField n (y t)) t) → y = x := by
  obtain ⟨x, hx0, hx⟩ := singleGapField_global_exists n u
  exact ⟨x, ⟨hx0, hx⟩, fun y hy => singleGapField_global_unique n hy.2 hx (hy.1.trans hx0.symm)⟩
-- END G1080-DEPENDENT
end Specific

end
end NlsGge.Atomic.G1081Sup3
