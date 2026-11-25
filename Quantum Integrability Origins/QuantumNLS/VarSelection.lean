import Mathlib
import QuantumNLS.VarCoupling
import QuantumNLS.VarSelectionBand
import QuantumNLS.VarLocalHeightUniform
import QuantumNLS.F04SelConv
import QuantumNLS.F04SelSeparation

/-!
# CC:F04:variable-coupling (R-C88B5D59), step 4: Proposition CC:F04:selection at contact `c_N = κ_N/N`

Source: `F04.tex` line 412 (proof): "Therefore (CC:F04:external-limit), Lemma CC:F04:local-height and Proposition CC:F04:selection hold with the same limiting phase."

The proofs of `F04SelConv.selection_conv` and `F04SelSeparation.selection_separation` and the assembly `F04Selection.selection` (all read-only, stated at the fixed contact `κ/(n+1)`) are followed line by line with
`VarCoupling.qPath_realBetheV`, `VarCoupling.path_weak0V`, `VarSelectionBand.selection_coreV` and `VarLocalHeightUniform.local_height_uniformV`; the physical band data (`F04SelBand`), the rank bracketing (`F04SelRank`) and the interpolation data (`F04SelSetup`: `rk`, `sParam`, `other_labels`) do not depend on the contact and are used unchanged.
`selectionV`: for every non-integer `λ ∈ (k, k+1)`, `b ≤ k < a`: `x(λ)` exists, the selected root `q_{i_N,N}(s_N(λ))` (roots of the real-label equations at contact `κs N/(N+1)`) converges to every solution, and the other roots stay at a fixed distance.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.VarSelection

open QuantumNLS.BetheLabels QuantumNLS.AdjacentResponse QuantumNLS.F02FiniteGap
open QuantumNLS.LocalHeight QuantumNLS.F04SelRank QuantumNLS.F04SelSetup QuantumNLS.F04SelBand
open QuantumNLS.VarCoupling
open PhysicalTensor (L2T)

theorem separation_coreV {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {κs : ℕ → ℝ}
    (hκs : Tendsto κs atTop (𝓝 κ)) (hpos : ∀ N, 0 < κs N) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {q ν : (N : ℕ) → Fin (N + 1) → ℝ}
    (hB : ∀ N, RealBetheV L κs N (q N) (ν N)) (hw : EmpiricalWeakConv q μ)
    (i : (N : ℕ) → Fin (N + 1)) {x : ℝ}
    (hx : Tendsto (fun N => q N (i N)) atTop (𝓝 x)) (hsupp : x ∉ μ.support) {lam : ℝ}
    (hθ : theta L κ μ x = Real.pi * lam) {κ₀ : ℝ} (hκ₀ : 0 < κ₀)
    (hlab : ∀ N : ℕ, ∀ j : Fin (N + 1), j ≠ i N → κ₀ ≤ |ν N j - lam|) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ N : ℕ in atTop, ∀ j : Fin (N + 1), j ≠ i N →
      c₀ ≤ |q N j - q N (i N)| := by
  obtain ⟨ε₀, hε₀, hev⟩ := QuantumNLS.VarLocalHeightUniform.local_height_uniformV hL hκ hκs hpos hB
    hw hsupp (η := κ₀ / 2) (by positivity)
  refine ⟨ε₀ / 2, by positivity, ?_⟩
  have hxe : ∀ᶠ N : ℕ in atTop, |q N (i N) - x| < ε₀ / 2 := by
    have := (Metric.tendsto_nhds.mp hx) (ε₀ / 2) (by positivity)
    simpa [Real.dist_eq] using this
  filter_upwards [hev, hxe] with N hN hNx j hj
  by_contra hlt
  push Not at hlt
  have hqj : |q N j - x| ≤ ε₀ := by
    calc |q N j - x| = |(q N j - q N (i N)) + (q N (i N) - x)| := by ring_nf
      _ ≤ |q N j - q N (i N)| + |q N (i N) - x| := abs_add_le _ _
      _ ≤ ε₀ := by linarith
  have h1 := hN j hqj
  have hth : theta L κ μ x / Real.pi = lam := by
    rw [hθ]; field_simp
  rw [hth] at h1
  have h2 := hlab N j hj
  linarith

theorem selection_separationV {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {κs : ℕ → ℝ}
    (hκs : Tendsto κs atTop (𝓝 κ)) (hpos : ∀ N, 0 < κs N) (u : L2T L) (hu : ‖u‖ = 1)
    {b a k : ℤ} (hbk : b ≤ k) (hka : k < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) {x : ℝ}
    (hx : th hκ u x = lam * Real.pi)
    (hw : EmpiricalWeakConv (fun n => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
      (sParam (η n) (hηb n) (a := a) hbk lam)) (Mu hκ u))
    (hconv : Tendsto (fun n : ℕ => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
      (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)) atTop (𝓝 x)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : Fin (n + 1), j ≠ rk (η n) (hηb n) hbk →
      c₀ ≤ |qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) j -
        qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)| := by
  haveI := Mu_prob hκ u hu
  have hL : 0 < L := Fact.out
  have hu0 := ne_zero_of_II_pos hκ hb
  have hab : b < a := lt_of_le_of_lt hbk hka
  have hk : k ∈ Finset.Ico b a := Finset.mem_Ico.2 ⟨hbk, hka⟩
  obtain ⟨j, ℓ, r, l, hbj, hjk, hkl, hla, hrl, hnull, hrth, hlth, hlow, hup⟩ :=
    band_data hκ u hu hb ha hbk hka
  obtain ⟨-, hall⟩ := xlam_data hκ u hu hjk hkl hrth hlth hrl hu0 h1 h2
  obtain ⟨hxm, hxθ⟩ := hall x hx
  have hsupp : x ∉ (Mu hκ u).support :=
    Measure.notMem_support_iff_exists.mpr ⟨Ioo r l, isOpen_Ioo.mem_nhds hxm, hnull⟩
  have hθ : theta L κ (Mu hκ u) x = Real.pi * lam := by rw [hxθ]; ring
  set s : ℕ → ℝ := fun n => sParam (η n) (hηb n) (a := a) hbk lam with hs
  have hs01 : ∀ n, 0 < s n ∧ s n < 1 ∧
      nuPath (η n) (hηb n) a (s n) (rk (η n) (hηb n) hbk) = lam :=
    fun n => sParam_spec (η n) (hηb n) hab hk h1 h2
  have hB : ∀ n : ℕ, RealBetheV L κs n (qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a (s n))
      (nuPath (η n) (hηb n) a (s n)) := fun n =>
    qPath_realBetheV hL hpos (η n) (hηb n) a (hs01 n).1.le (hs01 n).2.1.le
  set κ₀ : ℝ := min (lam - k) ((k : ℝ) + 1 - lam) with hκ₀
  have hκ₀pos : 0 < κ₀ := lt_min (by linarith) (by linarith)
  have hlab : ∀ n : ℕ, ∀ j : Fin (n + 1), j ≠ rk (η n) (hηb n) hbk →
      κ₀ ≤ |nuPath (η n) (hηb n) a (s n) j - lam| := by
    intro n j hj
    obtain ⟨o1, o2⟩ := other_labels (η n) (hηb n) hab hk (hs01 n).1.le (hs01 n).2.1.le j
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · have := o1 hlt
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      exact (min_le_left _ _).trans (by linarith)
    · have := o2 hgt
      rw [abs_of_nonneg (by linarith)]
      exact (min_le_right _ _).trans (by linarith)
  exact separation_coreV hL hκ hκs hpos hB hw
    (fun n => rk (η n) (hηb n) hbk) hconv hsupp hθ hκ₀pos hlab

theorem selection_convV {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {κs : ℕ → ℝ}
    (hκs : Tendsto κs atTop (𝓝 κ)) (hpos : ∀ N, 0 < κs N) (u : L2T L) (hu : ‖u‖ = 1)
    {b a k : ℤ} (hbk : b ≤ k) (hka : k < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hend : EmpiricalWeakConv (fun n : ℕ => arrRoots L (κs n / ((n : ℝ) + 1)) (η n)) (Mu hκ u))
    {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) :
    (∃ x, th hκ u x = lam * Real.pi) ∧ ∀ x, th hκ u x = lam * Real.pi →
      Tendsto (fun n : ℕ => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
        (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)) atTop (𝓝 x) := by
  haveI := Mu_prob hκ u hu
  have hL : 0 < L := Fact.out
  have hu0 := ne_zero_of_II_pos hκ hb
  have hab : b < a := lt_of_le_of_lt hbk hka
  have hk : k ∈ Finset.Ico b a := Finset.mem_Ico.2 ⟨hbk, hka⟩
  obtain ⟨j, ℓ, r, l, hbj, hjk, hkl, hla, hrl, hnull, hrth, hlth, hlow, hup⟩ :=
    band_data hκ u hu hb ha hbk hka
  obtain ⟨hex, hall⟩ := xlam_data hκ u hu hjk hkl hrth hlth hrl hu0 h1 h2
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨x, -, hx⟩ := hex
    exact ⟨x, hx⟩
  set s : ℕ → ℝ := fun n => sParam (η n) (hηb n) (a := a) hbk lam with hs
  have hs01 : ∀ n, 0 < s n ∧ s n < 1 ∧
      nuPath (η n) (hηb n) a (s n) (rk (η n) (hηb n) hbk) = lam :=
    fun n => sParam_spec (η n) (hηb n) hab hk h1 h2
  have hend0 : EmpiricalWeakConv (fun n : ℕ => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a 0)
      (Mu hκ u) := by
    have : (fun n : ℕ => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a 0) =
        fun n : ℕ => arrRoots L (κs n / ((n : ℝ) + 1)) (η n) := by
      funext n
      exact qPath_zero L _ (η n) (hηb n) a
    rw [this]
    exact hend
  have hw : EmpiricalWeakConv (fun n => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a (s n))
      (Mu hκ u) :=
    path_weak0V hL hpos hab η hηb hend0 s (fun n => (hs01 n).1.le) (fun n => (hs01 n).2.1.le)
  have hB : ∀ n : ℕ, RealBetheV L κs n (qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a (s n))
      (nuPath (η n) (hηb n) a (s n)) := fun n =>
    qPath_realBetheV hL hpos (η n) (hηb n) a (hs01 n).1.le (hs01 n).2.1.le
  set q : (n : ℕ) → Fin (n + 1) → ℝ := fun n => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a (s n)
    with hq
  set i : (n : ℕ) → Fin (n + 1) := fun n => rk (η n) (hηb n) hbk with hi
  have hna : ∀ y, Mu hκ u {y} = 0 := Mu_singleton hκ u
  have hmono : ∀ n, Monotone (q n) := fun n => (hB n).sorted.monotone
  have hfrac : Tendsto (fun n : ℕ => (((i n : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)) atTop
      (𝓝 (∑' m : ℤ, (if m ≤ k then II hκ u m else 0))) := by
    refine (Ccum_tendsto hκ u (b := b) η hη k).congr fun n => ?_
    have := rk_val (η n) (hηb n) hbk
    have h' : (((rk (η n) (hηb n) hbk).val : ℕ) : ℝ) + 1 = ((Ccum (η n) k : ℕ) : ℝ) := by
      exact_mod_cast this
    simp only [hi]
    rw [h']
  have hloc : ∀ h : ℝ, 0 < h → ∀ᶠ n : ℕ in atTop, q n (i n) ∈ Ioo (r - h) (l + h) := by
    intro h hh
    filter_upwards [rank_lower (hna) hmono hw hfrac (hlow (r - h) (by linarith)),
      rank_upper (hna) hmono hw hfrac (hup (l + h) (by linarith))] with n hn1 hn2
    exact ⟨hn1, hn2⟩
  have hlab : Tendsto (fun n : ℕ => nuPath (η n) (hηb n) a (s n) (i n)) atTop (𝓝 lam) := by
    have : (fun n : ℕ => nuPath (η n) (hηb n) a (s n) (i n)) = fun _ => lam :=
      funext fun n => (hs01 n).2.2
    rw [this]
    exact tendsto_const_nhds
  obtain ⟨hxm, hxθ⟩ := hall x hx
  have hθ : theta L κ (Mu hκ u) x = Real.pi * lam := by rw [hxθ]; ring
  exact QuantumNLS.VarSelectionBand.selection_coreV hL hκ hκs hpos hna hrl hnull hB hw i hloc hlab
    hxm hθ

/-- **`CC:F04:selection` at contact `κs N/(N+1)`** (the variable-coupling form of `F04Selection.selection`). -/
theorem selectionV {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {κs : ℕ → ℝ}
    (hκs : Tendsto κs atTop (𝓝 κ)) (hpos : ∀ N, 0 < κs N) (u : L2T L) (hu : ‖u‖ = 1)
    {b a k : ℤ} (hbk : b ≤ k) (hka : k < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hend : EmpiricalWeakConv (fun n : ℕ => arrRoots L (κs n / ((n : ℝ) + 1)) (η n)) (Mu hκ u))
    {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) :
    (∃ x, th hκ u x = lam * Real.pi) ∧
    (∀ x, th hκ u x = lam * Real.pi →
      Tendsto (fun n : ℕ => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
        (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)) atTop (𝓝 x)) ∧
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : Fin (n + 1), j ≠ rk (η n) (hηb n) hbk →
      c₀ ≤ |qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) j -
        qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)| := by
  haveI := Mu_prob hκ u hu
  have hL : 0 < L := Fact.out
  have hab : b < a := lt_of_le_of_lt hbk hka
  have hk : k ∈ Finset.Ico b a := Finset.mem_Ico.2 ⟨hbk, hka⟩
  obtain ⟨hex, hconv⟩ := selection_convV hκ hκs hpos u hu hbk hka hb ha η hηb hη hend h1 h2
  refine ⟨hex, hconv, ?_⟩
  obtain ⟨x, hx⟩ := hex
  have hs01 : ∀ n, 0 < sParam (η n) (hηb n) (a := a) hbk lam ∧
      sParam (η n) (hηb n) (a := a) hbk lam < 1 :=
    fun n => ⟨(sParam_spec (η n) (hηb n) hab hk h1 h2).1, (sParam_spec (η n) (hηb n) hab hk h1 h2).2.1⟩
  have hend0 : EmpiricalWeakConv (fun n : ℕ => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a 0)
      (Mu hκ u) := by
    have : (fun n : ℕ => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a 0) =
        fun n : ℕ => arrRoots L (κs n / ((n : ℝ) + 1)) (η n) := by
      funext n
      exact qPath_zero L _ (η n) (hηb n) a
    rw [this]
    exact hend
  have hw := path_weak0V hL hpos hab η hηb hend0
    (fun n => sParam (η n) (hηb n) (a := a) hbk lam) (fun n => (hs01 n).1.le)
    (fun n => (hs01 n).2.le)
  exact selection_separationV hκ hκs hpos u hu hbk hka hb ha η hηb h1 h2 hx hw (hconv x hx)

end QuantumNLS.VarSelection

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.VarSelection.separation_coreV
#print axioms QuantumNLS.VarSelection.selection_separationV
#print axioms QuantumNLS.VarSelection.selection_convV
#print axioms QuantumNLS.VarSelection.selectionV
