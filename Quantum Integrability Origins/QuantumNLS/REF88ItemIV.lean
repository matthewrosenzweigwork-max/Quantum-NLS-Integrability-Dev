import Mathlib
import QuantumNLS.REF88StageE
import QuantumNLS.REF88SRoughLimit
import QuantumNLS.REF88SH1Approximation
import QuantumNLS.REF88SH1Identification

/-!
# REF88ItemIV: item (iv) of R-EF8C2837 (`thm:global-physical-dynamics`), assembled from `REF88S*`

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e0215716404f81e6dabec749fe6cab471b8ff7ed8284127f8160c275115`),
theorem lines 76-81 and proof paragraph 316-337.

`itemIV hκ hΦ : ItemIVInput hκ Φ` (the statement of `REF88StageE.ItemIVInput` is NOT weakened).

* `RoughLimit` (lines 77-78, 331-337): the finite-support truncations `actions a n n j` of `REF88SRoughLimit` supply the
  existence of finite-action approximants (`actions_tendsto`, `actions_pair`); the unique limit follows from the
  continuity of `ν n` on the active domain (the hypothesis of `ItemIVInput`), exactly as in
  `REF88SRoughLimit.active_limit`, but for an ARBITRARY finite-action `ℓ¹`-approximating sequence.
* `H1Pair` (lines 78-80, 316-330): the `H¹` truncations of `REF88SH1Approximation.H1_approximation_of_final`
  (conditional on REG-015 through `REF88Reg015Bridge`) and `REF88SH1Identification.pair_identification_of_approximants`.
  The finite physical pair identity at the approximants (`finite_pair`, the premise of the latter) is proved here
  (`finite_pair_chart`) from the chart: `ν_a - ν_b = λ_a - λ_b = ω_{ab}` (`REF88QuantumReduce.nu_eq_lamAt`,
  `REF88QuantumReduce.pair_identity` with the quantum derivatives `REF88StageD.quantumDerivatives_of_chart`), where the
  uniqueness of the rotation frequency used by `nu_eq_lamAt` is derived from the rotation formula (`huniq_of_rot`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology
open Filter

namespace QuantumNLS.REF88ItemIV

open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88PrintedChart QuantumNLS.Sobolev QuantumNLS.REF88FieldRotation
open QuantumNLS.REF88QuantumDef QuantumNLS.REF88QuantumReduce QuantumNLS.REF88QuantumLine
open QuantumNLS.REF88StageDReduce QuantumNLS.REF88StageE
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ActualGapDataR26 (Data)
open QuantumNLS.ActionTorus (PosL1)
open QuantumNLS.REF88PrintedChartLocal (PrintedChartLocal printedChart_of_local)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The rotation formula determines the frequency: any `ν'` rotating coordinate `n` equals `ν n`. -/
theorem huniq_of_rot {Φ : L2T L → K} (hκ : 0 < κ) (hΦ : PrintedChart hκ Φ) {ν : ℤ → PosL1 → ℝ}
    (hrot : FreqRotation hκ Φ ν) :
    ∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n → ∀ ν' : ℝ,
      (∀ t : ℝ, Φ (flowMap hκ.le u t) n =
        Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * Φ u n) →
        ν' = ν n (RootIndexedMasses.masses hκ u) := by
  intro u n hn ν' hν'
  have hne : Φ u n ≠ 0 := by
    intro h0
    have := hΦ.moduli u n
    rw [h0, norm_zero] at this
    have h1 : (RootIndexedMasses.masses hκ u).1 n = 0 := by rw [← this]; norm_num
    exact absurd hn (by rw [h1]; exact lt_irrefl 0)
  by_contra hd
  have hd' : ν' - ν n (RootIndexedMasses.masses hκ u) ≠ 0 := sub_ne_zero.2 hd
  set d := ν' - ν n (RootIndexedMasses.masses hκ u) with hdd
  set t : ℝ := Real.pi / d with ht
  have h1 := hν' t
  have h2 := hrot u t n hn
  have h3 : Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) :=
    mul_right_cancel₀ hne (h1.symm.trans h2)
  have h4 : Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * ((t * d : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hdd]
    push_cast
    ring
  have h5 : Complex.exp (-Complex.I * ((t * d : ℝ) : ℂ)) = 1 := by
    have hpos := Complex.exp_ne_zero (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ))
    have : Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * ((t * d : ℝ) : ℂ)) =
        Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) * 1 := by
      rw [← h4, h3, mul_one]
    exact mul_left_cancel₀ hpos this
  have h6 : t * d = Real.pi := by rw [ht]; field_simp
  rw [h6] at h5
  have h7 : Complex.exp (-Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
    have : -Complex.I * ((Real.pi : ℝ) : ℂ) = -((Real.pi : ℂ) * Complex.I) := by ring
    rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  rw [h7] at h5
  norm_num at h5

/-- **Finite physical pair identity** (printed `ν_a - ν_b = ω_{ab}` at a finite-action field, lines 303-307):
for a finite positive action vector `F`, every unit profile `v` with the indexed probabilities and every actual-gap
datum `D`, `ν_a(I(u)) - ν_b(I(u)) = ω_{ab}` for `b < a` in `F`. -/
theorem finite_pair_chart {Φ : L2T L → K} (hκ : 0 < κ) (hΦ : PrintedChart hκ Φ) {ν : ℤ → PosL1 → ℝ}
    (hrot : FreqRotation hκ Φ ν)
    (u : L2T L) (F : Finset ℤ) (hFne : F.Nonempty)
    (hF : ∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n)
    (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L) (hv : ‖v‖ = 1)
    (hvI : ∀ n, II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) (D : Data hK v)
    {a b : ℤ} (hab : b < a) (ha : a ∈ F) (hb : b ∈ F) :
    ν a (RootIndexedMasses.masses hκ u) - ν b (RootIndexedMasses.masses hκ u) = D.omega a b := by
  have hR : Reg015Input L κ hκ := REF88Reg015Bridge.reg015Input_of_final hκ
  have hD := REF88StageD.quantumDerivatives_of_chart hκ hR hΦ u F hFne hF hK v hv hvI D
  set m : ℝ := ‖u‖ ^ 2 with hmdef
  set z : K := Φ u with hz
  have hmass : ∀ j, ‖z j‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 j := fun j => hΦ.moduli u j
  have hz0 : ∀ j, j ∉ F → z j = 0 := by
    intro j hj
    have h1 : (RootIndexedMasses.masses hκ u).1 j = 0 := by
      have := (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1 j
      by_contra hne
      exact hj ((hF j).2 (lt_of_le_of_ne this (Ne.symm hne)))
    have : ‖z j‖ = 0 := by nlinarith [norm_nonneg (z j), hmass j]
    exact norm_eq_zero.1 this
  have hzne : ∀ j ∈ F, z j ≠ 0 := by
    intro j hj h0
    have := hmass j
    rw [h0, norm_zero] at this
    have := (hF j).1 hj
    simp at *
    linarith
  have hm : m = ∑ j ∈ F, ‖z j‖ ^ 2 := by
    rw [hmdef, ← (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.2.2.1,
      tsum_eq_sum (s := F) (fun j hj => by
        have h1 : (RootIndexedMasses.masses hκ u).1 j = 0 := by
          have := (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1 j
          by_contra hne
          exact hj ((hF j).2 (lt_of_le_of_ne this (Ne.symm hne)))
        exact h1)]
    exact Finset.sum_congr rfl fun j _ => (hmass j).symm
  have hmpos : 0 < m := by
    obtain ⟨j, hj⟩ := hFne
    rw [hm]
    exact Finset.sum_pos (fun i hi => by have := hzne i hi; positivity) ⟨j, hj⟩
  have hvI' : ∀ j, II hK v j = ‖z j‖ ^ 2 / m := fun j => by rw [hvI j, hmass j]
  have hx : (fun j => ‖z j‖ ^ 2 / m) = fun j => II hK v j := funext fun j => (hvI' j).symm
  have hD1 : HasDerivAt (fun s : ℝ => Efun L (κ * m) (lineX (fun n => ‖z n‖ ^ 2 / m) a b s))
      (D.omega a b) 0 := by
    rw [hx]; exact hD.1 a b ha hb hab
  have hnu : ∀ n ∈ F, ν n (RootIndexedMasses.masses hκ u) = lamAt hκ hΦ.symp z n := fun n hn =>
    nu_eq_lamAt hκ hR hΦ ν (huniq_of_rot hκ hΦ hrot) u F (fun j hj => by
      by_contra hne
      exact hj ((hF j).2 (lt_of_le_of_ne ((RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1 j)
        (Ne.symm hne)))) n ((hF n).1 hn)
  rw [hnu a ha, hnu b hb]
  exact pair_identity hκ hΦ.symp hΦ.moduli hR F z hz0 hzne hFne m hm hmpos v hv hK hvI' D ha hb hD1

/-- **Item (iv)** of R-EF8C2837: the rough continuous-limit clause and the `H¹` pair identification, for every
rotation-frequency family `ν` that is continuous on the active domains (and satisfies the finite formula, which is
not needed here: the finite pair identity is derived from the chart). -/
theorem itemIV {Φ : L2T L → K} (hκ : 0 < κ) (hΦ : PrintedChartLocal hκ Φ) : ItemIVInput hκ Φ := by
  classical
  intro ν hrot hcont _hform
  have hΦ' : PrintedChart hκ Φ := printedChart_of_local hκ hΦ
  refine ⟨?_, ?_⟩
  · -- RoughLimit
    intro a n hn
    refine ⟨⟨REF88SRoughLimit.actions a n n, fun j => ⟨⟨REF88STruncation.supports n n j, fun k hk => ?_⟩, ?_⟩,
      REF88SRoughLimit.actions_tendsto a n n⟩, ?_⟩
    · simp only [REF88SRoughLimit.actions_apply, if_neg hk]
    · rw [(REF88SRoughLimit.actions_pair a n n j).1]; exact hn
    · intro aj haj hlim
      have h : Tendsto (fun j => ν n (aj j)) atTop (𝓝 (ν n a)) :=
        ((hcont n) a hn).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim,
          Eventually.of_forall fun j => (haj j).2⟩)
      exact ⟨h, fun l hl => tendsto_nhds_unique hl h⟩
  · -- H1Pair
    intro u a b hab ha hb hK D0
    obtain ⟨v, hv, hcoord, hp, hz, -⟩ :=
      REF88SH1Approximation.H1_approximation_of_final hκ hΦ' u a b ha hb
    have hav : ∀ j, 0 < II hκ (v j).val a := fun j => by
      show 0 < (RootIndexedMasses.masses hκ (v j).val).1 a
      rw [(hp j).1]; exact ha
    have hbv : ∀ j, 0 < II hκ (v j).val b := fun j => by
      show 0 < (RootIndexedMasses.masses hκ (v j).val).1 b
      rw [(hp j).2]; exact hb
    refine REF88SH1Identification.pair_identification_of_approximants hκ ν hcont v u hv hab ha hb hav hbv
      ?_ hK D0
    intro j hKj D
    set w : L2T L := (v j).val with hw
    have hw0 : w ≠ 0 := hz j
    let F : Finset ℤ := (REF88STruncation.supports a b j).filter
      (fun n => 0 < (RootIndexedMasses.masses hκ w).1 n)
    have hF : ∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ w).1 n := by
      intro n
      constructor
      · intro hn
        exact (Finset.mem_filter.1 hn).2
      · intro hn
        refine Finset.mem_filter.2 ⟨?_, hn⟩
        by_contra hns
        have h0 := hΦ'.moduli w n
        have h1 := hcoord j n
        rw [if_neg hns] at h1
        have : (RootIndexedMasses.masses hκ w).1 n = 0 := by
          rw [← h0]
          show ‖Φ (v j).val n‖ ^ 2 = 0
          rw [h1]; simp
        exact absurd hn (by rw [this]; exact lt_irrefl 0)
    have haF : a ∈ F := (hF a).2 (by rw [hw, (hp j).1]; exact ha)
    have hbF : b ∈ F := (hF b).2 (by rw [hw, (hp j).2]; exact hb)
    have hv1 : ‖FullMass.unitDir w‖ = 1 := FullMass.norm_unitDir hw0
    have hn2 : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.2 hw0)
    have hvI : ∀ n, II hKj (FullMass.unitDir w) n = (RootIndexedMasses.masses hκ w).1 n / ‖w‖ ^ 2 := by
      intro n
      have h := REF88QuantumDef.II_unitDir hκ hw0 hKj n
      have h2 : II hκ w n = (RootIndexedMasses.masses hκ w).1 n := rfl
      rw [h2] at h
      rw [h]; field_simp
    exact finite_pair_chart hκ hΦ' hrot w F ⟨a, haF⟩ hF hKj _ hv1 hvI D hab haF hbF

#print axioms huniq_of_rot
#print axioms finite_pair_chart
#print axioms itemIV

end QuantumNLS.REF88ItemIV
