import Mathlib
import QuantumNLS.REF88StageC
import QuantumNLS.REF88QuantumReduce

/-!
# REF88StageDReduce: stage C plus the printed frequency formula, REDUCED to the quantum derivative facts
(R-EF8C2837, item (iii); NOT the final stage D)

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), theorem statement lines 52-65
(`eq:global-absolute-frequency`: `ν_n(a) = ℰ(K,x) + 𝒯(K,x) + ∑_{j∈F} x_j ω_{nj}(K,x)`, `K = κm`, `x_j = a_j/m`) and the
proof paragraph "Quantum derivatives at arbitrary finite mass" (printed lines 215-315).

* `QuantumDerivatives K hK v D F`: the two printed derivative facts at the point `(K, x)`, `x = II hK v`:
  `∂_{e_a-e_b} ℰ = ω_{ab}` (`b < a` active; the other orientation follows from `omega_swap`) and `K ∂_K ℰ = 𝒯`.
  These are the conclusions of the printed limiting argument; they are NOT proved yet in Lean.
* `frequency_formula` (one field, all in `REF88QuantumReduce`): given `QuantumDerivatives`, the stage-C frequency is
  `ν_n(masses u) = qEnergy(Mu hK v) + qT D.bd D.F + ∑_{j∈F} II hK v j * D.omega n j` for every unit `H¹` profile `v` with
  `II hK v = masses u / m` and every actual-gap datum `D : Data hK v` (so for EVERY choice of profile and data).
* `stageD_of_derivatives`: the conclusions of `REF88StageC.stageC` with the SAME `ν`, plus that formula for every finite
  positive action vector, from the hypotheses of `stageC` and the hypothesis `HD` (`QuantumDerivatives` at every such
  point).  `HD` is not an accepted input.  Reducing `HD` to the accepted gap theorems is the remaining content of (iii).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ENNReal Topology
open Filter

namespace QuantumNLS.REF88StageDReduce

open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88Finite QuantumNLS.REF88PrintedChart QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Fourier QuantumNLS.REF88QuantumDef QuantumNLS.REF88QuantumReduce
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ActualGapDataR26 (Data)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The two printed derivative facts at one point `(K, x)` of the quantum parameter space, `x = II hK v`:
`∂_{e_a - e_b} ℰ = ω_{ab}` for every ordered active pair `b < a` and `K ∂_K ℰ = 𝒯`
(proved in the printed text from the sequential limit statements; NOT yet proved in Lean). -/
def QuantumDerivatives (K : ℝ) (hK : 0 < K) (v : L2T L) (D : Data hK v) (F : Finset ℤ) : Prop :=
  (∀ a b : ℤ, a ∈ F → b ∈ F → b < a →
    HasDerivAt (fun s : ℝ => Efun L K (lineX (fun n => II hK v n) a b s)) (D.omega a b) 0) ∧
  HasDerivAt (fun K' : ℝ => Efun L K' (fun n => II hK v n)) (qT D.bd D.F / K) K

/-- **Frequency formula for one finite-action field** (printed `eq:global-absolute-frequency`), reduced to the
quantum derivatives. -/
theorem frequency_formula {Φ : L2T L → K} (hκ : 0 < κ) (hR : Reg015Input L κ hκ)
    (hΦ : PrintedChart hκ Φ) (ν : ℤ → ActionTorus.PosL1 → ℝ)
    (huniq : ∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n → ∀ ν' : ℝ,
        (∀ t : ℝ, Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * Φ u n) →
          ν' = ν n (RootIndexedMasses.masses hκ u))
    (u : L2T L) (F : Finset ℤ) (hFne : F.Nonempty)
    (hF : ∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n)
    (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L) (hv : ‖v‖ = 1)
    (hvI : ∀ n, II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) (D : Data hK v)
    (hD : QuantumDerivatives (κ * ‖u‖ ^ 2) hK v D F) {n : ℤ} (hn : n ∈ F) :
    ν n (RootIndexedMasses.masses hκ u) = qEnergy (Mu hK v) + qT D.bd D.F +
      ∑ j ∈ F, II hK v j * D.omega n j := by
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
  have hD1 : ∀ a b : ℤ, a ∈ F → b ∈ F → b < a →
      HasDerivAt (fun s : ℝ => Efun L (κ * m) (lineX (fun n => ‖z n‖ ^ 2 / m) a b s))
        (D.omega a b) 0 := by
    intro a b ha hb hab
    rw [hx]; exact hD.1 a b ha hb hab
  have hD2 : HasDerivAt (fun K' : ℝ => Efun L K' (fun n => ‖z n‖ ^ 2 / m))
      (qT D.bd D.F / (κ * m)) (κ * m) := by
    rw [hx]; exact hD.2
  have hlam := lam_formula hκ hΦ.symp hΦ.moduli hR F z hz0 hzne hFne m hm hmpos v hv hK hvI' D hD1 hD2 hn
  have hnu := nu_eq_lamAt hκ hR hΦ ν huniq u F (fun j hj => by
    by_contra hne
    exact hj ((hF j).2 (lt_of_le_of_ne ((RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.1 j)
      (Ne.symm hne)))) n ((hF n).1 hn)
  rw [hnu, hlam]
  simp only [hvI']


/-- **STAGE D, REDUCED FORM (NOT the final stage D).**  The conclusions of `stageC` (same `ν`), together with the
printed frequency formula `ν_n(a) = ℰ + 𝒯 + ∑_j x_j ω_{nj}` for every finite positive action vector, ASSUMING
the two printed quantum derivative facts `QuantumDerivatives` at every such point.  Hypotheses: exactly those of
`stageC` plus `HD`.  `HD` is NOT an accepted input; it is the output of the printed limiting argument
(sequential statements, to be proved). -/
theorem stageD_of_derivatives {Φ : L2T L → K} (hκ : 0 < κ) (hR : Reg015Input L κ hκ)
    (hΦ : PrintedChart hκ Φ)
    (HD : ∀ (u : L2T L) (F : Finset ℤ), F.Nonempty →
      (∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n) →
      ∀ (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L), ‖v‖ = 1 →
      (∀ n, II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) →
      ∀ D : Data hK v, QuantumDerivatives (κ * ‖u‖ ^ 2) hK v D F) :
    (∃ ν : ℤ → ActionTorus.PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n →
        Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) *
            Φ u n) ∧
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), (RootIndexedMasses.masses hκ u).1 n = 0 →
        Φ (flowMap hκ.le u t) n = 0) ∧
      (∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n → ∀ ν' : ℝ,
        (∀ t : ℝ, Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * Φ u n) →
          ν' = ν n (RootIndexedMasses.masses hκ u)) ∧
      (∀ n : ℤ, ContinuousOn (ν n) {a : ActionTorus.PosL1 | 0 < a.1 n}) ∧
      (∀ a : ActionTorus.PosL1, ∀ z ∈ ActionTorus.actionTorus a, ∀ s t : ℝ,
        chartFlow hΦ.symp hκ.le t z ∈ ActionTorus.actionTorus a ∧ chartFlow hΦ.symp hκ.le 0 z = z ∧
        chartFlow hΦ.symp hκ.le (s + t) z = chartFlow hΦ.symp hκ.le s (chartFlow hΦ.symp hκ.le t z) ∧
        Continuous (fun t : ℝ => chartFlow hΦ.symp hκ.le t z)) ∧
      (∀ w : ℤ → ℝ, (∀ n, 0 ≤ w n) → ∀ z : K, (Summable fun n => w n * ‖z n‖ ^ 2) →
        (∀ t : ℝ, ∑' n, w n * ‖chartFlow hΦ.symp hκ.le t z n‖ ^ 2 = ∑' n, w n * ‖z n‖ ^ 2) ∧
        ∀ t0 : ℝ, Tendsto (fun t : ℝ => ∑' n, w n * ‖chartFlow hΦ.symp hκ.le t z n -
          chartFlow hΦ.symp hκ.le t0 z n‖ ^ 2) (𝓝 t0) (𝓝 0))
      ∧ (∀ (u : L2T L) (F : Finset ℤ), F.Nonempty →
        (∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n) →
        ∀ (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L), ‖v‖ = 1 →
        (∀ n, QuantumNLS.F04SelBand.II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) →
        ∀ D : QuantumNLS.ActualGapDataR26.Data hK v,
        ∀ n ∈ F, ν n (RootIndexedMasses.masses hκ u) =
          QuantumNLS.REF88QuantumDef.qEnergy (QuantumNLS.F04SelBand.Mu hK v) +
          QuantumNLS.REF88QuantumDef.qT D.bd D.F +
          ∑ j ∈ F, QuantumNLS.F04SelBand.II hK v j * D.omega n j)) ∧
    (∀ (s : ℝ) (hs : 0 ≤ s), ∃ e : H02 L s ≃ₜ h02 L s,
      ∀ u : H02 L s, toK hs (e u) = Φ (H02.toL2 hs u)) ∧
    (∀ (u : L2T L), (∃ F : Finset ℤ, ∀ n, n ∉ F → (RootIndexedMasses.masses hκ u).1 n = 0) →
      ∀ (s : ℝ), 0 ≤ s → MemHsLp L s u) := by
  obtain ⟨⟨ν, hν⟩, hS, hFin⟩ := QuantumNLS.REF88StageC.stageC hκ hR hΦ
  refine ⟨⟨ν, hν.1, hν.2.1, hν.2.2.1, hν.2.2.2.1, hν.2.2.2.2.1, hν.2.2.2.2.2, ?_⟩, hS, hFin⟩
  intro u F hFne hF hK v hv hvI D n hn
  exact frequency_formula hκ hR hΦ ν hν.2.2.1 u F hFne hF hK v hv hvI D
    (HD u F hFne hF hK v hv hvI D) hn


end QuantumNLS.REF88StageDReduce

#print axioms QuantumNLS.REF88StageDReduce.frequency_formula
#print axioms QuantumNLS.REF88StageDReduce.stageD_of_derivatives
