import Mathlib
import QuantumNLS.REF88QuantumLine

/-!
# REF88QuantumCouple: `K ∂_K ℰ = 𝒯` (R-EF8C2837, item (iii), coupling direction)

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), printed lines 245-250 and 288-290:
"the exact finite identity in Proposition `prop:finite-coupling-response` gives `K ∂_K ℰ_N = 2ℰ_N - 2L ∫ Q_N W_N → 𝒯`"
and "Integrating the exact finite coupling identity over a compact interval of `K > 0` gives `K ∂_K ℰ = 𝒯`.  Both derivatives
have been obtained from integrated finite identities."

Printed step -> Lean:
* the exact finite identity: `REF88QuantumBridge.finiteE_hasDerivAt` (accepted R-3C2D6BAB `F07EnergyR6.intensive_response`);
* its limit along varying couplings `κ_n → K` for a fixed integer rounding: `REF88QuantumSeq.coupling_conv` (accepted
  `VarStrong.strong_response_V`; `W_N → W`), and the energy limit `energy_conv`;
* continuity of `𝒯/K` / uniform convergence of the finite derivatives on a compact `K`-interval
  (`REF88QuantumAbstract.seq_continuousOn`, `seq_uniform`), integration (`coupling_increment`) and FTC
  (`hasDerivAt_of_increments`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

open Filter Topology Set
open scoped BigOperators

namespace QuantumNLS.REF88QuantumCouple

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ActualGapDataR26 (Data)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.ProductEnergyPreparation (OneH1)
open QuantumNLS.REF88QuantumDef (qEnergy qT Efun Efun_eq)
open QuantumNLS.REF88QuantumArrays
open QuantumNLS.REF88QuantumSeq
open QuantumNLS.REF88QuantumAbstract
open QuantumNLS.REF88QuantumLine (Avail)

variable {L : ℝ} [Fact (0 < L)]

/-- The finite energy `ℰ_N` at coupling `K'` of the fixed rounding `k_n`. -/
def Ec (L : ℝ) (k : ∀ n : ℕ, MArr (n + 1)) (n : ℕ) (K' : ℝ) : ℝ :=
  (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, arrRoots L (K' / ((n + 1 : ℕ) : ℝ)) (k n) i ^ 2

/-- Its derivative (finite coupling identity). -/
def Dc (L : ℝ) (k : ∀ n : ℕ, MArr (n + 1)) (n : ℕ) (K' : ℝ) : ℝ :=
  (K')⁻¹ *
    (2 * ((((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, arrRoots L (K' / ((n + 1 : ℕ) : ℝ)) (k n) i ^ 2) -
      2 * L * ((((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, arrRoots L (K' / ((n + 1 : ℕ) : ℝ)) (k n) i *
        (BetheRoots.gaudin L (K' / ((n + 1 : ℕ) : ℝ)) (arrRoots L (K' / ((n + 1 : ℕ) : ℝ)) (k n))).inverse
          (arrRoots L (K' / ((n + 1 : ℕ) : ℝ)) (k n)) i))

theorem Ec_hasDerivAt (hL : 0 < L) (k : ∀ n : ℕ, MArr (n + 1)) (n : ℕ) {K' : ℝ} (hK' : 0 < K') :
    HasDerivAt (Ec L k n) (Dc L k n K') K' :=
  REF88QuantumBridge.finiteE_hasDerivAt (Nat.succ_pos n) hL hK' (k n)

def CoupPt (L : ℝ) [Fact (0 < L)] (x : ℤ → ℝ) (K' w : ℝ) : Prop :=
  ∃ hK' : 0 < K', ∃ v' : L2T L, ‖v'‖ = 1 ∧ OneH1 v' ∧ (∀ n, II hK' v' n = x n) ∧
    ∃ D' : Data hK' v', qT D'.bd D'.F / K' = w

def coupG (L : ℝ) [Fact (0 < L)] (x : ℤ → ℝ) (K w0 : ℝ) (K' : ℝ) : ℝ := by
  classical
  exact if K' = K then w0 else if h : ∃ w, CoupPt L x K' w then h.choose else 0

theorem coupG_spec (x : ℤ → ℝ) (K w0 K' : ℝ) (h0 : K' = K → CoupPt L x K' w0)
    (hex : ∃ w, CoupPt L x K' w) : CoupPt L x K' (coupG L x K w0 K') := by
  classical
  unfold coupG
  by_cases hs : K' = K
  · subst hs; simp only [if_true]; exact h0 rfl
  · simp only [hs, if_false, dif_pos hex]; exact hex.choose_spec

/-- **`K ∂_K ℰ = 𝒯`** (printed), for a unit `H¹` profile `v` at coupling `K` with indexed probabilities supported
in `F`: `K' ↦ ℰ(K', x)` is differentiable at `K` with derivative `qT D.bd D.F / K`. -/
theorem coupling_derivative {F : Finset ℤ} (hAv : Avail L F) {K : ℝ} (hK : 0 < K) {v : L2T L}
    (hv : ‖v‖ = 1) (hH : OneH1 v) (D : Data hK v) (hxF : ∀ n, n ∉ F → II hK v n = 0) :
    HasDerivAt (fun K' : ℝ => Efun L K' (fun n => II hK v n)) (qT D.bd D.F / K) K := by
  classical
  have hL : 0 < L := Fact.out
  set x : ℤ → ℝ := fun n => II hK v n with hx
  have hx0 : ∀ n, 0 ≤ x n := fun n => F04SelBand.II_nonneg hK v n
  have hx1 : ∑ n ∈ F, x n = 1 := by
    obtain ⟨-, -, -, htot, -⟩ := RootIndexedMasses.root_indexed_masses_proved_clauses hK v
    have h := htot
    rw [hv, tsum_eq_sum (s := F) (fun n hn => hxF n hn)] at h
    simpa using h
  have hFne : F.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hx1
    simp at hx1
  obtain ⟨j0, hj0⟩ := hFne
  obtain ⟨k, hksupp, hkx, hkl1⟩ := exists_rounding F j0 hj0 x hx0 hxF hx1
  set C : Set ℝ := Icc (K / 2) (2 * K) with hC
  have hKpos : ∀ K' ∈ C, 0 < K' := fun K' hK' => lt_of_lt_of_le (half_pos hK) hK'.1
  have hprof : ∀ K' ∈ C, ∃ w, CoupPt L x K' w := by
    intro K' hK'
    obtain ⟨v', hv', hH', hK'0, hxv'⟩ := hAv K' (hKpos K' hK') x hx0 hxF hx1
    obtain ⟨D'⟩ := ActualGapDataR26.data_exists hK'0 v' hv' hH'
    exact ⟨_, hK'0, v', hv', hH', hxv', D', rfl⟩
  set g : ℝ → ℝ := coupG L x K (qT D.bd D.F / K) with hg
  have hspec : ∀ K' ∈ C, CoupPt L x K' (g K') := by
    intro K' hK'
    refine coupG_spec x K _ K' (fun h0 => ?_) (hprof K' hK')
    subst h0
    exact ⟨hK, v, hv, hH, fun n => rfl, D, rfl⟩
  have hgK : g K = qT D.bd D.F / K := by simp [hg, coupG]
  set EN : ℕ → ℝ → ℝ := fun N K' => Ec L k (N - 1) K' with hEN
  set DN : ℕ → ℝ → ℝ := fun N K' => Dc L k (N - 1) K' with hDN
  set pos : ℕ → ℝ → ℝ := fun _ K' => K' with hpos
  have hA : ∀ s ∈ C, ∃ e : ℕ → ℝ, Tendsto (fun N => pos N (e N)) atTop (𝓝 s) :=
    fun s _ => ⟨fun _ => s, tendsto_const_nhds⟩
  have hB : ∀ (i : ℕ → ℝ) (s : ℝ), s ∈ C → Tendsto (fun N => pos N (i N)) atTop (𝓝 s) →
      Tendsto (fun N => DN N (i N)) atTop (𝓝 (g s)) := by
    intro i s hs hi
    obtain ⟨hs0, v', hv', hH', hxv', D', hgD'⟩ := hspec s hs
    have hκs : Tendsto (fun n : ℕ => i (n + 1)) atTop (𝓝 s) := (tendsto_add_atTop_iff_nat 1).2 hi
    have hη' : Tendsto (fun n : ℕ => ∑' j : ℤ, |(((k n).1 j : ℕ) : ℝ) / ((n : ℝ) + 1) - II hs0 v' j|)
        atTop (𝓝 0) := by
      refine hkl1.congr fun n => ?_
      refine tsum_congr fun j => ?_
      rw [hxv' j]
    have hcc := coupling_conv hs0 v' hv' hH' D' k F hksupp hη' (fun n => i (n + 1)) hκs
      (hκs.eventually (lt_mem_nhds hs0))
    rw [hgD'] at hcc
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    exact hcc
  have hcont : ContinuousOn g C := seq_continuousOn pos DN g C hA hB
  have hunif := fun {ε : ℝ} (hε : 0 < ε) => seq_uniform pos DN g C isCompact_Icc hA hB hcont hε
  have hend : ∀ K' ∈ C, Tendsto (fun N : ℕ => EN N K') atTop (𝓝 (Efun L K' x)) := by
    intro K' hK'
    obtain ⟨hs0, v', hv', hH', hxv', D', -⟩ := hspec K' hK'
    have hη' : Tendsto (fun n : ℕ => ∑' j : ℤ, |(((k n).1 j : ℕ) : ℝ) / ((n : ℝ) + 1) - II hs0 v' j|)
        atTop (𝓝 0) := by
      refine hkl1.congr fun n => ?_
      refine tsum_congr fun j => ?_
      rw [hxv' j]
    have hen := energy_conv hs0 v' hv' hH' D' k F hksupp hη' (fun _ => K') tendsto_const_nhds
      (Eventually.of_forall fun _ => hs0)
    have hE : Efun L K' x = qEnergy (Mu hs0 v') := Efun_eq hs0 hv' (fun n => hxv' n)
    rw [hE]
    exact (tendsto_add_atTop_iff_nat 1).1 hen
  have hinc : ∀ p q : ℝ, K - K / 2 ≤ p → p < q → q ≤ K + K / 2 → ∀ c ε : ℝ,
      (∀ t ∈ Set.Icc p q, |g t - c| ≤ ε) →
      |Efun L q x - Efun L p x - c * (q - p)| ≤ ε * (q - p) := by
    intro p q hp hpq hq c ε hgc
    have hpC : p ∈ C := ⟨by linarith, by linarith⟩
    have hqC : q ∈ C := ⟨by linarith, by linarith⟩
    refine coupling_increment EN DN g (fun K' => Efun L K' x) hpq (fun N K' hK' => ?_)
      (fun ε hε => ?_) (hend p hpC) (hend q hqC) hgc
    · exact Ec_hasDerivAt hL k (N - 1) (hKpos K' ⟨by linarith [hK'.1], by linarith [hK'.2]⟩)
    · filter_upwards [hunif hε] with N hN K' hK'
      exact hN K' ⟨by linarith [hK'.1], by linarith [hK'.2]⟩
  have hgcont : ContinuousAt g K :=
    hcont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hder := hasDerivAt_of_increments (fun K' => Efun L K' x) g K hgcont (K / 2) (half_pos hK) hinc
  rwa [hgK] at hder

end QuantumNLS.REF88QuantumCouple

#print axioms QuantumNLS.REF88QuantumCouple.coupling_derivative
