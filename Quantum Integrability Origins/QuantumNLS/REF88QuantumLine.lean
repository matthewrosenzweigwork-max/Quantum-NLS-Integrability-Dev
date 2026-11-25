import Mathlib
import QuantumNLS.REF88QuantumAbstract
import QuantumNLS.REF88QuantumArrays
import QuantumNLS.REF88QuantumSeq
import QuantumNLS.REF88QuantumReduce

/-!
# REF88QuantumLine: `∂_{e_a - e_b} ℰ = ω_{ab}` (R-EF8C2837, item (iii), line direction)

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), printed lines 262-296:
"Along a compact line `x + s(e_a - e_b)` in the positive simplex ... use the arrays `k_N + r d` ... For endpoints
`r_0 < r_1` the exact telescoping identity is `ℰ_N(k_N + r_1 d) - ℰ_N(k_N + r_0 d) = N⁻¹ ∑ [Q_2(k_N+(r+1)d) - Q_2(k_N+rd)]` ...
The uniform adjacent-gap limits turn this identity into the Riemann integral of the continuous `ω_ab` along the line.
Endpoint rounding tends to zero by the already proved root-energy convergence.  The fundamental theorem of calculus
consequently gives `∂_{e_a - e_b} ℰ = ω_{ab}`."  and "The sequential statements imply continuity of the limits and uniform
convergence on compact subsets of that parameter region."

Printed step -> Lean:
* arrays `k_N + r d`: `REF88QuantumArrays.lineArr` (`lineArr_transfer`: consecutive arrays differ by one transfer);
* the sequential adjacent-gap statement: `REF88QuantumSeq.gap_conv` (accepted `ActualGapTransferR26.forward`);
* the sequential energy statement (endpoint rounding): `REF88QuantumSeq.energy_conv`;
* continuity / uniform convergence of the limit `ω(s) = ω_ab(K, x + s d)`: `REF88QuantumAbstract.seq_continuousOn`,
  `seq_uniform`; Riemann-sum step and FTC: `line_increment`, `hasDerivAt_of_increments`.
* `Avail L F`: the printed "global surjectivity supplies the smooth normalized physical profile" (every positive
  probability vector on `F` at every coupling `K' > 0` is the indexed-probability vector of a unit `H¹` profile), a
  hypothesis here; discharged from the chart in `REF88QuantumProfile.exists_profile`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

open Filter Topology Set
open scoped BigOperators

namespace QuantumNLS.REF88QuantumLine

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ActualGapDataR26 (Data)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.ProductEnergyPreparation (OneH1)
open QuantumNLS.REF88QuantumDef (qEnergy Efun Efun_eq)
open QuantumNLS.REF88QuantumReduce (lineX)
open QuantumNLS.REF88QuantumArrays
open QuantumNLS.REF88QuantumSeq
open QuantumNLS.REF88QuantumAbstract

variable {L : ℝ} [Fact (0 < L)]

/-- Availability of unit `H¹` profiles for every probability vector on `F` at every coupling. -/
def Avail (L : ℝ) [Fact (0 < L)] (F : Finset ℤ) : Prop :=
  ∀ (K' : ℝ), 0 < K' → ∀ x' : ℤ → ℝ, (∀ n, 0 ≤ x' n) → (∀ n, n ∉ F → x' n = 0) → ∑ n ∈ F, x' n = 1 →
    ∃ v : L2T L, ‖v‖ = 1 ∧ OneH1 v ∧ ∃ hK' : 0 < K', ∀ n, II hK' v n = x' n

/-- The normalized finite energy of the line array `k_n + r d`. -/
def Ep (L K : ℝ) (k : ∀ n : ℕ, MArr (n + 1)) (a b : ℤ) (n : ℕ) (r : ℤ) : ℝ :=
  (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, arrRoots L (K / ((n + 1 : ℕ) : ℝ)) (lineArr (k n) a b r) i ^ 2

/-- `N (E(r) - E(r-1))`. -/
def Gp (L K : ℝ) (k : ∀ n : ℕ, MArr (n + 1)) (a b : ℤ) (n : ℕ) (r : ℤ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (Ep L K k a b n r - Ep L K k a b n (r - 1))

theorem Gp_eq (L K : ℝ) (k : ∀ n : ℕ, MArr (n + 1)) (a b : ℤ) (n : ℕ) (r : ℤ) :
    Gp L K k a b n r =
      ∑ i, arrRoots L (K / ((n + 1 : ℕ) : ℝ)) (lineArr (k n) a b r) i ^ 2 -
        ∑ i, arrRoots L (K / ((n + 1 : ℕ) : ℝ)) (lineArr (k n) a b (r - 1)) i ^ 2 := by
  unfold Gp Ep
  have hN : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

theorem lineArr_b {N : ℕ} (m : MArr N) {a b r : ℤ} (hab : a ≠ b) (ha : 0 ≤ (m.1 a : ℤ) + r)
    (hb : 0 ≤ (m.1 b : ℤ) - r) : (((lineArr m a b r).1 b : ℕ) : ℤ) = m.1 b - r := by
  have := lineArr_apply m hab ha hb b
  simpa [hab.symm] using this

theorem Gp_eq_gapSum (L K : ℝ) (k : ∀ n : ℕ, MArr (n + 1)) {a b : ℤ} (hab : a ≠ b) (n : ℕ) (r : ℤ)
    (h1 : 0 ≤ ((k n).1 a : ℤ) + r - 1) (h2 : 0 ≤ ((k n).1 b : ℤ) - r) :
    Gp L K k a b n r = gapSum L (K / ((n + 1 : ℕ) : ℝ)) a b (lineArr (k n) a b (r - 1)) := by
  rw [Gp_eq]
  have hb1 : 1 ≤ (lineArr (k n) a b (r - 1)).1 b := by
    have := lineArr_b (k n) hab (r := r - 1) (by omega) (by omega)
    omega
  unfold gapSum
  rw [dif_pos hb1, lineArr_transfer (k n) hab h1 h2 hb1]
  rfl

/-- Parameter points on the line carrying a data/profile with the prescribed omega. -/
def LinePt (L : ℝ) [Fact (0 < L)] {K : ℝ} (hK : 0 < K) (x : ℤ → ℝ) (a b : ℤ) (s w : ℝ) : Prop :=
  ∃ v' : L2T L, ‖v'‖ = 1 ∧ OneH1 v' ∧ ∃ D' : Data hK v',
    (∀ n, II hK v' n = lineX x a b s n) ∧ D'.omega a b = w

def lineOmega (L : ℝ) [Fact (0 < L)] {K : ℝ} (hK : 0 < K) (x : ℤ → ℝ) (a b : ℤ) (w0 s : ℝ) : ℝ := by
  classical
  exact if s = 0 then w0 else if h : ∃ w, LinePt L hK x a b s w then h.choose else 0

theorem lineOmega_spec {K : ℝ} (hK : 0 < K) (x : ℤ → ℝ) (a b : ℤ) (w0 s : ℝ)
    (h0 : s = 0 → LinePt L hK x a b s w0) (hex : ∃ w, LinePt L hK x a b s w) :
    LinePt L hK x a b s (lineOmega L hK x a b w0 s) := by
  classical
  unfold lineOmega
  by_cases hs : s = 0
  · subst hs; simp only [if_true]; exact h0 rfl
  · simp only [hs, if_false, dif_pos hex]; exact hex.choose_spec

theorem lineX_a (x : ℤ → ℝ) {a b : ℤ} (hab : a ≠ b) (s : ℝ) : lineX x a b s a = x a + s := by
  simp [lineX, hab]

theorem lineX_b (x : ℤ → ℝ) {a b : ℤ} (hab : a ≠ b) (s : ℝ) : lineX x a b s b = x b - s := by
  simp [lineX, hab.symm, sub_eq_add_neg]

theorem lineX_other (x : ℤ → ℝ) {a b : ℤ} {n : ℤ} (hna : n ≠ a) (hnb : n ≠ b) (s : ℝ) :
    lineX x a b s n = x n := by
  simp [lineX, hna, hnb]

theorem lineX_sum (x : ℤ → ℝ) {F : Finset ℤ} {a b : ℤ} (haF : a ∈ F) (hbF : b ∈ F) (s : ℝ) :
    ∑ n ∈ F, lineX x a b s n = ∑ n ∈ F, x n := by
  unfold lineX
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_eq', haF, hbF]

/-- **`∂_{e_a - e_b} ℰ = ω_{ab}`** (printed derivative along the line `x + s(e_a - e_b)`), for an active pair
`b < a` of a unit `H¹` profile `v` at coupling `K` with indexed probabilities supported in `F`. -/
theorem line_derivative {F : Finset ℤ} (hAv : Avail L F) {K : ℝ} (hK : 0 < K) {v : L2T L} (hv : ‖v‖ = 1)
    (hH : OneH1 v) (D : Data hK v) {a b : ℤ} (haF : a ∈ F) (hbF : b ∈ F) (hba : b < a)
    (hxF : ∀ n, n ∉ F → II hK v n = 0) (hxa : 0 < II hK v a) (hxb : 0 < II hK v b) :
    HasDerivAt (fun s : ℝ => Efun L K (lineX (fun n => II hK v n) a b s)) (D.omega a b) 0 := by
  classical
  set x : ℤ → ℝ := fun n => II hK v n with hx
  have hx0 : ∀ n, 0 ≤ x n := fun n => F04SelBand.II_nonneg hK v n
  have hx1 : ∑ n ∈ F, x n = 1 := by
    obtain ⟨-, -, -, htot, -⟩ := RootIndexedMasses.root_indexed_masses_proved_clauses hK v
    have h := htot
    rw [hv, tsum_eq_sum (s := F) (fun n hn => hxF n hn)] at h
    simpa using h
  have hab : a ≠ b := ne_of_gt hba
  set δ : ℝ := min (x a) (x b) / 2 with hδ
  have hδpos : 0 < δ := half_pos (lt_min hxa hxb)
  have hδa : δ ≤ x a / 2 := by
    have := min_le_left (x a) (x b); rw [hδ]; linarith
  have hδb : δ ≤ x b / 2 := by
    have := min_le_right (x a) (x b); rw [hδ]; linarith
  -- profiles on the line
  have hprof : ∀ s ∈ Icc (-δ) δ, ∃ w, LinePt L hK x a b s w := by
    intro s hs
    have hnn : ∀ n, 0 ≤ lineX x a b s n := by
      intro n
      by_cases hna : n = a
      · subst hna; rw [lineX_a x hab]; linarith [hs.1]
      · by_cases hnb : n = b
        · subst hnb; rw [lineX_b x hab]; linarith [hs.2]
        · rw [lineX_other x hna hnb]; exact hx0 n
    have hsupp : ∀ n, n ∉ F → lineX x a b s n = 0 := by
      intro n hn
      have hna : n ≠ a := fun e => hn (e ▸ haF)
      have hnb : n ≠ b := fun e => hn (e ▸ hbF)
      rw [lineX_other x hna hnb]; exact hxF n hn
    have hsum : ∑ n ∈ F, lineX x a b s n = 1 := by rw [lineX_sum x haF hbF, hx1]
    obtain ⟨v', hv', hH', hK', hxv'⟩ := hAv K hK (lineX x a b s) hnn hsupp hsum
    obtain ⟨D'⟩ := ActualGapDataR26.data_exists hK v' hv' hH'
    exact ⟨D'.omega a b, v', hv', hH', D', hxv', rfl⟩
  set ω : ℝ → ℝ := lineOmega L hK x a b (D.omega a b) with hω
  have hspec : ∀ s ∈ Icc (-δ) δ, LinePt L hK x a b s (ω s) := by
    intro s hs
    refine lineOmega_spec hK x a b (D.omega a b) s (fun h0 => ?_) (hprof s hs)
    subst h0
    exact ⟨v, hv, hH, D, fun n => by simp [lineX, hx], rfl⟩
  have hω0 : ω 0 = D.omega a b := by simp [hω, lineOmega]
  -- the roundings
  obtain ⟨k, hksupp, hkx, -⟩ := exists_rounding F a haF x hx0 hxF hx1
  -- sequences indexed by N
  set pos : ℕ → ℤ → ℝ := fun N r => (r : ℝ) / N with hpos
  set EN : ℕ → ℤ → ℝ := fun N r => Ep L K k a b (N - 1) r with hEN
  set GN : ℕ → ℤ → ℝ := fun N r => Gp L K k a b (N - 1) r with hGN
  set ℰ : ℝ → ℝ := fun s => Efun L K (lineX x a b s) with hℰ
  set C : Set ℝ := Icc (-δ) δ with hC
  have hA : ∀ s ∈ C, ∃ e : ℕ → ℤ, Tendsto (fun N => pos N (e N)) atTop (𝓝 s) :=
    fun s _ => ⟨fun N => ⌊s * N⌋, tendsto_floor_div s⟩
  have hshift : ∀ (i : ℕ → ℤ) (s : ℝ), Tendsto (fun N => pos N (i N)) atTop (𝓝 s) →
      Tendsto (fun n : ℕ => ((i (n + 1) : ℤ) : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 s) := by
    intro i s h
    refine ((tendsto_add_atTop_iff_nat 1).2 h).congr fun n => ?_
    simp [pos]
  have hsa : ∀ s ∈ C, 0 < x a + s := fun s hs => by linarith [hs.1]
  have hsb : ∀ s ∈ C, 0 < x b - s := fun s hs => by linarith [hs.2]
  have hB : ∀ (i : ℕ → ℤ) (s : ℝ), s ∈ C → Tendsto (fun N => pos N (i N)) atTop (𝓝 s) →
      Tendsto (fun N => GN N (i N)) atTop (𝓝 (ω s)) := by
    intro i s hs hi
    obtain ⟨v', hv', hH', D', hxD', hωD'⟩ := hspec s hs
    set r : ℕ → ℤ := fun n => i (n + 1) with hr
    have hr' : Tendsto (fun n : ℕ => (r n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 s) := hshift i s hi
    have hr1 : Tendsto (fun n : ℕ => ((r n - 1 : ℤ) : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 s) := by
      have h2 : Tendsto (fun n : ℕ => (r n : ℝ) / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (s - 0)) :=
        hr'.sub tendsto_one_div_add_atTop_nhds_zero_nat
      rw [sub_zero] at h2
      refine h2.congr fun n => ?_
      push_cast; ring
    have hrange0 := eventually_range k x hkx r hr' (hsa s hs) (hsb s hs)
    have hrange1 : ∀ᶠ n : ℕ in atTop, 0 ≤ ((k n).1 a : ℤ) + (r n - 1) ∧ 0 ≤ ((k n).1 b : ℤ) - (r n - 1) :=
      hrange0.mono fun n hn => ⟨by omega, by omega⟩
    have hl1 := line_l1 F k hksupp x hxF hkx haF hbF hab (fun n => r n - 1) hr1 hrange1
    have hl1' : Tendsto (fun n : ℕ => ∑' j : ℤ, |(((lineArr (k n) a b (r n - 1)).1 j : ℕ) : ℝ) / ((n : ℝ) + 1) -
        II hK v' j|) atTop (𝓝 0) := by
      refine hl1.congr fun n => ?_
      refine tsum_congr fun j => ?_
      rw [hxD' j]; rfl
    have hηb : ∀ᶠ n : ℕ in atTop, 1 ≤ (lineArr (k n) a b (r n - 1)).1 b := by
      filter_upwards [hrange0] with n hn
      have := lineArr_b (k n) hab (r := r n - 1) (by omega) (by omega)
      omega
    have ha' : 0 < II hK v' a := by rw [hxD' a, lineX_a x hab]; exact hsa s hs
    have hb' : 0 < II hK v' b := by rw [hxD' b, lineX_b x hab]; exact hsb s hs
    have hgap := gap_conv hK v' hv' hH' D' hba hb' ha' (fun n => lineArr (k n) a b (r n - 1)) F
      (fun n j hj => lineArr_support (k n) F (hksupp n) a b _ haF hbF j hj) hl1' hηb
    have hG : Tendsto (fun n : ℕ => Gp L K k a b n (r n)) atTop (𝓝 (ω s)) := by
      rw [← hωD']
      refine hgap.congr' ?_
      filter_upwards [hrange0] with n hn
      exact (Gp_eq_gapSum L K k hab n (r n) hn.1 hn.2).symm
    exact (tendsto_add_atTop_iff_nat 1).1 hG
  have hcont : ContinuousOn ω C := seq_continuousOn pos GN ω C hA hB
  have hunif := fun {ε : ℝ} (hε : 0 < ε) => seq_uniform pos GN ω C isCompact_Icc hA hB hcont hε
  have hend : ∀ s ∈ Icc (-δ) δ, Tendsto (fun N : ℕ => EN N ⌊s * N⌋) atTop (𝓝 (ℰ s)) := by
    intro s hs
    obtain ⟨v', hv', hH', D', hxD', -⟩ := hspec s hs
    set r : ℕ → ℤ := fun n => ⌊s * ((n + 1 : ℕ) : ℝ)⌋ with hr
    have hr' : Tendsto (fun n : ℕ => (r n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 s) := by
      refine ((tendsto_add_atTop_iff_nat 1).2 (tendsto_floor_div s)).congr fun n => ?_
      simp [hr]
    have hrange0 := eventually_range k x hkx r hr' (hsa s hs) (hsb s hs)
    have hrange : ∀ᶠ n : ℕ in atTop, 0 ≤ ((k n).1 a : ℤ) + r n ∧ 0 ≤ ((k n).1 b : ℤ) - r n :=
      hrange0.mono fun n hn => ⟨by omega, hn.2⟩
    have hl1 := line_l1 F k hksupp x hxF hkx haF hbF hab r hr' hrange
    have hl1' : Tendsto (fun n : ℕ => ∑' j : ℤ, |(((lineArr (k n) a b (r n)).1 j : ℕ) : ℝ) / ((n : ℝ) + 1) -
        II hK v' j|) atTop (𝓝 0) := by
      refine hl1.congr fun n => ?_
      refine tsum_congr fun j => ?_
      rw [hxD' j]; rfl
    have hen := energy_conv hK v' hv' hH' D' (fun n => lineArr (k n) a b (r n)) F
      (fun n j hj => lineArr_support (k n) F (hksupp n) a b _ haF hbF j hj) hl1' (fun _ => K)
      tendsto_const_nhds (Eventually.of_forall fun _ => hK)
    have hE : ℰ s = qEnergy (Mu hK v') := Efun_eq hK hv' (fun n => by rw [hxD' n])
    rw [hE]
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    refine hen.congr fun n => ?_
    simp [hEN, Ep, hr]
  -- the increment estimates and the derivative
  have hinc : ∀ p q : ℝ, 0 - δ ≤ p → p < q → q ≤ 0 + δ → ∀ c ε : ℝ,
      (∀ t ∈ Set.Icc p q, |ω t - c| ≤ ε) → |ℰ q - ℰ p - c * (q - p)| ≤ ε * (q - p) := by
    intro p q hp hpq hq c ε hωc
    refine line_increment EN GN ω ℰ (-δ) δ ?_ (fun ε hε => ?_) hend (by linarith) hpq (by linarith) hωc
    · intro N hN r
      have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hN
      simp only [hEN, hGN, Gp]
      have : (((N - 1 + 1 : ℕ) : ℝ)) = N := by rw [hN1]
      rw [this]
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
    · filter_upwards [hunif hε] with N hN r hr1 hr2
      exact hN r ⟨hr1, hr2⟩
  have hωcont : ContinuousAt ω 0 :=
    hcont.continuousAt (Icc_mem_nhds (by linarith) hδpos)
  have hder := hasDerivAt_of_increments ℰ ω 0 hωcont δ hδpos hinc
  rwa [hω0] at hder

end QuantumNLS.REF88QuantumLine

#print axioms QuantumNLS.REF88QuantumLine.line_derivative
