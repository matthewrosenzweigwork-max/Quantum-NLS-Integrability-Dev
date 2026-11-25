import QuantumNLS.PhysicalProductPreparation
import QuantumNLS.RootMassProperR27

/-!
# R-52CF5DA1 stage 7: the tested profile class and the finite-subcover step

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101): "uniformly over smooth unit profiles with `H^1`
norm at most `R`" and, in the proof, "Finally the `L^2` closure of the smooth unit `H^1` ball of radius `R` is
compact. Cover it by the fixed rough-center neighborhoods above and take a finite subcover. Taking maxima of the
finitely many constants ... proves the asserted uniform convergence."

* `profileClass L R`: the smooth unit profiles (`ClassicalCharges.SmoothPeriodic`, `PhysicalProductPreparation.smoothClass`)
  with DEF-002 squared `H^1` norm `Σ (1+|2πn/L|)² |û_n|² ≤ R²` (`Fourier.hsNormSq L 1`);
* `memHs_smooth`: every smooth profile has a finite DEF-002 `H^1` norm (from the accepted `oneH1_smooth`);
* **`closure_compact`**: the `L²` closure of `profileClass L R` is compact and consists of unit vectors
  (accepted `RootMassCompactR27.totallyBounded_of_tails` through the Fourier isometry);
* **`uniform_of_local`**: a property holding eventually in `N` uniformly on a neighborhood of every point of a compact
  set holds eventually in `N` uniformly on the set (finite subcover, maximum of the thresholds).
No hypothesis is added; all inherited modules are read-only.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped BigOperators

namespace QuantumNLS.R52CFCompact

open PhysicalTensor (L2T)
open QuantumNLS.Fourier (fourierL2 hsNormSq MemHs sobolevWeight)

variable {L : ℝ} [Fact (0 < L)]

/-- The smooth unit profiles with DEF-002 `H^1` norm at most `R`. -/
def profileClass (L : ℝ) [Fact (0 < L)] (R : ℝ) : Set (L2T L) :=
  {u | (∃ (ũ : ℝ → ℂ) (hũ : ClassicalCharges.SmoothPeriodic L ũ), u = PhysicalProductPreparation.smoothClass hũ) ∧
    ‖u‖ = 1 ∧ hsNormSq L 1 (fun n => fourierL2 L u n) ≤ R ^ 2}

theorem sobolevWeight_one (n : ℤ) :
    sobolevWeight L 1 n = (1 + |2 * Real.pi * (n : ℝ) / L|) ^ 2 := by
  unfold sobolevWeight
  rw [show (2 * (1 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem memHs_smooth {ũ : ℝ → ℂ} (hũ : ClassicalCharges.SmoothPeriodic L ũ) :
    MemHs L 1 (fun n => fourierL2 L (PhysicalProductPreparation.smoothClass hũ) n) := by
  have h := PhysicalProductPreparation.oneH1_smooth hũ
  unfold ProductEnergyPreparation.OneH1 Fourier.Mem04 at h
  unfold MemHs
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by unfold sobolevWeight; positivity) (sq_nonneg _))
    (fun n => ?_) (h.mul_left 2)
  rw [sobolevWeight_one]
  unfold Fourier.f04Weight Fourier.freq
  rw [Real.rpow_one]
  have hx := sq_abs (2 * Real.pi * (n : ℝ) / L)
  have hy := sq_nonneg (|2 * Real.pi * (n : ℝ) / L| - 1)
  have hz : 0 ≤ ‖fourierL2 L (PhysicalProductPreparation.smoothClass hũ) n‖ ^ 2 := sq_nonneg _
  have hw : (1 + |2 * Real.pi * (n : ℝ) / L|) ^ 2 ≤ 2 * (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) := by
    nlinarith
  calc (1 + |2 * Real.pi * (n : ℝ) / L|) ^ 2 * ‖fourierL2 L (PhysicalProductPreparation.smoothClass hũ) n‖ ^ 2
      ≤ (2 * (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)) *
          ‖fourierL2 L (PhysicalProductPreparation.smoothClass hũ) n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hw hz
    _ = 2 * ((1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) *
          ‖fourierL2 L (PhysicalProductPreparation.smoothClass hũ) n‖ ^ 2) := by ring

/-- Large frequencies carry large weight. -/
theorem weight_large (n : ℤ) (M : ℕ) (hn : n ∉ Finset.Icc (-(M : ℤ)) M) :
    (2 * Real.pi * (M : ℝ) / L) ^ 2 ≤ sobolevWeight L 1 n := by
  rw [sobolevWeight_one]
  have hL : 0 < L := Fact.out
  have hM : (M : ℝ) ≤ |(n : ℝ)| := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    rcases hn with h | h
    · have : (n : ℝ) < -(M : ℝ) := by exact_mod_cast h
      rw [abs_of_neg (by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])]
      linarith
    · have : (M : ℝ) < n := by exact_mod_cast h
      rw [abs_of_pos (by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)])]
      linarith
  have h1 : 2 * Real.pi * (M : ℝ) / L ≤ |2 * Real.pi * (n : ℝ) / L| := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hL]
    gcongr
  have h0 : 0 ≤ 2 * Real.pi * (M : ℝ) / L := by positivity
  nlinarith [abs_nonneg (2 * Real.pi * (n : ℝ) / L)]

/-- **The `L²` closure of the tested profile class is compact and consists of unit vectors.** -/
theorem closure_compact (R : ℝ) :
    IsCompact (closure (profileClass L R)) ∧ ∀ u ∈ closure (profileClass L R), ‖u‖ = 1 := by
  set S := profileClass L R with hSdef
  have hL : 0 < L := Fact.out
  have hT : TotallyBounded ((fourierL2 L) '' S) := by
    apply RootMassCompactR27.totallyBounded_of_tails _ 1
    · rintro a ⟨u, hu, rfl⟩
      rw [Fourier.norm_fourierL2, hu.2.1]
    · intro ε hε
      set c : ℝ := (R ^ 2 + 1) / ε with hc
      have hcpos : 0 < c := by positivity
      obtain ⟨M, hM⟩ := exists_nat_gt (L / (2 * Real.pi) * Real.sqrt c)
      refine ⟨Finset.Icc (-(M : ℤ)) M, ?_⟩
      rintro a ⟨u, hu, rfl⟩
      obtain ⟨⟨ũ, hũ, hue⟩, -, hR⟩ := hu
      have hs : MemHs L 1 (fun n => fourierL2 L u n) := by rw [hue]; exact memHs_smooth hũ
      have hcw : ∀ n : ℤ, n ∉ Finset.Icc (-(M : ℤ)) M → c ≤ sobolevWeight L 1 n := by
        intro n hn
        refine le_trans ?_ (weight_large n M hn)
        have hpos : 0 < 2 * Real.pi / L := by positivity
        have h1 : Real.sqrt c < 2 * Real.pi * (M : ℝ) / L := by
          have := mul_lt_mul_of_pos_left hM hpos
          calc Real.sqrt c = 2 * Real.pi / L * (L / (2 * Real.pi) * Real.sqrt c) := by
                field_simp
            _ < 2 * Real.pi / L * (M : ℝ) := this
            _ = 2 * Real.pi * (M : ℝ) / L := by ring
        have h2 := Real.sq_sqrt hcpos.le
        nlinarith [Real.sqrt_nonneg c]
      have hsum := hs
      unfold MemHs at hsum
      have hsub : Summable (fun n : {n : ℤ // n ∉ Finset.Icc (-(M : ℤ)) M} =>
          sobolevWeight L 1 n.1 * ‖fourierL2 L u n.1‖ ^ 2) :=
        hsum.comp_injective Subtype.val_injective
      have hsq : Summable (fun n : {n : ℤ // n ∉ Finset.Icc (-(M : ℤ)) M} => ‖fourierL2 L u n.1‖ ^ 2) :=
        (ActionTorus.summable_sq (fourierL2 L u)).comp_injective Subtype.val_injective
      calc (∑' n : {n : ℤ // n ∉ Finset.Icc (-(M : ℤ)) M}, ‖fourierL2 L u n‖ ^ 2)
          ≤ ∑' n : {n : ℤ // n ∉ Finset.Icc (-(M : ℤ)) M},
              sobolevWeight L 1 n.1 * ‖fourierL2 L u n.1‖ ^ 2 / c := by
            refine hsq.tsum_le_tsum (fun n => ?_) (hsub.div_const c)
            rw [le_div_iff₀ hcpos]
            have := hcw n.1 n.2
            have hz : 0 ≤ ‖fourierL2 L u n.1‖ ^ 2 := sq_nonneg _
            nlinarith
        _ = (∑' n : {n : ℤ // n ∉ Finset.Icc (-(M : ℤ)) M},
              sobolevWeight L 1 n.1 * ‖fourierL2 L u n.1‖ ^ 2) / c := tsum_div_const
        _ ≤ (∑' n : ℤ, sobolevWeight L 1 n * ‖fourierL2 L u n‖ ^ 2) / c := by
            gcongr
            exact tsum_comp_le_tsum_of_inj hsum
              (fun n => mul_nonneg (by unfold sobolevWeight; positivity) (sq_nonneg _)) Subtype.val_injective
        _ ≤ R ^ 2 / c := by gcongr; exact hR
        _ < ε := by
            rw [hc, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [sq_nonneg R]
  have hS : TotallyBounded S :=
    (totallyBounded_image_iff (fourierL2 L).isometry.isUniformInducing).mp hT
  have hsph : closure S ⊆ sphere (0 : L2T L) 1 := by
    apply closure_minimal _ isClosed_sphere
    intro u hu
    rw [mem_sphere_zero_iff_norm]
    exact hu.2.1
  refine ⟨hS.closure.isCompact_of_isClosed isClosed_closure, fun u hu => ?_⟩
  exact mem_sphere_zero_iff_norm.mp (hsph hu)

/-- **Finite subcover.**  A property holding eventually in `N`, uniformly on a neighborhood of each point of a
compact set, holds eventually in `N` uniformly on the whole set. -/
theorem uniform_of_local {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (P : ℕ → X → Prop) (hloc : ∀ x ∈ K, ∃ U ∈ 𝓝 x, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ v ∈ U, P N v) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ v ∈ K, P N v := by
  classical
  choose! U hU N₁ hN₁ using hloc
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover U hU
  refine ⟨t.sup N₁, fun N hN v hv => ?_⟩
  obtain ⟨x, hx, hvx⟩ := mem_iUnion₂.mp (hcov hv)
  exact hN₁ x (htK x hx) N ((Finset.le_sup hx).trans hN) v hvx

end QuantumNLS.R52CFCompact

#print axioms QuantumNLS.R52CFCompact.closure_compact
#print axioms QuantumNLS.R52CFCompact.uniform_of_local
