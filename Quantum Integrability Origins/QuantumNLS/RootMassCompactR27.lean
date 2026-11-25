import QuantumNLS.RootMassSpectralR27

/-! Finite Fourier projections and total boundedness, on the literal ell2 carrier. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootMassCompactR27
open ActionTorus RootWeightedCellsR26
abbrev E := lp (fun _ : ℤ => ℂ) 2

def project (F : Finset ℤ) (a : E) : E := ∑ n ∈ F,lp.single 2 n (a n)
def pack (F : Finset ℤ) (z : F → ℂ) : E := ∑ n : F,lp.single 2 n (z n)

lemma pack_project (F : Finset ℤ) (a : E) : pack F (fun n => a n) = project F a := by
  exact Finset.sum_coe_sort F (fun n : ℤ => lp.single 2 n (a n))

lemma project_error (F : Finset ℤ) (a : E) :
    ‖a-project F a‖^2 = ∑' n : {n : ℤ // n ∉ F},‖a n‖^2 := by
  have h := lp.norm_compl_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) a F
  have he := (summable_sq a).sum_add_tsum_subtype_compl F
  have hn := tsum_sq_eq a
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at h
  dsimp [project]
  linarith

lemma compact_projections (F : Finset ℤ) (M : ℝ) :
    ∃ C : Set E,IsCompact C ∧ ∀ a : E,‖a‖ ≤ M → project F a ∈ C := by
  let C := pack F '' Metric.closedBall (0 : F → ℂ) M
  have hc : Continuous (pack F) := by
    unfold pack
    apply continuous_finsetSum
    intro n _
    exact (lp.isometry_single (p := (2 : ℝ≥0∞)) (E := fun _ : ℤ => ℂ) n).continuous.comp (continuous_apply n)
  refine ⟨C,(isCompact_closedBall (0 : F → ℂ) M).image hc,fun a ha => ?_⟩
  refine ⟨fun n => a n,?_,pack_project F a⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg ((norm_nonneg a).trans ha)).mpr
  intro n
  exact (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) a n).trans ha

/-- Bounded ell2 sets with uniformly small finite-complement square tails
are totally bounded. The finite-dimensional nets are constructed above. -/
lemma totallyBounded_of_tails (S : Set E) (M : ℝ) (hM : ∀ a ∈ S,‖a‖ ≤ M)
    (ht : ∀ ε : ℝ,0 < ε → ∃ F : Finset ℤ,∀ a ∈ S,
      (∑' n : {n : ℤ // n ∉ F},‖a n‖^2) < ε) : TotallyBounded S := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨F,hF⟩ := ht (ε^2/4) (by positivity)
  obtain ⟨C,hC,hPC⟩ := compact_projections F M
  obtain ⟨t,htf,hcov⟩ := Metric.totallyBounded_iff.mp hC.totallyBounded (ε/2) (by positivity)
  refine ⟨t,htf,fun a ha => ?_⟩
  obtain ⟨b,hb,hpb⟩ := Set.mem_iUnion₂.mp (hcov (hPC a (hM a ha)))
  apply Set.mem_iUnion₂.mpr
  refine ⟨b,hb,?_⟩
  have he : dist a (project F a) < ε/2 := by
    rw [dist_eq_norm]
    have hh := hF a ha
    rw [← project_error] at hh
    nlinarith [norm_nonneg (a-project F a)]
  have hp : dist (project F a) b < ε/2 := Metric.mem_ball.mp hpb
  exact (dist_triangle a (project F a) b).trans_lt (by linarith)

variable {L : ℝ} [Fact (0 < L)]

def frequencies (L Y : ℝ) : Finset ℤ :=
  Finset.Icc (-⌈Y*L/(2*Real.pi)⌉) ⌈Y*L/(2*Real.pi)⌉

lemma outside_frequencies {Y : ℝ} (_hY : 0 < Y) {n : ℤ}
    (hn : n ∉ frequencies L Y) : Y ≤ |momentum L n| := by
  by_contra h
  have hp : |momentum L n| < Y := lt_of_not_ge h
  have hL : 0 < L := Fact.out
  have hc : Y*L/(2*Real.pi) ≤ (⌈Y*L/(2*Real.pi)⌉ : ℤ) := Int.le_ceil _
  have ha := abs_lt.mp hp
  have h1 : -(Y*L/(2*Real.pi)) < (n:ℝ) := by
    have hh := (lt_div_iff₀ hL).mp ha.1
    rw [← neg_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith
  have h2 : (n:ℝ) < Y*L/(2*Real.pi) := by
    have hh := (div_lt_iff₀ hL).mp ha.2
    apply (lt_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr
    nlinarith
  apply hn
  simp only [frequencies,Finset.mem_Icc]
  constructor
  · exact_mod_cast (show -((⌈Y*L/(2*Real.pi)⌉ : ℤ):ℝ) ≤ (n:ℝ) by linarith)
  · exact_mod_cast (show (n:ℝ) ≤ ((⌈Y*L/(2*Real.pi)⌉ : ℤ):ℝ) by linarith)
end QuantumNLS.RootMassCompactR27
