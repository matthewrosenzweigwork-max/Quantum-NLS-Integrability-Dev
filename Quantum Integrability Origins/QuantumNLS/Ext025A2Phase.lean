import QuantumNLS.Ext025A2Quotient

/-! GP-01's compact phase quotient, on an arbitrary compact invariant
subset of a complex Hilbert space. Its rank-one quadratic generators
separate points; their generated complex star algebra is dense.
The zero vector is included and no unit-norm hypothesis is added. -/
set_option autoImplicit false
noncomputable section
open Set Topology InnerProductSpace
namespace QuantumNLS.Ext025A2
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Rank-one quadratic tests determine every vector up to common phase,
including zero. The norm is recovered, rather than assumed fixed. -/
theorem gp01_quadratics_separate_all {u v : H}
    (hq : ∀ w : H, ‖inner ℂ w u‖ ^ 2 = ‖inner ℂ w v‖ ^ 2) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ v = c • u := by
  have hs (w : H) : ‖inner ℂ w w‖ = ‖w‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg w)]
  have h1 := hq u
  have h2 := hq v
  rw [hs] at h1 h2
  rw [norm_inner_symm v u] at h2
  have hn2 : ‖u‖ ^ 2 = ‖v‖ ^ 2 :=
    (sq_eq_sq₀ (sq_nonneg ‖u‖) (sq_nonneg ‖v‖)).mp (h1.trans h2)
  have hn : ‖u‖ = ‖v‖ := (sq_eq_sq₀ (norm_nonneg u) (norm_nonneg v)).mp hn2
  by_cases hu : u = 0
  · have hv : v = 0 := norm_eq_zero.mp (by simpa [hu] using hn.symm)
    exact ⟨1, norm_one, by simp [hu, hv]⟩
  have hv : v ≠ 0 := by
    intro h
    apply hu
    apply norm_eq_zero.mp
    simpa [h] using hn
  have he : ‖inner ℂ u v‖ = ‖u‖ * ‖v‖ := by
    rw [← hn]
    have hnonneg : 0 ≤ ‖u‖ * ‖u‖ := mul_self_nonneg _
    apply (sq_eq_sq₀ (norm_nonneg _) hnonneg).mp
    nlinarith [h1]
  obtain ⟨c, _, hc⟩ := (norm_inner_eq_norm_iff hu hv).mp he
  refine ⟨c, ?_, hc⟩
  have hnorm : ‖u‖ = ‖c‖ * ‖u‖ := calc
    ‖u‖ = ‖v‖ := hn
    _ = ‖c‖ * ‖u‖ := by rw [hc, norm_smul]
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  nlinarith

variable (K : SubMulAction Circle H)

/-- A finite-rank quadratic test on the invariant compact set. -/
def gp01_quadratic (w : H) : C(K, ℂ) where
  toFun x := ((‖inner ℂ w (x : H)‖ ^ 2 : ℝ) : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((continuous_const.inner continuous_subtype_val).norm.pow 2)

/-- Common phase invariance is proved from the normalization of Circle. -/
theorem gp01_quadratic_invariant (w : H) (c : Circle) (x : K) :
    gp01_quadratic K w (c • x) = gp01_quadratic K w x := by
  change ((‖inner ℂ w ((c : ℂ) • (x : H))‖ ^ 2 : ℝ) : ℂ) = _
  simp [gp01_quadratic]

/-- The actual descended rank-one quadratic, with its quotient topology. -/
def gp01_phase_quadratic (w : H) : C(Quotient (MulAction.orbitRel Circle K), ℂ) :=
  gp01_descend (gp01_quadratic K w) (gp01_quadratic_invariant K w)

/-- Complex constants, conjugates and products of the descended quadratics. -/
def gp01_phase_algebra : StarSubalgebra ℂ C(Quotient (MulAction.orbitRel Circle K), ℂ) :=
  StarAlgebra.adjoin ℂ (range (gp01_phase_quadratic K))

/-- Rank-one quadratics separate phase orbits in the full Hilbert space. -/
theorem gp01_phase_algebra_separates : (gp01_phase_algebra K).SeparatesPoints := by
  intro q r hne
  induction q using Quotient.inductionOn with
  | h u =>
    induction r using Quotient.inductionOn with
    | h v =>
      by_contra h
      have heq : ∀ w : H,
          gp01_phase_quadratic K w (Quotient.mk _ u) =
            gp01_phase_quadratic K w (Quotient.mk _ v) := by
        intro w
        by_contra hw
        apply h
        exact ⟨_, ⟨gp01_phase_quadratic K w,
          StarAlgebra.subset_adjoin ℂ _ (mem_range_self w), rfl⟩, hw⟩
      have hquadratic : ∀ w : H, ‖inner ℂ w (u : H)‖ ^ 2 = ‖inner ℂ w (v : H)‖ ^ 2 := by
        intro w
        exact Complex.ofReal_injective (heq w)
      obtain ⟨c, hc, hcu⟩ := gp01_quadratics_separate_all hquadratic
      apply hne
      symm
      apply Quotient.sound
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨(⟨c, by change dist c 0 = 1; simpa using hc⟩ : Circle), ?_⟩
      apply Subtype.ext
      exact hcu.symm

/-- The phase-invariant quadratic star algebra is dense on every compact
invariant Hilbert subset. Compactness is exactly the source assumption. -/
theorem gp01_phase_stone_weierstrass [CompactSpace K] :
    (gp01_phase_algebra K).topologicalClosure = ⊤ := by
  exact ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    _ (gp01_phase_algebra_separates K)

/-- The same concrete quotient is compact Hausdorff. -/
theorem gp01_phase_quotient_topology (hK : IsCompact (K : Set H)) :
    CompactSpace (Quotient (MulAction.orbitRel Circle K)) ∧
      T2Space (Quotient (MulAction.orbitRel Circle K)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : ContinuousSMul Circle K := ⟨by
    apply Continuous.subtype_mk
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)⟩
  exact gp01_quotient_compact_hausdorff
end QuantumNLS.Ext025A2
#print axioms QuantumNLS.Ext025A2.gp01_quadratics_separate_all
#print axioms QuantumNLS.Ext025A2.gp01_quadratic
#print axioms QuantumNLS.Ext025A2.gp01_quadratic_invariant
#print axioms QuantumNLS.Ext025A2.gp01_phase_quadratic
#print axioms QuantumNLS.Ext025A2.gp01_phase_algebra
#print axioms QuantumNLS.Ext025A2.gp01_phase_algebra_separates
#print axioms QuantumNLS.Ext025A2.gp01_phase_stone_weierstrass
#print axioms QuantumNLS.Ext025A2.gp01_phase_quotient_topology
