import QuantumNLS.InverseR01
import QuantumNLS.ReconstructionR33m
import QuantumNLS.MainTheoremR01Algebra

/-!
# MainTheoremR02Phase: part (v) of R-AF8F7562 `thm:main`, the exact common-phase characterization (gap G3)

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex` (sha256 `6008c7e6…da56`) line 71, inside
part (v): "The limit determines the nonlinear Fourier ray at the prescribed mass, and loses exactly the common
phase."  Precise formulation used (review record r107 ruling on G3):
`source-text/chapters/core/projective_reconstruction.tex` (sha256 `bc1188a0…`) lines 392-398
(prop:obstruction, R-682AC0EB): "For unit vectors `z, z̃ ∈ h`, `|z⟩⟨z| = |z̃⟩⟨z̃|` iff `z̃ = e^{iθ}z` for some real
`θ`. Thus the limiting matrix determines exactly the nonlinear Fourier ray at the prescribed mass."  Proof lines
400-409 ("`(e^{iθ}u)^{⊗N} = e^{iNθ}u^{⊗N}`; every quadratic expectation in a fixed-`N` sector … is unchanged. The
`U(1)` equivariance of the classical map gives `w(e^{iθ}u) = e^{iθ}w(u)`").

Objects: the accepted DEF-021 chart record `C = Def021ChartR41b.chart L κ hκ` (R-F5355ABD, `w = C.Φ`,
`w^{-1} = C.Ψ`, `‖w(v)‖ = ‖v‖`), its R-CA92819A `U(1)` equivariance `InverseR01.chart_phase`, the rank-one
projector `ReconstructionR33m.projector = AuxiliaryDensity.rankOneOperator` (the limit in eq:projective-main), the
target `ReconstructionR33m.w hκ F u R t = w(Φ_t u)`, and the auxiliary matrix `ReconstructionR33m.density`.

Proved here (no new hypothesis, no new object):
* `projector_eq_iff` — the fixed-mass ray equivalence on `ℓ²(ℤ)`;
* `chart_projector_eq_iff` — for unit-mass profiles `v, v'`: `|w(v)⟩⟨w(v)| = |w(v')⟩⟨w(v')|` iff `v' = e^{iθ}v`
  (the limit loses exactly the common phase, through the chart);
* `target_projector_eq_iff` — the same for the dynamic targets `w(Φ_t u)` of part (v);
* `inverse_projector_eq_iff` — a unit vector represents the limit ray iff the inverse maps it to a common-phase
  rotation of `Φ_t u` (connection to the normalized-column inverse of R-154AFD4C);
* `density_phase` — `Γ_N[e^{iθ}φ] = Γ_N[φ]`: the fixed-`N` auxiliary matrix does not see the common phase.
`CommonPhaseClause` packages these as the G3 clause of `MainTheoremR02`.  No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace QuantumNLS.MainTheoremR02Phase

open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.BetheOccupationGauge (Gauge)
open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth)
open QuantumNLS.ActualModelTargetR53a (HigherFlows hamFlows)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The unit phase `e^{iθ}`. -/
abbrev ph (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem norm_ph (θ : ℝ) : ‖ph θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

/-- A unit complex number is `e^{iθ}` for `θ = arg c`. -/
theorem ph_arg {c : ℂ} (hc : ‖c‖ = 1) : ph (Complex.arg c) = c := by
  have h := Complex.norm_mul_exp_arg_mul_I c
  rw [hc, Complex.ofReal_one, one_mul] at h
  exact h

theorem conj_mul_self_of_norm {c : ℂ} (hc : ‖c‖ = 1) : conj c * c = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
  simp

/-! ### The fixed-mass ray equivalence (prop:obstruction, first sentence) -/

/-- `|c z⟩⟨c z| = |z⟩⟨z|` for `|c| = 1`. -/
theorem projector_smul (c : ℂ) (hc : ‖c‖ = 1) (z : OneParticle) :
    ReconstructionR33m.projector (c • z) = ReconstructionR33m.projector z := by
  apply ContinuousLinearMap.ext
  intro v
  change InnerProductSpace.rankOne ℂ (c • z) (c • z) v = InnerProductSpace.rankOne ℂ z z v
  rw [InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul]
  congr 1
  calc conj c * ⟪z, v⟫_ℂ * c = (conj c * c) * ⟪z, v⟫_ℂ := by ring
    _ = ⟪z, v⟫_ℂ := by rw [conj_mul_self_of_norm hc, one_mul]

theorem projector_apply_self (z : OneParticle) (hz : ‖z‖ = 1) :
    ReconstructionR33m.projector z z = z := by
  change InnerProductSpace.rankOne ℂ z z z = z
  rw [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hz]
  simp

/-- **Fixed-mass ray equivalence.** For unit vectors `z, z'` of `ℓ²(ℤ)`, `|z⟩⟨z| = |z'⟩⟨z'|` iff `z' = e^{iθ}z`
for some real `θ` (projective_reconstruction.tex:394-396). -/
theorem projector_eq_iff (z z' : OneParticle) (hz : ‖z‖ = 1) (hz' : ‖z'‖ = 1) :
    ReconstructionR33m.projector z = ReconstructionR33m.projector z' ↔ ∃ θ : ℝ, z' = ph θ • z := by
  constructor
  · intro h
    have h1 : z = ⟪z', z⟫_ℂ • z' := by
      have e : ReconstructionR33m.projector z z = ReconstructionR33m.projector z' z := by rw [h]
      rw [projector_apply_self z hz] at e
      exact e.trans (InnerProductSpace.rankOne_apply (𝕜 := ℂ) z' z' z)
    set α := ⟪z', z⟫_ℂ with hα
    have hn : ‖α‖ = 1 := by
      have e := congrArg norm h1
      rw [norm_smul, hz, hz', mul_one] at e
      exact e.symm
    refine ⟨Complex.arg (conj α), ?_⟩
    rw [ph_arg (by rw [Complex.norm_conj, hn]), h1, smul_smul, conj_mul_self_of_norm hn, one_smul]
  · rintro ⟨θ, rfl⟩
    exact (projector_smul _ (norm_ph θ) z).symm

/-! ### The chart: the limit loses exactly the common phase -/

section Chart

variable (hκ : 0 < κ)

/-- The DEF-021 chart record of the accepted R-F5355ABD chart (the `w` of every part). -/
abbrev C : Def021ChartR41b.Chart L κ hκ := Def021ChartR41b.chart L κ hκ

theorem chart_norm (v : L2T L) : ‖(C (L := L) hκ).Φ v‖ = ‖v‖ := by
  have h := (C (L := L) hκ).norm v
  have h0 := norm_nonneg ((C (L := L) hκ).Φ v)
  have h1 := norm_nonneg v
  nlinarith [sq_nonneg (‖(C (L := L) hκ).Φ v‖ - ‖v‖), sq_nonneg (‖(C (L := L) hκ).Φ v‖ + ‖v‖)]

/-- `w(e^{iθ}v) = e^{iθ}w(v)` (accepted R-CA92819A covariance, via `InverseR01.chart_phase`). -/
theorem chart_ph (θ : ℝ) (v : L2T L) :
    (C (L := L) hκ).Φ (ph θ • v) = ph θ • (C (L := L) hκ).Φ v :=
  InverseR01.chart_phase hκ (C (L := L) hκ) θ v

/-- **The limit determines the nonlinear Fourier ray at the prescribed mass and loses exactly the common phase.**
For unit-mass `v, v'`: `|w(v)⟩⟨w(v)| = |w(v')⟩⟨w(v')|` iff `v' = e^{iθ}v` for some real `θ`. -/
theorem chart_projector_eq_iff (v v' : L2T L) (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1) :
    ReconstructionR33m.projector ((C (L := L) hκ).Φ v) =
        ReconstructionR33m.projector ((C (L := L) hκ).Φ v') ↔ ∃ θ : ℝ, v' = ph θ • v := by
  rw [projector_eq_iff _ _ ((chart_norm hκ v).trans hv) ((chart_norm hκ v').trans hv')]
  constructor
  · rintro ⟨θ, h⟩
    refine ⟨θ, ?_⟩
    rw [← chart_ph] at h
    have e := congrArg (C (L := L) hκ).Ψ h
    rwa [(C (L := L) hκ).left_inverse, (C (L := L) hκ).left_inverse] at e
  · rintro ⟨θ, rfl⟩
    exact ⟨θ, chart_ph hκ θ v⟩

/-- The common phase of the profile leaves the limit projector unchanged. -/
theorem chart_projector_phase (θ : ℝ) (v : L2T L) :
    ReconstructionR33m.projector ((C (L := L) hκ).Φ (ph θ • v)) =
      ReconstructionR33m.projector ((C (L := L) hκ).Φ v) := by
  rw [chart_ph, projector_smul _ (norm_ph θ)]

end Chart

/-! ### The dynamic targets of part (v) -/

theorem norm_eq_of_coordinate_moduli {z v : OneParticle} (hm : ∀ a : ℤ, ‖z a‖ = ‖v a‖) : ‖z‖ = ‖v‖ := by
  have htwo : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow htwo, lp.norm_eq_tsum_rpow htwo]
  simp only [hm]

section Dynamic

/-- The evolved profile `Φ_t u` has unit mass. -/
theorem evolved_unit (hκ : 0 < κ) (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (F : HigherFlows L κ) (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ) (t : ℕ → ℝ) :
    ‖physical (jointSmooth (hamFlows F R) t u)‖ = 1 := by
  have h1 : ‖(C (L := L) hκ).Φ (physical (jointSmooth (hamFlows F R) t u))‖ =
      ‖(C (L := L) hκ).Φ (physical u)‖ :=
    norm_eq_of_coordinate_moduli (ReconstructionR33m.coordinate_modulus hκ H F u R t)
  rw [chart_norm hκ (physical (jointSmooth (hamFlows F R) t u)), chart_norm hκ (physical u), hu] at h1
  exact h1

/-- **Part (v), dynamic form.** The limiting projectors of eq:projective-main at two (profile, time) data agree iff
the evolved profiles differ by a common phase. -/
theorem target_projector_eq_iff (hκ : 0 < κ) (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (F : HigherFlows L κ) (u u' : Smooth L) (hu : ‖physical u‖ = 1) (hu' : ‖physical u'‖ = 1)
    (R R' : Finset ℕ) (t t' : ℕ → ℝ) :
    ReconstructionR33m.projector (ReconstructionR33m.w hκ F u R t) =
        ReconstructionR33m.projector (ReconstructionR33m.w hκ F u' R' t') ↔
      ∃ θ : ℝ, physical (jointSmooth (hamFlows F R') t' u') =
        ph θ • physical (jointSmooth (hamFlows F R) t u) :=
  chart_projector_eq_iff hκ _ _ (evolved_unit hκ H F u hu R t) (evolved_unit hκ H F u' hu' R' t')

/-- **Connection to the inverse.** A unit vector `z` represents the limit ray `|w(Φ_tu)⟩⟨w(Φ_tu)|` iff the
quantum-derived inverse maps it to a common-phase rotation `e^{iθ}Φ_tu`. -/
theorem inverse_projector_eq_iff (hκ : 0 < κ) (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (F : HigherFlows L κ) (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ) (t : ℕ → ℝ)
    (z : OneParticle) (hz : ‖z‖ = 1) :
    ReconstructionR33m.projector z = ReconstructionR33m.projector (ReconstructionR33m.w hκ F u R t) ↔
      ∃ θ : ℝ, (C (L := L) hκ).Ψ z = ph θ • physical (jointSmooth (hamFlows F R) t u) := by
  have hw : ‖ReconstructionR33m.w hκ F u R t‖ = 1 :=
    (chart_norm hκ _).trans (evolved_unit hκ H F u hu R t)
  rw [eq_comm, projector_eq_iff _ _ hw hz]
  constructor
  · rintro ⟨θ, h⟩
    refine ⟨θ, ?_⟩
    rw [h]
    change (C (L := L) hκ).Ψ (ph θ • (C (L := L) hκ).Φ _) = _
    rw [← chart_ph, (C (L := L) hκ).left_inverse]
  · rintro ⟨θ, h⟩
    refine ⟨θ, ?_⟩
    have e := congrArg (C (L := L) hκ).Φ h
    rw [(C (L := L) hκ).right_inverse, chart_ph] at e
    exact e

end Dynamic

/-! ### The fixed-`N` auxiliary matrix does not see the common phase -/

/-- Bounded operators on `ℓ²(ℤ)` with the same matrix are equal. -/
theorem op_ext_entries (T T' : OneParticle →L[ℂ] OneParticle)
    (h : ∀ a b : ℤ, ⟪oneBasis a, T (oneBasis b)⟫_ℂ = ⟪oneBasis a, T' (oneBasis b)⟫_ℂ) : T = T' := by
  have hb : ∀ b, T (oneBasis b) = T' (oneBasis b) := by
    intro b
    apply oneBasis.repr.injective
    ext a
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, h]
  apply ContinuousLinearMap.ext
  intro x
  have hx := oneBasis.hasSum_repr x
  have h1 := hx.mapL T
  have h2 := hx.mapL T'
  simp only [map_smul, hb] at h1 h2
  exact h1.unique h2

/-- **`Γ_N[e^{iθ}φ] = Γ_N[φ]`** (projective_reconstruction.tex:402-404: every quadratic expectation in a fixed-`N`
sector, including the entries of `Γ_N`, is unchanged by the common phase). -/
theorem density_phase (hκ : 0 < κ) (g : Gauge) (n : ℕ) (φ : HN L (1 + n)) (θ : ℝ) :
    ReconstructionR33m.density hκ g n (ph θ • φ) = ReconstructionR33m.density hκ g n φ := by
  apply op_ext_entries
  intro a b
  rw [PreparationStability.density_entry, PreparationStability.density_entry, AuxiliaryDensity.gammaEntry,
    AuxiliaryDensity.gammaEntry, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
    conj_mul_self_of_norm (norm_ph θ), one_mul]

/-- The quantum evolution commutes with the common phase (it is complex linear), so the auxiliary matrices of the
preparations `ψ_N` and `e^{iθ}ψ_N` coincide at every time. -/
theorem evolved_density_phase (hκ : 0 < κ) (g : Gauge) (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ)
    (φ : HN L (1 + n)) (θ : ℝ) :
    ReconstructionR33m.density hκ g n (ReconstructionR33m.U (L := L) hκ R t n (ph θ • φ)) =
      ReconstructionR33m.density hκ g n (ReconstructionR33m.U (L := L) hκ R t n φ) := by
  rw [LinearIsometryEquiv.map_smul, density_phase]

/-! ### The G3 clause -/

/-- **G3 clause of part (v)** ("The limit determines the nonlinear Fourier ray at the prescribed mass, and loses
exactly the common phase"): the fixed-mass ray equivalence; through the chart `w`, equal limit projectors at unit
mass iff the profiles differ by a common phase; the same for the evolved targets `w(Φ_tu)` of eq:projective-main;
the unit representatives of the limit ray are exactly those whose inverse image is `e^{iθ}Φ_tu`; and the
fixed-`N` matrix `Γ_N(t)` is unchanged by a common phase of the preparation. -/
def CommonPhaseClause (hκ : 0 < κ) (F : HigherFlows L κ) : Prop :=
  (∀ z z' : OneParticle, ‖z‖ = 1 → ‖z'‖ = 1 →
    (ReconstructionR33m.projector z = ReconstructionR33m.projector z' ↔ ∃ θ : ℝ, z' = ph θ • z)) ∧
  (∀ v v' : L2T L, ‖v‖ = 1 → ‖v'‖ = 1 →
    (ReconstructionR33m.projector ((Def021ChartR41b.chart L κ hκ).Φ v) =
        ReconstructionR33m.projector ((Def021ChartR41b.chart L κ hκ).Φ v') ↔ ∃ θ : ℝ, v' = ph θ • v)) ∧
  (∀ (u u' : Smooth L), ‖physical u‖ = 1 → ‖physical u'‖ = 1 → ∀ (R R' : Finset ℕ) (t t' : ℕ → ℝ),
    (ReconstructionR33m.projector (ReconstructionR33m.w hκ F u R t) =
        ReconstructionR33m.projector (ReconstructionR33m.w hκ F u' R' t') ↔
      ∃ θ : ℝ, physical (jointSmooth (hamFlows F R') t' u') =
        ph θ • physical (jointSmooth (hamFlows F R) t u))) ∧
  (∀ (u : Smooth L), ‖physical u‖ = 1 → ∀ (R : Finset ℕ) (t : ℕ → ℝ) (z : OneParticle), ‖z‖ = 1 →
    (ReconstructionR33m.projector z = ReconstructionR33m.projector (ReconstructionR33m.w hκ F u R t) ↔
      ∃ θ : ℝ, (Def021ChartR41b.chart L κ hκ).Ψ z = ph θ • physical (jointSmooth (hamFlows F R) t u))) ∧
  (∀ (g : Gauge) (R : Finset ℕ) (t : ℕ → ℝ) (n : ℕ) (φ : HN L (1 + n)) (θ : ℝ),
    ReconstructionR33m.density hκ g n (ReconstructionR33m.U (L := L) hκ R t n (ph θ • φ)) =
      ReconstructionR33m.density hκ g n (ReconstructionR33m.U (L := L) hκ R t n φ))

theorem common_phase_clause (hκ : 0 < κ) (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (F : HigherFlows L κ) : CommonPhaseClause (L := L) hκ F :=
  ⟨projector_eq_iff, chart_projector_eq_iff hκ, target_projector_eq_iff hκ H F,
    inverse_projector_eq_iff hκ H F, evolved_density_phase hκ⟩

end QuantumNLS.MainTheoremR02Phase

#print axioms QuantumNLS.MainTheoremR02Phase.common_phase_clause
