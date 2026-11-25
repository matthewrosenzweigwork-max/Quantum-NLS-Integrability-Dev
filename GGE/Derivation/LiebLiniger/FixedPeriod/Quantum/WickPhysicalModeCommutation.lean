import LiebLiniger.FixedPeriod.Quantum.OneModeWickNormalOrder

/-! Material Q2-024 proof unit: actual complete-sector and finite-particle
mode commutation. Imports only the checked genuine OneMode construction.
First actual failing direct-sum injection goal is normalized on BOTH sides,
using the exact checked parent CCR induction pattern. This is supporting
qualification, not a whole Q2-024 node closure. No new source assumption. -/

/-! Actual physical mode commutation, the second direct input in Q2-024.
Creation/annihilation are the SAME source Wick maps, on COMPLETE sectors and
their full algebraic direct sum. Adjointness is earned from the actual pure
matrix elements. Annihilation commutation is earned on pure inputs and extended
by actual complete-sector totality; creation commutation follows by adjoints.
Only the mixed distinct-mode conclusion assumes orthogonality of the fields.
No operator commutation or normal-order expansion is an input premise.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped DirectSum ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

private theorem q2024_sector_inner_smul_left (n : ℕ) (a : ℂ)
    (x y : SymmetricSector μ n) :
    inner ℂ (a • x) y = (starRingEnd ℂ) a * inner ℂ x y := by
  change inner ℂ (a • (x : ProductL2 μ (Fin n))) (y : ProductL2 μ (Fin n)) = _
  exact inner_smul_left (𝕜 := ℂ) _ _ _

private theorem q2024_sector_inner_smul_right (n : ℕ) (a : ℂ)
    (x y : SymmetricSector μ n) :
    inner ℂ x (a • y) = a * inner ℂ x y := by
  change inner ℂ (x : ProductL2 μ (Fin n)) (a • (y : ProductL2 μ (Fin n))) = _
  exact inner_smul_right (𝕜 := ℂ) _ _ _

/-- Actual complete-sector source creation is the Hilbert adjoint of actual
source annihilation, with the SAME real square-root/factorial coefficient. -/
theorem sourceWickCreation_eq_adjoint_annihilation (epsilon : ℝ)
    (h : Lp ℂ 2 μ) (n : ℕ) :
    sourceWickCreation μ epsilon h n = (sourceWickAnnihilation μ epsilon h n).adjoint := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  rw [sourceWickCreation_pairing, ContinuousLinearMap.adjoint_inner_right,
    sourceWickAnnihilation_pure, q2024_sector_inner_smul_left μ n,
    inner_pureSymmetricTensor]
  simp only [map_mul, Complex.conj_ofReal, inner_conj_symm]
  ring

/-- Two actual annihilations commute on every positive two-step input sector,
for arbitrary fields, without normalization or mutual orthogonality. -/
theorem sourceWickAnnihilation_commute_sector (epsilon : ℝ)
    (g h : Lp ℂ 2 μ) (n : ℕ) :
    (sourceWickAnnihilation μ epsilon g n).comp
        (sourceWickAnnihilation μ epsilon h (n + 1)) =
      (sourceWickAnnihilation μ epsilon h n).comp
        (sourceWickAnnihilation μ epsilon g (n + 1)) := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  congr 1
  simp only [ContinuousLinearMap.comp_apply, sourceWickAnnihilation_pure,
    map_smul, smul_smul]
  congr 1
  ring

/-- Two actual creations commute on every complete input sector. -/
theorem sourceWickCreation_commute_sector (epsilon : ℝ)
    (g h : Lp ℂ 2 μ) (n : ℕ) :
    (sourceWickCreation μ epsilon g (n + 1)).comp (sourceWickCreation μ epsilon h n) =
      (sourceWickCreation μ epsilon h (n + 1)).comp (sourceWickCreation μ epsilon g n) := by
  have hh := congrArg
    (fun T : SymmetricSector μ (n + 1 + 1) →L[ℂ] SymmetricSector μ n => T.adjoint)
    (sourceWickAnnihilation_commute_sector μ epsilon h g n)
  simpa only [ContinuousLinearMap.adjoint_comp,
    ← sourceWickCreation_eq_adjoint_annihilation] using hh

/-- Actual annihilations commute on ALL physical finite-particle vectors,
including the vacuum and one-particle zero branches. -/
theorem sourceFiniteParticleAnnihilation_commute_apply (epsilon : ℝ)
    (g h : Lp ℂ 2 μ) (v : SourceFiniteParticleSpace μ) :
    sourceFiniteParticleAnnihilation μ epsilon g
        (sourceFiniteParticleAnnihilation μ epsilon h v) =
      sourceFiniteParticleAnnihilation μ epsilon h
        (sourceFiniteParticleAnnihilation μ epsilon g v) := by
  induction v using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n x =>
    change sourceFiniteParticleAnnihilation μ epsilon g
      (sourceFiniteParticleAnnihilation μ epsilon h
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n x)) =
      sourceFiniteParticleAnnihilation μ epsilon h
        (sourceFiniteParticleAnnihilation μ epsilon g
          (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n x))
    cases n with
    | zero => simp only [sourceFiniteParticleAnnihilation_lof_zero, map_zero]
    | succ n =>
      cases n with
      | zero => simp only [sourceFiniteParticleAnnihilation_lof_succ,
          sourceFiniteParticleAnnihilation_lof_zero]
      | succ n =>
        simp only [sourceFiniteParticleAnnihilation_lof_succ]
        have hh := congrArg
          (fun T : SymmetricSector μ (n + 1 + 1) →L[ℂ] SymmetricSector μ n => T x)
          (sourceWickAnnihilation_commute_sector μ epsilon g h n)
        simpa only [ContinuousLinearMap.comp_apply] using
          congrArg (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n) hh
  | add v w hv hw => simpa only [map_add, hv, hw]

/-- The same global physical annihilation commutation as actual endomorphisms. -/
theorem sourceFiniteParticleAnnihilation_commute (epsilon : ℝ)
    (g h : Lp ℂ 2 μ) :
    Commute (sourceFiniteParticleAnnihilation μ epsilon g)
      (sourceFiniteParticleAnnihilation μ epsilon h) := by
  apply LinearMap.ext
  intro v
  exact sourceFiniteParticleAnnihilation_commute_apply μ epsilon g h v

/-- Actual creations commute on ALL physical finite-particle vectors. -/
theorem sourceFiniteParticleCreation_commute_apply (epsilon : ℝ)
    (g h : Lp ℂ 2 μ) (v : SourceFiniteParticleSpace μ) :
    sourceFiniteParticleCreation μ epsilon g (sourceFiniteParticleCreation μ epsilon h v) =
      sourceFiniteParticleCreation μ epsilon h (sourceFiniteParticleCreation μ epsilon g v) := by
  induction v using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n x =>
    change sourceFiniteParticleCreation μ epsilon g
      (sourceFiniteParticleCreation μ epsilon h
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n x)) =
      sourceFiniteParticleCreation μ epsilon h
        (sourceFiniteParticleCreation μ epsilon g
          (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n x))
    simp only [sourceFiniteParticleCreation_lof]
    have hh := congrArg
      (fun T : SymmetricSector μ n →L[ℂ] SymmetricSector μ (n + 1 + 1) => T x)
      (sourceWickCreation_commute_sector μ epsilon g h n)
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (n + 1 + 1)) hh
  | add v w hv hw => simpa only [map_add, hv, hw]

/-- The same global physical creation commutation as actual endomorphisms. -/
theorem sourceFiniteParticleCreation_commute (epsilon : ℝ)
    (g h : Lp ℂ 2 μ) :
    Commute (sourceFiniteParticleCreation μ epsilon g)
      (sourceFiniteParticleCreation μ epsilon h) := by
  apply LinearMap.ext
  intro v
  exact sourceFiniteParticleCreation_commute_apply μ epsilon g h v

/-- Distinct orthogonal physical modes commute across annihilation/creation.
Orthogonality is a field property; the actual operator relation is earned from
its already proved source Wick CCR, not supplied as a hypothesis. -/
theorem sourceFiniteParticle_distinct_mode_commute (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (g h : Lp ℂ 2 μ) (horth : inner ℂ g h = 0) :
    Commute (sourceFiniteParticleAnnihilation μ epsilon g)
      (sourceFiniteParticleCreation μ epsilon h) := by
  change sourceFiniteParticleAnnihilation μ epsilon g * sourceFiniteParticleCreation μ epsilon h = _
  rw [sourceFiniteParticle_CCR μ epsilon hepsilon g h, horth,
    mul_zero, zero_smul, add_zero]
end LiebLiniger.FixedPeriod.Quantum
end
