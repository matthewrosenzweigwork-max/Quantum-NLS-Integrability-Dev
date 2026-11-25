import QuantumNLS.UniformStaticR49b

/-! SupportPersistH01Born: Born probabilities of the donor-empty events in the Bethe
basis for an arbitrary (not necessarily product) vector.

Source: principal_correspondence.tex line 31 (strong symbols, support and projective
conclusions persist under uniformly norm-close normalized preparations); uniform_static.tex
(thm:uniform-static, support clauses); shift_affinity.tex (support probabilities p_a^0, p_b^0).

The event for the initial (resp. final) support of a label a is {m : m_a = 0}, indexed by
the Bethe-basis labels m. The Q06 gauge enters the physical operators only through
unit-modulus phases on the basis vectors; the definition below takes no gauge parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Set Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace QuantumNLS.SupportPersistH01Born
open PhysicalTensor BetheLabels BetheCoefficientTransform Occupation
variable {L κ : ℝ} [Fact (0 < L)]

/-- Born weight of the event `{m : m_a = 0}` for a family of vectors `Ψ` indexed by
the arrays `MArr N`: `∑_{m_a = 0} |⟨Ψ_m, ψ⟩|²`. -/
def bornEmptyFam {N : ℕ} (Ψ : MArr N → HN L N) (a : ℤ) (ψ : HN L N) : ℝ :=
  ∑' m : {m : MArr N // (marrArr N m).1 a = 0}, ‖⟪Ψ m.1, ψ⟫_ℂ‖ ^ 2

/-- The support probability of a general vector `ψ` in the Bethe basis `Ψ`: the Born
probability of the event `{m : m_a = 0}`. For `ψ = u^{⊗N}` this is the product-law
quantity `missing`. -/
def bornEmpty {N : ℕ} (Ψ : BetheBasis L N) (a : ℤ) (ψ : HN L N) : ℝ :=
  bornEmptyFam (fun m => Ψ m) a ψ

theorem bornEmptyFam_nonneg {N : ℕ} (Ψ : MArr N → HN L N) (a : ℤ) (ψ : HN L N) :
    0 ≤ bornEmptyFam Ψ a ψ :=
  tsum_nonneg fun _ => sq_nonneg _

/-- The Born weight is the literal full occupation sum of the Bethe coefficients
`g_m = ⟨Ψ_m, ψ⟩`, i.e. the quantity `ExactShiftResidual.missing` of the coordinate vector. -/
theorem bornEmpty_eq_missing {N : ℕ} (Ψ : BetheBasis L N) (a : ℤ) (ψ : HN L N) :
    bornEmpty Ψ a ψ = ExactShiftResidual.missing a (occupationCoefficient Ψ ψ) := by
  unfold bornEmpty bornEmptyFam ExactShiftResidual.missing
  refine Eq.trans ?_ ((Equiv.subtypeEquiv (p := fun m : MArr N => (marrArr N m).1 a = 0)
      (q := fun x : Arr N => x.1 a = 0) (marrArr N) (fun _ => Iff.rfl)).tsum_eq _)
  refine tsum_congr fun m => ?_
  simp [occupationCoefficient_apply]

/-- The Born weight is bounded by the squared norm of the vector. -/
theorem bornEmpty_le_norm_sq {N : ℕ} (Ψ : BetheBasis L N) (a : ℤ) (ψ : HN L N) :
    bornEmpty Ψ a ψ ≤ ‖ψ‖ ^ 2 := by
  rw [bornEmpty_eq_missing]
  have h := ExactShiftResidual.support_partition a (occupationCoefficient Ψ ψ)
  have hs : 0 ≤ ‖FullOccupationAffinity.sourceCoefficients a (occupationCoefficient Ψ ψ)‖ ^ 2 :=
    sq_nonneg _
  have hn : ‖occupationCoefficient Ψ ψ‖ = ‖ψ‖ := LinearIsometryEquiv.norm_map _ _
  rw [hn] at h
  linarith

theorem emptyCoefficients_norm_le {N : ℕ} (a : ℤ) (g : OccupationHilbert.H N) :
    ‖ExactShiftResidual.emptyCoefficients a g‖ ≤ ‖g‖ :=
  OccupationHilbert.restrictL2_norm_le _ _ g

theorem emptyCoefficients_sub {N : ℕ} (a : ℤ) (g h : OccupationHilbert.H N) :
    ExactShiftResidual.emptyCoefficients a (g - h) =
      ExactShiftResidual.emptyCoefficients a g - ExactShiftResidual.emptyCoefficients a h := by
  simp only [ExactShiftResidual.emptyCoefficients, map_sub]

/-- Lipschitz bound for the missing probability on the unit ball, with constant 2:
`|‖Pg‖² − ‖Ph‖²| = |‖Pg‖ − ‖Ph‖| (‖Pg‖ + ‖Ph‖) ≤ ‖P(g − h)‖ · 2 ≤ 2‖g − h‖`. -/
theorem missing_lipschitz {N : ℕ} (a : ℤ) (g h : OccupationHilbert.H N)
    (hg : ‖g‖ ≤ 1) (hh : ‖h‖ ≤ 1) :
    |ExactShiftResidual.missing a g - ExactShiftResidual.missing a h| ≤ 2 * ‖g - h‖ := by
  rw [ExactShiftResidual.missing_eq_norm, ExactShiftResidual.missing_eq_norm]
  set Ag := ExactShiftResidual.emptyCoefficients a g with hAg_def
  set Ah := ExactShiftResidual.emptyCoefficients a h with hAh_def
  have hAg1 : ‖Ag‖ ≤ 1 := (emptyCoefficients_norm_le a g).trans hg
  have hAh1 : ‖Ah‖ ≤ 1 := (emptyCoefficients_norm_le a h).trans hh
  have hd : |‖Ag‖ - ‖Ah‖| ≤ ‖g - h‖ := by
    calc |‖Ag‖ - ‖Ah‖| ≤ ‖Ag - Ah‖ := abs_norm_sub_norm_le _ _
      _ = ‖ExactShiftResidual.emptyCoefficients a (g - h)‖ := by
          rw [hAg_def, hAh_def, emptyCoefficients_sub]
      _ ≤ ‖g - h‖ := emptyCoefficients_norm_le a (g - h)
  have hsum : ‖Ag‖ + ‖Ah‖ ≤ 2 := by linarith
  have hsum0 : 0 ≤ ‖Ag‖ + ‖Ah‖ := by positivity
  have key : ‖Ag‖ ^ 2 - ‖Ah‖ ^ 2 = (‖Ag‖ - ‖Ah‖) * (‖Ag‖ + ‖Ah‖) := by ring
  rw [key, abs_mul, abs_of_nonneg hsum0]
  calc |‖Ag‖ - ‖Ah‖| * (‖Ag‖ + ‖Ah‖) ≤ ‖g - h‖ * 2 :=
        mul_le_mul hd hsum hsum0 (norm_nonneg _)
    _ = 2 * ‖g - h‖ := mul_comm _ _

/-- The support probability is 1-Lipschitz up to the factor 2 on the unit ball:
`|bornEmpty ψ − bornEmpty φ| ≤ 2‖ψ − φ‖` whenever `‖ψ‖, ‖φ‖ ≤ 1`. -/
theorem bornEmpty_lipschitz {N : ℕ} (Ψ : BetheBasis L N) (a : ℤ) (ψ φ : HN L N)
    (hψ : ‖ψ‖ ≤ 1) (hφ : ‖φ‖ ≤ 1) :
    |bornEmpty Ψ a ψ - bornEmpty Ψ a φ| ≤ 2 * ‖ψ - φ‖ := by
  rw [bornEmpty_eq_missing, bornEmpty_eq_missing]
  have hsub : occupationCoefficient Ψ ψ - occupationCoefficient Ψ φ =
      occupationCoefficient Ψ (ψ - φ) := (map_sub _ _ _).symm
  have hd : ‖occupationCoefficient Ψ ψ - occupationCoefficient Ψ φ‖ = ‖ψ - φ‖ := by
    rw [hsub, LinearIsometryEquiv.norm_map]
  have h := missing_lipschitz a (occupationCoefficient Ψ ψ) (occupationCoefficient Ψ φ)
    (by rw [LinearIsometryEquiv.norm_map]; exact hψ) (by rw [LinearIsometryEquiv.norm_map]; exact hφ)
  rwa [hd] at h

/-- Unit-modulus phase conventions on the basis do not change the Born weights. -/
theorem bornEmptyFam_phase {N : ℕ} (Ψ : MArr N → HN L N) (θ : MArr N → ℂ)
    (hθ : ∀ m, ‖θ m‖ = 1) (a : ℤ) (ψ : HN L N) :
    bornEmptyFam (fun m => θ m • Ψ m) a ψ = bornEmptyFam Ψ a ψ := by
  unfold bornEmptyFam
  refine tsum_congr fun m => ?_
  simp only [inner_smul_left, norm_mul, Complex.norm_conj, hθ, one_mul]

/-- The Q06 gauge phases (the unit-modulus values of `particleGauge`) multiply the Bethe
basis vectors; the support probabilities are therefore gauge-independent. -/
theorem bornEmpty_at_q06_gauge (hκ : 0 < κ) (n : ℕ) (a : ℤ) (ψ : HN L (n+1)) :
    bornEmptyFam (fun m => (QuantumNLS.RetargetSelectionR49b.particleGauge (L := L) hκ (n+1) m).1 •
        Def044D1SpectralR51a.basis (L := L) hκ n m) a ψ =
      bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) a ψ := by
  unfold bornEmpty
  exact bornEmptyFam_phase _ (fun m => (QuantumNLS.RetargetSelectionR49b.particleGauge (L := L) hκ (n+1) m).1)
    (fun m => (QuantumNLS.RetargetSelectionR49b.particleGauge (L := L) hκ (n+1) m).2) a ψ

/-! ### Reduction to the product law -/

theorem product_norm_eq_one (hκ : 0 < κ) (n : ℕ) (u : L2T L) (hu : ‖u‖ = 1) :
    ‖UniformStaticR49b.product n u‖ = 1 := by
  have h := RetargetStageR48b.coefficients_unit hκ n u hu
  unfold RetargetStageR48b.coefficients at h
  rwa [LinearIsometryEquiv.norm_map] at h

/-- At `ψ = u^{⊗N}` the initial support probability is the printed product-law quantity. -/
theorem missingInitial_eq_bornEmpty (hκ : 0 < κ) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) :
    UniformStaticR49b.missingInitial hκ n u p =
      bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) p.1 (UniformStaticR49b.product n u) := by
  unfold UniformStaticR49b.missingInitial
  exact (bornEmpty_eq_missing (Def044D1SpectralR51a.basis (L := L) hκ n) p.1
    (UniformStaticR49b.product n u)).symm

/-- At `ψ = u^{⊗N}` the final support probability is the printed product-law quantity. -/
theorem missingFinal_eq_bornEmpty (hκ : 0 < κ) (n : ℕ) (u : L2T L) (p : ℤ × ℤ) :
    UniformStaticR49b.missingFinal hκ n u p =
      bornEmpty (Def044D1SpectralR51a.basis (L := L) hκ n) p.2 (UniformStaticR49b.product n u) := by
  unfold UniformStaticR49b.missingFinal
  exact (bornEmpty_eq_missing (Def044D1SpectralR51a.basis (L := L) hκ n) p.2
    (UniformStaticR49b.product n u)).symm

theorem missingInitial_le_one (hκ : 0 < κ) (n : ℕ) (u : L2T L) (hu : ‖u‖ = 1) (p : ℤ × ℤ) :
    UniformStaticR49b.missingInitial hκ n u p ≤ 1 := by
  rw [missingInitial_eq_bornEmpty]
  have h := bornEmpty_le_norm_sq (Def044D1SpectralR51a.basis (L := L) hκ n) p.1
    (UniformStaticR49b.product n u)
  rw [product_norm_eq_one hκ n u hu] at h
  linarith

theorem missingFinal_le_one (hκ : 0 < κ) (n : ℕ) (u : L2T L) (hu : ‖u‖ = 1) (p : ℤ × ℤ) :
    UniformStaticR49b.missingFinal hκ n u p ≤ 1 := by
  rw [missingFinal_eq_bornEmpty]
  have h := bornEmpty_le_norm_sq (Def044D1SpectralR51a.basis (L := L) hκ n) p.2
    (UniformStaticR49b.product n u)
  rw [product_norm_eq_one hκ n u hu] at h
  linarith

end QuantumNLS.SupportPersistH01Born

#print axioms QuantumNLS.SupportPersistH01Born.bornEmpty_eq_missing
#print axioms QuantumNLS.SupportPersistH01Born.bornEmpty_lipschitz
#print axioms QuantumNLS.SupportPersistH01Born.bornEmpty_at_q06_gauge
#print axioms QuantumNLS.SupportPersistH01Born.missingInitial_eq_bornEmpty
#print axioms QuantumNLS.SupportPersistH01Born.missingFinal_eq_bornEmpty
