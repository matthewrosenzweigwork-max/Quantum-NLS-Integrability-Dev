import QuantumNLS.Prop023Number

/-! PROP-023 physical-form interface, stage 2: the physical Fock space in free occupation
coordinates.

`Phi : Fock L ≃ₗᵢ[ℂ] ℓ²(Occ)`, `x ↦ (coefficient x m)_m`, is a unitary (the repository's
`Ext006PhysicalVacuum.coefficient`, packaged: isometric by Parseval over the sectors, onto by
gluing sectorwise preimages).  The physical finite-support CCR core is the transport
`physCore = Phi⁻¹ ∘ coreEmbedding` of the repository's `Occupation.FS` (with `Cre`, `Ann`), so that

  `⟨physCore (Cre a (ket m)), x⟩ = √(m_a+1) · coefficient x (m + e_a)`,
  `⟨physCore (Ann a (ket m)), x⟩ = √(m_a) · coefficient x (m - e_a)`,
  `⟨physCore (ket m), x⟩ = coefficient x m`,

the same sqrt coefficients as `Ext006PhysicalVacuum.inner_core_Cre/Ann`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace QuantumNLS.Ext006PhysFockCoord
open Occupation OccupationHilbert BetheCoefficientTransform Ext025B3PhysicalSectors
  Ext006PhysicalVacuum
variable {L : ℝ} [Fact (0 < L)]

lemma coefficient_add (x y : Fock L) (m : Occ) :
    coefficient (x + y) m = coefficient x m + coefficient y m := by
  simp [coefficient, lp.coeFn_add]

lemma memL2 (x : Fock L) : Memℓp (coefficient x) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact (Prop023Number.summable_normSq x).congr fun m => by rw [Complex.sq_norm]

/-- The occupation coordinates of a physical vector, as an element of `ℓ²(Occ)`. -/
def coefL2 (x : Fock L) : L2 Occ := ⟨coefficient x, memL2 x⟩

lemma sum_sq_eq (x : Fock L) : ∑' m : Occ, ‖coefficient x m‖ ^ 2 = ‖x‖ ^ 2 := by
  have hx := lp.hasSum_norm (E := fun n => HN L n) (p := 2) (by norm_num) x
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hx
  have hsum : Summable fun m : Occ => ‖coefficient x m‖ ^ 2 :=
    (Prop023Number.summable_normSq x).congr fun m => by rw [Complex.sq_norm]
  have h1 : ENNReal.ofReal (∑' m : Occ, ‖coefficient x m‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
    calc ENNReal.ofReal (∑' m : Occ, ‖coefficient x m‖ ^ 2)
        = ∑' m : Occ, ENNReal.ofReal (‖coefficient x m‖ ^ 2) :=
          ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsum
      _ = ∑' m : Occ, Prop023FiniteModeLimit.mass x m := rfl
      _ = ∑' n : ℕ, ENNReal.ofReal (‖x n‖ ^ 2) := by
          have := Prop023FiniteModeLimit.numberExpectation_eq_occupation x (fun _ => 1)
          simpa [Ext006NumberPhase.numberExpectation] using this.symm
      _ = ENNReal.ofReal (∑' n : ℕ, ‖x n‖ ^ 2) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hx.summable).symm
      _ = ENNReal.ofReal (‖x‖ ^ 2) := by rw [hx.tsum_eq]
  exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun _ => sq_nonneg _) (sq_nonneg _)).1 h1

lemma norm_coefL2 (x : Fock L) : ‖coefL2 x‖ = ‖x‖ := by
  have h := lp.hasSum_norm (E := fun _ : Occ => ℂ) (p := 2) (by norm_num) (coefL2 x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  have h2 : ‖coefL2 x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← h.tsum_eq, ← sum_sq_eq x]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- The coefficient map as a linear isometry into `ℓ²(Occ)`. -/
def Phi0 : Fock L →ₗᵢ[ℂ] L2 Occ where
  toFun := coefL2
  map_add' x y := by
    apply lp.ext; funext m
    exact coefficient_add x y m
  map_smul' c x := by
    apply lp.ext; funext m
    exact coefficient_smul c x m
  norm_map' := norm_coefL2

lemma summable_sq' (c : L2 Occ) : Summable fun m : Occ => ‖c m‖ ^ 2 := by
  have hs := lp.hasSum_norm (E := fun _ : Occ => ℂ) (p := 2) (by norm_num) c
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs.summable

/-- The sector vector with coordinates `c` restricted to the arrays of total `N`. -/
def sectorOf (c : L2 Occ) (N : ℕ) : H N :=
  ⟨fun a : Arr N => c a.1, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact (summable_sq' c).comp_injective Subtype.val_injective⟩

lemma Phi0_surjective : Function.Surjective (Phi0 (L := L)) := by
  intro c
  let y0 : ∀ N : ℕ, HN L N := fun N => (occupationCoefficient (freeBasis L N)).symm (sectorOf c N)
  have hnorm : ∀ N, ‖y0 N‖ ^ 2 = ∑' a : Arr N, ‖c a.1‖ ^ 2 := by
    intro N
    have h := lp.hasSum_norm (E := fun _ : Arr N => ℂ) (p := 2) (by norm_num) (sectorOf c N)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    have : ‖y0 N‖ = ‖sectorOf c N‖ := LinearIsometryEquiv.norm_map _ _
    rw [this, ← h.tsum_eq]
    rfl
  have hmem : Memℓp y0 2 := by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hs : Summable (fun p : (Σ N : ℕ, Arr N) => ‖c p.2.1‖ ^ 2) :=
      (Equiv.summable_iff (Equiv.sigmaFiberEquiv (fun m : Occ => total m))).2 (summable_sq' c)
    have := hs.sigma
    exact this.congr fun N => (hnorm N).symm
  refine ⟨⟨y0, hmem⟩, ?_⟩
  apply lp.ext; funext m
  change coefficient (⟨y0, hmem⟩ : Fock L) m = c m
  unfold coefficient
  change (occupationCoefficient (freeBasis L (total m))
    ((occupationCoefficient (freeBasis L (total m))).symm (sectorOf c (total m)))) ⟨m, rfl⟩ = c m
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- **The unitary `Fock L ≃ ℓ²(Occ)` of free occupation coordinates.** -/
def Phi : Fock L ≃ₗᵢ[ℂ] L2 Occ := LinearIsometryEquiv.ofSurjective Phi0 Phi0_surjective

lemma Phi_apply (x : Fock L) (m : Occ) : Phi x m = coefficient x m := rfl

lemma inner_Phi_symm (e : L2 Occ) (x : Fock L) :
    inner ℂ (Phi.symm e) x = inner ℂ e (Phi x) := by
  rw [← Phi.inner_map_map (Phi.symm e) x, LinearIsometryEquiv.apply_symm_apply]

/-- The physical finite-support CCR core: the transport of the repository's `Occupation.FS`. -/
def physCore : FS →ₗ[ℂ] Fock L :=
  (Phi (L := L)).symm.toLinearEquiv.toLinearMap ∘ₗ coreEmbedding

lemma inner_physCore (v : FS) (x : Fock L) :
    inner ℂ (physCore v) x = inner ℂ (coreEmbedding v) (Phi x) := by
  change inner ℂ ((Phi (L := L)).symm (coreEmbedding v)) x = _
  exact inner_Phi_symm _ _

lemma inner_physCore_ket (m : Occ) (x : Fock L) :
    inner ℂ (physCore (ket m)) x = coefficient x m := by
  rw [inner_physCore, inner_core_ket]; rfl

lemma inner_physCore_Cre (a : ℤ) (m : Occ) (x : Fock L) :
    inner ℂ (physCore (Cre a (ket m))) x =
      (Real.sqrt ((m a : ℝ) + 1) : ℂ) * coefficient x (m + e a) := by
  rw [inner_physCore, inner_core_Cre]; rfl

lemma inner_physCore_Ann (a : ℤ) (m : Occ) (x : Fock L) :
    inner ℂ (physCore (Ann a (ket m))) x =
      (Real.sqrt (m a : ℝ) : ℂ) * coefficient x (m - e a) := by
  rw [inner_physCore, inner_core_Ann]; rfl

lemma physCore_ket (m : Occ) : physCore (ket m) = (Phi (L := L)).symm (lp.single 2 m (1 : ℂ)) := by
  change (Phi (L := L)).symm (coreEmbedding (ket m)) = _
  rw [coreEmbedding_ket]

/-- The physical vacuum `Ω`: the unit vector with free occupation array `0`. -/
def vac : Fock L := physCore (ket 0)

end QuantumNLS.Ext006PhysFockCoord
#print axioms QuantumNLS.Ext006PhysFockCoord.Phi
#print axioms QuantumNLS.Ext006PhysFockCoord.inner_physCore_Cre
#print axioms QuantumNLS.Ext006PhysFockCoord.inner_physCore_Ann
#print axioms QuantumNLS.Ext006PhysFockCoord.inner_physCore_ket
