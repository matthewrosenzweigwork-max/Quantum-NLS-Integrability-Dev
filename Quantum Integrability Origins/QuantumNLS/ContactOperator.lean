import QuantumNLS.ContactForm

/-!
# R-98129FE7 (`contact:thm:form`), remaining assertions: density, the associated self-adjoint
operator, compactness

Source (pinned PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`, `chapters/foundations/A01.tex:44`):
"The form is densely defined, closed, and nonnegative. Its unique associated self-adjoint nonnegative
operator `H_{N,c}` has compact resolvent."  Proof (as written): the form domain is dense by symmetrizing
trigonometric polynomials; the coercive form `q(φ,ψ)+⟨φ,ψ⟩` gives, by Riesz in the form norm, a unique
`Rf ∈ D(q)` with `q(φ,Rf)+⟨φ,Rf⟩ = ⟨φ,f⟩`; `R` is bounded, self-adjoint, injective (density),
positive; `H = R⁻¹ − I` is self-adjoint with domain `{ψ ∈ D(q) : q(φ,ψ) = ⟨φ,f⟩ ∀φ ∈ D(q)}`,
`Hψ = f`; compactness of `H¹ ↪ L²` by Fourier truncation gives compact `R`.

Frozen inputs (read-only): `ContactForm` `06da9b2b…` (closed nonnegative form on `H¹`), `CollisionTrace`
`e249be71…` (trace), `PhysicalEnergy` `01370715…` (physical `H¹`, `H¹_sym`).  No representation
result is assumed: every step is constructed here.

No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate Real InnerProductSpace
open MeasureTheory QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.CollisionTrace
  QuantumNLS.ContactForm QuantumNLS.Fourier QuantumNLS.PhysicalTensor

namespace QuantumNLS.ContactOperator

/-! ## §1 Permutation-invariant cubes in `ℤ^N` -/

section Cubes

variable {N : ℕ}

/-- The cube `{w : ‖w‖_∞ ≤ R}` in `ℤ^N`. -/
def cube (N : ℕ) (R : ℕ) : Finset (Fin N → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R

theorem mem_cube {R : ℕ} {w : Fin N → ℤ} : w ∈ cube N R ↔ ∀ l, |w l| ≤ R := by
  simp [cube, Fintype.mem_piFinset, abs_le]

theorem cube_mono {R R' : ℕ} (h : R ≤ R') : cube N R ⊆ cube N R' := fun w hw => by
  rw [mem_cube] at hw ⊢
  exact fun l => (hw l).trans (by exact_mod_cast h)

theorem exists_cube (S : Finset (Fin N → ℤ)) : ∃ R : ℕ, S ⊆ cube N R := by
  classical
  have h : ∀ w : Fin N → ℤ, ∃ R : ℕ, w ∈ cube N R := fun w => by
    refine ⟨(Finset.univ.sup fun l => (w l).natAbs), ?_⟩
    rw [mem_cube]
    intro l
    have := Finset.le_sup (f := fun l => (w l).natAbs) (Finset.mem_univ l)
    have h2 : (|w l| : ℤ) = ((w l).natAbs : ℤ) := Int.abs_eq_natAbs _
    rw [h2]
    exact_mod_cast this
  choose f hf using h
  refine ⟨S.sup f, fun w hw => ?_⟩
  exact cube_mono (Finset.le_sup hw) (hf w)

theorem cube_comp {R : ℕ} (σ : Equiv.Perm (Fin N)) {w : Fin N → ℤ} :
    w ∘ σ ∈ cube N R ↔ w ∈ cube N R := by
  rw [mem_cube, mem_cube]
  exact ⟨fun h l => by simpa using h (σ.symm l), fun h l => h (σ l)⟩

/-- Outside the cube of radius `R`, some coordinate has `|w_l| ≥ R+1`. -/
theorem exists_big {R : ℕ} {w : Fin N → ℤ} (h : w ∉ cube N R) : ∃ l, (R : ℝ) + 1 ≤ |(w l : ℝ)| := by
  rw [mem_cube, not_forall] at h
  obtain ⟨l, hl⟩ := h
  have hl := not_le.1 hl
  refine ⟨l, ?_⟩
  have : (R : ℤ) + 1 ≤ |w l| := by exact_mod_cast hl
  have h2 : (((R : ℤ) + 1 : ℤ) : ℝ) ≤ ((|w l| : ℤ) : ℝ) := by exact_mod_cast this
  simpa using h2

end Cubes

/-! ## §2 Compactness of `H¹(T_L^N) ↪ L²(T_L^N)` (Fourier truncation) -/

section Compact

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

theorem norm_mulCLM_le {ι : Type*} (c : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ n, |c n| ≤ M) :
    ‖mulCLM c M hM hc‖ ≤ M := by
  unfold mulCLM
  exact LinearMap.mkContinuous_norm_le _ hM _

/-- A multiplier supported on a finite set is a finite-rank, hence compact, operator. -/
theorem isCompactOperator_mulCLM_of_finite (c : (Fin N → ℤ) → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hc : ∀ n, |c n| ≤ M) (B : Finset (Fin N → ℤ)) (hB : ∀ w, w ∉ B → c w = 0) :
    IsCompactOperator (mulCLM c M hM hc : L2 (Fin N → ℤ) →L[ℂ] L2 (Fin N → ℤ)) := by
  classical
  set W : Submodule ℂ (L2 (Fin N → ℤ)) :=
    Submodule.span ℂ (Set.range fun w : B => (lp.single 2 (w : Fin N → ℤ) (1 : ℂ) : L2 (Fin N → ℤ)))
    with hW
  have : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hmem : ∀ x : L2 (Fin N → ℤ), mulCLM c M hM hc x ∈ W := by
    intro x
    have hx : mulCLM c M hM hc x =
        ∑ w ∈ B, ((c w : ℂ) * (x : (Fin N → ℤ) → ℂ) w) • (lp.single 2 w (1 : ℂ) : L2 (Fin N → ℤ)) := by
      apply Subtype.ext; funext w'
      rw [mulCLM_apply, lp.coeFn_sum, Finset.sum_apply]
      simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
      by_cases h : w' ∈ B
      · simp [h]
      · simp [h, hB w' h]
    rw [hx]
    exact Submodule.sum_mem _ fun w hw =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩)
  have h1 := isCompactOperator_of_locallyCompactSpace_dom
    ((mulCLM c M hM hc).codRestrict W hmem)
  have h2 := h1.clm_comp W.subtypeL
  exact h2

/-- `Σ_w`-truncated `A^{-1/2}`: multiplier `1_{cube R}/√a_N`. -/
def truncMul (L : ℝ) (N R : ℕ) : L2 (Fin N → ℤ) →L[ℂ] L2 (Fin N → ℤ) :=
  mulCLM (fun w => if w ∈ cube N R then (kinSqrt L N w)⁻¹ else 0) 1 zero_le_one (fun w => by
    split_ifs
    · rw [abs_of_pos (inv_pos.2 (by linarith [one_le_kinSqrt L N w]))]
      exact inv_le_one_of_one_le₀ (one_le_kinSqrt L N w)
    · simp)

/-- The tail multiplier `1_{cube R}ᶜ/√a_N`, of operator norm `≤ L/(2π(R+1))`. -/
def tailMul (L : ℝ) [Fact (0 < L)] (N R : ℕ) : L2 (Fin N → ℤ) →L[ℂ] L2 (Fin N → ℤ) :=
  mulCLM (fun w => if w ∈ cube N R then 0 else (kinSqrt L N w)⁻¹) (L / (2 * Real.pi * (R + 1)))
    (by have := Fact.out (p := 0 < L); positivity) (fun w => by
    have hL : 0 < L := Fact.out
    split_ifs with h
    · simp only [abs_zero]; positivity
    · obtain ⟨l, hl⟩ := exists_big h
      have hs : 0 < kinSqrt L N w := by linarith [one_le_kinSqrt L N w]
      rw [abs_of_pos (inv_pos.2 hs), inv_le_comm₀ hs (by positivity), inv_div]
      -- `2π(R+1)/L ≤ |freq(w_l)| ≤ √a`
      have h1 : freq L (w l) ^ 2 ≤ kinSqrt L N w ^ 2 := by
        rw [kinSqrt_sq]; unfold kinWeight
        have := Finset.single_le_sum (f := fun l => freq L (w l) ^ 2) (fun l _ => sq_nonneg _)
          (Finset.mem_univ l)
        linarith
      have h2 : |freq L (w l)| ≤ kinSqrt L N w := abs_le_of_sq_le_sq h1 hs.le
      have h3 : 2 * Real.pi * ((R : ℝ) + 1) / L ≤ |freq L (w l)| := by
        unfold freq
        rw [abs_div, abs_mul, abs_of_pos hL, abs_mul, abs_of_pos Real.pi_pos]
        simp only [abs_two]
        exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hL.le
      exact h3.trans h2)

theorem truncMul_add_tailMul (R : ℕ) : truncMul L N R + tailMul L N R = AhalfInv L N := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply Subtype.ext; funext w
  show ((truncMul L N R x : L2 (Fin N → ℤ)) : (Fin N → ℤ) → ℂ) w +
    ((tailMul L N R x : L2 (Fin N → ℤ)) : (Fin N → ℤ) → ℂ) w = (AhalfInv L N x : (Fin N → ℤ) → ℂ) w
  unfold truncMul tailMul
  rw [mulCLM_apply, mulCLM_apply]
  show _ + _ = ((((kinSqrt L N w)⁻¹ : ℝ)) : ℂ) * (x : (Fin N → ℤ) → ℂ) w
  by_cases h : w ∈ cube N R <;> simp [h]

omit [Fact (0 < L)] in
theorem isCompactOperator_truncMul (R : ℕ) : IsCompactOperator (truncMul L N R) :=
  isCompactOperator_mulCLM_of_finite _ _ _ _ (cube N R) fun w hw => by simp [hw]

theorem tendsto_truncMul :
    Filter.Tendsto (fun R : ℕ => truncMul L N R) Filter.atTop (nhds (AhalfInv L N)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hL : 0 < L := Fact.out
  have h0 : Filter.Tendsto (fun R : ℕ => L / (2 * Real.pi * ((R : ℝ) + 1))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun R : ℕ => (2 * Real.pi) * ((R : ℝ) + 1)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity)
        (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    exact h1.const_div_atTop L |> fun h => by simpa using h
  refine squeeze_zero (fun R => norm_nonneg _) (fun R => ?_) h0
  have : truncMul L N R - AhalfInv L N = -tailMul L N R := by
    rw [← truncMul_add_tailMul R]; abel
  rw [this, norm_neg]
  exact norm_mulCLM_le _ _ _ _

/-- **`AhalfInv` (`A^{-1/2}` on `ℓ²(ℤ^N)`) is compact**: norm limit of finite-rank truncations. -/
theorem isCompactOperator_AhalfInv : IsCompactOperator (AhalfInv L N) :=
  isCompactOperator_of_tendsto tendsto_truncMul (Filter.Eventually.of_forall isCompactOperator_truncMul)

/-- The inclusion `H¹ ↪ L²` factors as `U⁻¹ ∘ A^{-1/2} ∘ Ψ`. -/
theorem valCLM_eq : (PhysH1.valCLM : PhysH1 L N →L[ℂ] L2TN L N) =
    (momUnitary L N).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L AhalfInv L N ∘L
      (Psi (L := L) (N := N)).toContinuousLinearEquiv.toContinuousLinearMap := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply (momUnitary L N).injective
  apply Subtype.ext; funext w
  show (momUnitary L N x.val : (Fin N → ℤ) → ℂ) w = (momUnitary L N ((momUnitary L N).symm
    (AhalfInv L N (Psi x))) : (Fin N → ℤ) → ℂ) w
  rw [LinearIsometryEquiv.apply_symm_apply]
  show (coeffFun x w) = ((((kinSqrt L N w)⁻¹ : ℝ)) : ℂ) * ((Psi x : L2 (Fin N → ℤ)) w)
  rw [Psi_apply]
  have hs : (kinSqrt L N w : ℂ) ≠ 0 := by
    exact_mod_cast (by linarith [one_le_kinSqrt L N w] : kinSqrt L N w ≠ 0)
  push_cast
  field_simp

/-- **Compact embedding `H¹(T_L^N) ↪ L²(T_L^N)`** (Fourier truncation; source, proof of
`contact:thm:form`, last paragraph). -/
theorem isCompactOperator_valCLM : IsCompactOperator (PhysH1.valCLM : PhysH1 L N →L[ℂ] L2TN L N) := by
  rw [valCLM_eq]
  have h1 : IsCompactOperator (AhalfInv L N) := isCompactOperator_AhalfInv
  have h2 := h1.comp_clm (Psi (L := L) (N := N)).toContinuousLinearEquiv.toContinuousLinearMap
  have h3 := h2.clm_comp (momUnitary L N).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact h3

end Compact

/-! ## §3 The symmetric space `L²_sym` and density of `H¹_sym` in it -/

section Density

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `L²_sym(T_L^N)`: the permutation-invariant wave functions (a closed subspace of `L²(T_L^N)`). -/
def SymL2 (L : ℝ) [Fact (0 < L)] (N : ℕ) : Submodule ℂ (L2TN L N) :=
  ⨅ σ : Equiv.Perm (Fin N),
    LinearMap.ker ((physPerm (L := L) σ).toLinearMap - LinearMap.id)

theorem mem_SymL2_iff (F : L2TN L N) :
    F ∈ SymL2 L N ↔ ∀ σ : Equiv.Perm (Fin N), physPerm σ F = F := by
  unfold SymL2
  rw [Submodule.mem_iInf]
  refine forall_congr' fun σ => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

theorem isClosed_SymL2 : IsClosed ((SymL2 L N : Submodule ℂ (L2TN L N)) : Set (L2TN L N)) := by
  have : ((SymL2 L N : Submodule ℂ (L2TN L N)) : Set (L2TN L N)) =
      ⋂ σ : Equiv.Perm (Fin N), {F : L2TN L N | physPerm σ F = F} := by
    ext F
    simp only [SetLike.mem_coe, Set.mem_iInter]
    exact mem_SymL2_iff F
  rw [this]
  exact isClosed_iInter fun σ => isClosed_eq (physPerm σ).continuous continuous_id

instance : CompleteSpace (SymL2 L N) := isClosed_SymL2.completeSpace_coe

/-- The finite Fourier truncation to the cube of radius `R` of the `L²` function `F`
(a trigonometric polynomial, an element of `H¹`). -/
def cubeTrunc (R : ℕ) (F : L2TN L N) : PhysH1 L N :=
  trigElem (L := L) (cube N R) (fun w => (momUnitary L N F : (Fin N → ℤ) → ℂ) w)

/-- Truncations of a symmetric function are symmetric (the cube is permutation invariant). -/
theorem cubeTrunc_mem_sym {F : L2TN L N} (hF : F ∈ SymL2 L N) (R : ℕ) :
    cubeTrunc R F ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) := by
  rw [PhysH1.mem_sym_iff, isSymm_iff_coeff]
  intro σ w
  have hco : ∀ (σ : Equiv.Perm (Fin N)) (w : Fin N → ℤ),
      (momUnitary L N F : (Fin N → ℤ) → ℂ) (w ∘ σ) =
      (momUnitary L N F : (Fin N → ℤ) → ℂ) w := (isSymm_iff_coeff F).1 ((mem_SymL2_iff F).1 hF)
  have h1 : ∀ w, (momUnitary L N (cubeTrunc R F).val : (Fin N → ℤ) → ℂ) w =
      if w ∈ cube N R then (momUnitary L N F : (Fin N → ℤ) → ℂ) w else 0 := by
    intro w
    unfold cubeTrunc
    rw [momUnitary_trigElem]
    rfl
  rw [h1, h1]
  by_cases h : w ∈ cube N R
  · have h' : w ∘ σ ∈ cube N R := (cube_comp σ).2 h
    simp [h, h', hco σ w]
  · have h' : w ∘ σ ∉ cube N R := fun hh => h ((cube_comp σ).1 hh)
    simp [h, h']

/-- The `L²` class of the truncation is the Fourier partial sum. -/
theorem momUnitary_cubeTrunc (R : ℕ) (F : L2TN L N) :
    momUnitary L N (cubeTrunc R F).val =
      ∑ w ∈ cube N R, lp.single 2 w ((momUnitary L N F : L2 (Fin N → ℤ)) w) := by
  unfold cubeTrunc
  rw [momUnitary_trigElem]
  apply Subtype.ext; funext w'
  rw [finVec_apply, lp.coeFn_sum, Finset.sum_apply]
  simp [lp.single_apply, Pi.single_apply]

/-- **Density** (source: "dense by symmetrizing trigonometric polynomials"): the permutation-invariant
cube truncations of `F ∈ L²_sym` lie in `H¹_sym` and converge to `F` in `L²`. -/
theorem cubeTrunc_tendsto (F : L2TN L N) :
    Filter.Tendsto (fun R : ℕ => (cubeTrunc R F).val) Filter.atTop (nhds F) := by
  have hs := lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) (momUnitary L N F)
  have ht : Filter.Tendsto (fun S : Finset (Fin N → ℤ) =>
      ∑ w ∈ S, lp.single 2 w ((momUnitary L N F : L2 (Fin N → ℤ)) w)) Filter.atTop
      (nhds (momUnitary L N F)) := hs
  have hcof : Filter.Tendsto (fun R : ℕ => cube N R) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro S
    obtain ⟨R0, hR0⟩ := exists_cube S
    exact ⟨R0, fun R hR => hR0.trans (cube_mono hR)⟩
  have h2 := ((momUnitary L N).symm.continuous.tendsto _).comp (ht.comp hcof)
  rw [LinearIsometryEquiv.symm_apply_apply] at h2
  refine h2.congr fun R => ?_
  show (momUnitary L N).symm (∑ w ∈ cube N R,
    lp.single 2 w ((momUnitary L N F : L2 (Fin N → ℤ)) w)) = _
  rw [← momUnitary_cubeTrunc, LinearIsometryEquiv.symm_apply_apply]

/-- The inclusion `H¹_sym → L²_sym`. -/
def valSym : (PhysH1.sym : Submodule ℂ (PhysH1 L N)) →L[ℂ] SymL2 L N :=
  ((PhysH1.valCLM : PhysH1 L N →L[ℂ] L2TN L N).comp
    (PhysH1.sym : Submodule ℂ (PhysH1 L N)).subtypeL).codRestrict (SymL2 L N) (fun x => by
      rw [mem_SymL2_iff]
      exact (PhysH1.mem_sym_iff x.1).1 x.2)

@[simp] theorem valSym_val (x : (PhysH1.sym : Submodule ℂ (PhysH1 L N))) :
    ((valSym x : SymL2 L N) : L2TN L N) = x.1.val := rfl

/-- **`H¹_sym` is dense in `L²_sym`**: the inclusion has dense range. -/
theorem denseRange_valSym : DenseRange (valSym : (PhysH1.sym : Submodule ℂ (PhysH1 L N)) →L[ℂ]
    SymL2 L N) := by
  intro F
  rw [mem_closure_iff_seq_limit]
  refine ⟨fun R => valSym ⟨cubeTrunc R (F : L2TN L N), cubeTrunc_mem_sym F.2 R⟩,
    fun R => ⟨_, rfl⟩, ?_⟩
  rw [tendsto_subtype_rng]
  exact cubeTrunc_tendsto (F : L2TN L N)

end Density

/-! ## §4 The coercive form on `H¹_sym` and its Riesz operator -/

section Resolvent

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The form domain `H¹_sym(T_L^N)` as a Hilbert space (energy norm). -/
abbrev VSym (L : ℝ) [Fact (0 < L)] (N : ℕ) : Type :=
  ↥(PhysH1.sym : Submodule ℂ (PhysH1 L N))

theorem val_add' (φ ψ : PhysH1 L N) : (φ + ψ).val = φ.val + ψ.val :=
  (PhysH1.valₗ (L := L) (k := N)).map_add φ ψ

theorem val_smul' (r : ℂ) (φ : PhysH1 L N) : (r • φ).val = r • φ.val :=
  (PhysH1.valₗ (L := L) (k := N)).map_smul r φ

/-- `B_c(φ,ψ) = q_{N,c}(φ,ψ) + ⟨φ,ψ⟩_{L²}`: the coercive form of the source's variational
resolvent (conjugate-linear in `φ`, linear in `ψ`). -/
def Bform (c : ℝ) (φ ψ : VSym L N) : ℂ := q c φ.1 ψ.1 + ⟪φ.1.val, ψ.1.val⟫_ℂ

theorem Bform_add_left (c : ℝ) (φ φ' ψ : VSym L N) :
    Bform c (φ + φ') ψ = Bform c φ ψ + Bform c φ' ψ := by
  unfold Bform
  have : (φ + φ' : VSym L N).1 = φ.1 + φ'.1 := rfl
  rw [this, q_add_left, val_add', inner_add_left]
  ring

theorem Bform_smul_left (c : ℝ) (r : ℂ) (φ ψ : VSym L N) :
    Bform c (r • φ) ψ = conj r * Bform c φ ψ := by
  unfold Bform
  have : (r • φ : VSym L N).1 = r • φ.1 := rfl
  rw [this, q_smul_left, val_smul', inner_smul_left]
  ring

theorem Bform_add_right (c : ℝ) (φ ψ ψ' : VSym L N) :
    Bform c φ (ψ + ψ') = Bform c φ ψ + Bform c φ ψ' := by
  unfold Bform
  have : (ψ + ψ' : VSym L N).1 = ψ.1 + ψ'.1 := rfl
  rw [this, q_add_right, val_add', inner_add_right]
  ring

theorem Bform_smul_right (c : ℝ) (r : ℂ) (φ ψ : VSym L N) :
    Bform c φ (r • ψ) = r * Bform c φ ψ := by
  unfold Bform
  have : (r • ψ : VSym L N).1 = r • ψ.1 := rfl
  rw [this, q_smul_right, val_smul', inner_smul_right]
  ring

/-- **Hermitian symmetry of the form.** -/
theorem q_conj_symm (c : ℝ) (φ ψ : PhysH1 L N) : conj (q c φ ψ) = q c ψ φ := by
  simp only [q, kinSum, contactSum, map_add, map_mul, map_sum, inner_conj_symm,
    Complex.conj_ofReal]

theorem Bform_conj_symm (c : ℝ) (φ ψ : VSym L N) : conj (Bform c φ ψ) = Bform c ψ φ := by
  unfold Bform
  rw [map_add, q_conj_symm, inner_conj_symm]

theorem norm_Dj_le (j : Fin N) (x : PhysH1 L N) : ‖Dj j x‖ ≤ ‖x‖ := by
  have h1 : ‖Dj j x‖ ^ 2 ≤ ∑ j', ‖Dj j' x‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖Dj j' x‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  rw [sum_norm_sq_Dj] at h1
  have h2 : ‖Dj j x‖ ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x.val‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

theorem norm_Tpair_le (p : Pair N) (x : PhysH1 L N) : ‖Tpair p x‖ ≤ (1 + L⁻¹) * ‖x‖ := by
  have hL : 0 < L := Fact.out
  have h1 : ‖Tpair p x‖ ^ 2 ≤ (1 + L⁻¹) * ‖x‖ ^ 2 :=
    norm_sq_traceMap_le p.1.1 p.1.2 (ne_of_lt p.2) x
  have hc : 1 ≤ 1 + L⁻¹ := by linarith [inv_nonneg.2 hL.le]
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [mul_pow]
  nlinarith [sq_nonneg ‖x‖]

/-- A bound for the coercive form. -/
def Cform (L : ℝ) (N : ℕ) (c : ℝ) : ℝ :=
  N + 2 * c * (Fintype.card (Pair N) * (1 + L⁻¹) ^ 2) + 1

theorem Cform_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ Cform L N c := by
  have hL : 0 < L := Fact.out
  unfold Cform
  positivity

theorem norm_Bform_le {c : ℝ} (hc : 0 ≤ c) (φ ψ : VSym L N) :
    ‖Bform c φ ψ‖ ≤ Cform L N c * ‖φ‖ * ‖ψ‖ := by
  have hL : 0 < L := Fact.out
  have hφ : ‖φ.1‖ = ‖φ‖ := rfl
  have hψ : ‖ψ.1‖ = ‖ψ‖ := rfl
  have h0 : 0 ≤ ‖φ‖ * ‖ψ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  -- kinetic part
  have hk : ‖kinSum φ.1 ψ.1‖ ≤ N * (‖φ‖ * ‖ψ‖) := by
    unfold kinSum
    calc ‖∑ j, ⟪Dj j φ.1, Dj j ψ.1⟫_ℂ‖ ≤ ∑ j, ‖⟪Dj j φ.1, Dj j ψ.1⟫_ℂ‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin N, ‖φ‖ * ‖ψ‖ := Finset.sum_le_sum fun j _ =>
          (norm_inner_le_norm _ _).trans (by
            have := norm_Dj_le j φ.1
            have := norm_Dj_le j ψ.1
            exact mul_le_mul (by assumption) (by assumption) (norm_nonneg _) (norm_nonneg _))
      _ = N * (‖φ‖ * ‖ψ‖) := by simp
  -- contact part
  have hcont : ‖contactSum φ.1 ψ.1‖ ≤ Fintype.card (Pair N) * (1 + L⁻¹) ^ 2 * (‖φ‖ * ‖ψ‖) := by
    unfold contactSum
    calc ‖∑ p : Pair N, ⟪Tpair p φ.1, Tpair p ψ.1⟫_ℂ‖
        ≤ ∑ p : Pair N, ‖⟪Tpair p φ.1, Tpair p ψ.1⟫_ℂ‖ := norm_sum_le _ _
      _ ≤ ∑ _p : Pair N, (1 + L⁻¹) ^ 2 * (‖φ‖ * ‖ψ‖) := Finset.sum_le_sum fun p _ =>
          (norm_inner_le_norm _ _).trans (by
            have h1 := norm_Tpair_le p φ.1
            have h2 := norm_Tpair_le p ψ.1
            calc ‖Tpair p φ.1‖ * ‖Tpair p ψ.1‖ ≤ ((1 + L⁻¹) * ‖φ‖) * ((1 + L⁻¹) * ‖ψ‖) :=
                  mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
              _ = (1 + L⁻¹) ^ 2 * (‖φ‖ * ‖ψ‖) := by ring)
      _ = Fintype.card (Pair N) * (1 + L⁻¹) ^ 2 * (‖φ‖ * ‖ψ‖) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hl2 : ‖⟪φ.1.val, ψ.1.val⟫_ℂ‖ ≤ ‖φ‖ * ‖ψ‖ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (PhysH1.norm_val_le φ.1) (PhysH1.norm_val_le ψ.1)
      (norm_nonneg _) (norm_nonneg _))
  unfold Bform q Cform
  calc ‖kinSum φ.1 ψ.1 + ((2 * c : ℝ) : ℂ) * contactSum φ.1 ψ.1 + ⟪φ.1.val, ψ.1.val⟫_ℂ‖
      ≤ ‖kinSum φ.1 ψ.1‖ + ‖((2 * c : ℝ) : ℂ)‖ * ‖contactSum φ.1 ψ.1‖ + ‖⟪φ.1.val, ψ.1.val⟫_ℂ‖ := by
        have e1 := norm_add_le (kinSum φ.1 ψ.1 + ((2 * c : ℝ) : ℂ) * contactSum φ.1 ψ.1)
          ⟪φ.1.val, ψ.1.val⟫_ℂ
        have e2 := norm_add_le (kinSum φ.1 ψ.1) (((2 * c : ℝ) : ℂ) * contactSum φ.1 ψ.1)
        have e3 := norm_mul (((2 * c : ℝ) : ℂ)) (contactSum φ.1 ψ.1)
        linarith
    _ ≤ N * (‖φ‖ * ‖ψ‖) + 2 * c * (Fintype.card (Pair N) * (1 + L⁻¹) ^ 2 * (‖φ‖ * ‖ψ‖)) +
          ‖φ‖ * ‖ψ‖ := by
        have h2c : ‖((2 * c : ℝ) : ℂ)‖ = 2 * c := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        rw [h2c]
        have := mul_le_mul_of_nonneg_left hcont (by positivity : (0:ℝ) ≤ 2 * c)
        linarith
    _ = (N + 2 * c * (Fintype.card (Pair N) * (1 + L⁻¹) ^ 2) + 1) * ‖φ‖ * ‖ψ‖ := by ring

/-! ### The Riesz operator `M_c` of the coercive form -/

section Riesz

variable {c : ℝ} (hc : 0 ≤ c)

/-- The bounded sesquilinear form `B_c` on `H¹_sym`. -/
def BformCLM (c : ℝ) (hc : 0 ≤ c) : VSym L N →L⋆[ℂ] VSym L N →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (Bform c) (Bform_add_left c)
      (fun r φ ψ => by rw [smul_eq_mul]; exact Bform_smul_left c r φ ψ) (Bform_add_right c)
      (fun r φ ψ => by rw [smul_eq_mul]; exact Bform_smul_right c r φ ψ))
    (Cform L N c) (norm_Bform_le hc)

theorem BformCLM_apply (φ ψ : VSym L N) : BformCLM c hc φ ψ = Bform c φ ψ := rfl

/-- **The Riesz operator** `M_c : H¹_sym → H¹_sym` with `⟪M_c φ, ψ⟫_{H¹} = q(φ,ψ) + ⟨φ,ψ⟩_{L²}`
(Riesz representation of the bounded form, constructed). -/
def Mop (c : ℝ) (hc : 0 ≤ c) : VSym L N →L[ℂ] VSym L N :=
  InnerProductSpace.continuousLinearMapOfBilin (BformCLM c hc)

theorem inner_Mop_left (φ ψ : VSym L N) : ⟪Mop c hc φ, ψ⟫_ℂ = Bform c φ ψ := by
  unfold Mop
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

theorem inner_Mop_right (φ ψ : VSym L N) : ⟪φ, Mop c hc ψ⟫_ℂ = Bform c φ ψ := by
  rw [← inner_conj_symm, inner_Mop_left, Bform_conj_symm]

theorem Mop_symm (φ ψ : VSym L N) : ⟪Mop c hc φ, ψ⟫_ℂ = ⟪φ, Mop c hc ψ⟫_ℂ := by
  rw [inner_Mop_left, inner_Mop_right]

/-- `re ⟪ψ, M_c ψ⟫ = q[ψ] + ‖ψ‖²_{L²}` (the form norm squared). -/
theorem re_inner_Mop_self (ψ : VSym L N) : (⟪ψ, Mop c hc ψ⟫_ℂ).re = formNormSq c ψ.1 := by
  rw [inner_Mop_right]
  unfold Bform formNormSq
  rw [Complex.add_re, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/-- **Coercivity**: `‖ψ‖²_{H¹} ≤ re ⟪ψ, M_c ψ⟫` (the source's `q[ψ]+‖ψ‖² ≥ ‖ψ‖²_{H¹}`). -/
theorem coercive_Mop (ψ : VSym L N) : ‖ψ‖ ^ 2 ≤ (⟪ψ, Mop c hc ψ⟫_ℂ).re := by
  rw [re_inner_Mop_self]
  exact H1_le_formNormSq hc ψ.1

theorem norm_le_norm_Mop (ψ : VSym L N) : ‖ψ‖ ≤ ‖Mop c hc ψ‖ := by
  have h1 := coercive_Mop hc ψ
  have h2 : (⟪ψ, Mop c hc ψ⟫_ℂ).re ≤ ‖ψ‖ * ‖Mop c hc ψ‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  by_cases h0 : ‖ψ‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hp : 0 < ‖ψ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have : ‖ψ‖ * ‖ψ‖ ≤ ‖ψ‖ * ‖Mop c hc ψ‖ := by nlinarith
    exact le_of_mul_le_mul_left this hp

theorem Mop_ker : LinearMap.ker (Mop (L := L) (N := N) c hc).toLinearMap = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro ψ h
  have := norm_le_norm_Mop hc ψ
  have h0 : ‖ψ‖ ≤ 0 := by
    have : ‖Mop c hc ψ‖ = 0 := by
      have h' : Mop c hc ψ = 0 := h
      rw [h', norm_zero]
    linarith
  exact norm_le_zero_iff.1 h0

theorem Mop_range : LinearMap.range (Mop (L := L) (N := N) c hc).toLinearMap = ⊤ := by
  have hclosed : IsClosed (Set.range (Mop c hc : VSym L N →L[ℂ] VSym L N)) := by
    have hanti : AntilipschitzWith 1 (Mop c hc : VSym L N →L[ℂ] VSym L N) :=
      (Mop c hc).antilipschitz_of_bound (K := 1) (fun x => by simpa using norm_le_norm_Mop hc x)
    exact hanti.isClosed_range (Mop c hc).uniformContinuous
  have hdense : Dense (Set.range (Mop c hc : VSym L N →L[ℂ] VSym L N)) := by
    have horth : (LinearMap.range (Mop (L := L) (N := N) c hc).toLinearMap)ᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      rw [Submodule.mem_orthogonal] at hy
      have h0 : ∀ x : VSym L N, ⟪x, Mop c hc y⟫_ℂ = 0 := fun x => by
        rw [← Mop_symm]
        exact hy (Mop c hc x) ⟨x, rfl⟩
      have h1 : Mop c hc y = 0 := inner_self_eq_zero.1 (by
        have := h0 (Mop c hc y)
        rwa [← inner_conj_symm, map_eq_zero] at this)
      have h2 := norm_le_norm_Mop hc y
      rw [h1, norm_zero] at h2
      exact norm_le_zero_iff.1 h2
    have hd := Submodule.topologicalClosure_eq_top_iff.2 horth
    intro z
    have hz : z ∈ (LinearMap.range (Mop (L := L) (N := N) c hc).toLinearMap).topologicalClosure := by
      rw [hd]; trivial
    have hz' : z ∈ closure ((LinearMap.range (Mop (L := L) (N := N) c hc).toLinearMap :
        Submodule ℂ (VSym L N)) : Set (VSym L N)) := by
      rw [← Submodule.topologicalClosure_coe]; exact hz
    simpa [LinearMap.coe_range] using hz'
  rw [Submodule.eq_top_iff']
  intro z
  have := hdense z
  rw [hclosed.closure_eq] at this
  exact this

/-- The bounded inverse `M_c⁻¹`. -/
def Minv (c : ℝ) (hc : 0 ≤ c) : VSym L N →L[ℂ] VSym L N :=
  (ContinuousLinearEquiv.ofBijective (Mop c hc) (Mop_ker hc) (Mop_range hc)).symm.toContinuousLinearMap

theorem Mop_Minv (y : VSym L N) : Mop c hc (Minv c hc y) = y :=
  (ContinuousLinearEquiv.ofBijective (Mop c hc) (Mop_ker hc) (Mop_range hc)).apply_symm_apply y

theorem Minv_Mop (x : VSym L N) : Minv c hc (Mop c hc x) = x :=
  (ContinuousLinearEquiv.ofBijective (Mop c hc) (Mop_ker hc) (Mop_range hc)).symm_apply_apply x

theorem Minv_symm (x y : VSym L N) : ⟪Minv c hc x, y⟫_ℂ = ⟪x, Minv c hc y⟫_ℂ := by
  have h1 : ⟪Minv c hc x, y⟫_ℂ = ⟪Minv c hc x, Mop c hc (Minv c hc y)⟫_ℂ := by rw [Mop_Minv]
  rw [h1, ← Mop_symm, Mop_Minv]

/-- `‖M_c⁻¹ x‖² ≤ re ⟪x, M_c⁻¹ x⟫`: `M_c⁻¹` is positive and definite. -/
theorem norm_sq_Minv_le (x : VSym L N) : ‖Minv c hc x‖ ^ 2 ≤ (⟪x, Minv c hc x⟫_ℂ).re := by
  have h := coercive_Mop hc (Minv c hc x)
  rw [Mop_Minv] at h
  rw [← inner_conj_symm, Complex.conj_re]
  exact h

end Riesz

/-! ### The variational resolvent `R_c : L²_sym → L²_sym` -/

section ResolventOp

variable {c : ℝ} (hc : 0 ≤ c)

/-- `G = (val)†`, the adjoint of the inclusion `H¹_sym → L²_sym`. -/
def Gop : SymL2 L N →L[ℂ] VSym L N := (valSym (L := L) (N := N)).adjoint

/-- **The variational resolvent** `R f = val (M_c⁻¹ val† f)`: the unique `Rf ∈ H¹_sym` with
`q(φ,Rf) + ⟨φ,Rf⟩ = ⟨φ,f⟩` for all `φ ∈ H¹_sym` (source, proof of `contact:thm:form`). -/
def Rop (c : ℝ) (hc : 0 ≤ c) : SymL2 L N →L[ℂ] SymL2 L N :=
  (valSym (L := L) (N := N)).comp ((Minv c hc).comp (Gop (L := L) (N := N)))

theorem Rop_apply (f : SymL2 L N) :
    Rop c hc f = valSym (Minv c hc (Gop f)) := rfl

/-- The representing vector `ψ_f = M_c⁻¹ G f ∈ H¹_sym`. -/
def psi (c : ℝ) (hc : 0 ≤ c) (f : SymL2 L N) : VSym L N := Minv c hc (Gop f)

theorem Rop_eq_valSym_psi (f : SymL2 L N) : Rop c hc f = valSym (psi c hc f) := rfl

/-- **The source's variational equation**: for all `φ ∈ H¹_sym`,
`q(φ, ψ_f) + ⟨φ, ψ_f⟩ = ⟨φ, f⟩`. -/
theorem resolvent_eq (f : SymL2 L N) (φ : VSym L N) :
    Bform c φ (psi c hc f) = ⟪(valSym φ : SymL2 L N), f⟫_ℂ := by
  rw [← inner_Mop_right hc, psi, Mop_Minv]
  exact ContinuousLinearMap.adjoint_inner_right (valSym (L := L) (N := N)) φ f

/-- `R` is symmetric (self-adjoint as a bounded operator). -/
theorem Rop_symm (f g : SymL2 L N) : ⟪Rop c hc f, g⟫_ℂ = ⟪f, Rop c hc g⟫_ℂ := by
  have h1 : ⟪Rop c hc f, g⟫_ℂ = ⟪Minv c hc (Gop f), Gop g⟫_ℂ := by
    rw [Rop_apply]
    exact (ContinuousLinearMap.adjoint_inner_right (valSym (L := L) (N := N)) _ g).symm
  have h2 : ⟪f, Rop c hc g⟫_ℂ = ⟪Gop f, Minv c hc (Gop g)⟫_ℂ := by
    rw [Rop_apply]
    exact (ContinuousLinearMap.adjoint_inner_left (valSym (L := L) (N := N)) _ f).symm
  rw [h1, h2, Minv_symm]

theorem Rop_isSelfAdjoint : IsSelfAdjoint (Rop c hc : SymL2 L N →L[ℂ] SymL2 L N) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 (fun f g => Rop_symm hc f g)

/-- **Positivity of `R`**: `re ⟪f, R f⟫ ≥ ‖M_c⁻¹ G f‖² ≥ 0`. -/
theorem Rop_pos (f : SymL2 L N) :
    ‖psi c hc f‖ ^ 2 ≤ (⟪f, Rop c hc f⟫_ℂ).re := by
  have h : ⟪f, Rop c hc f⟫_ℂ = ⟪Gop f, Minv c hc (Gop f)⟫_ℂ := by
    rw [Rop_apply]
    exact (ContinuousLinearMap.adjoint_inner_left (valSym (L := L) (N := N)) _ f).symm
  rw [h]
  exact norm_sq_Minv_le hc (Gop f)

/-- **Injectivity of `R`** (source: "injectivity follows from density of the form domain"). -/
theorem Rop_injective : Function.Injective (Rop c hc : SymL2 L N →L[ℂ] SymL2 L N) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h1 : ⟪f, Rop c hc f⟫_ℂ = 0 := by rw [hf, inner_zero_right]
  have h2 := Rop_pos hc f
  rw [h1, Complex.zero_re] at h2
  have h3 : psi c hc f = 0 := norm_le_zero_iff.1 (by nlinarith [norm_nonneg (psi c hc f)])
  have h4 : Gop f = 0 := by
    have := congrArg (Mop c hc) h3
    rw [psi, Mop_Minv, map_zero] at this
    exact this
  -- `f ⟂ range(val)`, which is dense
  have h5 : ∀ φ : VSym L N, ⟪f, (valSym φ : SymL2 L N)⟫_ℂ = 0 := fun φ => by
    have := (ContinuousLinearMap.adjoint_inner_left (valSym (L := L) (N := N)) φ f)
    rw [← this]
    show ⟪Gop f, φ⟫_ℂ = 0
    rw [h4, inner_zero_left]
  have hcl : IsClosed {y : SymL2 L N | ⟪f, y⟫_ℂ = 0} :=
    isClosed_eq (innerSL ℂ f).continuous continuous_const
  have h6 : ∀ y : SymL2 L N, ⟪f, y⟫_ℂ = 0 := fun y => by
    have hy : y ∈ closure (Set.range (valSym (L := L) (N := N))) := denseRange_valSym y
    have hsub : Set.range (valSym (L := L) (N := N)) ⊆ {y : SymL2 L N | ⟪f, y⟫_ℂ = 0} := by
      rintro _ ⟨φ, rfl⟩; exact h5 φ
    exact (closure_minimal hsub hcl) hy
  exact inner_self_eq_zero.1 (h6 f)

/-- `val : H¹_sym → L²_sym` is compact (Fourier truncation). -/
theorem isCompactOperator_valSym :
    IsCompactOperator (valSym : VSym L N →L[ℂ] SymL2 L N) := by
  have h : IsCompactOperator ((PhysH1.valCLM : PhysH1 L N →L[ℂ] L2TN L N) ∘
      ((PhysH1.sym : Submodule ℂ (PhysH1 L N)).subtypeL)) :=
    isCompactOperator_valCLM.comp_clm _
  obtain ⟨K, hK, hKf⟩ := h
  refine ⟨(Subtype.val : SymL2 L N → L2TN L N) ⁻¹' K, ?_, hKf⟩
  exact isClosed_SymL2.isClosedEmbedding_subtypeVal.isCompact_preimage hK

/-- **Compact resolvent**: `R_c` is a compact operator on `L²_sym`. -/
theorem isCompactOperator_Rop : IsCompactOperator (Rop c hc : SymL2 L N →L[ℂ] SymL2 L N) :=
  (isCompactOperator_valSym (L := L) (N := N)).comp_clm _

end ResolventOp

/-! ### The associated operator `R⁻¹ = H + I` and `H` -/

section Operator

open scoped LinearPMap

variable {c : ℝ} (hc : 0 ≤ c)

/-- `R⁻¹` as an unbounded operator on `L²_sym`, with domain `range R` (the injectivity of `R` makes
it well defined). -/
def Tinv (c : ℝ) (hc : 0 ≤ c) : SymL2 L N →ₗ.[ℂ] SymL2 L N where
  domain := LinearMap.range (Rop c hc).toLinearMap
  toFun := (LinearEquiv.ofInjective (Rop c hc).toLinearMap (Rop_injective hc)).symm.toLinearMap

theorem mem_Tinv_domain (g : SymL2 L N) : Rop c hc g ∈ (Tinv c hc).domain := ⟨g, rfl⟩

theorem Tinv_Rop (g : SymL2 L N) : Tinv c hc ⟨Rop c hc g, mem_Tinv_domain hc g⟩ = g :=
  (LinearEquiv.ofInjective (Rop c hc).toLinearMap (Rop_injective hc)).symm_apply_apply g

theorem exists_of_mem_Tinv_domain (x : (Tinv (L := L) (N := N) c hc).domain) :
    ∃ g : SymL2 L N, Rop c hc g = (x : SymL2 L N) := by
  obtain ⟨g, hg⟩ := x.2
  exact ⟨g, hg⟩

theorem Tinv_apply_of_eq (x : (Tinv (L := L) (N := N) c hc).domain) (g : SymL2 L N) (h : Rop c hc g = (x : SymL2 L N)) :
    Tinv c hc x = g := by
  have hx : x = ⟨Rop c hc g, mem_Tinv_domain hc g⟩ := Subtype.ext h.symm
  rw [hx]
  exact Tinv_Rop hc g

/-- **`R⁻¹ = H + I` is self-adjoint** (source: "the inverse of a bounded injective self-adjoint
operator on its dense range is self-adjoint"), here derived from the abstract criterion
`isSelfAdjoint_of_inverse` (symmetric, with bounded symmetric right inverse `R`). -/
theorem Tinv_isSelfAdjoint : IsSelfAdjoint (Tinv c hc : SymL2 L N →ₗ.[ℂ] SymL2 L N) := by
  refine isSelfAdjoint_of_inverse (Tinv c hc) (Rop c hc) (fun x y => Rop_symm hc x y)
    (fun y => mem_Tinv_domain hc y) (fun y => Tinv_Rop hc y) ?_
  intro x y
  obtain ⟨f, hf⟩ := exists_of_mem_Tinv_domain hc x
  obtain ⟨g, hg⟩ := exists_of_mem_Tinv_domain hc y
  rw [Tinv_apply_of_eq hc x f hf, Tinv_apply_of_eq hc y g hg, ← hf, ← hg]
  exact (Rop_symm hc f g).symm

end Operator

end Resolvent

/-! ## §5 Shifting a self-adjoint operator by the identity -/

section Shift

open scoped LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `T - I`, on the domain of `T`. -/
def shiftPMap (T : E →ₗ.[ℂ] E) : E →ₗ.[ℂ] E where
  domain := T.domain
  toFun := T.toFun - T.domain.subtype

omit [CompleteSpace E] in
theorem shiftPMap_apply (T : E →ₗ.[ℂ] E) (x : (shiftPMap T).domain) :
    shiftPMap T x = T ⟨x.1, x.2⟩ - x.1 := rfl

/-- **If `T` is self-adjoint then so is `T - I`.** -/
theorem isSelfAdjoint_shift {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (shiftPMap T) := by
  have hd : Dense (T.domain : Set E) := hT.dense_domain
  have hTeq : T† = T := LinearPMap.isSelfAdjoint_def.1 hT
  -- symmetry of `T`
  have hsym : ∀ x y : T.domain, ⟪T x, (y : E)⟫_ℂ = ⟪(x : E), T y⟫_ℂ := by
    intro x y
    have hfa := LinearPMap.adjoint_isFormalAdjoint hd
    have hx' : (x : E) ∈ T†.domain := by rw [hTeq]; exact x.2
    have h := hfa ⟨x, hx'⟩ y
    obtain ⟨_, hh⟩ := LinearPMap.ext_iff.1 hTeq
    have h2 : T† ⟨x, hx'⟩ = T x := hh (x := (x : E)) (hf := hx') (hg := x.2)
    rw [h2] at h
    exact h
  -- domain of the adjoint
  have hDom : ∀ y : E, y ∈ (shiftPMap T)†.domain ↔ y ∈ T.domain := by
    intro y
    rw [LinearPMap.mem_adjoint_domain_iff]
    have hT' : y ∈ T.domain ↔ y ∈ T†.domain := by rw [hTeq]
    rw [hT', LinearPMap.mem_adjoint_domain_iff]
    have hg : Continuous fun x : T.domain => ⟪y, (x : E)⟫_ℂ :=
      (innerSL ℂ y).continuous.comp continuous_subtype_val
    have hfun : ∀ x : T.domain, ((innerₛₗ ℂ y).comp (shiftPMap T).toFun) x =
        ((innerₛₗ ℂ y).comp T.toFun) x - ⟪y, (x : E)⟫_ℂ := fun x => by
      change ⟪y, T x - (x : E)⟫_ℂ = ⟪y, T x⟫_ℂ - ⟪y, (x : E)⟫_ℂ
      exact inner_sub_right _ _ _
    constructor
    · intro h
      have := h.add hg
      refine this.congr fun x => ?_
      show ((innerₛₗ ℂ y).comp (shiftPMap T).toFun) x + ⟪y, (x : E)⟫_ℂ =
        ((innerₛₗ ℂ y).comp T.toFun) x
      rw [hfun x]; ring
    · intro h
      have := h.sub hg
      refine this.congr fun x => ?_
      show ((innerₛₗ ℂ y).comp T.toFun) x - ⟪y, (x : E)⟫_ℂ =
        ((innerₛₗ ℂ y).comp (shiftPMap T).toFun) x
      rw [hfun x]
  refine LinearPMap.isSelfAdjoint_def.2 ?_
  refine LinearPMap.ext (Submodule.ext fun y => hDom y) ?_
  intro x hx hy
  have hxT : x ∈ T.domain := hy
  have hres : (shiftPMap T)† ⟨x, hx⟩ = T ⟨x, hxT⟩ - x := by
    refine LinearPMap.adjoint_apply_eq (T := shiftPMap T) hd ⟨x, hx⟩ (fun w => ?_)
    rw [shiftPMap_apply, inner_sub_left, inner_sub_right]
    have := hsym ⟨x, hxT⟩ ⟨w.1, w.2⟩
    simp only at this
    show ⟪T ⟨x, hxT⟩, (w : E)⟫_ℂ - ⟪x, (w : E)⟫_ℂ = ⟪x, T ⟨w.1, w.2⟩⟫_ℂ - ⟪x, (w : E)⟫_ℂ
    rw [this]
  rw [hres]
  rfl

end Shift

/-! ## §6 The contact Hamiltonian `H_{N,c}` -/

section Hamiltonian

open scoped LinearPMap

variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ} (hc : 0 ≤ c)

/-- **The self-adjoint operator `H_{N,c}` associated with the closed form `q_{N,c}`**:
`H = R⁻¹ − I` on `L²_sym(T_L^N)`, domain `range R`. -/
def Hop (c : ℝ) (hc : 0 ≤ c) : SymL2 L N →ₗ.[ℂ] SymL2 L N := shiftPMap (Tinv c hc)

theorem Hop_domain : (Hop (L := L) (N := N) c hc).domain =
    LinearMap.range (Rop (L := L) (N := N) c hc).toLinearMap := rfl

/-- **`H_{N,c}` is self-adjoint.** -/
theorem Hop_isSelfAdjoint : IsSelfAdjoint (Hop (L := L) (N := N) c hc) :=
  isSelfAdjoint_shift (Tinv_isSelfAdjoint hc)

/-- `H` is closed (a self-adjoint operator is closed). -/
theorem Hop_isClosed : (Hop (L := L) (N := N) c hc).IsClosed := (Hop_isSelfAdjoint hc).isClosed

/-- `R = (H + I)⁻¹`: `R g ∈ D(H)` and `H(R g) + R g = g`. -/
theorem Hop_Rop (g : SymL2 L N) :
    ∃ h : Rop c hc g ∈ (Hop (L := L) (N := N) c hc).domain,
      Hop c hc ⟨Rop c hc g, h⟩ + Rop c hc g = g := by
  refine ⟨mem_Tinv_domain hc g, ?_⟩
  show Tinv c hc ⟨Rop c hc g, mem_Tinv_domain hc g⟩ - Rop c hc g + Rop c hc g = g
  rw [Tinv_Rop]
  abel

/-- **Compact resolvent**: `(H + I)⁻¹ = R` is compact. -/
theorem Hop_compact_resolvent : IsCompactOperator (Rop c hc : SymL2 L N →L[ℂ] SymL2 L N) :=
  isCompactOperator_Rop hc

/-- Forward direction of the source's domain characterization: for `ψ = R g ∈ D(H)` there is
`x ∈ H¹_sym` with `val x = ψ` and `q(φ,x) = ⟨φ, Hψ⟩` for all `φ ∈ H¹_sym`. -/
theorem variational_of_domain (g : SymL2 L N) (φ : VSym L N) :
    q c φ.1 (psi c hc g).1 = ⟪(valSym φ : SymL2 L N), g - Rop c hc g⟫_ℂ := by
  have h1 := resolvent_eq hc g φ
  unfold Bform at h1
  have h2 : ⟪φ.1.val, (psi c hc g).1.val⟫_ℂ = ⟪(valSym φ : SymL2 L N), Rop c hc g⟫_ℂ := rfl
  rw [h2] at h1
  rw [inner_sub_right]
  linear_combination h1

/-- **Converse (the source's exact domain)**: if `x ∈ H¹_sym` and `f ∈ L²_sym` satisfy
`q(φ,x) = ⟨φ,f⟩` for every `φ ∈ H¹_sym`, then `val x ∈ D(H)` and `H(val x) = f`. -/
theorem mem_domain_of_variational (x : VSym L N) (f : SymL2 L N)
    (hq : ∀ φ : VSym L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), f⟫_ℂ) :
    ∃ h : (valSym x : SymL2 L N) ∈ (Hop (L := L) (N := N) c hc).domain,
      Hop c hc ⟨valSym x, h⟩ = f := by
  -- `g = f + val x`, and `x = M⁻¹ G g`
  set g : SymL2 L N := f + valSym x with hg
  have hB : ∀ φ : VSym L N, Bform c φ x = ⟪(valSym φ : SymL2 L N), g⟫_ℂ := fun φ => by
    unfold Bform
    rw [hq φ, hg, inner_add_right]
    rfl
  have hMx : Mop c hc x = Gop g := by
    refine ext_inner_left ℂ (fun φ => ?_)
    rw [inner_Mop_right]
    exact (hB φ).trans (ContinuousLinearMap.adjoint_inner_right (valSym (L := L) (N := N)) φ g).symm
  have hx : x = psi c hc g := by
    have := congrArg (Minv c hc) hMx
    rwa [Minv_Mop] at this
  have hR : Rop c hc g = valSym x := by rw [Rop_eq_valSym_psi, ← hx]
  have hmem : (valSym x : SymL2 L N) ∈ (Hop (L := L) (N := N) c hc).domain := by
    rw [← hR]; exact mem_Tinv_domain hc g
  refine ⟨hmem, ?_⟩
  have hH : Hop c hc ⟨valSym x, hmem⟩ = Tinv c hc ⟨valSym x, hmem⟩ - valSym x := rfl
  have hT : Tinv c hc ⟨valSym x, hmem⟩ = g :=
    Tinv_apply_of_eq hc _ g hR
  rw [hH, hT, hg]
  abel

/-- **Nonnegativity of `H_{N,c}`**: for `ψ = val x ∈ D(H)`,
`⟨ψ, Hψ⟩ = q_{N,c}[x] ≥ 0`. -/
theorem Hop_nonneg (g : SymL2 L N) :
    0 ≤ (⟪Rop c hc g, g - Rop c hc g⟫_ℂ).re := by
  have h := variational_of_domain hc g (psi c hc g)
  have h2 : ((valSym (psi c hc g)) : SymL2 L N) = Rop c hc g := rfl
  rw [h2] at h
  rw [← h]
  exact q_nonneg hc _

end Hamiltonian

end QuantumNLS.ContactOperator
