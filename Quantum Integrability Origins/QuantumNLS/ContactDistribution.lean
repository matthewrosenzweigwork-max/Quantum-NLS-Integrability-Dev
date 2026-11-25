import QuantumNLS.ContactOperator
import QuantumNLS.ProductWeakDerivatives

/-!
# `contact:eq:distdomain`: variational ⇒ distributional domain of `H_{N,c}`, independent steps

Source (pinned PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`, `chapters/foundations/A01.tex:44`,
R-98129FE7): the exact domain of `H_{N,c}` is
`{ψ ∈ H¹_sym : −Δψ + 2c Σ_{i<j} δ_L(x_i−x_j) T_ijψ is represented by an f ∈ ℋ_N}`, `Hψ = f`, "The contact
distribution is defined by its pairing `∫ conj(T_ijφ) T_ijψ dy_ij` with a smooth test function `φ`".
Proof route in the source: the variational identity `q(φ,ψ) = ⟨φ,f⟩ ∀ φ ∈ D(q)` is, by integration by
parts, the distributional identity; "symmetric tests suffice"; "equality on smooth tests extends to all
`H¹` tests by continuity, using Lemma `contact:lem:trace`"; "`f` is unique by density".

This module proves the steps that do **not** use the identification of the trace with the literal
restriction (that bridge, `CollisionIdentification`, is Sol's and is not assumed or duplicated here):

* §1 symmetric Fourier cubes converge to any element of `H¹_sym` in the `H¹` energy norm;
* §2 **test-class extension**: if a variational identity holds for every symmetric trigonometric
  polynomial then it holds for every `φ ∈ H¹_sym` (continuity of both sides in the `H¹` norm, the
  step "extends to all `H¹` tests by continuity");
* §3 **uniqueness of `f`** (density of `H¹_sym` in `L²_sym`);
* §4 **the domain of `H` through an arbitrary test class `𝒯 ⊆ H¹_sym` that contains the symmetric
  trigonometric polynomials**: `ψ ∈ D(H)`, `Hψ = f` ⟺ `∃ x ∈ H¹_sym, val x = ψ ∧ ∀ φ ∈ 𝒯, q(φ,x) = ⟨φ,f⟩`;
* §5 symmetric trigonometric polynomials are genuine smooth lattice-periodic symmetric test functions
  in the sense of `ProductWeakDerivatives`, and their `L²` class is the `H¹` element `trigElem`.

Frozen imports (read-only): `ContactOperator` `c847ea9b…`, `ProductWeakDerivatives` `91ec7338…`
(and transitively `ContactForm`, `CollisionTrace`, `PhysicalEnergy`, `Fourier`).  No assumption.

No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate Real InnerProductSpace ContDiff
open MeasureTheory QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.CollisionTrace
  QuantumNLS.ContactForm QuantumNLS.ContactOperator QuantumNLS.Fourier QuantumNLS.PhysicalTensor

namespace QuantumNLS.ContactDistribution

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-! ## §1 Symmetric Fourier cubes converge in the `H¹` energy norm -/

theorem tendsto_cube_atTop : Filter.Tendsto (fun R : ℕ => cube N R) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro S
  obtain ⟨R0, hR0⟩ := exists_cube S
  exact ⟨R0, fun R hR => hR0.trans (cube_mono hR)⟩

/-- The cube truncations `ψ_R` (trigonometric polynomials) of `ψ ∈ H¹(T_L^N)` converge to `ψ`
in the `H¹` energy norm. -/
theorem trigElem_cube_tendsto (x : PhysH1 L N) :
    Filter.Tendsto (fun R : ℕ => trigElem (L := L) (cube N R) (coeffFun x)) Filter.atTop (nhds x) :=
  (trigElem_tendsto x).comp tendsto_cube_atTop

theorem trigElem_cube_mem_sym (x : VSym L N) (R : ℕ) :
    trigElem (L := L) (cube N R) (coeffFun x.1) ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N)) := by
  have hF : x.1.val ∈ SymL2 L N := (mem_SymL2_iff _).2 ((PhysH1.mem_sym_iff x.1).1 x.2)
  exact cubeTrunc_mem_sym hF R

/-! ## §2 Extension from symmetric trigonometric polynomials to all of `H¹_sym` -/

/-- Both sides of the variational identity are continuous in `φ ∈ H¹_sym`. -/
theorem continuous_q_left {c : ℝ} (hc : 0 ≤ c) (x : VSym L N) :
    Continuous fun φ : VSym L N => q c φ.1 x.1 := by
  have h1 : Continuous fun φ : VSym L N => BformCLM c hc φ x :=
    (ContinuousLinearMap.apply ℂ ℂ x).continuous.comp (BformCLM c hc).continuous
  have h2 : Continuous fun φ : VSym L N => ⟪(valSym φ : SymL2 L N), valSym x⟫_ℂ :=
    ((valSym (L := L) (N := N)).continuous.inner continuous_const)
  have h3 : (fun φ : VSym L N => q c φ.1 x.1) =
      fun φ => BformCLM c hc φ x - ⟪(valSym φ : SymL2 L N), valSym x⟫_ℂ := by
    funext φ
    rw [BformCLM_apply]
    unfold Bform
    rw [show ⟪(valSym φ : SymL2 L N), valSym x⟫_ℂ = ⟪φ.1.val, x.1.val⟫_ℂ from rfl]
    ring
  rw [h3]
  exact h1.sub h2

/-- **Test-class extension** (source: "equality on smooth tests extends to all `H¹` tests by
continuity"): if `q(φ,x) = ⟨φ,f⟩` for every symmetric trigonometric polynomial `φ ∈ H¹_sym`, then it
holds for every `φ ∈ H¹_sym`. -/
theorem variational_of_trig {c : ℝ} (hc : 0 ≤ c) (x : VSym L N) (f : SymL2 L N)
    (h : ∀ (S : Finset (Fin N → ℤ)) (c' : (Fin N → ℤ) → ℂ)
      (hs : trigElem (L := L) S c' ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))),
      q c (trigElem (L := L) S c') x.1 =
        ⟪(valSym (⟨trigElem (L := L) S c', hs⟩ : VSym L N) : SymL2 L N), f⟫_ℂ) :
    ∀ φ : VSym L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), f⟫_ℂ := by
  intro φ
  have hcont : Continuous fun φ : VSym L N => q c φ.1 x.1 - ⟪(valSym φ : SymL2 L N), f⟫_ℂ :=
    (continuous_q_left hc x).sub ((valSym (L := L) (N := N)).continuous.inner continuous_const)
  let φR : ℕ → VSym L N := fun R =>
    ⟨trigElem (L := L) (cube N R) (coeffFun φ.1), trigElem_cube_mem_sym φ R⟩
  have hφR : Filter.Tendsto φR Filter.atTop (nhds φ) := by
    rw [tendsto_subtype_rng]
    exact trigElem_cube_tendsto φ.1
  have h2 := (hcont.tendsto φ).comp hφR
  have h0 : ∀ R, (fun φ : VSym L N => q c φ.1 x.1 - ⟪(valSym φ : SymL2 L N), f⟫_ℂ) (φR R) = 0 :=
    fun R => sub_eq_zero.2 (h _ _ _)
  have h3 : Filter.Tendsto (fun R => (fun φ : VSym L N =>
      q c φ.1 x.1 - ⟪(valSym φ : SymL2 L N), f⟫_ℂ) (φR R)) Filter.atTop (nhds 0) := by
    simp only [h0]; exact tendsto_const_nhds
  exact sub_eq_zero.1 (tendsto_nhds_unique h2 h3)

/-! ## §3 Uniqueness of the representing `f` -/

/-- **`f` is unique** (source: "the vector `f` is unique by density"): if `⟨φ,f⟩ = ⟨φ,f'⟩` for all
`φ ∈ H¹_sym` then `f = f'`. -/
theorem eq_of_inner_eq (f f' : SymL2 L N)
    (h : ∀ φ : VSym L N, ⟪(valSym φ : SymL2 L N), f⟫_ℂ = ⟪(valSym φ : SymL2 L N), f'⟫_ℂ) :
    f = f' := by
  have hcl : IsClosed {y : SymL2 L N | ⟪f - f', y⟫_ℂ = 0} :=
    isClosed_eq (innerSL ℂ (f - f')).continuous continuous_const
  have h5 : ∀ y : SymL2 L N, ⟪f - f', y⟫_ℂ = 0 := fun y => by
    have hy : y ∈ closure (Set.range (valSym (L := L) (N := N))) := denseRange_valSym y
    have hsub : Set.range (valSym (L := L) (N := N)) ⊆ {y : SymL2 L N | ⟪f - f', y⟫_ℂ = 0} := by
      rintro _ ⟨φ, rfl⟩
      show ⟪f - f', (valSym φ : SymL2 L N)⟫_ℂ = 0
      rw [inner_sub_left, ← inner_conj_symm f (valSym φ), ← inner_conj_symm f' (valSym φ), h φ,
        sub_self]
    exact (closure_minimal hsub hcl) hy
  have h6 : inner ℂ (f - f') (f - f') = 0 := h5 (f - f')
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h6)

/-! ## §4 The domain of `H_{N,c}` through a general test class -/

/-- **Domain of `H` through any test class containing the symmetric trigonometric polynomials**:
`ψ ∈ D(H)` with `Hψ = f` iff `ψ = val x` for some `x ∈ H¹_sym` whose weak identity
`q(φ,x) = ⟨φ,f⟩` holds for all `φ` in the class `𝒯`. -/
theorem mem_domain_iff_testwise {c : ℝ} (hc : 0 ≤ c) (𝒯 : Set (VSym L N))
    (h𝒯 : ∀ (S : Finset (Fin N → ℤ)) (c' : (Fin N → ℤ) → ℂ)
      (hs : trigElem (L := L) S c' ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))),
      (⟨trigElem (L := L) S c', hs⟩ : VSym L N) ∈ 𝒯)
    (ψ f : SymL2 L N) :
    (∃ h : ψ ∈ (Hop (L := L) (N := N) c hc).domain, Hop c hc ⟨ψ, h⟩ = f) ↔
      ∃ x : VSym L N, (valSym x : SymL2 L N) = ψ ∧
        ∀ φ ∈ 𝒯, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), f⟫_ℂ := by
  constructor
  · rintro ⟨hψ, hH⟩
    obtain ⟨g, hg⟩ := hψ
    refine ⟨psi c hc g, hg, fun φ _ => ?_⟩
    have hg' : Rop c hc g = ψ := hg
    have hmem : ψ ∈ (Hop (L := L) (N := N) c hc).domain := ⟨g, hg⟩
    have hHψ : Hop c hc ⟨ψ, hmem⟩ = g - ψ := by
      have h1 : Tinv c hc ⟨ψ, hmem⟩ = g := Tinv_apply_of_eq hc _ g hg
      show Tinv c hc ⟨ψ, hmem⟩ - ψ = g - ψ
      rw [h1]
    have hfg : f = g - ψ := by rw [← hH]; exact hHψ
    rw [variational_of_domain hc g φ, hg', hfg]
  · rintro ⟨x, hx, hq⟩
    subst hx
    have hall : ∀ φ : VSym L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), f⟫_ℂ :=
      variational_of_trig hc x f (fun S c' hs => hq ⟨trigElem (L := L) S c', hs⟩ (h𝒯 S c' hs))
    obtain ⟨h, hH⟩ := mem_domain_of_variational hc x f hall
    exact ⟨h, hH⟩

/-- **`H` is determined by the variational identity**: the representing `f` of `ψ ∈ D(H)` is unique. -/
theorem Hop_unique {c : ℝ} (x : VSym L N) (f f' : SymL2 L N)
    (hf : ∀ φ : VSym L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), f⟫_ℂ)
    (hf' : ∀ φ : VSym L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), f'⟫_ℂ) : f = f' :=
  eq_of_inner_eq f f' fun φ => (hf φ).symm.trans (hf' φ)

/-! ## §5 Symmetric trigonometric polynomials are smooth symmetric test functions -/

section TrigTest

open QuantumNLS.ProductWeakDerivatives

/-- `e_n(x) = L^{-1/2} e^{2πinx/L}` on `ℝ` (the report's orthonormal mode, mass-`L` normalization). -/
def efun (L : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * n * x / L)

theorem mode_eq_efun (n : ℤ) (y : AddCircle L) : mode L n y = efun L n (rep y) := by
  have h := mode_coe (L := L) n (rep y)
  rw [coe_rep] at h
  exact h

theorem efun_smooth (L : ℝ) (n : ℤ) : ContDiff ℝ ∞ (efun L n) := by
  unfold efun
  have hid : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  exact contDiff_const.mul (Complex.contDiff_exp.comp
    (((contDiff_const.mul hid)).div_const _))

theorem efun_periodic {L : ℝ} (hL : L ≠ 0) (n m : ℤ) (x : ℝ) :
    efun L n (x + m * L) = efun L n x := by
  unfold efun
  congr 1
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have h : 2 * (Real.pi : ℂ) * Complex.I * n * ((x + m * L : ℝ) : ℂ) / L =
      2 * (Real.pi : ℂ) * Complex.I * n * x / L + ((n * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The trigonometric polynomial `φ_{S,c}(x) = Σ_{w∈S} c_w ∏_l e_{w_l}(x_l)` on `ℝ^N`. -/
def trigTest (L : ℝ) (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) (x : Fin N → ℝ) : ℂ :=
  ∑ w ∈ S, c w * ∏ l, efun L (w l) (x l)

/-- **A trigonometric polynomial is a genuine smooth lattice-periodic test function.** -/
theorem trigTest_isTest (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    IsTorusTest L (trigTest L S c) where
  smooth := by
    unfold trigTest
    refine ContDiff.sum fun w _ => contDiff_const.mul (contDiff_prod fun l _ => ?_)
    exact (efun_smooth L (w l)).comp (contDiff_apply ℝ ℝ l)
  periodic := by
    intro x m
    unfold trigTest
    refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    exact efun_periodic (Fact.out : 0 < L).ne' (w l) (m l) (x l)

/-- The `L²(T_L^N)` class of a continuous lattice-periodic function. -/
def smoothClass {φ : (Fin N → ℝ) → ℂ} (hφ : Continuous φ) : L2TN L N :=
  (memLp_liftK (L := L) hφ).toLp (liftK φ)

/-- **The class of the test function `φ_{S,c}` is the `H¹` element `trigElem S c`.** -/
theorem smoothClass_trigTest (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    smoothClass (L := L) (trigTest_isTest (L := L) S c).smooth.continuous =
      (trigElem (L := L) S c).val := by
  refine Lp.ext ?_
  have h1 := (memLp_liftK (L := L) (trigTest_isTest (L := L) S c).smooth.continuous).coeFn_toLp
  have h2 := trigElem_ae (L := L) S c
  filter_upwards [h1, h2] with y hy1 hy2
  rw [smoothClass, hy1, hy2]
  unfold liftK trigTest
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  exact (mode_eq_efun _ _).symm

/-- A function on `ℝ^N` invariant under permuting the coordinates. -/
def SymmFun (φ : (Fin N → ℝ) → ℂ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), φ (fun i => x (σ i)) = φ x

omit [Fact (0 < L)] in
/-- A trigonometric polynomial with permutation-invariant coefficients is a symmetric function. -/
theorem trigTest_symm (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ)
    (hc : ∀ (σ : Equiv.Perm (Fin N)) (w : Fin N → ℤ), c (w ∘ σ) = c w)
    (hS : ∀ w, w ∉ S → c w = 0) : SymmFun (trigTest L S c) := by
  have hsum : ∀ y : Fin N → ℝ, trigTest L S c y = ∑' w, c w * ∏ l, efun L (w l) (y l) :=
    fun y => (tsum_eq_sum (s := S) (fun w hw => by simp [hS w hw])).symm
  intro σ x
  rw [hsum, hsum]
  have hprod : ∀ w : Fin N → ℤ, ∏ l, efun L (w l) (x (σ l)) =
      ∏ l, efun L ((w ∘ σ.symm) l) (x l) := fun w => by
    have := Equiv.prod_comp σ (fun l => efun L ((w ∘ σ.symm) l) (x l))
    rw [← this]
    refine Finset.prod_congr rfl fun l _ => ?_
    simp
  have hterm : ∀ w : Fin N → ℤ, c w * ∏ l, efun L (w l) (x (σ l)) =
      (fun w' => c w' * ∏ l, efun L (w' l) (x l)) (w ∘ σ.symm) := fun w => by
    rw [hprod w]
    have : c (w ∘ σ.symm) = c w := by
      have := hc σ (w ∘ σ.symm)
      rw [show (w ∘ σ.symm) ∘ σ = w from by funext l; simp] at this
      exact this.symm
    simp only [this]
  simp_rw [hterm]
  exact (permEquiv σ.symm).tsum_eq (fun w' => c w' * ∏ l, efun L (w' l) (x l))

/-- **The class `𝒯` of `H¹_sym` elements represented by genuine smooth, lattice-periodic,
permutation-symmetric test functions** on `ℝ^N`. -/
def testClass (L : ℝ) [Fact (0 < L)] (N : ℕ) : Set (VSym L N) :=
  {φ | ∃ (ψ : (Fin N → ℝ) → ℂ) (hψ : IsTorusTest L ψ), SymmFun ψ ∧
    φ.1.val = smoothClass (L := L) hψ.smooth.continuous}

/-- **Every symmetric trigonometric polynomial of `H¹_sym` is a smooth symmetric test function.** -/
theorem trigElem_mem_testClass (S : Finset (Fin N → ℤ)) (c' : (Fin N → ℤ) → ℂ)
    (hs : trigElem (L := L) S c' ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) :
    (⟨trigElem (L := L) S c', hs⟩ : VSym L N) ∈ testClass L N := by
  set c'' : (Fin N → ℤ) → ℂ := fun w => if w ∈ S then c' w else 0 with hc''
  -- the coefficient function is symmetric
  have hco : ∀ w, (momUnitary L N (trigElem (L := L) S c').val : (Fin N → ℤ) → ℂ) w = c'' w := by
    intro w
    rw [momUnitary_trigElem]
    rfl
  have hsymm : ∀ (σ : Equiv.Perm (Fin N)) (w : Fin N → ℤ), c'' (w ∘ σ) = c'' w := by
    intro σ w
    have := (isSymm_iff_coeff _).1 ((PhysH1.mem_sym_iff _).1 hs) σ w
    rw [hco, hco] at this
    exact this
  have hS0 : ∀ w, w ∉ S → c'' w = 0 := fun w hw => by simp [hc'', hw]
  have hval : (trigElem (L := L) S c'').val = (trigElem (L := L) S c').val := by
    apply (momUnitary L N).injective
    rw [momUnitary_trigElem, momUnitary_trigElem]
    apply Subtype.ext; funext w
    by_cases hw : w ∈ S <;> simp [finVec_apply, hc'', hw]
  refine ⟨trigTest L S c'', trigTest_isTest S c'', trigTest_symm S c'' hsymm hS0, ?_⟩
  show (trigElem (L := L) S c').val = _
  rw [← hval, smoothClass_trigTest]

/-- **The domain of `H_{N,c}` through genuine smooth symmetric test functions**:
`ψ ∈ D(H)`, `Hψ = f` iff `ψ = val x` for some `x ∈ H¹_sym` with
`q_{N,c}(φ,x) = ⟨φ,f⟩` for every `φ` represented by a smooth, lattice-periodic, symmetric test
function.  (Here `q` is the Fourier-defined form; its identification with the literal distributional
pairing `Σ_j∫ conj∂_jφ ∂_jψ + 2cΣ∫ conj T_ijφ T_ijψ dy_ij` is the separate bridge of
`CollisionIdentification`.) -/
theorem mem_domain_iff_smooth_tests {c : ℝ} (hc : 0 ≤ c) (ψ f : SymL2 L N) :
    (∃ h : ψ ∈ (Hop (L := L) (N := N) c hc).domain, Hop c hc ⟨ψ, h⟩ = f) ↔
      ∃ x : VSym L N, (valSym x : SymL2 L N) = ψ ∧
        ∀ φ ∈ testClass L N, q c φ.1 x.1 = ⟪(valSym φ : SymL2 L N), f⟫_ℂ :=
  mem_domain_iff_testwise hc (testClass L N) (fun S c' hs => trigElem_mem_testClass S c' hs) ψ f

end TrigTest

end QuantumNLS.ContactDistribution
