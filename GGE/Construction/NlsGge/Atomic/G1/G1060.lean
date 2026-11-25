                                                                                                                                                                                                                                                                                                                              
import Mathlib
import NlsGge.GK38.GradEigenPeriodic
import NlsGge.GK38.GradEigenRealNeumann
import NlsGge.GK38.NeumannChar
import NlsGge.GK38.GradEigenRealPeriodicGradient

                                                                                       
                                                                                                                            
                                                                               
                                                                                            
                                                                                                                                                               
                                                                                                                                                                                                                                   
                                                                                                                                     
                                                                                                                                                             
                                                                                           
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.GK38.GradEigen38

namespace NlsGge.GK38.SimpleBoundary38

noncomputable section

def dirichletTrace (a b : PairVec38) : Prop :=
  a 0 = a 1 ∧ b 0 = b 1

def neumannTrace (a b : PairVec38) : Prop :=
  a 0 = -a 1 ∧ b 0 = -b 1

def floquetTrace (c : ℂ) (a b : PairVec38) : Prop := b = c • a

def IsSourceBoundary
    (χ : PotPair → ℂ → ℂ)
    (B : PairVec38 → PairVec38 → Prop) : Prop :=
  (χ = dirichletChar ∧ B = dirichletTrace) ∨
  (χ = neumannChar38 ∧ B = neumannTrace) ∨
  ∃ c : ℂ, c ^ 2 = 1 ∧
    χ = (fun φ z => NlsGge.GK38.discrim φ z - 2 * c) ∧ B = floquetTrace c

structure BoundaryProblem where
  characteristic : PotPair → ℂ → ℂ
  boundary : PairVec38 → PairVec38 → Prop
  source : IsSourceBoundary characteristic boundary

def dirichletProblem : BoundaryProblem :=
  ⟨dirichletChar, dirichletTrace, Or.inl ⟨rfl, rfl⟩⟩

def neumannProblem : BoundaryProblem :=
  ⟨neumannChar38, neumannTrace, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩

def floquetProblem (c : ℂ) (hc : c ^ 2 = 1) : BoundaryProblem :=
  ⟨fun φ z => NlsGge.GK38.discrim φ z - 2 * c, floquetTrace c,
    Or.inr (Or.inr ⟨c, hc, rfl, rfl⟩)⟩

def periodicProblem : BoundaryProblem :=
  floquetProblem 1 (by norm_num)

def antiperiodicProblem : BoundaryProblem :=
  floquetProblem (-1) (by norm_num)

def IsSimpleBoundaryEigenvalue
    (P : BoundaryProblem) (φ : PotPair) (z : ℂ) : Prop :=
  P.characteristic φ z = 0 ∧
    analyticOrderAt (P.characteristic φ) z = 1

def IsBoundaryEigenfunction
    (P : BoundaryProblem) (φ : PotPair) (z : ℂ)
    (w : PairKernelCont38) : Prop :=
  ∃ a : PairVec38, a ≠ 0 ∧ w = state φ z a ∧
    P.boundary a (w t1)

structure LocalEigenvalueBranch
    (P : BoundaryProblem) (φ : PotPair) (z : ℂ) where
  toFun : PotPair → ℂ
  domain : Set PotPair
  isOpen_domain : IsOpen domain
  base_mem : φ ∈ domain
  analytic : AnalyticOnNhd ℂ toFun domain
  value : toFun φ = z
  root : ∀ ψ ∈ domain, P.characteristic ψ (toFun ψ) = 0

noncomputable def spectralGradient
    {P : BoundaryProblem} {φ : PotPair} {z : ℂ}
    (b : LocalEigenvalueBranch P φ z) : PotPair →L[ℂ] ℂ :=
  fderiv ℂ b.toFun φ

/-- A01 -/
theorem boundary_characteristic_analytic (P : BoundaryProblem) :
    AnalyticOnNhd ℂ
      (fun p : PotPair × ℂ => P.characteristic p.1 p.2) Set.univ := by
  obtain ⟨χ, B, hsrc⟩ := P
  rcases hsrc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨c, hc, rfl, rfl⟩
  · exact analyticOnNhd_dirichletChar
  · exact analyticOnNhd_neumannChar38
  · exact analyticOnNhd_discrim.sub analyticOnNhd_const

theorem boundary_characteristic_analytic_z (P : BoundaryProblem) (φ : PotPair) :
    AnalyticOnNhd ℂ (P.characteristic φ) Set.univ := fun z _ =>
  AnalyticAt.comp (g := fun p : PotPair × ℂ => P.characteristic p.1 p.2) (f := fun w : ℂ => (φ, w))
    (boundary_characteristic_analytic P (φ, z) (mem_univ _))
    ((analyticAt_const (v := φ)).prod analyticAt_id)

/-- A02 -/
theorem simple_boundary_iff (P : BoundaryProblem) (φ : PotPair) (z : ℂ) :
    IsSimpleBoundaryEigenvalue P φ z ↔
      P.characteristic φ z = 0 ∧ deriv (P.characteristic φ) z ≠ 0 := by
  have hA : AnalyticAt ℂ (P.characteristic φ) z := boundary_characteristic_analytic_z P φ z (mem_univ _)
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨h0, ?_⟩
    have h := hA.analyticOrderAt_deriv_add_one
    have hsub : (fun w => P.characteristic φ w - P.characteristic φ z) = P.characteristic φ := by
      funext w; rw [h0]; simp
    rw [hsub, h1] at h
    have hz : analyticOrderAt (deriv (P.characteristic φ)) z = 0 := by
      generalize analyticOrderAt (deriv (P.characteristic φ)) z = x at h
      induction x using ENat.recTopCoe with
      | top => simp at h
      | coe n =>
        have h2 : (n + 1 : ℕ) = 1 := by exact_mod_cast h
        have h3 : n = 0 := by omega
        simp [h3]
    intro hd
    have := (analyticOrderAt_eq_zero.mp hz)
    rcases this with hna | hne
    · exact hna hA.deriv
    · exact hne hd
  · rintro ⟨h0, h1⟩
    exact ⟨h0, hA.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 h1⟩


theorem boundary_joint_spectral_partial (P : BoundaryProblem) (φ : PotPair) (z : ℂ) :
    (fderiv ℂ (fun p : PotPair × ℂ => P.characteristic p.1 p.2) (φ, z)) (0, 1) =
      deriv (P.characteristic φ) z := by
  have hf := (boundary_characteristic_analytic P (φ, z) (mem_univ _)).differentiableAt.hasFDerivAt
  have hcurve : HasDerivAt (fun w : ℂ => (φ, w)) ((0 : PotPair), (1 : ℂ)) z :=
    (hasDerivAt_const z φ).prodMk (hasDerivAt_id z)
  have hs : HasDerivAt (P.characteristic φ)
      ((fderiv ℂ (fun p : PotPair × ℂ => P.characteristic p.1 p.2) (φ, z)) (0, 1)) z :=
    hf.comp_hasDerivAt z hcurve
  exact hs.deriv.symm

/-- A03 -/
theorem localEigenvalue_exists
    (P : BoundaryProblem) (φ : PotPair) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue P φ z) :
    Nonempty (LocalEigenvalueBranch P φ z) := by
  obtain ⟨h0, hd⟩ := (simple_boundary_iff P φ z).mp hs
  have hc : (fderiv ℂ (fun p : PotPair × ℂ => P.characteristic p.1 p.2) (φ, z)) (0, 1) ≠ 0 := by
    rw [boundary_joint_spectral_partial]; exact hd
  obtain ⟨U, κ, hU, hφU, hκ, hκz, hroot, -⟩ := simple_root_branch_target
    (fun p : PotPair × ℂ => P.characteristic p.1 p.2) φ z
    (boundary_characteristic_analytic P (φ, z) (mem_univ _)) h0 hc
  exact ⟨⟨κ, U, hU, hφU, hκ, hκz, hroot⟩⟩

noncomputable def localEigenvalue
    (P : BoundaryProblem) (φ : PotPair) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue P φ z) :
    LocalEigenvalueBranch P φ z :=
  Classical.choice (localEigenvalue_exists P φ z hs)

/-- A04 -/
theorem branch_implicit_derivative
    (P : BoundaryProblem) (φ : PotPair) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue P φ z)
    (b : LocalEigenvalueBranch P φ z) :
    HasFDerivAt b.toFun
      (-(deriv (P.characteristic φ) z)⁻¹ •
        ((fderiv ℂ (fun p : PotPair × ℂ => P.characteristic p.1 p.2)
          (φ, z)).comp potentialInclusion)) φ := by
  obtain ⟨h0, hd⟩ := (simple_boundary_iff P φ z).mp hs
  have hfd := boundary_joint_spectral_partial P φ z
  have hroot : ∀ᶠ ψ in 𝓝 φ,
      (fun p : PotPair × ℂ => P.characteristic p.1 p.2) (ψ, b.toFun ψ) = 0 :=
    Filter.mem_of_superset (b.isOpen_domain.mem_nhds b.base_mem) (fun ψ hψ => b.root ψ hψ)
  have h := complex_root_derivative (fun p : PotPair × ℂ => P.characteristic p.1 p.2) φ z
    (boundary_characteristic_analytic P (φ, z) (mem_univ _))
    (by rw [hfd]; exact hd) b.toFun (b.analytic φ b.base_mem) b.value hroot
  rwa [hfd] at h

theorem spectralGradient_eq_of_branches
    (P : BoundaryProblem) (φ : PotPair) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue P φ z)
    (b₁ b₂ : LocalEigenvalueBranch P φ z) :
    spectralGradient b₁ = spectralGradient b₂ := by
  unfold spectralGradient
  rw [(branch_implicit_derivative P φ z hs b₁).fderiv, (branch_implicit_derivative P φ z hs b₂).fderiv]

/-! ### Dirichlet -/

theorem dirichlet_seed_multiple (a : PairVec38)
    (ha : a ≠ 0) (hb : a 0 = a 1) :
    a 0 ≠ 0 ∧ a = a 0 • (![1, 1] : PairVec38) := by
  refine ⟨fun h0 => ha ?_, ?_⟩
  · funext i
    fin_cases i
    · simpa using h0
    · simp [← hb, h0]
  · funext i
    fin_cases i
    · simp
    · simp [← hb]

theorem dirichlet_eigenfunction_multiple
    (φ : PotPair) (z : ℂ) (w : PairKernelCont38)
    (hw : IsBoundaryEigenfunction dirichletProblem φ z w) :
    ∃ c : ℂ, c ≠ 0 ∧ w = c • state φ z (![1, 1] : PairVec38) := by
  obtain ⟨a, ha, hwa, hbd⟩ := hw
  obtain ⟨hne, hmul⟩ := dirichlet_seed_multiple a ha hbd.1
  refine ⟨a 0, hne, ?_⟩
  calc w = state φ z a := hwa
    _ = state φ z (a 0 • (![1, 1] : PairVec38)) := by rw [← hmul]
    _ = a 0 • state φ z (![1, 1] : PairVec38) := state_seed_smul _ _ _ _

theorem dirichlet_arbitrary_gradient
    (φ : PotPair) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue dirichletProblem φ z)
    (w : PairKernelCont38)
    (hw : IsBoundaryEigenfunction dirichletProblem φ z w) :
    Q w ≠ 0 ∧ dirImplicitGradient φ z = bilinearGradient w := by
  obtain ⟨c, hc, hwc⟩ := dirichlet_eigenfunction_multiple φ z w hw
  obtain ⟨h0, hd⟩ := (simple_boundary_iff dirichletProblem φ z).mp hs
  have hroot : dirichletChar φ z = 0 := h0
  have hsimple : deriv (dirichletChar φ) z ≠ 0 := hd
  have hQ := dirichlet_Q_ne_zero φ z hroot hsimple
  rw [hwc]
  refine ⟨?_, ?_⟩
  · rw [Q_smul]; exact mul_ne_zero (pow_ne_zero 2 hc) hQ
  · rw [bilinear_gradient_smul c _ hc hQ, complex_dirichlet_gradient_identity φ z hroot hsimple]

/-- pure branch derivative for the Dirichlet problem (no eigenfunction needed). -/
theorem dirichlet_branch_hasFDerivAt
    (φ : PotPair) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue dirichletProblem φ z)
    (b : LocalEigenvalueBranch dirichletProblem φ z) :
    HasFDerivAt b.toFun (dirImplicitGradient φ z) φ := by
  have h := branch_implicit_derivative dirichletProblem φ z hs b
  have e : (fderiv ℂ (fun p : PotPair × ℂ => dirichletProblem.characteristic p.1 p.2) (φ, z)).comp
      potentialInclusion = dirCLM φ z := dirichlet_joint_potential_partial φ z
  rw [e] at h
  exact h

/-- A16 -/
theorem dirichlet_branch_gradient
    (φ : PotPair) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue dirichletProblem φ z)
    (w : PairKernelCont38)
    (hw : IsBoundaryEigenfunction dirichletProblem φ z w)
    (b : LocalEigenvalueBranch dirichletProblem φ z) :
    Q w ≠ 0 ∧ HasFDerivAt b.toFun (bilinearGradient w) φ := by
  obtain ⟨hQ, hg⟩ := dirichlet_arbitrary_gradient φ z hs w hw
  exact ⟨hQ, hg ▸ dirichlet_branch_hasFDerivAt φ z hs b⟩

/-! ### Floquet -/

theorem floquet_simple_iff (φ : PotPair) (z c : ℂ) (hc : c ^ 2 = 1) :
    IsSimpleBoundaryEigenvalue (floquetProblem c hc) φ z ↔
      NlsGge.GK38.discrim φ z = 2 * c ∧ deriv (perChar φ) z ≠ 0 := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h] at hc; norm_num at hc
  rw [simple_boundary_iff]
  have hder : deriv ((floquetProblem c hc).characteristic φ) z = deriv (NlsGge.GK38.discrim φ) z := by
    change deriv (fun w => NlsGge.GK38.discrim φ w - 2 * c) z = _
    exact deriv_sub_const _
  rw [hder, periodic_perChar_deriv]
  change NlsGge.GK38.discrim φ z - 2 * c = 0 ∧ _ ↔ _
  constructor
  · rintro ⟨h0, hd⟩
    have h1 : NlsGge.GK38.discrim φ z = 2 * c := sub_eq_zero.mp h0
    refine ⟨h1, ?_⟩
    rw [h1]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (mul_ne_zero two_ne_zero hc0)) hd
  · rintro ⟨h1, hd⟩
    refine ⟨sub_eq_zero.mpr h1, ?_⟩
    intro h
    apply hd
    rw [h, mul_zero]

theorem floquet_branch_gradient
    (φ : PotPair) (z c : ℂ) (hc : c ^ 2 = 1)
    (hs : IsSimpleBoundaryEigenvalue (floquetProblem c hc) φ z)
    (w : PairKernelCont38)
    (hw : IsBoundaryEigenfunction (floquetProblem c hc) φ z w)
    (b : LocalEigenvalueBranch (floquetProblem c hc) φ z) :
    Q w ≠ 0 ∧ HasFDerivAt b.toFun (bilinearGradient w) φ := by
  obtain ⟨a, ha, hwa, hbd⟩ := hw
  obtain ⟨hdisc, hsimple⟩ := (floquet_simple_iff φ z c hc).mp hs
  have hbd' : w t1 = c • a := hbd
  have he : Matrix.mulVec (monodromyPair φ z) a = c • a := by
    rw [← hbd', hwa, state_eq_mulVec]
    rfl
  obtain ⟨hQ, hdd, hgrad⟩ := periodic_arbitrary_eigenvector_gradient φ z c a hc hsimple ha he
  rw [hwa]
  refine ⟨hQ, ?_⟩
  rw [← hgrad]
  have h := branch_implicit_derivative (floquetProblem c hc) φ z hs b
  have hf1 : (fderiv ℂ (fun p : PotPair × ℂ => (floquetProblem c hc).characteristic p.1 p.2) (φ, z)) =
      fderiv ℂ (fun p : PotPair × ℂ => NlsGge.GK38.discrim p.1 p.2) (φ, z) := by
    change fderiv ℂ (fun p : PotPair × ℂ => NlsGge.GK38.discrim p.1 p.2 - 2 * c) (φ, z) = _
    exact fderiv_sub_const _
  have hf2 : deriv ((floquetProblem c hc).characteristic φ) z = deriv (NlsGge.GK38.discrim φ) z := by
    change deriv (fun w => NlsGge.GK38.discrim φ w - 2 * c) z = _
    exact deriv_sub_const _
  rw [hf1, discrim_joint_potential_partial, hf2] at h
  exact h

/-! ### Neumann -/

theorem complex_neumann_state_gauge
    (φ : PotPair) (z : ℂ) (t : Time) (i : Fin 2) :
    state φ z (![Complex.I, -Complex.I] : PairVec38) t i =
      (Complex.I * gaugeSign38 i) * state (-φ) z (![1, 1] : PairVec38) t i := by
  rw [state_eq_mulVec, state_eq_mulVec, fundPair_neg_gauge38]
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, gaugeJ38_conj_apply, gaugeSign38] <;> ring

theorem complex_neumann_square (φ : PotPair) (z : ℂ) :
    square (state φ z (![Complex.I, -Complex.I] : PairVec38)) =
      (-1 : ℂ) • square (state (-φ) z (![1, 1] : PairVec38)) := by
  ext t i
  fin_cases i <;> simp [square, starProd38, complex_neumann_state_gauge, gaugeSign38] <;> ring_nf <;>
    simp [Complex.I_sq]

theorem complex_neumann_Q (φ : PotPair) (z : ℂ) :
    Q (state φ z (![Complex.I, -Complex.I] : PairVec38)) =
      Q (state (-φ) z (![1, 1] : PairVec38)) := by
  unfold Q
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hm : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
  dsimp only
  rw [pairKernelExt38_of_mem _ hm, pairKernelExt38_of_mem _ hm,
    complex_neumann_state_gauge φ z ⟨s, hm⟩ 0, complex_neumann_state_gauge φ z ⟨s, hm⟩ 1]
  simp only [gaugeSign38]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
  linear_combination (-(state (-φ) z (![1, 1] : PairVec38) ⟨s, hm⟩ 0 *
    state (-φ) z (![1, 1] : PairVec38) ⟨s, hm⟩ 1)) * Complex.I_sq

theorem complex_neumann_canonical_gradient
    (φ : PotPair) (z : ℂ)
    (hr : neumannChar38 φ z = 0)
    (hs : deriv (neumannChar38 φ) z ≠ 0) :
    Q (state φ z (![Complex.I, -Complex.I] : PairVec38)) ≠ 0 ∧
    bilinearGradient (state φ z (![Complex.I, -Complex.I] : PairVec38)) =
      -dirImplicitGradient (-φ) z := by
  have hfe := neumannChar38_fun_eq_dirichlet_neg φ
  have hroot : dirichletChar (-φ) z = 0 := by rw [← hfe]; exact hr
  have hsimple : deriv (dirichletChar (-φ)) z ≠ 0 := by rw [← hfe]; exact hs
  have hQ := dirichlet_Q_ne_zero (-φ) z hroot hsimple
  refine ⟨by rw [complex_neumann_Q]; exact hQ, ?_⟩
  unfold bilinearGradient
  rw [complex_neumann_Q, complex_neumann_square, integralPairCLM38_kernelSmul]
  have hg := complex_dirichlet_gradient_identity (-φ) z hroot hsimple
  unfold bilinearGradient at hg
  rw [hg]
  exact ContinuousLinearMap.ext fun p => by simp

theorem neumann_seed_multiple (a : PairVec38)
    (ha : a ≠ 0) (hb : a 0 = -a 1) :
    ∃ c : ℂ, c ≠ 0 ∧ a = c • (![Complex.I, -Complex.I] : PairVec38) := by
  have h1 : a 1 = -a 0 := by linear_combination hb
  refine ⟨-Complex.I * a 0, ?_, ?_⟩
  · intro h
    have h0 : a 0 = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd (neg_eq_zero.mp h') Complex.I_ne_zero
      · exact h'
    apply ha
    funext i
    fin_cases i
    · simpa using h0
    · simp [h1, h0]
  · funext i
    fin_cases i
    · simp
      linear_combination (a 0) * Complex.I_sq
    · simp [h1]
      linear_combination (-(a 0)) * Complex.I_sq

theorem neumann_branch_gradient
    (φ : PotPair) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue neumannProblem φ z)
    (w : PairKernelCont38)
    (hw : IsBoundaryEigenfunction neumannProblem φ z w)
    (b : LocalEigenvalueBranch neumannProblem φ z) :
    Q w ≠ 0 ∧ HasFDerivAt b.toFun (bilinearGradient w) φ := by
  obtain ⟨a, ha, hwa, hbd⟩ := hw
  have hbd1 : a 0 = -a 1 := hbd.1
  obtain ⟨c, hc, hac⟩ := neumann_seed_multiple a ha hbd1
  obtain ⟨h0, hd⟩ := (simple_boundary_iff neumannProblem φ z).mp hs
  have hr : neumannChar38 φ z = 0 := h0
  have hsd : deriv (neumannChar38 φ) z ≠ 0 := hd
  obtain ⟨hQ, hgrad⟩ := complex_neumann_canonical_gradient φ z hr hsd
  have hw' : w = c • state φ z (![Complex.I, -Complex.I] : PairVec38) := by
    rw [hwa, hac, state_seed_smul]
  have hQw : Q w ≠ 0 := by rw [hw', Q_smul]; exact mul_ne_zero (pow_ne_zero 2 hc) hQ
  have hgw : bilinearGradient w = bilinearGradient (state φ z (![Complex.I, -Complex.I] : PairVec38)) := by
    rw [hw', bilinear_gradient_smul c _ hc hQ]
  refine ⟨hQw, ?_⟩
  rw [hgw, hgrad]
  -- transport the branch to the Dirichlet problem at -φ
  have hfe := neumannChar38_fun_eq_dirichlet_neg φ
  have hs' : IsSimpleBoundaryEigenvalue dirichletProblem (-φ) z := by
    refine (simple_boundary_iff dirichletProblem (-φ) z).mpr ⟨?_, ?_⟩
    · change dirichletChar (-φ) z = 0
      rw [← hfe]; exact hr
    · change deriv (dirichletChar (-φ)) z ≠ 0
      rw [← hfe]; exact hsd
  let b' : LocalEigenvalueBranch dirichletProblem (-φ) z :=
    { toFun := fun ψ => b.toFun (-ψ)
      domain := (fun ψ : PotPair => -ψ) ⁻¹' b.domain
      isOpen_domain := b.isOpen_domain.preimage continuous_neg
      base_mem := by simpa using b.base_mem
      analytic := fun ψ hψ => (b.analytic (-ψ) hψ).comp (analyticAt_id.neg)
      value := by simpa using b.value
      root := fun ψ hψ => by
        have h := b.root (-ψ) hψ
        change neumannChar38 (-ψ) (b.toFun (-ψ)) = 0 at h
        change dirichletChar ψ (b.toFun (-ψ)) = 0
        have e := neumannChar38_eq_dirichlet_neg (-ψ) (b.toFun (-ψ))
        rw [neg_neg] at e
        rw [← e]; exact h }
  have hD := dirichlet_branch_hasFDerivAt (-φ) z hs' b'
  have hcomp := hD.comp φ (hasFDerivAt_id φ).neg
  have hb_eq : b.toFun = fun ψ => b'.toFun (-ψ) := by
    funext ψ; change b.toFun ψ = b.toFun (-(-ψ)); rw [neg_neg]
  rw [hb_eq]
  have e : (dirImplicitGradient (-φ) z).comp (-ContinuousLinearMap.id ℂ PotPair) =
      -dirImplicitGradient (-φ) z :=
    ContinuousLinearMap.ext fun h => by simp
  rw [e] at hcomp
  exact hcomp

/-! ### Assembly -/

theorem spectral_gradient
    (P : BoundaryProblem) (φ : PotPair) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue P φ z)
    (w : PairKernelCont38)
    (hw : IsBoundaryEigenfunction P φ z w)
    (b : LocalEigenvalueBranch P φ z) :
    Q w ≠ 0 ∧
    HasFDerivAt b.toFun (bilinearGradient w) φ ∧
    spectralGradient b = bilinearGradient w := by
  have key : Q w ≠ 0 ∧ HasFDerivAt b.toFun (bilinearGradient w) φ := by
    obtain ⟨χ, B, hsrc⟩ := P
    rcases hsrc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨c, hc, rfl, rfl⟩
    · exact dirichlet_branch_gradient φ z hs w hw b
    · exact neumann_branch_gradient φ z hs w hw b
    · exact floquet_branch_gradient φ z c hc hs w hw b
  exact ⟨key.1, key.2, key.2.fderiv⟩

theorem spectral_gradient_integrability (w : PairKernelCont38) :
    IntervalIntegrable
      (fun s => pairKernelExt38 w s 0 * pairKernelExt38 w s 1) volume 0 1 ∧
    IntervalIntegrable
      (fun s => ‖pairKernelExt38 w s 0‖ ^ 2 +
        ‖pairKernelExt38 w s 1‖ ^ 2) volume 0 1 ∧
    ∀ h : PotPair, IntervalIntegrable
      (fun s => pairKernelExt38 (square w) s 0 * potRepFst38 h s +
        pairKernelExt38 (square w) s 1 * potRepSnd38 h s) volume 0 1 :=
  kernel_integrability w

theorem spectral_gradient_real_denominator
    (P : BoundaryProblem) (u : PhysicalL2) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue P (realSlice u) z)
    (w : PairKernelCont38)
    (hw : IsBoundaryEigenfunction P (realSlice u) z w)
    (hwr : realSymmetric w)
    (b : LocalEigenvalueBranch P (realSlice u) z) :
    0 < energy w ∧ Q w = (energy w : ℂ) ∧
    spectralGradient b =
      (energy w : ℂ)⁻¹ • integralPairCLM38 (square w) t1 := by
  obtain ⟨hQ, -, hsg⟩ := spectral_gradient P (realSlice u) z hs w hw b
  obtain ⟨a, ha, hwa, -⟩ := hw
  have hpos : 0 < energy w := by rw [hwa]; exact state_energy_positive _ _ _ ha
  have hQe : Q w = (energy w : ℂ) := real_denominator w hwr
  refine ⟨hpos, hQe, ?_⟩
  rw [hsg]
  unfold bilinearGradient
  rw [hQe]


/-! ### A20, A21: real-type eigenfunctions and the real-slice derivative -/

def conjSwap (a : PairVec38) : PairVec38 := ![star (a 1), star (a 0)]

theorem conjSwap_zero_iff (a : PairVec38) : conjSwap a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp [conjSwap] at h0 h1
    funext i
    fin_cases i <;> simp [h0, h1]
  · intro h; rw [h]; funext i; fin_cases i <;> simp [conjSwap]

theorem state_add (φ : PotPair) (z : ℂ) (a b : PairVec38) :
    state φ z (a + b) = state φ z a + state φ z b := by
  ext t i
  simp [state_eq_mulVec, Matrix.mulVec_add]

theorem state_conjSwap (u : PhysicalL2) (x : ℝ) (a : PairVec38) (t : Time) :
    state (realSlice u) (x : ℂ) (conjSwap a) t = conjSwap (state (realSlice u) (x : ℂ) a t) := by
  have h00 := fundPair_real_entry_star38 u x t 0 0
  have h01 := fundPair_real_entry_star38 u x t 0 1
  have h10 := fundPair_real_entry_star38 u x t 1 0
  have h11 := fundPair_real_entry_star38 u x t 1 1
  have h00' : (starRingEnd ℂ) (fundPair (realSlice u) (x : ℂ) t 0 0) = fundPair (realSlice u) (x : ℂ) t 1 1 := h00
  have h01' : (starRingEnd ℂ) (fundPair (realSlice u) (x : ℂ) t 0 1) = fundPair (realSlice u) (x : ℂ) t 1 0 := h01
  have h10' : (starRingEnd ℂ) (fundPair (realSlice u) (x : ℂ) t 1 0) = fundPair (realSlice u) (x : ℂ) t 0 1 := h10
  have h11' : (starRingEnd ℂ) (fundPair (realSlice u) (x : ℂ) t 1 1) = fundPair (realSlice u) (x : ℂ) t 0 0 := h11
  rw [state_eq_mulVec, state_eq_mulVec]
  generalize fundPair (realSlice u) (x : ℂ) t = M at h00' h01' h10' h11' ⊢
  funext i
  fin_cases i
  · simp [conjSwap, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h10', h11']
    ring
  · simp [conjSwap, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00', h01']
    ring

theorem boundary_linear_closed (P : BoundaryProblem) :
    (∀ a b a' b', P.boundary a b → P.boundary a' b' → P.boundary (a + a') (b + b')) ∧
    (∀ (s : ℂ) a b, P.boundary a b → P.boundary (s • a) (s • b)) := by
  obtain ⟨χ, B, hsrc⟩ := P
  rcases hsrc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨c, hc, rfl, rfl⟩
  · refine ⟨fun a b a' b' h h' => ⟨?_, ?_⟩, fun s a b h => ⟨?_, ?_⟩⟩
    · simp [h.1, h'.1]
    · simp [h.2, h'.2]
    · simp [h.1]
    · simp [h.2]
  · refine ⟨fun a b a' b' h h' => ⟨?_, ?_⟩, fun s a b h => ⟨?_, ?_⟩⟩
    · simp [h.1, h'.1]; ring
    · simp [h.2, h'.2]; ring
    · simp [h.1]
    · simp [h.2]
  · refine ⟨fun a b a' b' h h' => ?_, fun s a b h => ?_⟩
    · change b + b' = c • (a + a')
      have h1 : b = c • a := h
      have h2 : b' = c • a' := h'
      rw [h1, h2, smul_add]
    · change s • b = c • (s • a)
      have h1 : b = c • a := h
      rw [h1, smul_comm]

theorem boundary_conjSwap_closed (P : BoundaryProblem)
    (hc : ∀ c : ℂ, c ^ 2 = 1 → star c = c) (a b : PairVec38) (h : P.boundary a b) :
    P.boundary (conjSwap a) (conjSwap b) := by
  obtain ⟨χ, B, hsrc⟩ := P
  rcases hsrc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨c, hc1, rfl, rfl⟩
  · refine ⟨?_, ?_⟩
    · simp [conjSwap, h.1]
    · simp [conjSwap, h.2]
  · refine ⟨?_, ?_⟩
    · have := congrArg star h.1
      simp [conjSwap, star_neg] at this ⊢
      linear_combination this
    · have := congrArg star h.2
      simp [conjSwap, star_neg] at this ⊢
      linear_combination this
  · change conjSwap b = c • conjSwap a
    have h1 : b = c • a := h
    have hcr := hc c hc1
    rw [h1]
    funext i
    fin_cases i <;> simp [conjSwap, star_mul', hcr]

theorem exists_real_boundary_eigenfunction
    (P : BoundaryProblem) (u : PhysicalL2) (x : ℝ)
    (w : PairKernelCont38)
    (hw : IsBoundaryEigenfunction P (realSlice u) (x : ℂ) w) :
    ∃ v : PairKernelCont38,
      IsBoundaryEigenfunction P (realSlice u) (x : ℂ) v ∧ realSymmetric v := by
  obtain ⟨a, ha, hwa, hbd⟩ := hw
  obtain ⟨hadd, hsmul⟩ := boundary_linear_closed P
  have hcreal : ∀ c : ℂ, c ^ 2 = 1 → star c = c := by
    intro c hc
    have : (c - 1) * (c + 1) = 0 := by linear_combination hc
    rcases mul_eq_zero.mp this with h | h
    · have : c = 1 := by linear_combination h
      simp [this]
    · have : c = -1 := by linear_combination h
      simp [this]
  have hC : P.boundary (conjSwap a) (state (realSlice u) (x : ℂ) (conjSwap a) t1) := by
    rw [state_conjSwap]
    rw [hwa] at hbd
    exact boundary_conjSwap_closed P hcreal a _ hbd
  rw [hwa] at hbd
  by_cases hs : a + conjSwap a = 0
  · -- use I • (a - conjSwap a)
    have hCa : conjSwap a = -a := by linear_combination hs
    have hsub : a - conjSwap a ≠ 0 := by
      rw [hCa, sub_neg_eq_add]
      intro h0
      apply ha
      have : (2 : ℂ) • a = 0 := by rw [two_smul]; exact h0
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
    have hne : Complex.I • (a - conjSwap a) ≠ 0 := by
      intro h0
      exact hsub ((smul_eq_zero.mp h0).resolve_left Complex.I_ne_zero)
    have hb1 : P.boundary (a - conjSwap a)
        (state (realSlice u) (x : ℂ) a t1 - state (realSlice u) (x : ℂ) (conjSwap a) t1) := by
      have h := hadd a _ ((-1 : ℂ) • conjSwap a) _ hbd (hsmul (-1) _ _ hC)
      simpa [sub_eq_add_neg, state_seed_smul] using h
    have hb2 : P.boundary (Complex.I • (a - conjSwap a))
        (state (realSlice u) (x : ℂ) (Complex.I • (a - conjSwap a)) t1) := by
      have h := hsmul Complex.I _ _ hb1
      have e : state (realSlice u) (x : ℂ) (Complex.I • (a - conjSwap a)) =
          Complex.I • (state (realSlice u) (x : ℂ) a - state (realSlice u) (x : ℂ) (conjSwap a)) := by
        rw [state_seed_smul, sub_eq_add_neg, state_add, sub_eq_add_neg]
        have : state (realSlice u) (x : ℂ) (-conjSwap a) = -state (realSlice u) (x : ℂ) (conjSwap a) := by
          ext t i
          simp [state_eq_mulVec, Matrix.mulVec_neg]
        rw [this]
      rw [e]
      exact h
    refine ⟨state (realSlice u) (x : ℂ) (Complex.I • (a - conjSwap a)),
      ⟨_, hne, rfl, hb2⟩, ?_⟩
    apply real_state_symmetry
    simp only [Pi.smul_apply, Pi.sub_apply, conjSwap, Matrix.cons_val_zero, Matrix.cons_val_one,
      smul_eq_mul, star_mul', star_sub, star_star]
    have hI : star Complex.I = -Complex.I := by simp [Complex.star_def]
    rw [hI]
    ring
  · have hb1 : P.boundary (a + conjSwap a)
        (state (realSlice u) (x : ℂ) (a + conjSwap a) t1) := by
      have h := hadd a _ (conjSwap a) _ hbd hC
      have e : state (realSlice u) (x : ℂ) (a + conjSwap a) =
          state (realSlice u) (x : ℂ) a + state (realSlice u) (x : ℂ) (conjSwap a) := state_add _ _ _ _
      rw [e]
      exact h
    refine ⟨state (realSlice u) (x : ℂ) (a + conjSwap a), ⟨_, hs, rfl, hb1⟩, ?_⟩
    apply real_state_symmetry
    simp [conjSwap, add_comm]

/-- A21 -/
theorem real_slice_branch_derivative
    (P : BoundaryProblem) (u : PhysicalL2) (z : ℂ)
    (hs : IsSimpleBoundaryEigenvalue P (realSlice u) z)
    (w : PairKernelCont38)
    (hw : IsBoundaryEigenfunction P (realSlice u) z w)
    (hwr : realSymmetric w)
    (b : LocalEigenvalueBranch P (realSlice u) z) :
    HasFDerivAt (fun v : PhysicalL2 => (b.toFun (realSlice v)).re)
      (realEnergyGradient w) u := by
  obtain ⟨-, hb, -⟩ := spectral_gradient P (realSlice u) z hs w hw b
  have h1 := (hb.restrictScalars ℝ).comp u (realSlice.hasFDerivAt (x := u))
  have h2 := (Complex.reCLM.hasFDerivAt (x := b.toFun (realSlice u))).comp u h1
  have e : Complex.reCLM.comp (((bilinearGradient w).restrictScalars ℝ).comp realSlice) =
      realEnergyGradient w :=
    ContinuousLinearMap.ext fun h => by
      simpa using bilinear_real_energy w hwr h
  rw [e] at h2
  exact h2

end

end NlsGge.GK38.SimpleBoundary38
