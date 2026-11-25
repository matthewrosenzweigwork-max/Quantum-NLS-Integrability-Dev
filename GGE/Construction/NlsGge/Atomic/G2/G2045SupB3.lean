import Mathlib
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.Round6
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.WkbStructure
import NlsGge.Atomic.G2.G2045SupB1
import NlsGge.Atomic.G2.G2045SupB2

                                                                     
                                                                                
                                                                                                          
                                                                                                              
                                                                                                       
                                                                                               
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

theorem g2045b_h1_of (m : ℕ) (hm : 1 ≤ m) {u : PhysicalL2} (hu : physicalSobolev (m : ℝ) u) :
    physicalSobolev 1 u := by
  have := (psn_mono hm hu).1
  simpa using this

theorem g2045b_fS_add (u v : PhysicalL2) (n : ℤ) :
    fourierSeq38 (u + v) n = fourierSeq38 u n + fourierSeq38 v n := by
  show (reflectedFourierL2 (u + v) : ℤ → ℂ) n = _
  rw [map_add]; rfl

theorem g2045b_fS_smul (c : ℂ) (u : PhysicalL2) (n : ℤ) :
    fourierSeq38 (c • u) n = c * fourierSeq38 u n := by
  show (reflectedFourierL2 (c • u) : ℤ → ℂ) n = _
  rw [map_smul]; rfl

theorem g2045b_wd_add (u v : PhysicalL2) (hu : physicalSobolev 1 u) (hv : physicalSobolev 1 v) :
    weakDerivative (u + v) = weakDerivative u + weakDerivative v := by
  have huv : physicalSobolev 1 (u + v) := by
    have := (psn_add 1 (by simpa using hu) (by simpa using hv)).1
    simpa using this
  apply fourierSeq38_injective
  funext n
  have e := congrFun (fS_weakDerivative (u + v) huv) n
  have e1 := congrFun (fS_weakDerivative u hu) n
  have e2 := congrFun (fS_weakDerivative v hv) n
  rw [g2045b_fS_add (weakDerivative u) (weakDerivative v), e, e1, e2]
  simp only [Pi.neg_apply, dx, g2045b_fS_add]
  ring

theorem g2045b_wd_smul (c : ℂ) (u : PhysicalL2) (hu : physicalSobolev 1 u) :
    weakDerivative (c • u) = c • weakDerivative u := by
  have hcu : physicalSobolev 1 (c • u) := by
    exact g2045b_psob_smul 1 c u hu
  apply fourierSeq38_injective
  funext n
  have e := congrFun (fS_weakDerivative (c • u) hcu) n
  have e1 := congrFun (fS_weakDerivative u hu) n
  rw [g2045b_fS_smul, e1, e]
  simp only [Pi.neg_apply, dx, g2045b_fS_smul]
  ring


theorem g2045b_wd_zero : weakDerivative (0 : PhysicalL2) = 0 := by
  have h := g2045b_wd_smul 0 (0 : PhysicalL2) (g2045b_psob_zero 1)
  simpa using h

/-! ### physicalProduct is bilinear when the first factor is in H^1 -/

theorem g2045b_pP_add_left (u u' v : PhysicalL2) (hu : physicalSobolev 1 u)
    (hu' : physicalSobolev 1 u') :
    physicalProduct (u + u') v = physicalProduct u v + physicalProduct u' v := by
  have huu : physicalSobolev 1 (u + u') := by
    have := (psn_add 1 (by simpa using hu) (by simpa using hu')).1
    simpa using this
  have h1 : productInL2 u v := productInL2_of_H1 u v hu
  have h2 : productInL2 u' v := productInL2_of_H1 u' v hu'
  have h3 : productInL2 (u + u') v := productInL2_of_H1 (u + u') v huu
  apply Lp.ext
  filter_upwards [physicalProduct_ae _ _ h3, Lp.coeFn_add (physicalProduct u v) (physicalProduct u' v),
    physicalProduct_ae _ _ h1, physicalProduct_ae _ _ h2, Lp.coeFn_add u u'] with x a b c d e
  rw [a, b, Pi.add_apply, c, d, e]
  simp only [Pi.add_apply]
  ring

theorem g2045b_pP_add_right (u v v' : PhysicalL2) (hu : physicalSobolev 1 u) :
    physicalProduct u (v + v') = physicalProduct u v + physicalProduct u v' := by
  have h1 : productInL2 u v := productInL2_of_H1 u v hu
  have h2 : productInL2 u v' := productInL2_of_H1 u v' hu
  have h3 : productInL2 u (v + v') := productInL2_of_H1 u (v + v') hu
  apply Lp.ext
  filter_upwards [physicalProduct_ae _ _ h3, Lp.coeFn_add (physicalProduct u v) (physicalProduct u v'),
    physicalProduct_ae _ _ h1, physicalProduct_ae _ _ h2, Lp.coeFn_add v v'] with x a b c d e
  rw [a, b, Pi.add_apply, c, d, e]
  simp only [Pi.add_apply]
  ring

theorem g2045b_pP_smul_left (a : ℂ) (u v : PhysicalL2) (hu : physicalSobolev 1 u) :
    physicalProduct (a • u) v = a • physicalProduct u v := by
  have h1 : productInL2 u v := productInL2_of_H1 u v hu
  have h3 : productInL2 (a • u) v := productInL2_of_H1 (a • u) v (g2045b_psob_smul 1 a u hu)
  apply Lp.ext
  filter_upwards [physicalProduct_ae _ _ h3, Lp.coeFn_smul a (physicalProduct u v),
    physicalProduct_ae _ _ h1, Lp.coeFn_smul a u] with x a' b c d
  rw [a', b, Pi.smul_apply, c, d]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem g2045b_pP_smul_right (a : ℂ) (u v : PhysicalL2) (hu : physicalSobolev 1 u) :
    physicalProduct u (a • v) = a • physicalProduct u v := by
  have h1 : productInL2 u v := productInL2_of_H1 u v hu
  have h3 : productInL2 u (a • v) := productInL2_of_H1 u (a • v) hu
  apply Lp.ext
  filter_upwards [physicalProduct_ae _ _ h3, Lp.coeFn_smul a (physicalProduct u v),
    physicalProduct_ae _ _ h1, Lp.coeFn_smul a v] with x a' b c d
  rw [a', b, Pi.smul_apply, c, d]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem g2045b_pP_zero_left (v : PhysicalL2) : physicalProduct 0 v = 0 := by
  have h := g2045b_pP_smul_left 0 (0 : PhysicalL2) v (g2045b_psob_zero 1)
  simpa using h

/-! ### t-polynomial vector functions with H^m coefficients -/

/-- Monomials `t ↦ t^j • c` with `c ∈ H^m`. -/
def polyGen (m : ℕ) : Set (ℂ → PhysicalL2) :=
  {g | ∃ (j : ℕ) (c : PhysicalL2), physicalSobolev (m : ℝ) c ∧ g = fun t : ℂ => t ^ j • c}

/-- The complex span of the monomials with `H^m` coefficients. -/
def polyVec (m : ℕ) : Submodule ℂ (ℂ → PhysicalL2) := Submodule.span ℂ (polyGen m)

theorem g2045b_polyVec_val {m : ℕ} {f : ℂ → PhysicalL2} (hf : f ∈ polyVec m) (t : ℂ) :
    physicalSobolev (m : ℝ) (f t) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨j, c, hc, rfl⟩ := hg
    exact g2045b_psob_smul _ _ _ hc
  | zero => exact g2045b_psob_zero _
  | add f g _ _ ihf ihg => exact (psn_add m ihf ihg).1
  | smul a f _ ih => exact g2045b_psob_smul _ a _ ih

theorem g2045b_polyVec_mono {m m' : ℕ} (h : m ≤ m') : polyVec m' ≤ polyVec m :=
  Submodule.span_mono (fun g ⟨j, c, hc, e⟩ => ⟨j, c, (psn_mono h hc).1, e⟩)

theorem g2045b_polyVec_const {m : ℕ} (c : PhysicalL2) (hc : physicalSobolev (m : ℝ) c) :
    (fun _ : ℂ => c) ∈ polyVec m :=
  Submodule.subset_span ⟨0, c, hc, by funext t; simp⟩

theorem g2045b_polyVec_lin {m : ℕ} (c : PhysicalL2) (hc : physicalSobolev (m : ℝ) c) :
    (fun t : ℂ => t • c) ∈ polyVec m :=
  Submodule.subset_span ⟨1, c, hc, by funext t; simp⟩

theorem g2045b_polyVec_deriv {m : ℕ} {f : ℂ → PhysicalL2} (hf : f ∈ polyVec (m + 1)) :
    (fun t => weakDerivative (f t)) ∈ polyVec m := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨j, c, hc, rfl⟩ := hg
    have h1 := g2045b_h1_of (m + 1) (by omega) hc
    have e : (fun t : ℂ => weakDerivative (t ^ j • c)) = fun t : ℂ => t ^ j • weakDerivative c :=
      funext fun t => g2045b_wd_smul _ c h1
    rw [e]
    exact Submodule.subset_span ⟨j, weakDerivative c, (psn_deriv m hc).1, rfl⟩
  | zero =>
    have e : (fun t : ℂ => weakDerivative ((0 : ℂ → PhysicalL2) t)) = 0 :=
      funext fun t => g2045b_wd_zero
    rw [e]
    exact Submodule.zero_mem _
  | add f g hf hg ihf ihg =>
    have e : (fun t : ℂ => weakDerivative ((f + g) t)) =
        (fun t => weakDerivative (f t)) + fun t => weakDerivative (g t) :=
      funext fun t => g2045b_wd_add _ _ (g2045b_h1_of (m + 1) (by omega) (g2045b_polyVec_val hf t))
        (g2045b_h1_of (m + 1) (by omega) (g2045b_polyVec_val hg t))
    rw [e]
    exact Submodule.add_mem _ ihf ihg
  | smul a f hf ih =>
    have e : (fun t : ℂ => weakDerivative ((a • f) t)) = a • fun t => weakDerivative (f t) :=
      funext fun t => g2045b_wd_smul a _ (g2045b_h1_of (m + 1) (by omega) (g2045b_polyVec_val hf t))
    rw [e]
    exact Submodule.smul_mem _ a ih

theorem g2045b_polyVec_prod_gen {m : ℕ} (hm : 1 ≤ m) (c : PhysicalL2)
    (hc : physicalSobolev (m : ℝ) c) (j : ℕ) {g : ℂ → PhysicalL2} (hg : g ∈ polyVec m) :
    (fun t : ℂ => physicalProduct (t ^ j • c) (g t)) ∈ polyVec m := by
  obtain ⟨C, -, hP⟩ := psn_prod m hm
  have hc1 := g2045b_h1_of m hm hc
  have hu : ∀ t : ℂ, physicalSobolev 1 (t ^ j • c) := fun t => g2045b_psob_smul 1 _ c hc1
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨i, d, hd, rfl⟩ := hg
    have e : (fun t : ℂ => physicalProduct (t ^ j • c) (t ^ i • d)) =
        fun t : ℂ => t ^ (j + i) • physicalProduct c d := by
      funext t
      rw [g2045b_pP_smul_right _ _ _ (hu t), g2045b_pP_smul_left _ _ _ hc1, smul_smul, pow_add,
        mul_comm]
    rw [e]
    exact Submodule.subset_span ⟨j + i, physicalProduct c d, (hP c d hc hd).1, rfl⟩
  | zero =>
    have e : (fun t : ℂ => physicalProduct (t ^ j • c) ((0 : ℂ → PhysicalL2) t)) = 0 :=
      funext fun t => physicalProduct_zero' _
    rw [e]
    exact Submodule.zero_mem _
  | add f g _ _ ihf ihg =>
    have e : (fun t : ℂ => physicalProduct (t ^ j • c) ((f + g) t)) =
        (fun t => physicalProduct (t ^ j • c) (f t)) + fun t => physicalProduct (t ^ j • c) (g t) :=
      funext fun t => g2045b_pP_add_right _ _ _ (hu t)
    rw [e]
    exact Submodule.add_mem _ ihf ihg
  | smul a f _ ih =>
    have e : (fun t : ℂ => physicalProduct (t ^ j • c) ((a • f) t)) =
        a • fun t => physicalProduct (t ^ j • c) (f t) :=
      funext fun t => g2045b_pP_smul_right a _ _ (hu t)
    rw [e]
    exact Submodule.smul_mem _ a ih

theorem g2045b_polyVec_prod {m : ℕ} (hm : 1 ≤ m) {f g : ℂ → PhysicalL2} (hf : f ∈ polyVec m)
    (hg : g ∈ polyVec m) : (fun t : ℂ => physicalProduct (f t) (g t)) ∈ polyVec m := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, c, hc, rfl⟩ := hf
    exact g2045b_polyVec_prod_gen hm c hc j hg
  | zero =>
    have e : (fun t : ℂ => physicalProduct ((0 : ℂ → PhysicalL2) t) (g t)) = 0 :=
      funext fun t => g2045b_pP_zero_left _
    rw [e]
    exact Submodule.zero_mem _
  | add f f' hf hf' ihf ihf' =>
    have e : (fun t : ℂ => physicalProduct ((f + f') t) (g t)) =
        (fun t => physicalProduct (f t) (g t)) + fun t => physicalProduct (f' t) (g t) :=
      funext fun t => g2045b_pP_add_left _ _ _ (g2045b_h1_of m hm (g2045b_polyVec_val hf t))
        (g2045b_h1_of m hm (g2045b_polyVec_val hf' t))
    rw [e]
    exact Submodule.add_mem _ ihf ihf'
  | smul a f hf ih =>
    have e : (fun t : ℂ => physicalProduct ((a • f) t) (g t)) =
        a • fun t => physicalProduct (f t) (g t) :=
      funext fun t => g2045b_pP_smul_left a _ _ (g2045b_h1_of m hm (g2045b_polyVec_val hf t))
    rw [e]
    exact Submodule.smul_mem _ a ih

/-! ### The wkb coefficients along a complex line -/

theorem g2045b_wkb_poly (N : ℕ) (hN : 1 ≤ N) (A B : PotPair) (hA : pairSobolev (N : ℝ) A)
    (hB : pairSobolev (N : ℝ) B) :
    ∀ n : ℕ, ∀ k : ℕ, 1 ≤ k → k ≤ n → k ≤ N + 1 →
      (fun t : ℂ => wkbR (A + t • B) k) ∈ polyVec (N + 1 - k) := by
  intro n
  induction n with
  | zero => intro k h1 h2 h3; omega
  | succ n ih =>
    intro k hk1 hkn hkN
    by_cases hkn' : k ≤ n
    · exact ih k hk1 hkn' hkN
    have hk : k = n + 1 := by omega
    subst hk
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have e : (fun t : ℂ => wkbR (A + t • B) (0 + 1)) =
          fun t : ℂ => (-A.2) + t • (-B.2) := by
        funext t
        rw [show (0 : ℕ) + 1 = 1 from rfl, wkbR_one]
        show -(A.2 + t • B.2) = _
        module
      rw [e, show N + 1 - (0 + 1) = N by omega]
      exact Submodule.add_mem _ (g2045b_polyVec_const _ (psn_neg N hA.2).1)
        (g2045b_polyVec_lin _ (psn_neg N hB.2).1)
    · have hnN : n ≤ N := by omega
      set q := N - n + 1 with hq
      have hw : (fun t : ℂ => wkbR (A + t • B) n) ∈ polyVec ((N - n) + 1) := by
        have := ih n hpos le_rfl (by omega)
        rwa [show N + 1 - n = N - n + 1 by omega] at this
      have hD := g2045b_polyVec_deriv hw
      have hphi : (fun t : ℂ => A.1 + t • B.1) ∈ polyVec q :=
        Submodule.add_mem _ (g2045b_polyVec_const _ (psn_mono (by omega) hA.1).1)
          (g2045b_polyVec_lin _ (psn_mono (by omega) hB.1).1)
      have hS : (fun t : ℂ => ∑ j ∈ Finset.Icc 1 (n - 1),
          physicalProduct (wkbR (A + t • B) j) (wkbR (A + t • B) (n - j))) ∈ polyVec q := by
        have e : (fun t : ℂ => ∑ j ∈ Finset.Icc 1 (n - 1),
            physicalProduct (wkbR (A + t • B) j) (wkbR (A + t • B) (n - j))) =
            ∑ j ∈ Finset.Icc 1 (n - 1),
              (fun t : ℂ => physicalProduct (wkbR (A + t • B) j) (wkbR (A + t • B) (n - j))) := by
          funext t
          simp [Finset.sum_apply]
        rw [e]
        refine Submodule.sum_mem _ (fun j hj => ?_)
        rw [Finset.mem_Icc] at hj
        have h1 := g2045b_polyVec_mono (m := q) (m' := N + 1 - j) (by omega)
          (ih j hj.1 (by omega) (by omega))
        have h2 := g2045b_polyVec_mono (m := q) (m' := N + 1 - (n - j)) (by omega)
          (ih (n - j) (by omega) (by omega) (by omega))
        exact g2045b_polyVec_prod (by omega) (h1) (h2)
      have hP := g2045b_polyVec_prod (m := q) (by omega) hphi hS
      have hP' := g2045b_polyVec_mono (m := N - n) (m' := q) (by omega) hP
      have e : (fun t : ℂ => wkbR (A + t • B) (n + 1)) =
          (fun t : ℂ => weakDerivative (wkbR (A + t • B) n)) +
          fun t : ℂ => physicalProduct (A.1 + t • B.1) (∑ j ∈ Finset.Icc 1 (n - 1),
            physicalProduct (wkbR (A + t • B) j) (wkbR (A + t • B) (n - j))) := by
        funext t
        exact wkbR_succ (A + t • B) n hpos
      rw [e, show N + 1 - (n + 1) = N - n by omega]
      exact Submodule.add_mem _ hD hP'

/-! ### The scalar bilinear form -/

def g2045bB : PhysicalL2 →ₗ[ℂ] PhysicalL2 →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y : PhysicalL2 => inner ℂ (star x) y)
    (fun x₁ x₂ y => by rw [g2045b_star_add, inner_add_left])
    (fun c x y => by rw [g2045b_star_smul, inner_smul_left]; simp)
    (fun x y₁ y₂ => by rw [inner_add_right])
    (fun c x y => by rw [inner_smul_right]; simp)

theorem g2045bB_eq (x y : PhysicalL2) :
    g2045bB x y = ∫ z : PhysicalCircle, x z * y z ∂spatialMeasure := by
  show inner ℂ (star x) y = _
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star x] with z hz
  rw [hz]
  simp [RCLike.inner_apply, mul_comm]

theorem g2045b_scalar_poly {f g : ℂ → PhysicalL2} (hf : f ∈ polyVec 0) (hg : g ∈ polyVec 0) :
    ∃ p : Polynomial ℂ, ∀ t : ℂ, g2045bB (f t) (g t) = p.eval t := by
  have gen : ∀ (j : ℕ) (c : PhysicalL2), ∀ g : ℂ → PhysicalL2, g ∈ polyVec 0 →
      ∃ p : Polynomial ℂ, ∀ t : ℂ, g2045bB (t ^ j • c) (g t) = p.eval t := by
    intro j c g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨i, d, -, rfl⟩ := hg
      refine ⟨Polynomial.C (g2045bB c d) * Polynomial.X ^ (j + i), fun t => ?_⟩
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, pow_add]
      ring
    | zero => exact ⟨0, fun t => by simp⟩
    | add f g _ _ ihf ihg =>
      obtain ⟨p, hp⟩ := ihf
      obtain ⟨q, hq⟩ := ihg
      exact ⟨p + q, fun t => by
        show g2045bB (t ^ j • c) (f t + g t) = _
        rw [map_add, hp t, hq t, Polynomial.eval_add]⟩
    | smul a f _ ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨a • p, fun t => by
        show g2045bB (t ^ j • c) (a • f t) = _
        rw [map_smul, hp t, Polynomial.eval_smul]⟩
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨j, c, -, rfl⟩ := hf
    exact gen j c g hg
  | zero => exact ⟨0, fun t => by simp⟩
  | add f f' _ _ ihf ihf' =>
    obtain ⟨p, hp⟩ := ihf
    obtain ⟨q, hq⟩ := ihf'
    exact ⟨p + q, fun t => by
      show g2045bB (f t + f' t) (g t) = _
      rw [map_add, LinearMap.add_apply, hp t, hq t, Polynomial.eval_add]⟩
  | smul a f _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨a • p, fun t => by
      show g2045bB (a • f t) (g t) = _
      rw [map_smul, LinearMap.smul_apply, hp t, Polynomial.eval_smul]⟩

/-- `hierarchyHamiltonian k` is a polynomial in `t` along every complex line `A + t B` with
`A, B ∈ H^(k-1) × H^(k-1)`, `k ≥ 2`. -/
theorem g2045b_hamiltonian_poly (k : ℕ) (hk : 2 ≤ k) (A B : PotPair)
    (hA : pairSobolev ((k - 1 : ℕ) : ℝ) A) (hB : pairSobolev ((k - 1 : ℕ) : ℝ) B) :
    ∃ p : Polynomial ℂ, ∀ t : ℂ, hierarchyHamiltonian k (A + t • B) = p.eval t := by
  obtain ⟨N, rfl⟩ : ∃ N, k = N + 1 := ⟨k - 1, by omega⟩
  have hN : 1 ≤ N := by omega
  simp only [Nat.add_sub_cancel] at hA hB
  have hw := g2045b_wkb_poly N hN A B hA hB (N + 1) (N + 1) (by omega) le_rfl le_rfl
  rw [Nat.sub_self] at hw
  have hphi : (fun t : ℂ => A.1 + t • B.1) ∈ polyVec 0 :=
    Submodule.add_mem _ (g2045b_polyVec_const _ (psn_mono (by omega) hA.1).1)
      (g2045b_polyVec_lin _ (psn_mono (by omega) hB.1).1)
  obtain ⟨p, hp⟩ := g2045b_scalar_poly hphi hw
  refine ⟨p, fun t => ?_⟩
  rw [← hp t, g2045bB_eq]
  unfold hierarchyHamiltonian
  rw [if_neg (by omega)]
  rfl

theorem g2045b_hamiltonian_line_analytic (k : ℕ) (hk : 2 ≤ k) (x A : PotPair)
    (hx : pairSobolev ((k - 1 : ℕ) : ℝ) x) (hA : pairSobolev ((k - 1 : ℕ) : ℝ) A) :
    AnalyticOnNhd ℂ (fun s : ℂ => hierarchyHamiltonian k (x + s • A)) Set.univ := by
  obtain ⟨p, hp⟩ := g2045b_hamiltonian_poly k hk x A hx hA
  have e : (fun s : ℂ => hierarchyHamiltonian k (x + s • A)) = fun s => p.eval s := funext hp
  rw [e]
  exact (Polynomial.differentiable p).differentiableOn.analyticOnNhd isOpen_univ

end NlsGge.GKDefinitionDesign
end
