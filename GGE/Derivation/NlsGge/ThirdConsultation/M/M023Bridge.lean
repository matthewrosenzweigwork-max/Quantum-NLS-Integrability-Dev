import Mathlib
import NlsGge.ThirdConsultation.M.M023Host
import NlsGge.ThirdConsultation.M.M022Host
import NlsGge.Analysis.FullCoverFourier
import NlsGge.Sobolev.PeriodicBridge

/-!
# M-023 carrier bridges (proof development, AUTHOR; not self-reviewed)

Proof of `weighted_code_bridges` (Pro round 10 section 3, "Exact carrier construction obligations"),
printed head verbatim at the end. Every `tsum` identity is preceded by summability or is an `ENNReal`
identity; the real accessor is used only after finiteness.
-/

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
noncomputable section

open NlsGge.ThirdConsultation.MTwoMode
open NlsGge.Atomic.KST003

theorem w_ge_one_of_oneDerivative (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (k : ℤ) : 1 ≤ w k := by
  obtain ⟨v, hv1, _, _, hwv⟩ := hw
  rw [hwv k]
  have h1 : (1 : ℝ) ≤ NlsGge.Atomic.M.M054.indexWeight k := by
    unfold NlsGge.Atomic.M.M054.indexWeight
    have := abs_nonneg ((k : ℝ))
    linarith
  calc (1 : ℝ) ≤ NlsGge.Atomic.M.M054.indexWeight k := h1
    _ = NlsGge.Atomic.M.M054.indexWeight k * 1 := (mul_one _).symm
    _ ≤ NlsGge.Atomic.M.M054.indexWeight k * v k :=
        mul_le_mul_of_nonneg_left (hv1 k) (le_trans zero_le_one h1)

theorem tsum_bool_prod (g : Bool × ℤ → ℝ≥0∞) :
    ∑' p : Bool × ℤ, g p = ∑' k : ℤ, (g (true, k) + g (false, k)) := by
  have h1 : ∑' p : Bool × ℤ, g p = ∑' c : ℤ × Bool, g (c.2, c.1) :=
    ((Equiv.prodComm ℤ Bool).tsum_eq g).symm
  rw [h1]
  have h2 := ENNReal.tsum_prod (f := fun (k : ℤ) (b : Bool) => g (b, k))
  refine h2.trans (tsum_congr fun k => ?_)
  rw [tsum_fintype, Fintype.sum_bool]

theorem summable_of_tsum_ofReal_ne_top {ι : Type*} (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    (h : ∑' i, ENNReal.ofReal (g i) ≠ ⊤) : Summable g := by
  have h1 := ENNReal.summable_toReal h
  have h2 : (fun i => (ENNReal.ofReal (g i)).toReal) = g :=
    funext fun i => ENNReal.toReal_ofReal (hg i)
  rw [h2] at h1
  exact h1

theorem lp_hasSum_sq {ι : Type*} (x : lp (fun _ : ι => ℂ) 2) :
    HasSum (fun i => ‖x i‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem lp_energy {ι : Type*} (x : lp (fun _ : ι => ℂ) 2) :
    ∑' i, ENNReal.ofReal (‖x i‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have h := lp_hasSum_sq x
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h.summable, h.tsum_eq]

theorem memℓp_two_of_summable {ι : Type*} (c : ι → ℂ) (h : Summable fun i => ‖c i‖ ^ 2) :
    Memℓp c 2 := by
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem summable_of_energy_ne_top {ι : Type*} (c : ι → ℂ)
    (h : ∑' i, ENNReal.ofReal (‖c i‖ ^ 2) ≠ ⊤) : Memℓp c 2 :=
  memℓp_two_of_summable c (summable_of_tsum_ofReal_ne_top _ (fun i => sq_nonneg _) h)

theorem norm_real_cast_sq (r : ℝ) (z : ℂ) : ‖(r : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### Source bridge -/

def srcFun (w : ℤ → ℝ) (n : ℤ) (f : KSTPairL2) : Bool × ℤ → ℂ :=
  fun p => (shiftWeight w n p.1 p.2 : ℂ) * coefficientPair f p.1 p.2

theorem src_energy (w : ℤ → ℝ) (n : ℤ) (f : KSTPairL2) :
    shiftedPairEnergy w n false (coefficientPair f) =
      ∑' p : Bool × ℤ, ENNReal.ofReal (‖srcFun w n f p‖ ^ 2) := by
  rw [tsum_bool_prod]
  unfold shiftedPairEnergy
  refine tsum_congr fun k => ?_
  simp only [srcFun, shiftWeight, norm_real_cast_sq, ite_true, Bool.false_eq_true, ite_false]
  rw [← ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  congr 1
  simp only [sub_eq_add_neg, neg_neg]

theorem src_exists_unique_of_energy (w : ℤ → ℝ) (n : ℤ) (f : KSTPairL2)
    (h : shiftedPairEnergy w n false (coefficientPair f) ≠ ⊤) :
    ∃! x : SourceCode w n, RepresentsSource w n x f := by
  rw [src_energy] at h
  have hm : Memℓp (srcFun w n f) 2 := summable_of_energy_ne_top _ h
  refine ⟨⟨srcFun w n f, hm⟩, fun b k => rfl, ?_⟩
  intro y hy
  apply Subtype.ext
  funext p
  obtain ⟨b, k⟩ := p
  exact hy b k

theorem src_norm_of_represents (w : ℤ → ℝ) (n : ℤ) (x : SourceCode w n) (f : KSTPairL2)
    (h : RepresentsSource w n x f) :
    shiftedPairEnergy w n false (coefficientPair f) = ENNReal.ofReal (‖x‖ ^ 2) ∧
    shiftedPairNorm w n false (coefficientPair f) = ‖x‖ := by
  have hx : ∀ p : Bool × ℤ, x p = srcFun w n f p := fun p => h p.1 p.2
  have he : shiftedPairEnergy w n false (coefficientPair f) = ENNReal.ofReal (‖x‖ ^ 2) := by
    rw [src_energy, ← lp_energy x]
    exact tsum_congr fun p => by rw [hx p]
  refine ⟨he, ?_⟩
  unfold shiftedPairNorm
  rw [he, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem src_exists_of_code (w : ℤ → ℝ) (hw1 : ∀ k : ℤ, 1 ≤ w k) (n : ℤ) (x : SourceCode w n) :
    ∃! f : KSTPairL2, RepresentsSource w n x f := by
  have hW : ∀ b : Bool, ∀ k : ℤ, 1 ≤ shiftWeight w n b k := by
    intro b k
    unfold shiftWeight
    split_ifs <;> exact hw1 _
  have hWne : ∀ b : Bool, ∀ k : ℤ, (shiftWeight w n b k : ℂ) ≠ 0 := by
    intro b k
    exact_mod_cast (lt_of_lt_of_le one_pos (hW b k)).ne'
  set c : Bool × ℤ → ℂ := fun p => x p / (shiftWeight w n p.1 p.2 : ℂ) with hc
  have hcsum : Summable fun p : Bool × ℤ => ‖c p‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_) (lp_hasSum_sq x).summable
    simp only [hc, norm_div, Complex.norm_real, Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ |shiftWeight w n p.1 p.2| := by
      rw [abs_of_nonneg (le_trans zero_le_one (hW _ _))]
      exact hW _ _
    have h0 : 0 ≤ ‖x p‖ := norm_nonneg _
    have : ‖x p‖ / |shiftWeight w n p.1 p.2| ≤ ‖x p‖ :=
      div_le_self h0 h1
    exact pow_le_pow_left₀ (div_nonneg h0 (abs_nonneg _)) this 2
  have hcb : ∀ b : Bool, Memℓp (fun k : ℤ => c (b, k)) 2 := by
    intro b
    apply memℓp_two_of_summable
    exact hcsum.comp_injective (i := fun k : ℤ => (b, k)) (fun k k' h => by simpa using h)
  let ell : Bool → lp (fun _ : ℤ => ℂ) 2 := fun b => ⟨fun k => c (b, k), hcb b⟩
  let F : KSTPairL2 :=
    WithLp.toLp 2 (fun b : Bool => (fourierBasis (T := (2 : ℝ))).repr.symm (ell b))
  have hcoef : ∀ b : Bool, ∀ k : ℤ, coefficientPair F b k = c (b, k) := by
    intro b k
    have h1 : coefficientPair F b k = (fourierBasis (T := (2 : ℝ))).repr (F b) k :=
      (fourierBasis_repr _ _).symm
    rw [h1]
    have h2 : F b = (fourierBasis (T := (2 : ℝ))).repr.symm (ell b) := rfl
    rw [h2, LinearIsometryEquiv.apply_symm_apply]
  refine ⟨F, fun b k => ?_, ?_⟩
  · rw [hcoef b k]
    simp only [hc]
    rw [mul_div_cancel₀ _ (hWne b k)]
  · intro g hg
    apply PiLp.ext
    intro b
    apply (fourierBasis (T := (2 : ℝ))).repr.injective
    apply Subtype.ext
    funext k
    have e1 : (fourierBasis (T := (2 : ℝ))).repr (g b) k = coefficientPair g b k :=
      fourierBasis_repr _ _
    have e2 : (fourierBasis (T := (2 : ℝ))).repr (F b) k = coefficientPair F b k :=
      fourierBasis_repr _ _
    rw [e1, e2, hcoef b k]
    have := hg b k
    simp only [hc]
    rw [this]
    rw [mul_div_cancel_left₀ _ (hWne b k)]

/-! ### Potential bridge -/

def potFun (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) : Bool × ℤ → ℂ :=
  fun p => (w (2 * p.2) : ℂ) * potentialCoefficientPair φ p.1 (2 * p.2)

theorem pc_odd (φ : NlsGge.GK38.PotPair) (b : Bool) (k : ℤ) (hk : k % 2 ≠ 0) :
    potentialCoefficientPair φ b k = 0 := by
  unfold potentialCoefficientPair
  exact NlsGge.Analysis.naturalPhysicalCoverL2_fourier_odd _ k hk

theorem pc_even (φ : NlsGge.GK38.PotPair) (b : Bool) (j : ℤ) :
    potentialCoefficientPair φ b (2 * j) =
      NlsGge.Pilot.physicalFourier (if b then φ.1 else φ.2 : NlsGge.Pilot.PhysicalL2) j := by
  unfold potentialCoefficientPair
  exact NlsGge.Analysis.naturalPhysicalCoverL2_fourier_even _ j

theorem pot_energy (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair) :
    potentialCoefficientEnergy w φ =
      ∑' p : Bool × ℤ, ENNReal.ofReal (‖potFun w φ p‖ ^ 2) := by
  rw [tsum_bool_prod]
  unfold potentialCoefficientEnergy
  have hinj : Function.Injective (fun j : ℤ => 2 * j) := fun a b h => by simpa using h
  rw [← hinj.tsum_eq (f := fun k : ℤ => ENNReal.ofReal
    (w k ^ 2 * (‖potentialCoefficientPair φ true k‖ ^ 2 +
      ‖potentialCoefficientPair φ false k‖ ^ 2)))]
  · refine tsum_congr fun j => ?_
    simp only [potFun, norm_real_cast_sq]
    rw [← ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    congr 1
    ring
  · intro k hk
    by_contra hne
    apply hk
    have hodd : k % 2 ≠ 0 := by
      intro h0
      exact hne ⟨k / 2, by simp only; omega⟩
    simp [pc_odd φ true k hodd, pc_odd φ false k hodd]

theorem pot_exists_unique_of_energy (w : ℤ → ℝ) (φ : NlsGge.GK38.PotPair)
    (h : potentialCoefficientEnergy w φ ≠ ⊤) :
    ∃! a : PotentialCode w, RepresentsPotential w a φ := by
  rw [pot_energy] at h
  have hm : Memℓp (potFun w φ) 2 := summable_of_energy_ne_top _ h
  refine ⟨⟨potFun w φ, hm⟩, fun b k => rfl, ?_⟩
  intro y hy
  apply Subtype.ext
  funext p
  obtain ⟨b, k⟩ := p
  exact hy b k

theorem pot_norm_of_represents (w : ℤ → ℝ) (a : PotentialCode w) (φ : NlsGge.GK38.PotPair)
    (h : RepresentsPotential w a φ) :
    potentialCoefficientEnergy w φ = ENNReal.ofReal (‖a‖ ^ 2) ∧
    potentialCoefficientNorm w φ = ‖a‖ := by
  have hx : ∀ p : Bool × ℤ, a p = potFun w φ p := fun p => h p.1 p.2
  have he : potentialCoefficientEnergy w φ = ENNReal.ofReal (‖a‖ ^ 2) := by
    rw [pot_energy, ← lp_energy a]
    exact tsum_congr fun p => by rw [hx p]
  refine ⟨he, ?_⟩
  unfold potentialCoefficientNorm
  rw [he, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem pot_exists_of_code (w : ℤ → ℝ) (hw1 : ∀ k : ℤ, 1 ≤ w k) (a : PotentialCode w) :
    ∃! φ : NlsGge.GK38.PotPair, RepresentsPotential w a φ := by
  have hWne : ∀ k : ℤ, (w (2 * k) : ℂ) ≠ 0 := fun k =>
    by exact_mod_cast (lt_of_lt_of_le one_pos (hw1 _)).ne'
  set c : Bool × ℤ → ℂ := fun p => a p / (w (2 * p.2) : ℂ) with hc
  have hcsum : Summable fun p : Bool × ℤ => ‖c p‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_) (lp_hasSum_sq a).summable
    simp only [hc, norm_div, Complex.norm_real, Real.norm_eq_abs]
    have h1 : (1 : ℝ) ≤ |w (2 * p.2)| := by
      rw [abs_of_nonneg (le_trans zero_le_one (hw1 _))]
      exact hw1 _
    have h0 : 0 ≤ ‖a p‖ := norm_nonneg _
    exact pow_le_pow_left₀ (div_nonneg h0 (abs_nonneg _)) (div_le_self h0 h1) 2
  have hcb : ∀ b : Bool, Memℓp (fun k : ℤ => c (b, k)) 2 := by
    intro b
    apply memℓp_two_of_summable
    exact hcsum.comp_injective (i := fun k : ℤ => (b, k)) (fun k k' h => by simpa using h)
  let ell : Bool → lp (fun _ : ℤ => ℂ) 2 := fun b => ⟨fun k => c (b, k), hcb b⟩
  let φ0 : NlsGge.GK38.PotPair :=
    (NlsGge.Pilot.physicalFourierL2.symm (ell true), NlsGge.Pilot.physicalFourierL2.symm (ell false))
  have hphys : ∀ b : Bool, ∀ k : ℤ,
      NlsGge.Pilot.physicalFourier (if b then φ0.1 else φ0.2 : NlsGge.Pilot.PhysicalL2) k = c (b, k) := by
    intro b k
    cases b
    · show NlsGge.Pilot.physicalFourier (NlsGge.Pilot.physicalFourierL2.symm (ell false)) k = _
      rw [← NlsGge.Pilot.physicalFourierL2_apply, LinearIsometryEquiv.apply_symm_apply]
    · show NlsGge.Pilot.physicalFourier (NlsGge.Pilot.physicalFourierL2.symm (ell true)) k = _
      rw [← NlsGge.Pilot.physicalFourierL2_apply, LinearIsometryEquiv.apply_symm_apply]
  refine ⟨φ0, fun b k => ?_, ?_⟩
  · rw [pc_even, hphys b k]
    simp only [hc]
    rw [mul_div_cancel₀ _ (hWne k)]
  · intro φ hφ
    have hpc : ∀ b : Bool, ∀ k : ℤ,
        NlsGge.Pilot.physicalFourier (if b then φ.1 else φ.2 : NlsGge.Pilot.PhysicalL2) k = c (b, k) := by
      intro b k
      rw [← pc_even]
      have := hφ b k
      simp only [hc]
      rw [this, mul_div_cancel_left₀ _ (hWne k)]
    have hb : ∀ b : Bool, (if b then φ.1 else φ.2 : NlsGge.Pilot.PhysicalL2) =
        (if b then φ0.1 else φ0.2 : NlsGge.Pilot.PhysicalL2) := by
      intro b
      apply NlsGge.Pilot.physicalFourierL2.injective
      apply Subtype.ext
      funext k
      rw [NlsGge.Pilot.physicalFourierL2_apply, NlsGge.Pilot.physicalFourierL2_apply,
        hpc b k, hphys b k]
    exact Prod.ext (hb true) (hb false)

theorem weighted_code_bridges
    (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (n : ℤ) :
    (∀ φ : NlsGge.GK38.PotPair,
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤ →
        ∃! a : PotentialCode w, RepresentsPotential w a φ) ∧
    (∀ a : PotentialCode w,
      ∃! φ : NlsGge.GK38.PotPair, RepresentsPotential w a φ) ∧
    (∀ (a : PotentialCode w) (φ : NlsGge.GK38.PotPair),
      RepresentsPotential w a φ →
        NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ =
            ENNReal.ofReal (‖a‖ ^ 2) ∧
        NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ = ‖a‖) ∧
    (∀ f : NlsGge.Atomic.KST003.KSTPairL2,
      NlsGge.ThirdConsultation.MTwoMode.shiftedPairEnergy w n false
        (NlsGge.ThirdConsultation.MTwoMode.coefficientPair f) ≠ ⊤ →
        ∃! x : SourceCode w n, RepresentsSource w n x f) ∧
    (∀ x : SourceCode w n,
      ∃! f : NlsGge.Atomic.KST003.KSTPairL2, RepresentsSource w n x f) ∧
    (∀ (x : SourceCode w n) (f : NlsGge.Atomic.KST003.KSTPairL2),
      RepresentsSource w n x f →
        NlsGge.ThirdConsultation.MTwoMode.shiftedPairEnergy w n false
          (NlsGge.ThirdConsultation.MTwoMode.coefficientPair f) =
            ENNReal.ofReal (‖x‖ ^ 2) ∧
        NlsGge.ThirdConsultation.MTwoMode.shiftedPairNorm w n false
          (NlsGge.ThirdConsultation.MTwoMode.coefficientPair f) = ‖x‖) := by
  have hw1 := w_ge_one_of_oneDerivative w hw
  exact ⟨fun φ h => pot_exists_unique_of_energy w φ h,
    fun a => pot_exists_of_code w hw1 a,
    fun a φ h => pot_norm_of_represents w a φ h,
    fun f h => src_exists_unique_of_energy w n f h,
    fun x => src_exists_of_code w hw1 n x,
    fun x f h => src_norm_of_represents w n x f h⟩

end
end NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
