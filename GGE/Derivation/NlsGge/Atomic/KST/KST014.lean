-- INERT / UNCOMPILED smallest KST014 path-convergence prerequisite.
-- Candidate context only; no production source/import/interface change.
import NlsGge.Atomic.KST.KST013

set_option autoImplicit false
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST007
open scoped ENNReal

/-- One actual positive Fourier block earns its row mass and preserves the
nonnegative-real coefficient invariant used by finite path induction. -/
private lemma stage14A_positive_step_mass
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (upper : Bool)
    (f : SpectralScalarL2)
    (hf : ∀ j : ℤ, 0 ≤ (spectralCoeff f j).re ∧ (spectralCoeff f j).im = 0)
    (l : ℤ) :
    Summable (fun j : ℤ => positiveKernel φ n upper l j * (spectralCoeff f j).re) ∧
    spectralCoeff (positiveBlock φ n upper f) l =
      ((∑' j : ℤ, positiveKernel φ n upper l j * (spectralCoeff f j).re : ℝ) : ℂ) ∧
    (0 ≤ (spectralCoeff (positiveBlock φ n upper f) l).re ∧
      (spectralCoeff (positiveBlock φ n upper f) l).im = 0) ∧
    (∑' j : ℤ, ENNReal.ofReal
      (positiveKernel φ n upper l j * (spectralCoeff f j).re)) =
        ENNReal.ofReal (spectralCoeff (positiveBlock φ n upper f) l).re ∧
    (∑' j : ℤ, ENNReal.ofReal
      (positiveKernel φ n upper l j * (spectralCoeff f j).re)) ≠ ⊤ := by
  have hkernel (j : ℤ) : 0 ≤ positiveKernel φ n upper l j := by
    change 0 ≤ majorantCoeff φ (l - j) *
      reciprocalDistance n (if upper then j else -j)
    apply mul_nonneg (majorant_nonneg φ (l - j))
    unfold reciprocalDistance
    split_ifs <;> positivity
  have hreal (j : ℤ) : spectralCoeff f j = ((spectralCoeff f j).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact (hf j).2
  have hnonneg (j : ℤ) :
      0 ≤ positiveKernel φ n upper l j * (spectralCoeff f j).re :=
    mul_nonneg (hkernel j) (hf j).1
  have hnorm (j : ℤ) :
      ‖(positiveKernel φ n upper l j : ℂ) * spectralCoeff f j‖ =
        positiveKernel φ n upper l j * (spectralCoeff f j).re := by
    rw [hreal j, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hnonneg j)]
    simp only [Complex.ofReal_re]
  have hs : Summable
      (fun j : ℤ => positiveKernel φ n upper l j * (spectralCoeff f j).re) :=
    ((positiveBlock_coeff φ n upper f l).1).congr hnorm
  have hout : spectralCoeff (positiveBlock φ n upper f) l =
      ((∑' j : ℤ, positiveKernel φ n upper l j * (spectralCoeff f j).re : ℝ) : ℂ) := by
    rw [(positiveBlock_coeff φ n upper f l).2]
    calc
      (∑' j : ℤ, (positiveKernel φ n upper l j : ℂ) * spectralCoeff f j) =
          ∑' j : ℤ,
            ((positiveKernel φ n upper l j * (spectralCoeff f j).re : ℝ) : ℂ) := by
        apply tsum_congr
        intro j
        rw [hreal j, Complex.ofReal_mul]
        simp only [Complex.ofReal_re]
      _ = _ := (Complex.ofReal_tsum _).symm
  have houtre : (spectralCoeff (positiveBlock φ n upper f) l).re =
      ∑' j : ℤ, positiveKernel φ n upper l j * (spectralCoeff f j).re := by
    rw [hout]
    rfl
  have houtim : (spectralCoeff (positiveBlock φ n upper f) l).im = 0 := by
    rw [hout]
    rfl
  have hmass : (∑' j : ℤ, ENNReal.ofReal
      (positiveKernel φ n upper l j * (spectralCoeff f j).re)) =
        ENNReal.ofReal (spectralCoeff (positiveBlock φ n upper f) l).re := by
    rw [houtre]
    exact (ENNReal.ofReal_tsum_of_nonneg hnonneg hs).symm
  refine ⟨hs, hout, ⟨?_, houtim⟩, hmass, ?_⟩
  · rw [houtre]
    exact tsum_nonneg hnonneg
  · exact hs.tsum_ofReal_lt_top.ne

end NlsGge.Atomic.KST014
end

set_option autoImplicit false
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST007

/-- A literal integer translate of the actual Fourier majorant is the
Fourier family of an actual scalar L2 element, with real nonnegative entries. -/
private lemma stage14B_shifted_majorant_exists
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (p : ℤ) :
    ∃ f : SpectralScalarL2,
      (∀ j : ℤ, spectralCoeff f j = (majorantCoeff φ (j - p) : ℂ)) ∧
      ∀ j : ℤ, 0 ≤ (spectralCoeff f j).re ∧ (spectralCoeff f j).im = 0 := by
  let a : lp (fun _ : ℤ => ℂ) 2 :=
    (fourierBasis (T := (2 : ℝ))).repr (majorantFunction φ)
  have hs0 : Summable (fun j : ℤ => ‖a j‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num) a).summable
  have hinj : Function.Injective (fun j : ℤ => j - p) := by
    intro i j h
    have hc := congrArg (fun x : ℤ => x + p) h
    simpa only [sub_add_cancel] using hc
  have hs : Summable (fun j : ℤ => ‖a (j - p)‖ ^ 2) :=
    hs0.comp_injective hinj
  let c : lp (fun _ : ℤ => ℂ) 2 :=
    ⟨fun j => a (j - p), memℓp_gen (by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs)⟩
  let f : SpectralScalarL2 := (fourierBasis (T := (2 : ℝ))).repr.symm c
  have hcoeff (j : ℤ) : spectralCoeff f j = (majorantCoeff φ (j - p) : ℂ) := by
    change (fourierBasis (T := (2 : ℝ))).repr
      ((fourierBasis (T := (2 : ℝ))).repr.symm c) j = _
    rw [LinearIsometryEquiv.apply_symm_apply]
    change spectralCoeff (majorantFunction φ) (j - p) = _
    exact majorantFunction_coeff φ (j - p)
  refine ⟨f, hcoeff, ?_⟩
  intro j
  rw [hcoeff j]
  exact ⟨majorant_nonneg φ (j - p), rfl⟩

end NlsGge.Atomic.KST014
end

/- INERT / UNCOMPILED finite-path majorant and literal resonance support.
   Locally consumes the exact StageA02 and StageB01 commands in one file.
   No path convergence or small positive-operator norm is assumed. -/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST007
open scoped ENNReal

/-- Actual finite alternating compositions, with no inverse or infinite limit. -/
private def stage14C_positiveIter
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (f : SpectralScalarL2) :
    ℕ → Bool → SpectralScalarL2
  | 0, _ => f
  | m + 1, upper => positiveBlock φ n upper
      (stage14C_positiveIter φ n f m (!upper))

/-- Every factor is an actual source positive-kernel factor.  The endpoint
column is the literal shifted majorant, and all internal integer labels remain. -/
private def stage14C_pathWeight
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n p : ℤ) :
    (m : ℕ) → Bool → ℤ → (Fin m → ℤ) → ℝ≥0∞
  | 0, _, l, _ => ENNReal.ofReal (majorantCoeff φ (l - p))
  | m + 1, upper, l, v =>
      ENNReal.ofReal (positiveKernel φ n upper l (v 0)) *
        stage14C_pathWeight φ n p m (!upper) (v 0) (Fin.tail v)

/-- The actual finite source exclusion: upper slots use raw j, lower slots
use reflected −j.  This is a literal index predicate, not a convergence gate. -/
private def stage14C_validPath (n : ℤ) :
    (m : ℕ) → Bool → (Fin m → ℤ) → Prop
  | 0, _, _ => True
  | m + 1, upper, v =>
      (if upper then v 0 else -(v 0)) ≠ n ∧
        stage14C_validPath n m (!upper) (Fin.tail v)

private lemma stage14C_pathWeight_zero_of_not_valid
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n p : ℤ) (m : ℕ) :
    ∀ (upper : Bool) (l : ℤ) (v : Fin m → ℤ),
      ¬ stage14C_validPath n m upper v → stage14C_pathWeight φ n p m upper l v = 0 := by
  induction m with
  | zero =>
      intro upper l v h
      exact (h trivial).elim
  | succ m ih =>
      intro upper l v h
      by_cases hfirst : (if upper then v 0 else -(v 0)) = n
      · simp only [stage14C_pathWeight, positiveKernel, reciprocalDistance,
          hfirst, ite_true, mul_zero, ENNReal.ofReal_zero, zero_mul]
      · have htail : ¬ stage14C_validPath n m (!upper) (Fin.tail v) := by
          intro hv
          exact h ⟨hfirst, hv⟩
        change ENNReal.ofReal (positiveKernel φ n upper l (v 0)) *
          stage14C_pathWeight φ n p m (!upper) (v 0) (Fin.tail v) = 0
        rw [ih (!upper) (v 0) (Fin.tail v) htail, mul_zero]

/-- Every fixed-length positive path family has finite joint mass, identified
with the same actual L2 coefficient.  The initial L2 witness is earned by B. -/
private lemma stage14C_finite_path_mass
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n p : ℤ) :
    ∃ f : SpectralScalarL2,
      (∀ j : ℤ, spectralCoeff f j = (majorantCoeff φ (j - p) : ℂ)) ∧
      ∀ (m : ℕ) (upper : Bool) (l : ℤ),
        (0 ≤ (spectralCoeff (stage14C_positiveIter φ n f m upper) l).re ∧
          (spectralCoeff (stage14C_positiveIter φ n f m upper) l).im = 0) ∧
        (∑' v : Fin m → ℤ, stage14C_pathWeight φ n p m upper l v) =
          ENNReal.ofReal (spectralCoeff (stage14C_positiveIter φ n f m upper) l).re ∧
        (∑' v : Fin m → ℤ, stage14C_pathWeight φ n p m upper l v) ≠ ⊤ := by
  obtain ⟨f, hcoeff, hf⟩ := stage14B_shifted_majorant_exists φ p
  refine ⟨f, hcoeff, ?_⟩
  intro m
  induction m with
  | zero =>
      intro upper l
      letI : Unique (Fin 0 → ℤ) :=
        ⟨⟨fun _ => 0⟩, fun v => funext fun i => Fin.elim0 i⟩
      have hmass :
          (∑' v : Fin 0 → ℤ, stage14C_pathWeight φ n p 0 upper l v) =
            ENNReal.ofReal (spectralCoeff f l).re := by
        rw [tsum_eq_single (default : Fin 0 → ℤ)
          (fun v hv => (hv (Subsingleton.elim _ _)).elim)]
        change ENNReal.ofReal (majorantCoeff φ (l - p)) =
          ENNReal.ofReal (spectralCoeff f l).re
        rw [hcoeff l]
        rfl
      refine ⟨hf l, hmass, ?_⟩
      rw [hmass]
      exact ENNReal.ofReal_ne_top
  | succ m ih =>
      intro upper l
      obtain ⟨hs, _hout, hpos, hmass, hfinite⟩ :=
        stage14A_positive_step_mass φ n upper
          (stage14C_positiveIter φ n f m (!upper))
          (fun j => (ih (!upper) j).1) l
      have hkernel (j : ℤ) : 0 ≤ positiveKernel φ n upper l j := by
        change 0 ≤ majorantCoeff φ (l - j) *
          reciprocalDistance n (if upper then j else -j)
        apply mul_nonneg (majorant_nonneg φ (l - j))
        unfold reciprocalDistance
        split_ifs <;> positivity
      have hflatten :
          (∑' v : Fin (m + 1) → ℤ, stage14C_pathWeight φ n p (m + 1) upper l v) =
            ∑' j : ℤ, ENNReal.ofReal (positiveKernel φ n upper l j *
              (spectralCoeff (stage14C_positiveIter φ n f m (!upper)) j).re) := by
        calc
          (∑' v : Fin (m + 1) → ℤ,
              stage14C_pathWeight φ n p (m + 1) upper l v) =
              ∑' q : ℤ × (Fin m → ℤ),
                stage14C_pathWeight φ n p (m + 1) upper l
                  (Fin.consEquiv (fun _ : Fin (m + 1) => ℤ) q) :=
            ((Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)).tsum_eq
              (fun v => stage14C_pathWeight φ n p (m + 1) upper l v)).symm
          _ = ∑' j : ℤ, ∑' v : Fin m → ℤ,
                ENNReal.ofReal (positiveKernel φ n upper l j) *
                  stage14C_pathWeight φ n p m (!upper) j v := by
            rw [ENNReal.tsum_prod']
            rfl
          _ = ∑' j : ℤ, ENNReal.ofReal (positiveKernel φ n upper l j) *
                (∑' v : Fin m → ℤ, stage14C_pathWeight φ n p m (!upper) j v) := by
            apply tsum_congr
            intro j
            exact ENNReal.tsum_mul_left
          _ = ∑' j : ℤ, ENNReal.ofReal (positiveKernel φ n upper l j) *
                ENNReal.ofReal
                  (spectralCoeff (stage14C_positiveIter φ n f m (!upper)) j).re := by
            apply tsum_congr
            intro j
            rw [(ih (!upper) j).2.1]
          _ = ∑' j : ℤ, ENNReal.ofReal (positiveKernel φ n upper l j *
                (spectralCoeff (stage14C_positiveIter φ n f m (!upper)) j).re) := by
            apply tsum_congr
            intro j
            exact (ENNReal.ofReal_mul (hkernel j)).symm
      refine ⟨hpos, hflatten.trans hmass, ?_⟩
      rw [hflatten]
      exact hfinite

end NlsGge.Atomic.KST014
end

/- INERT / UNCOMPILED actual signed finite path family.
   Consumes complete local A/B/C, not private imports or assumed convergence. -/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST007 NlsGge.Atomic.KST004
open scoped ENNReal

/-- Exact actual complex potential/resolvent factors at each finite step. -/
private def stage14D_signedPathWeight
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ) (p : ℤ) :
    (m : ℕ) → Bool → ℤ → (Fin m → ℤ) → ℂ
  | 0, upper, l, _ => potentialCoeff φ upper (l - p)
  | m + 1, upper, l, v =>
      (potentialCoeff φ upper (l - v 0) *
        complementaryResolventCoeff n z (if upper then v 0 else -(v 0))) *
          stage14D_signedPathWeight φ n z p m (!upper) (v 0) (Fin.tail v)

private lemma stage14D_resolvent_norm_le_distance
    (n j : ℤ) (z : ℂ) (hz : z ∈ spectralStrip n) :
    ‖complementaryResolventCoeff n z j‖ ≤ reciprocalDistance n j := by
  have hdist : reciprocalDistance n j = 1 / (Int.natAbs (j - n) : ℝ) := by
    have habs : Int.natAbs (n - j) = Int.natAbs (j - n) := by
      rw [show n - j = -(j - n) by ring, Int.natAbs_neg]
    by_cases h : j = n
    · simp only [reciprocalDistance, h, ite_true, sub_self,
        Int.natAbs_zero, Nat.cast_zero, div_zero]
    · simp only [reciprocalDistance, h, ite_false, habs]
  rw [hdist]
  exact complementaryResolventCoeff_bound n j z hz

private lemma stage14D_signedPathWeight_norm_le
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (p : ℤ) (m : ℕ) :
    ∀ (upper : Bool) (l : ℤ) (v : Fin m → ℤ),
      ENNReal.ofReal ‖stage14D_signedPathWeight φ n z p m upper l v‖ ≤
        stage14C_pathWeight φ n p m upper l v := by
  induction m with
  | zero =>
      intro upper l v
      change ENNReal.ofReal ‖potentialCoeff φ upper (l - p)‖ ≤
        ENNReal.ofReal (majorantCoeff φ (l - p))
      exact ENNReal.ofReal_le_ofReal (potentialCoeff_norm_le_majorant φ upper (l - p))
  | succ m ih =>
      intro upper l v
      have hfactor : ‖potentialCoeff φ upper (l - v 0) *
          complementaryResolventCoeff n z (if upper then v 0 else -(v 0))‖ ≤
          positiveKernel φ n upper l (v 0) := by
        change ‖potentialCoeff φ upper (l - v 0) *
            complementaryResolventCoeff n z (if upper then v 0 else -(v 0))‖ ≤
          majorantCoeff φ (l - v 0) *
            reciprocalDistance n (if upper then v 0 else -(v 0))
        rw [norm_mul]
        exact mul_le_mul (potentialCoeff_norm_le_majorant φ upper (l - v 0))
          (stage14D_resolvent_norm_le_distance n
            (if upper then v 0 else -(v 0)) z hz)
          (norm_nonneg _) (majorant_nonneg φ (l - v 0))
      change ENNReal.ofReal ‖(potentialCoeff φ upper (l - v 0) *
          complementaryResolventCoeff n z (if upper then v 0 else -(v 0))) *
          stage14D_signedPathWeight φ n z p m (!upper) (v 0) (Fin.tail v)‖ ≤
        ENNReal.ofReal (positiveKernel φ n upper l (v 0)) *
          stage14C_pathWeight φ n p m (!upper) (v 0) (Fin.tail v)
      rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor)
        (ih (!upper) (v 0) (Fin.tail v))

/-- Genuine joint absolute summability at every finite path length, earned
from C's actual finite extended mass; there is no convergence premise. -/
private lemma stage14D_signedPathWeight_summable
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (p : ℤ) (m : ℕ) (upper : Bool) (l : ℤ) :
    Summable (fun v : Fin m → ℤ => ‖stage14D_signedPathWeight φ n z p m upper l v‖) ∧
      Summable (fun v : Fin m → ℤ => stage14D_signedPathWeight φ n z p m upper l v) := by
  obtain ⟨_f, _hcoeff, hmass⟩ := stage14C_finite_path_mass φ n p
  have hnormmass :
      (∑' v : Fin m → ℤ, ENNReal.ofReal
        ‖stage14D_signedPathWeight φ n z p m upper l v‖) ≠ ⊤ :=
    ne_top_of_le_ne_top (hmass m upper l).2.2
      (ENNReal.tsum_le_tsum (fun v =>
        stage14D_signedPathWeight_norm_le φ n z hz p m upper l v))
  have hs : Summable
      (fun v : Fin m → ℤ => ‖stage14D_signedPathWeight φ n z p m upper l v‖) :=
    (ENNReal.summable_toReal hnormmass).congr
      (fun v => ENNReal.toReal_ofReal (norm_nonneg _))
  exact ⟨hs, hs.of_norm⟩

private lemma stage14D_signedPathWeight_zero_of_not_valid
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (p : ℤ) (m : ℕ)
    (upper : Bool) (l : ℤ) (v : Fin m → ℤ)
    (h : ¬ stage14C_validPath n m upper v) :
    stage14D_signedPathWeight φ n z p m upper l v = 0 := by
  have hzero := stage14C_pathWeight_zero_of_not_valid φ n p m upper l v h
  have hbound := stage14D_signedPathWeight_norm_le φ n z hz p m upper l v
  rw [hzero] at hbound
  have hnorm : ‖stage14D_signedPathWeight φ n z p m upper l v‖ ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp (le_antisymm hbound bot_le)
  exact norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))

end NlsGge.Atomic.KST014
end

/- INERT / UNCOMPILED actual raw/reflected coordinates to common source labels.
   Locally consumes exact C/D, preserving all integer and zero coordinates. -/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST007 NlsGge.Atomic.KST004

/-- At each alternating block, convert its raw scalar Fourier coordinate to
its actual source resolvent label: upper raw j, lower reflected −j. -/
private def stage14E_commonLabels :
    (m : ℕ) → Bool → (Fin m → ℤ) → (Fin m → ℤ)
  | 0, _, v => v
  | m + 1, upper, v =>
      Fin.cons (if upper then v 0 else -(v 0))
        (stage14E_commonLabels m (!upper) (Fin.tail v))

private lemma stage14E_commonLabels_involutive (m : ℕ) :
    ∀ (upper : Bool) (v : Fin m → ℤ),
      stage14E_commonLabels m upper (stage14E_commonLabels m upper v) = v := by
  induction m with
  | zero => intro upper v; rfl
  | succ m ih =>
      intro upper v
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (if upper then (if upper then v 0 else -(v 0))
            else -(if upper then v 0 else -(v 0))) = v 0
        cases upper <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_neg]
      · change stage14E_commonLabels m (!upper)
          (stage14E_commonLabels m (!upper) (Fin.tail v)) j = v j.succ
        exact congrFun (ih (!upper) (Fin.tail v)) j

private def stage14E_commonLabelEquiv (m : ℕ) (upper : Bool) :
    (Fin m → ℤ) ≃ (Fin m → ℤ) where
  toFun := stage14E_commonLabels m upper
  invFun := stage14E_commonLabels m upper
  left_inv := stage14E_commonLabels_involutive m upper
  right_inv := stage14E_commonLabels_involutive m upper

private lemma stage14E_valid_iff_common_labels (n : ℤ) (m : ℕ) :
    ∀ (upper : Bool) (v : Fin m → ℤ),
      stage14C_validPath n m upper v ↔
        ∀ i : Fin m, stage14E_commonLabels m upper v i ≠ n := by
  induction m with
  | zero =>
      intro upper v
      constructor
      · intro _ i
        exact Fin.elim0 i
      · intro _
        trivial
  | succ m ih =>
      intro upper v
      constructor
      · rintro ⟨hfirst, htail⟩ i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hfirst
        · exact ((ih (!upper) (Fin.tail v)).1 htail) j
      · intro h
        refine ⟨h 0, ?_⟩
        apply (ih (!upper) (Fin.tail v)).2
        intro j
        exact h j.succ

private lemma stage14E_valid_reindexed_iff (n : ℤ) (m : ℕ)
    (upper : Bool) (v : Fin m → ℤ) :
    stage14C_validPath n m upper (stage14E_commonLabelEquiv m upper v) ↔
      ∀ i : Fin m, v i ≠ n := by
  rw [stage14E_valid_iff_common_labels]
  change (∀ i : Fin m,
    stage14E_commonLabels m upper (stage14E_commonLabels m upper v) i ≠ n) ↔ _
  rw [stage14E_commonLabels_involutive]

/-- Reindex only after D has earned genuine complex summability.  The total
bijection includes zero and every removed-resonance tuple before masking. -/
private lemma stage14E_signed_sum_common_labels
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (p : ℤ) (m : ℕ) (upper : Bool) (l : ℤ) :
    Summable (fun v : Fin m → ℤ =>
      stage14D_signedPathWeight φ n z p m upper l (stage14E_commonLabelEquiv m upper v)) ∧
    (∑' v : Fin m → ℤ,
      stage14D_signedPathWeight φ n z p m upper l (stage14E_commonLabelEquiv m upper v)) =
        ∑' v : Fin m → ℤ, stage14D_signedPathWeight φ n z p m upper l v := by
  have hs := (stage14D_signedPathWeight_summable φ n z hz p m upper l).2
  refine ⟨?_, (stage14E_commonLabelEquiv m upper).tsum_eq _⟩
  exact ((stage14E_commonLabelEquiv m upper).summable_iff
    (f := fun v : Fin m → ℤ => stage14D_signedPathWeight φ n z p m upper l v)).2 hs

private lemma stage14E_signed_path_zero_at_common_resonance
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (p : ℤ) (m : ℕ)
    (upper : Bool) (l : ℤ) (v : Fin m → ℤ)
    (h : ¬ ∀ i : Fin m, v i ≠ n) :
    stage14D_signedPathWeight φ n z p m upper l
      (stage14E_commonLabelEquiv m upper v) = 0 := by
  apply stage14D_signedPathWeight_zero_of_not_valid φ n z hz p m upper l
  rw [stage14E_valid_reindexed_iff]
  exact h

end NlsGge.Atomic.KST014
end

set_option autoImplicit false
noncomputable section
namespace NlsGge.Atomic.KST014
open MeasureTheory NlsGge.Schur NlsGge.Atomic.KST007
open scoped ENNReal

private lemma stage14F_multiplier_coeff
    (p : ℤ) (f : SpectralScalarL2) (l : ℤ) :
    Integrable (fun x : SpectralCircle => fourier (-l) x • (fourier p x * f x))
      (AddCircle.haarAddCircle : Measure SpectralCircle) ∧
    Integrable (fun x : SpectralCircle => fourier (-(l - p)) x • f x)
      (AddCircle.haarAddCircle : Measure SpectralCircle) ∧
    spectralCoeff (fourierMultiplier p f) l = fourierCoeff f (l - p) := by
  letI : IsProbabilityMeasure spectralHaar := by
    change IsProbabilityMeasure (AddCircle.haarAddCircle : Measure SpectralCircle)
    infer_instance
  have hf : Integrable (f : SpectralCircle → ℂ)
      (AddCircle.haarAddCircle : Measure SpectralCircle) := by
    simpa only [spectralHaar] using
      (MemLp.integrable (by norm_num) (Lp.memLp f))
  have hpf : Integrable (fun x : SpectralCircle => fourier p x * f x)
      (AddCircle.haarAddCircle : Measure SpectralCircle) := by
    simpa only [smul_eq_mul] using hf.fourier_smul p
  have hleft := hpf.fourier_smul (-l)
  have hright := hf.fourier_smul (-(l - p))
  refine ⟨hleft, hright, ?_⟩
  have hrepr : spectralCoeff (fourierMultiplier p f) l =
      fourierCoeff (fourierMultiplier p f) l := by
    simpa only [spectralCoeff, spectralHaar] using!
      (fourierBasis_repr (T := (2 : ℝ)) (fourierMultiplier p f) l)
  have hae : (fourierMultiplier p f : SpectralCircle → ℂ) =ᵐ[
      (AddCircle.haarAddCircle : Measure SpectralCircle)]
        (fun x => fourier p x * f x) := by
    change (fourierMultiplierValue p f : SpectralCircle → ℂ) =ᵐ[
      (AddCircle.haarAddCircle : Measure SpectralCircle)]
        (fun x => fourier p x * f x)
    simpa only [spectralHaar] using (fourierMultiplierValue_ae p f)
  rw [hrepr, congrFun (fourierCoeff_congr_ae hae) l]
  change (∫ x : SpectralCircle, fourier (-l) x • (fourier p x * f x)
      ∂(AddCircle.haarAddCircle : Measure SpectralCircle)) =
    ∫ x : SpectralCircle, fourier (-(l - p)) x • f x
      ∂(AddCircle.haarAddCircle : Measure SpectralCircle)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change fourier (-l) x * (fourier p x * f x) = fourier (-(l - p)) x * f x
    rw [← mul_assoc, ← fourier_add]
    rw [show -l + p = -(l - p) by ring]

end NlsGge.Atomic.KST014
end

set_option autoImplicit false
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST007

private lemma stage14G_qOperator_component
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (f : KSTPairL2) (upper : Bool) :
    NlsGge.Atomic.KST006.qOperator φ n z hz f upper =
      qBlock φ n z hz upper (f (!upper)) := by
  let B : HilbertBasis ℤ ℂ SpectralScalarL2 := fourierBasis (T := (2 : ℝ))
  apply B.repr.injective
  apply lp.ext
  funext l
  change spectralCoeff (NlsGge.Atomic.KST006.qOperator φ n z hz f upper) l =
    spectralCoeff (qBlock φ n z hz upper (f (!upper))) l
  rw [qBlock_coeff]
  cases upper
  · exact NlsGge.Atomic.KST006.qOperator_lower_coeff φ n z hz f l
  · exact NlsGge.Atomic.KST006.qOperator_upper_coeff φ n z hz f l

/-- The actual input component selected by m off-diagonal steps. -/
private def stage14G_inputChannel : ℕ → Bool → Bool
  | 0, upper => upper
  | m + 1, upper => stage14G_inputChannel m (!upper)

private lemma stage14G_inputChannel_even (k : ℕ) :
    ∀ upper : Bool, stage14G_inputChannel (2 * k) upper = upper := by
  induction k with
  | zero => intro upper; rfl
  | succ k ih =>
      intro upper
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      change stage14G_inputChannel (2 * k) (!(!upper)) = upper
      rw [Bool.not_not]
      exact ih upper

private lemma stage14G_inputChannel_odd (k : ℕ) (upper : Bool) :
    stage14G_inputChannel (2 * k + 1) upper = !upper := by
  change stage14G_inputChannel (2 * k) (!upper) = !upper
  exact stage14G_inputChannel_even k (!upper)

/-- Finite powers depend on the single genuine input component selected by
that actual off-diagonal power; this is data equality, not a convergence premise. -/
private lemma stage14G_pow_component_congr
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (m : ℕ) :
    ∀ (f g : KSTPairL2) (upper : Bool),
      f (stage14G_inputChannel m upper) = g (stage14G_inputChannel m upper) →
      (((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ m) f) upper =
        (((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ m) g) upper := by
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
  change ∀ (f g : KSTPairL2) (upper : Bool),
    f (stage14G_inputChannel m upper) = g (stage14G_inputChannel m upper) →
      ((T ^ m) f) upper = ((T ^ m) g) upper
  induction m with
  | zero =>
      intro f g upper h
      simpa only [pow_zero, one_apply_eq_self, stage14G_inputChannel] using h
  | succ m ih =>
      intro f g upper h
      have hprev : f (stage14G_inputChannel m (!upper)) =
          g (stage14G_inputChannel m (!upper)) := h
      calc
        ((T ^ (m + 1)) f) upper = qBlock φ n z hz upper (((T ^ m) f) (!upper)) := by
          rw [pow_succ', mul_apply_eq_comp]
          exact stage14G_qOperator_component φ n z hz ((T ^ m) f) upper
        _ = qBlock φ n z hz upper (((T ^ m) g) (!upper)) :=
          congrArg (qBlock φ n z hz upper) (ih f g (!upper) hprev)
        _ = ((T ^ (m + 1)) g) upper := by
          rw [pow_succ', mul_apply_eq_comp]
          exact (stage14G_qOperator_component φ n z hz ((T ^ m) g) upper).symm

end NlsGge.Atomic.KST014
end

/- INERT / UNCOMPILED finite actual T-power/path coefficient identification.
   Exact local D/F/G providers required; no convergence premise is introduced. -/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST007

/-- Finite actual scalar blocks, starting at the genuine shifted potential
in each component. No inverse or formal kernel field is assumed. -/
private def stage14H_blockIter
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (p : ℤ) : ℕ → Bool → SpectralScalarL2
  | 0, upper => fourierMultiplier p (NlsGge.Analysis.naturalPhysicalCoverL2 (φ upper))
  | m + 1, upper => qBlock φ n z hz upper
      (stage14H_blockIter φ n z hz p m (!upper))

private lemma stage14H_pow_seed_component
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (p : ℤ) (m : ℕ) :
    ∀ upper : Bool,
      (((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ m)
        (WithLp.toLp 2 (fun b : Bool =>
          fourierMultiplier p (NlsGge.Analysis.naturalPhysicalCoverL2 (φ b))))) upper =
        stage14H_blockIter φ n z hz p m upper := by
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
  let seed : KSTPairL2 := WithLp.toLp 2 (fun b : Bool =>
    fourierMultiplier p (NlsGge.Analysis.naturalPhysicalCoverL2 (φ b)))
  change ∀ upper : Bool, ((T ^ m) seed) upper = stage14H_blockIter φ n z hz p m upper
  induction m with
  | zero =>
      intro upper
      simp only [pow_zero, one_apply_eq_self, seed, PiLp.toLp_apply, stage14H_blockIter]
  | succ m ih =>
      intro upper
      calc
        ((T ^ (m + 1)) seed) upper =
            qBlock φ n z hz upper (((T ^ m) seed) (!upper)) := by
          rw [pow_succ', mul_apply_eq_comp]
          exact stage14G_qOperator_component φ n z hz ((T ^ m) seed) upper
        _ = qBlock φ n z hz upper (stage14H_blockIter φ n z hz p m (!upper)) :=
          congrArg (qBlock φ n z hz upper) (ih (!upper))
        _ = stage14H_blockIter φ n z hz p (m + 1) upper := rfl

/-- The actual finite scalar iteration equals the genuinely absolutely
summable signed path sum; D is consumed before any sum is flattened. -/
private lemma stage14H_blockIter_coeff_paths
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (p : ℤ) (m : ℕ) :
    ∀ (upper : Bool) (l : ℤ),
      spectralCoeff (stage14H_blockIter φ n z hz p m upper) l =
        ∑' v : Fin m → ℤ, stage14D_signedPathWeight φ n z p m upper l v := by
  induction m with
  | zero =>
      intro upper l
      letI : Unique (Fin 0 → ℤ) :=
        ⟨⟨fun _ => 0⟩, fun v => funext fun i => Fin.elim0 i⟩
      rw [tsum_eq_single (default : Fin 0 → ℤ)
        (fun v hv => (hv (Subsingleton.elim _ _)).elim)]
      change spectralCoeff
          (fourierMultiplier p (NlsGge.Analysis.naturalPhysicalCoverL2 (φ upper))) l =
        potentialCoeff φ upper (l - p)
      simpa only [potentialCoeff] using
        (stage14F_multiplier_coeff p
          (NlsGge.Analysis.naturalPhysicalCoverL2 (φ upper)) l).2.2
  | succ m ih =>
      intro upper l
      have hsJoint : Summable (fun q : ℤ × (Fin m → ℤ) =>
          (potentialCoeff φ upper (l - q.1) *
            complementaryResolventCoeff n z (if upper then q.1 else -q.1)) *
              stage14D_signedPathWeight φ n z p m (!upper) q.1 q.2) := by
        have hs := (stage14D_signedPathWeight_summable φ n z hz p (m + 1) upper l).2
        have he := ((Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)).summable_iff
          (f := fun v => stage14D_signedPathWeight φ n z p (m + 1) upper l v)).2 hs
        change Summable (fun q : ℤ × (Fin m → ℤ) =>
          stage14D_signedPathWeight φ n z p (m + 1) upper l (Fin.cons q.1 q.2)) at he
        exact he
      calc
        spectralCoeff (stage14H_blockIter φ n z hz p (m + 1) upper) l =
            ∑' j : ℤ, potentialCoeff φ upper (l - j) *
              (complementaryResolventCoeff n z (if upper then j else -j) *
                spectralCoeff (stage14H_blockIter φ n z hz p m (!upper)) j) :=
          qBlock_coeff φ n z hz upper (stage14H_blockIter φ n z hz p m (!upper)) l
        _ = ∑' j : ℤ, (potentialCoeff φ upper (l - j) *
              complementaryResolventCoeff n z (if upper then j else -j)) *
                (∑' v : Fin m → ℤ, stage14D_signedPathWeight φ n z p m (!upper) j v) := by
          apply tsum_congr
          intro j
          rw [ih (!upper) j]
          ring
        _ = ∑' j : ℤ, ∑' v : Fin m → ℤ,
              (potentialCoeff φ upper (l - j) *
                complementaryResolventCoeff n z (if upper then j else -j)) *
                  stage14D_signedPathWeight φ n z p m (!upper) j v := by
          apply tsum_congr
          intro j
          exact (((stage14D_signedPathWeight_summable φ n z hz p m (!upper) j).2).tsum_mul_left
             (potentialCoeff φ upper (l - j) *
              complementaryResolventCoeff n z (if upper then j else -j))).symm
        _ = ∑' q : ℤ × (Fin m → ℤ),
              (potentialCoeff φ upper (l - q.1) *
                complementaryResolventCoeff n z (if upper then q.1 else -q.1)) *
                  stage14D_signedPathWeight φ n z p m (!upper) q.1 q.2 :=
          hsJoint.tsum_prod.symm
        _ = ∑' v : Fin (m + 1) → ℤ,
              stage14D_signedPathWeight φ n z p (m + 1) upper l v :=
          (Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)).tsum_eq
            (fun v : Fin (m + 1) → ℤ =>
              stage14D_signedPathWeight φ n z p (m + 1) upper l v)

private lemma stage14H_actual_pow_seed_coeff_paths
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (p : ℤ) (m : ℕ) (upper : Bool) (l : ℤ) :
    spectralCoeff
      ((((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ m)
        (WithLp.toLp 2 (fun b : Bool =>
          fourierMultiplier p (NlsGge.Analysis.naturalPhysicalCoverL2 (φ b))))) upper) l =
      ∑' v : Fin m → ℤ, stage14D_signedPathWeight φ n z p m upper l v := by
  rw [stage14H_pow_seed_component]
  exact stage14H_blockIter_coeff_paths φ n z hz p m upper l

end NlsGge.Atomic.KST014
end

/- INERT / UNCOMPILED genuine single-column consumption of H. -/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST007

private lemma stage14I_actual_columns
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) :
    NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n) =
      PiLp.single 2 true
        (fourierMultiplier n (NlsGge.Analysis.naturalPhysicalCoverL2 (φ true))) ∧
    NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n) =
      PiLp.single 2 false
        (fourierMultiplier (-n) (NlsGge.Analysis.naturalPhysicalCoverL2 (φ false))) := by
  have h := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have hul : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by
    simpa [kstPnFrame] using h true false
  have hlu : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by
    simpa [kstPnFrame] using h false true
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by
    simpa [kstPnFrame] using h true true
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by
    simpa [kstPnFrame] using h false false
  constructor
  · simp only [NlsGge.Atomic.KST012.potentialOnPn, ContinuousLinearMap.add_apply,
      InnerProductSpace.rankOne_apply, hll, hul, one_smul, zero_smul, add_zero]
  · simp only [NlsGge.Atomic.KST012.potentialOnPn, ContinuousLinearMap.add_apply,
      InnerProductSpace.rankOne_apply, hlu, huu, one_smul, zero_smul, zero_add]

/-- Source matrix entry 11 uses the genuine lower input and lower output. -/
private lemma stage14I_lower_odd_power_paths
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (k : ℕ) :
    spectralCoeff
      ((((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ (2 * k + 1))
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))) false) n =
      ∑' v : Fin (2 * k + 1) → ℤ,
        stage14D_signedPathWeight φ n z n (2 * k + 1) false n v := by
  let seed : KSTPairL2 := WithLp.toLp 2 (fun b : Bool =>
    fourierMultiplier n (NlsGge.Analysis.naturalPhysicalCoverL2 (φ b)))
  have hc :
      (((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ (2 * k + 1))
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))) false =
      (((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ (2 * k + 1)) seed) false := by
    apply stage14G_pow_component_congr φ n z hz (2 * k + 1)
    rw [stage14G_inputChannel_odd]
    simpa only [Bool.not_false, (stage14I_actual_columns φ n).1,
      PiLp.single_eq_same, seed, PiLp.toLp_apply]
  rw [hc]
  exact stage14H_actual_pow_seed_coeff_paths φ n z hz n (2 * k + 1) false n

/-- Source matrix entry 22 uses the genuine upper reflected input/output. -/
private lemma stage14I_upper_odd_power_paths
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (k : ℕ) :
    spectralCoeff
      ((((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ (2 * k + 1))
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n))) true) (-n) =
      ∑' v : Fin (2 * k + 1) → ℤ,
        stage14D_signedPathWeight φ n z (-n) (2 * k + 1) true (-n) v := by
  let seed : KSTPairL2 := WithLp.toLp 2 (fun b : Bool =>
    fourierMultiplier (-n) (NlsGge.Analysis.naturalPhysicalCoverL2 (φ b)))
  have hc :
      (((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ (2 * k + 1))
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n))) true =
      (((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ (2 * k + 1)) seed) true := by
    apply stage14G_pow_component_congr φ n z hz (2 * k + 1)
    rw [stage14G_inputChannel_odd]
    simpa only [Bool.not_true, (stage14I_actual_columns φ n).2,
      PiLp.single_eq_same, seed, PiLp.toLp_apply]
  rw [hc]
  exact stage14H_actual_pow_seed_coeff_paths φ n z hz (-n) (2 * k + 1) true (-n)

end NlsGge.Atomic.KST014
end

/- INERT / UNCOMPILED finite source factor algebra.
   Reversal of complex tsums remains a later consumption of earned D/E summability. -/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST007 NlsGge.Atomic.KST004

private def stage14K_edge
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (upper : Bool) (i j : ℤ) : ℂ :=
  potentialCoeff φ upper (if upper then -(i + j) else i + j)

private lemma stage14K_edge_symm
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (upper : Bool) (i j : ℤ) :
    stage14K_edge φ upper i j = stage14K_edge φ upper j i := by
  simp only [stage14K_edge, add_comm]

private def stage14K_chain
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ) :
    Bool → ℤ → List ℤ → ℤ → ℂ
  | upper, s, [], t => stage14K_edge φ upper s t
  | upper, s, j :: js, t =>
      (stage14K_edge φ upper s j * complementaryResolventCoeff n z j) *
        stage14K_chain φ n z (!upper) j js t

private lemma stage14K_channel_not (m : ℕ) :
    ∀ upper : Bool, stage14G_inputChannel m (!upper) = !(stage14G_inputChannel m upper) := by
  induction m with
  | zero => intro upper; rfl
  | succ m ih =>
      intro upper
      change stage14G_inputChannel m (!(!upper)) = !(stage14G_inputChannel m (!upper))
      rw [Bool.not_not, ih upper, Bool.not_not]

private lemma stage14K_channel_involutive (m : ℕ) :
    ∀ upper : Bool,
      stage14G_inputChannel m (stage14G_inputChannel m upper) = upper := by
  induction m with
  | zero => intro upper; rfl
  | succ m ih =>
      intro upper
      change stage14G_inputChannel m (!(stage14G_inputChannel m (!upper))) = upper
      rw [stage14K_channel_not, ih (!upper), Bool.not_not]

private lemma stage14K_chain_append_singleton
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ) (js : List ℤ) :
    ∀ (upper : Bool) (s j t : ℤ),
      stage14K_chain φ n z upper s (js ++ [j]) t =
        (stage14K_chain φ n z upper s js j * complementaryResolventCoeff n z j) *
          stage14K_edge φ (stage14G_inputChannel (js.length + 1) upper) j t := by
  induction js with
  | nil => intro upper s j t; rfl
  | cons i js ih =>
      intro upper s j t
      simp only [List.cons_append, stage14K_chain, List.length_cons]
      rw [ih (!upper) i j t]
      change (stage14K_edge φ upper s i * complementaryResolventCoeff n z i) *
          ((stage14K_chain φ n z (!upper) i js j * complementaryResolventCoeff n z j) *
            stage14K_edge φ (stage14G_inputChannel (js.length + 1) (!upper)) j t) =
        (((stage14K_edge φ upper s i * complementaryResolventCoeff n z i) *
            stage14K_chain φ n z (!upper) i js j) * complementaryResolventCoeff n z j) *
          stage14K_edge φ (stage14G_inputChannel (js.length + 1) (!upper)) j t
      ring

/-- Finite chain reversal, with the genuine terminal channel and every
masked resolvent factor retained (including zeros at resonances). -/
private lemma stage14K_chain_reverse
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ) (js : List ℤ) :
    ∀ (upper : Bool) (s t : ℤ),
      stage14K_chain φ n z upper s js t =
        stage14K_chain φ n z (stage14G_inputChannel js.length upper) t js.reverse s := by
  induction js with
  | nil =>
      intro upper s t
      exact stage14K_edge_symm φ upper s t
  | cons j js ih =>
      intro upper s t
      simp only [List.length_cons, List.reverse_cons]
      rw [stage14K_chain_append_singleton]
      change (stage14K_edge φ upper s j * complementaryResolventCoeff n z j) *
          stage14K_chain φ n z (!upper) j js t =
        (stage14K_chain φ n z (stage14G_inputChannel (js.length + 1) upper)
            t js.reverse j * complementaryResolventCoeff n z j) *
          stage14K_edge φ
            (stage14G_inputChannel (js.reverse.length + 1)
              (stage14G_inputChannel (js.length + 1) upper)) j s
      rw [List.length_reverse, stage14K_channel_involutive,
        stage14K_edge_symm φ upper j s, ih (!upper) j t]
      change (stage14K_edge φ upper s j * complementaryResolventCoeff n z j) *
          stage14K_chain φ n z (stage14G_inputChannel (js.length + 1) upper)
            t js.reverse j =
        (stage14K_chain φ n z (stage14G_inputChannel (js.length + 1) upper)
            t js.reverse j * complementaryResolventCoeff n z j) *
          stage14K_edge φ upper s j
      ring

/-- Exact common-source factor formula for the already-defined actual path.
The final multiplier index is fixed by the genuine selected input channel. -/
private lemma stage14K_actual_common_path_eq_chain
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ) (m : ℕ) :
    ∀ (upper : Bool) (s t : ℤ) (v : Fin m → ℤ),
      stage14D_signedPathWeight φ n z
        (if stage14G_inputChannel m upper then t else -t) m upper
        (if upper then -s else s) (stage14E_commonLabelEquiv m upper v) =
      stage14K_chain φ n z upper s (List.ofFn v) t := by
  induction m with
  | zero =>
      intro upper s t v
      cases upper <;>
        simp only [stage14D_signedPathWeight, stage14G_inputChannel, List.ofFn_zero,
          stage14K_chain, stage14K_edge, Bool.false_eq_true, ↓reduceIte]
      · rw [sub_neg_eq_add]
      · congr 1
        ring
  | succ m ih =>
      intro upper s t v
      rw [List.ofFn_succ]
      cases upper
      · change (potentialCoeff φ false (s - -(v 0)) *
              complementaryResolventCoeff n z (-(-(v 0)))) *
            stage14D_signedPathWeight φ n z
              (if stage14G_inputChannel m true then t else -t) m true (-(v 0))
              (stage14E_commonLabelEquiv m true (Fin.tail v)) =
          (potentialCoeff φ false (s + v 0) * complementaryResolventCoeff n z (v 0)) *
            stage14K_chain φ n z true (v 0) (List.ofFn (Fin.tail v)) t
        rw [neg_neg, sub_neg_eq_add]
        apply congrArg (fun w : ℂ =>
          (potentialCoeff φ false (s + v 0) * complementaryResolventCoeff n z (v 0)) * w)
        simpa only [Bool.false_eq_true, ↓reduceIte] using
          (ih true (v 0) t (Fin.tail v))
      · change (potentialCoeff φ true (-s - v 0) *
              complementaryResolventCoeff n z (v 0)) *
            stage14D_signedPathWeight φ n z
              (if stage14G_inputChannel m false then t else -t) m false (v 0)
              (stage14E_commonLabelEquiv m false (Fin.tail v)) =
          (potentialCoeff φ true (-(s + v 0)) * complementaryResolventCoeff n z (v 0)) *
            stage14K_chain φ n z false (v 0) (List.ofFn (Fin.tail v)) t
        rw [show -s - v 0 = -(s + v 0) by ring]
        apply congrArg (fun w : ℂ =>
          (potentialCoeff φ true (-(s + v 0)) * complementaryResolventCoeff n z (v 0)) * w)
        simpa only [Bool.false_eq_true, ↓reduceIte] using
          (ih false (v 0) t (Fin.tail v))

end NlsGge.Atomic.KST014
end

/- INERT / UNCOMPILED actual odd path sum reversal.
   D/E summability is earned before the actual total tuple reindex. -/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST007 NlsGge.Atomic.KST004

private def stage14L_reverseTuple (m : ℕ) (v : Fin m → ℤ) : Fin m → ℤ :=
  fun i => (List.ofFn v).reverse[i.val]'(by
    simpa only [List.length_reverse, List.length_ofFn] using i.isLt)

private lemma stage14L_ofFn_reverseTuple (m : ℕ) (v : Fin m → ℤ) :
    List.ofFn (stage14L_reverseTuple m v) = (List.ofFn v).reverse := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_reverse]
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

private lemma stage14L_reverseTuple_involutive (m : ℕ) (v : Fin m → ℤ) :
    stage14L_reverseTuple m (stage14L_reverseTuple m v) = v := by
  apply List.ofFn_injective
  rw [stage14L_ofFn_reverseTuple, stage14L_ofFn_reverseTuple, List.reverse_reverse]

private def stage14L_reverseTupleEquiv (m : ℕ) : (Fin m → ℤ) ≃ (Fin m → ℤ) where
  toFun := stage14L_reverseTuple m
  invFun := stage14L_reverseTuple m
  left_inv := stage14L_reverseTuple_involutive m
  right_inv := stage14L_reverseTuple_involutive m

private lemma stage14L_actual_odd_path_reverse
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (k : ℕ) (v : Fin (2 * k + 1) → ℤ) :
    stage14D_signedPathWeight φ n z n (2 * k + 1) false n
        (stage14E_commonLabelEquiv (2 * k + 1) false v) =
      stage14D_signedPathWeight φ n z (-n) (2 * k + 1) true (-n)
        (stage14E_commonLabelEquiv (2 * k + 1) true
          (stage14L_reverseTupleEquiv (2 * k + 1) v)) := by
  have hf := stage14K_actual_common_path_eq_chain φ n z (2 * k + 1) false n n v
  have ht := stage14K_actual_common_path_eq_chain φ n z (2 * k + 1) true n n
    (stage14L_reverseTupleEquiv (2 * k + 1) v)
  have hfalse :
      stage14D_signedPathWeight φ n z n (2 * k + 1) false n
          (stage14E_commonLabelEquiv (2 * k + 1) false v) =
        stage14K_chain φ n z false n (List.ofFn v) n := by
    simpa only [stage14G_inputChannel_odd, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte] using hf
  have htrue :
      stage14D_signedPathWeight φ n z (-n) (2 * k + 1) true (-n)
          (stage14E_commonLabelEquiv (2 * k + 1) true
            (stage14L_reverseTupleEquiv (2 * k + 1) v)) =
        stage14K_chain φ n z true n
          (List.ofFn (stage14L_reverseTupleEquiv (2 * k + 1) v)) n := by
    simpa only [stage14G_inputChannel_odd, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] using ht
  rw [hfalse, htrue]
  have hr := stage14K_chain_reverse φ n z (List.ofFn v) false n n
  simpa only [List.length_ofFn, stage14G_inputChannel_odd, Bool.not_false,
    stage14L_reverseTupleEquiv, Equiv.coe_fn_mk,
    stage14L_ofFn_reverseTuple] using hr

/-- Both actual signed families are genuinely summable before reindexing.
The tuple bijection includes every integer and resonant zero tuple. -/
private lemma stage14L_actual_odd_path_tsum_eq
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (k : ℕ) :
    Summable (fun v : Fin (2 * k + 1) → ℤ =>
      stage14D_signedPathWeight φ n z n (2 * k + 1) false n v) ∧
    Summable (fun v : Fin (2 * k + 1) → ℤ =>
      stage14D_signedPathWeight φ n z (-n) (2 * k + 1) true (-n) v) ∧
    (∑' v : Fin (2 * k + 1) → ℤ,
      stage14D_signedPathWeight φ n z n (2 * k + 1) false n v) =
    ∑' v : Fin (2 * k + 1) → ℤ,
      stage14D_signedPathWeight φ n z (-n) (2 * k + 1) true (-n) v := by
  have hsf := (stage14D_signedPathWeight_summable φ n z hz n
    (2 * k + 1) false n).2
  have hst := (stage14D_signedPathWeight_summable φ n z hz (-n)
    (2 * k + 1) true (-n)).2
  have hef := stage14E_signed_sum_common_labels φ n z hz n (2 * k + 1) false n
  have het := stage14E_signed_sum_common_labels φ n z hz (-n) (2 * k + 1) true (-n)
  refine ⟨hsf, hst, ?_⟩
  calc
    (∑' v : Fin (2 * k + 1) → ℤ,
        stage14D_signedPathWeight φ n z n (2 * k + 1) false n v) =
      ∑' v : Fin (2 * k + 1) → ℤ,
        stage14D_signedPathWeight φ n z n (2 * k + 1) false n
          (stage14E_commonLabelEquiv (2 * k + 1) false v) := hef.2.symm
    _ = ∑' v : Fin (2 * k + 1) → ℤ,
        stage14D_signedPathWeight φ n z (-n) (2 * k + 1) true (-n)
          (stage14E_commonLabelEquiv (2 * k + 1) true
            (stage14L_reverseTupleEquiv (2 * k + 1) v)) :=
      tsum_congr (stage14L_actual_odd_path_reverse φ n z k)
    _ = ∑' v : Fin (2 * k + 1) → ℤ,
        stage14D_signedPathWeight φ n z (-n) (2 * k + 1) true (-n)
          (stage14E_commonLabelEquiv (2 * k + 1) true v) :=
      (stage14L_reverseTupleEquiv (2 * k + 1)).tsum_eq
        (fun v : Fin (2 * k + 1) → ℤ =>
          stage14D_signedPathWeight φ n z (-n) (2 * k + 1) true (-n)
            (stage14E_commonLabelEquiv (2 * k + 1) true v))
    _ = ∑' v : Fin (2 * k + 1) → ℤ,
        stage14D_signedPathWeight φ n z (-n) (2 * k + 1) true (-n) v := het.2

end NlsGge.Atomic.KST014
end

/- INERT / UNCOMPILED exact even channel vanishing and coefficient extraction. -/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST007
open scoped InnerProduct InnerProductSpace

private lemma stage14M_even_column_components_zero
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (k : ℕ) :
    ((((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ (2 * k))
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))) false) = 0 ∧
    ((((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ (2 * k))
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n))) true) = 0 := by
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
  constructor
  · calc
      ((T ^ (2 * k)) (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))) false =
          ((T ^ (2 * k)) 0) false := by
        apply stage14G_pow_component_congr φ n z hz (2 * k)
        rw [stage14G_inputChannel_even]
        simp only [(stage14I_actual_columns φ n).1, PiLp.single_apply,
          Bool.false_eq_true, ↓reduceIte, PiLp.zero_apply]
      _ = 0 := by rw [map_zero]; rfl
  · calc
      ((T ^ (2 * k)) (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n))) true =
          ((T ^ (2 * k)) 0) true := by
        apply stage14G_pow_component_congr φ n z hz (2 * k)
        rw [stage14G_inputChannel_even]
        simp only [(stage14I_actual_columns φ n).2, PiLp.single_apply,
          Bool.true_eq_false, ↓reduceIte, PiLp.zero_apply]
      _ = 0 := by rw [map_zero]; rfl

private lemma stage14M_inner_basis_spectralCoeff (f : SpectralScalarL2) (m : ℤ) :
    inner ℂ (spectralBasis m) f = spectralCoeff f m := by
  let B : HilbertBasis ℤ ℂ SpectralScalarL2 := fourierBasis (T := (2 : ℝ))
  have hb : B m = spectralBasis m := congrFun (coe_fourierBasis (T := (2 : ℝ))) m
  change inner ℂ (spectralBasis m) f = B.repr f m
  rw [B.repr_apply_apply, hb]

private lemma stage14M_inner_lower_spectralCoeff (n : ℤ) (f : KSTPairL2) :
    inner ℂ (kstPnLower n) f = spectralCoeff (f false) n := by
  calc
    inner ℂ (kstPnLower n) f = inner ℂ (spectralBasis n) (f false) := by
      simp [kstPnLower, PiLp.inner_apply, Fintype.sum_bool]
    _ = spectralCoeff (f false) n := stage14M_inner_basis_spectralCoeff _ _

private lemma stage14M_inner_upper_spectralCoeff (n : ℤ) (f : KSTPairL2) :
    inner ℂ (kstPnUpper n) f = spectralCoeff (f true) (-n) := by
  calc
    inner ℂ (kstPnUpper n) f = inner ℂ (spectralBasis (-n)) (f true) := by
      simp [kstPnUpper, PiLp.inner_apply, Fintype.sum_bool]
    _ = spectralCoeff (f true) (-n) := stage14M_inner_basis_spectralCoeff _ _

private lemma stage14M_actual_odd_diagonal_eq
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (k : ℕ) :
    inner ℂ (kstPnLower n)
      (((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ (2 * k + 1))
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))) =
    inner ℂ (kstPnUpper n)
      (((NlsGge.Atomic.KST006.qOperator φ n z hz) ^ (2 * k + 1))
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n))) := by
  rw [stage14M_inner_lower_spectralCoeff, stage14M_inner_upper_spectralCoeff,
    stage14I_lower_odd_power_paths, stage14I_upper_odd_power_paths]
  exact (stage14L_actual_odd_path_tsum_eq φ n z hz k).2.2

end NlsGge.Atomic.KST014
end

set_option autoImplicit false
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004

private lemma stage14J_opNorm_le_actual_hsNorm
    (S : KSTPairL2 →L[ℂ] KSTPairL2)
    (hS : NlsGge.Pilot.IsComplexHilbertSchmidt S) :
    ‖S‖ ≤ NlsGge.Pilot.complexHilbertSchmidtNorm S := by
  let b := NlsGge.Pilot.chosenComplexHilbertBasis (E := KSTPairL2)
  have hs := NlsGge.Pilot.summable_basis_of_isComplexHilbertSchmidt b hS
  calc
    ‖S‖ ≤ Real.sqrt (∑' i, ‖S (b i)‖ ^ 2) :=
      NlsGge.Atomic.LIB023.opNorm_le_sqrt_columns b S hs
    _ = NlsGge.Pilot.complexHilbertSchmidtNorm S :=
      (NlsGge.Pilot.complexHilbertSchmidtNorm_eq_basis b hs).symm

/-- Fixed actual potential, one common cutoff before signed n and complex z;
only the genuine square is estimated before the operator HasSum is used. -/
private lemma stage14J_actual_square_neumann
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧ ∀ (n : ℤ), N₀ ≤ n.natAbs →
      ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
        let T : KSTPairL2 →L[ℂ] KSTPairL2 :=
          NlsGge.Atomic.KST006.qOperator φ n z hz
        IsUnit (1 - T) ∧
        HasSum (fun k : ℕ => (1 + T) * (T ^ 2) ^ k)
          (Ring.inverse (1 - T)) := by
  obtain ⟨ε, hε, N₀, hN₀, hlocal⟩ := NlsGge.Atomic.KST011.hs_qOperator_sq_decay φ
  refine ⟨N₀, hN₀, ?_⟩
  intro n hn z hz
  dsimp only
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
  have hφ : ‖φ - φ‖ < ε := by simpa only [sub_self, norm_zero] using hε
  have hsq := (hlocal φ hφ n hn).2 z hz
  have hfinite : NlsGge.Pilot.IsComplexHilbertSchmidt (T ^ 2) := by
    simpa only [T, pow_two, ContinuousLinearMap.mul_def] using hsq.1
  have hbound : NlsGge.Pilot.complexHilbertSchmidtNorm (T ^ 2) ≤ (1 / 2 : ℝ) := by
    simpa only [T, pow_two, ContinuousLinearMap.mul_def] using hsq.2
  have hsmall : ‖T ^ 2‖ < 1 := by
    calc
      ‖T ^ 2‖ ≤ NlsGge.Pilot.complexHilbertSchmidtNorm (T ^ 2) :=
        stage14J_opNorm_le_actual_hsNorm (T ^ 2) hfinite
      _ ≤ (1 / 2 : ℝ) := hbound
      _ < 1 := by norm_num
  obtain ⟨hunit, hinverse, _hright, _hleft⟩ :=
    NlsGge.Atomic.KST012.inverse_one_sub_of_sq_norm_lt T hsmall
  refine ⟨hunit, ?_⟩
  have hs : HasSum (fun k : ℕ => (T ^ 2) ^ k) (Ring.inverse (1 - T ^ 2)) :=
    hasSum_geom_series_inverse (T ^ 2) hsmall
  simpa only [← hinverse] using hs.mul_left (1 + T)

end NlsGge.Atomic.KST014
end

/- INERT / UNCOMPILED actual grouped-series diagonal consumption. -/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST007
open scoped InnerProduct InnerProductSpace

lemma stage14N_grouped_finite_diagonal_eq
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (k : ℕ) :
    let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
    inner ℂ (kstPnLower n)
      (((1 + T) * (T ^ 2) ^ k : KSTPairL2 →L[ℂ] KSTPairL2)
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))) =
    inner ℂ (kstPnUpper n)
      (((1 + T) * (T ^ 2) ^ k : KSTPairL2 →L[ℂ] KSTPairL2)
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n))) := by
  dsimp only
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
  have hgroup : (1 + T) * (T ^ 2) ^ k = T ^ (2 * k) + T ^ (2 * k + 1) := by
    rw [add_mul, one_mul, ← pow_mul, ← pow_succ']
  have hlzero : inner ℂ (kstPnLower n)
      ((T ^ (2 * k)) (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))) = 0 := by
    rw [stage14M_inner_lower_spectralCoeff,
      (stage14M_even_column_components_zero φ n z hz k).1]
    change (fourierBasis (T := (2 : ℝ))).repr 0 n = 0
    rw [map_zero]
    rfl
  have huzero : inner ℂ (kstPnUpper n)
      ((T ^ (2 * k)) (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n))) = 0 := by
    rw [stage14M_inner_upper_spectralCoeff,
      (stage14M_even_column_components_zero φ n z hz k).2]
    change (fourierBasis (T := (2 : ℝ))).repr 0 (-n) = 0
    rw [map_zero]
    rfl
  change inner ℂ (kstPnLower n)
      (((1 + T) * (T ^ 2) ^ k : KSTPairL2 →L[ℂ] KSTPairL2)
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))) =
    inner ℂ (kstPnUpper n)
      (((1 + T) * (T ^ 2) ^ k : KSTPairL2 →L[ℂ] KSTPairL2)
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n)))
  rw [hgroup, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
    inner_add_right, inner_add_right, hlzero, huzero, zero_add, zero_add]
  exact stage14M_actual_odd_diagonal_eq φ n z hz k

/-- The actual inverse diagonal entries agree at one source cutoff. No
outer path convergence is assumed; both scalar HasSum are images of J's
actual operator HasSum under genuine continuous linear functionals. -/
private lemma stage14N_actual_inverse_diagonals_eq
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧ ∀ (n : ℤ), N₀ ≤ n.natAbs →
      ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
        let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
        inner ℂ (kstPnLower n)
          (Ring.inverse (1 - T)
            (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))) =
        inner ℂ (kstPnUpper n)
          (Ring.inverse (1 - T)
            (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n))) := by
  obtain ⟨N₀, hN₀, hlocal⟩ := stage14J_actual_square_neumann φ
  refine ⟨N₀, hN₀, ?_⟩
  intro n hn z hz
  dsimp only
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
  have hs := (hlocal n hn z hz).2
  let Ll : (KSTPairL2 →L[ℂ] KSTPairL2) →L[ℂ] ℂ :=
    (innerSL ℂ (kstPnLower n)).comp
      (ContinuousLinearMap.apply ℂ KSTPairL2
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n)))
  let Lu : (KSTPairL2 →L[ℂ] KSTPairL2) →L[ℂ] ℂ :=
    (innerSL ℂ (kstPnUpper n)).comp
      (ContinuousLinearMap.apply ℂ KSTPairL2
        (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n)))
  have hl : HasSum (fun k : ℕ => Ll ((1 + T) * (T ^ 2) ^ k))
      (Ll (Ring.inverse (1 - T))) := Ll.hasSum hs
  have hu : HasSum (fun k : ℕ => Lu ((1 + T) * (T ^ 2) ^ k))
      (Lu (Ring.inverse (1 - T))) := Lu.hasSum hs
  have hpoint : ∀ k : ℕ, Ll ((1 + T) * (T ^ 2) ^ k) =
      Lu ((1 + T) * (T ^ 2) ^ k) := by
    intro k
    exact stage14N_grouped_finite_diagonal_eq φ n z hz k
  have hsamelower : HasSum (fun k : ℕ => Ll ((1 + T) * (T ^ 2) ^ k))
      (Lu (Ring.inverse (1 - T))) := hu.congr_fun hpoint
  exact hl.unique hsamelower

end NlsGge.Atomic.KST014
end

/- INERT / UNCOMPILED final literal reducedS consumption.
   Proposed context imports acceptedKST013; public interface activation belongs to root. -/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Schur NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST013
open scoped InnerProduct InnerProductSpace

private lemma stage14O_actual_Pn_diagonal_inner (n : ℤ) (f : KSTPairL2) :
    inner ℂ (kstPnLower n) (spectralPn n f) = inner ℂ (kstPnLower n) f ∧
    inner ℂ (kstPnUpper n) (spectralPn n f) = inner ℂ (kstPnUpper n) f := by
  have h := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have hul : inner ℂ (kstPnUpper n) (kstPnLower n) = 0 := by
    simpa [kstPnFrame] using h true false
  have hlu : inner ℂ (kstPnLower n) (kstPnUpper n) = 0 := by
    simpa [kstPnFrame] using h false true
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by
    simpa [kstPnFrame] using h true true
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by
    simpa [kstPnFrame] using h false false
  constructor <;> rw [spectralPn_apply] <;>
    simp only [inner_add_right, inner_smul_right, hul, hlu, huu, hll,
      mul_zero, mul_one, add_zero, zero_add]

/-- Private literal packet head; it does not activate a new public interface. -/
private lemma stage14O_literal_reduced_diagonals_eq
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ n : ℤ, N₀ ≤ n.natAbs →
        ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
          let e₁ : resonantSubspace n :=
            ⟨kstPnLower n, ⟨kstPnLower n, spectralPn_lower n⟩⟩
          let e₂ : resonantSubspace n :=
            ⟨kstPnUpper n, ⟨kstPnUpper n, spectralPn_upper n⟩⟩
          inner ℂ (e₁ : KSTPairL2) (reducedS φ n z hz e₁ : KSTPairL2) =
            inner ℂ (e₂ : KSTPairL2) (reducedS φ n z hz e₂ : KSTPairL2) := by
  obtain ⟨N₀, hN₀, hlocal⟩ := stage14N_actual_inverse_diagonals_eq φ
  refine ⟨N₀, hN₀, ?_⟩
  intro n hn z hz
  dsimp only
  let T : KSTPairL2 →L[ℂ] KSTPairL2 := NlsGge.Atomic.KST006.qOperator φ n z hz
  let fl : KSTPairL2 := Ring.inverse (1 - T)
    (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnLower n))
  let fu : KSTPairL2 := Ring.inverse (1 - T)
    (NlsGge.Atomic.KST012.potentialOnPn φ n (kstPnUpper n))
  have hEq : inner ℂ (kstPnLower n) fl = inner ℂ (kstPnUpper n) fu :=
    hlocal n hn z hz
  have ho := orthonormal_iff_ite.mp (kstPnFrame_orthonormal n)
  have hll : inner ℂ (kstPnLower n) (kstPnLower n) = 1 := by
    simpa [kstPnFrame] using ho false false
  have huu : inner ℂ (kstPnUpper n) (kstPnUpper n) = 1 := by
    simpa [kstPnFrame] using ho true true
  change inner ℂ (kstPnLower n)
      ((z - (n : ℂ) * (Real.pi : ℂ)) • kstPnLower n - spectralPn n fl) =
    inner ℂ (kstPnUpper n)
      ((z - (n : ℂ) * (Real.pi : ℂ)) • kstPnUpper n - spectralPn n fu)
  rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right,
    (stage14O_actual_Pn_diagonal_inner n fl).1,
    (stage14O_actual_Pn_diagonal_inner n fu).2, hll, huu, mul_one, hEq]

end NlsGge.Atomic.KST014
end

/- INERT exact command proposal; not a Lean module, not staged/compiled.
   Candidate import: accepted qualified NlsGge.Atomic.KST.KST013; complete PRIVATE proof context9fba is required.
   No hypotheses beyond the actual fixed source potential and spectral strip.
-/
noncomputable section
namespace NlsGge.Atomic.KST014
open NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST013
open scoped InnerProductSpace

theorem reduced_diagonals_eq
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ n : ℤ, N₀ ≤ n.natAbs →
        ∀ (z : ℂ) (hz : z ∈ spectralStrip n),
          let e₁ : resonantSubspace n :=
            ⟨kstPnLower n, ⟨kstPnLower n, spectralPn_lower n⟩⟩
          let e₂ : resonantSubspace n :=
            ⟨kstPnUpper n, ⟨kstPnUpper n, spectralPn_upper n⟩⟩
          inner ℂ (e₁ : KSTPairL2) (reducedS φ n z hz e₁ : KSTPairL2) =
            inner ℂ (e₂ : KSTPairL2) (reducedS φ n z hz e₂ : KSTPairL2)
 := by
  exact stage14O_literal_reduced_diagonals_eq φ

end NlsGge.Atomic.KST014
end
