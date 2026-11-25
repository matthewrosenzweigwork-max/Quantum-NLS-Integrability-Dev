import Mathlib
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.WkbStructure
import NlsGge.ThirdConsultation.G1.Round7

/- G1-035 support A (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/G1/Wkb035A.lean.
   H^1 closure, weak derivative and product linearity on H^1, finite combinatorics, and the algebraic
   identity R = tail for the finite WKB residual. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

/-! ### H^1 closure -/

theorem g35_H1_nat (u : PhysicalL2) (h : physicalSobolev ((1 : ℕ) : ℝ) u) : physicalSobolev 1 u := by
  simpa using h

theorem g35_H1_cast (u : PhysicalL2) (h : physicalSobolev 1 u) : physicalSobolev ((1 : ℕ) : ℝ) u := by
  simpa using h

theorem g35_H1_zero : physicalSobolev 1 (0 : PhysicalL2) :=
  g35_H1_nat _ ((physicalSobolev_iff_mem 1 0).2 (by
    rw [fS_zero]; exact (weightedSubmodule (sobolevModeWeight ((1 : ℕ) : ℝ))).zero_mem))

theorem g35_H1_add {u v : PhysicalL2} (hu : physicalSobolev 1 u) (hv : physicalSobolev 1 v) :
    physicalSobolev 1 (u + v) :=
  g35_H1_nat _ (psn_add 1 (g35_H1_cast u hu) (g35_H1_cast v hv)).1

theorem g35_H1_smul (c : ℂ) {u : PhysicalL2} (hu : physicalSobolev 1 u) :
    physicalSobolev 1 (c • u) := by
  apply g35_H1_nat
  rw [physicalSobolev_iff_mem]
  have h1 : fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    (physicalSobolev_iff_mem 1 u).1 (g35_H1_cast u hu)
  have e : fourierSeq38 (c • u) = c • fourierSeq38 u := by
    funext n
    unfold fourierSeq38
    simp
  rw [e]
  exact (weightedSubmodule (sobolevModeWeight ((1 : ℕ) : ℝ))).smul_mem c h1

theorem g35_H1_sum (s : Finset ℕ) (f : ℕ → PhysicalL2) (hf : ∀ i ∈ s, physicalSobolev 1 (f i)) :
    physicalSobolev 1 (∑ i ∈ s, f i) :=
  g35_H1_nat _ (psn_sum 1 s f (fun i hi => g35_H1_cast _ (hf i hi))).1

/-! ### Weak derivative on H^1 -/

theorem g35_D_add {u v : PhysicalL2} (hu : physicalSobolev 1 u) (hv : physicalSobolev 1 v) :
    weakDerivative (u + v) = weakDerivative u + weakDerivative v := by
  apply reflectedFourierL2.injective
  apply lp.ext
  funext n
  have h1 := weakDerivative_coeff u (weakDerivative_domain_of_H1 u hu) n
  have h2 := weakDerivative_coeff v (weakDerivative_domain_of_H1 v hv) n
  have h3 := weakDerivative_coeff (u + v) (weakDerivative_domain_of_H1 (u + v) (g35_H1_add hu hv)) n
  simp only [map_add, lp.coeFn_add, Pi.add_apply] at h3 ⊢
  rw [h3, h1, h2]
  ring

theorem g35_D_smul (c : ℂ) {u : PhysicalL2} (hu : physicalSobolev 1 u) :
    weakDerivative (c • u) = c • weakDerivative u := by
  apply reflectedFourierL2.injective
  apply lp.ext
  funext n
  have h1 := weakDerivative_coeff u (weakDerivative_domain_of_H1 u hu) n
  have h3 := weakDerivative_coeff (c • u) (weakDerivative_domain_of_H1 (c • u) (g35_H1_smul c hu)) n
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at h3 ⊢
  rw [h3, h1]
  ring

theorem g35_D_zero : weakDerivative (0 : PhysicalL2) = 0 := by
  apply reflectedFourierL2.injective
  apply lp.ext
  funext n
  rw [weakDerivative_coeff 0 (weakDerivative_domain_of_H1 0 g35_H1_zero) n]
  simp

theorem g35_D_sum (s : Finset ℕ) (f : ℕ → PhysicalL2) (a : ℕ → ℂ) :
    (∀ i ∈ s, physicalSobolev 1 (f i)) →
      weakDerivative (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i • weakDerivative (f i) := by
  induction s using Finset.induction_on with
  | empty => intro _; simp [g35_D_zero]
  | insert i s hi ih =>
    intro hf
    have hfi : physicalSobolev 1 (f i) := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, physicalSobolev 1 (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hS : physicalSobolev 1 (∑ j ∈ s, a j • f j) :=
      g35_H1_sum s (fun j => a j • f j) (fun j hj => g35_H1_smul _ (hfs j hj))
    rw [Finset.sum_insert hi, Finset.sum_insert hi, g35_D_add (g35_H1_smul _ hfi) hS,
      g35_D_smul _ hfi, ih hfs]

/-! ### Physical product on H^1 -/

theorem g35_P_ae (u z : PhysicalL2) (hu : physicalSobolev 1 u) :
    (physicalProduct u z : PhysicalCircle → ℂ) =ᵐ[spatialMeasure] fun x => u x * z x :=
  physicalProduct_ae u z (productInL2_of_H1 u z hu)

theorem g35_P_add_right (u z w : PhysicalL2) (hu : physicalSobolev 1 u) :
    physicalProduct u (z + w) = physicalProduct u z + physicalProduct u w := by
  apply Lp.ext
  filter_upwards [g35_P_ae u (z + w) hu, g35_P_ae u z hu, g35_P_ae u w hu, Lp.coeFn_add z w,
    Lp.coeFn_add (physicalProduct u z) (physicalProduct u w)] with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.add_apply]
  ring

theorem g35_P_add_left (u v z : PhysicalL2) (hu : physicalSobolev 1 u) (hv : physicalSobolev 1 v) :
    physicalProduct (u + v) z = physicalProduct u z + physicalProduct v z := by
  apply Lp.ext
  filter_upwards [g35_P_ae (u + v) z (g35_H1_add hu hv), g35_P_ae u z hu, g35_P_ae v z hv,
    Lp.coeFn_add u v, Lp.coeFn_add (physicalProduct u z) (physicalProduct v z)] with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.add_apply]
  ring

theorem g35_P_smul_right (c : ℂ) (u z : PhysicalL2) (hu : physicalSobolev 1 u) :
    physicalProduct u (c • z) = c • physicalProduct u z := by
  apply Lp.ext
  filter_upwards [g35_P_ae u (c • z) hu, g35_P_ae u z hu, Lp.coeFn_smul c z,
    Lp.coeFn_smul c (physicalProduct u z)] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.smul_apply, smul_eq_mul]
  ring

theorem g35_P_smul_left (c : ℂ) (u z : PhysicalL2) (hu : physicalSobolev 1 u) :
    physicalProduct (c • u) z = c • physicalProduct u z := by
  apply Lp.ext
  filter_upwards [g35_P_ae (c • u) z (g35_H1_smul c hu), g35_P_ae u z hu, Lp.coeFn_smul c u,
    Lp.coeFn_smul c (physicalProduct u z)] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.smul_apply, smul_eq_mul]
  ring

theorem g35_P_zero_left (z : PhysicalL2) : physicalProduct 0 z = 0 := by
  apply Lp.ext
  filter_upwards [g35_P_ae 0 z g35_H1_zero, Lp.coeFn_zero ℂ 2 spatialMeasure] with x h1 h2
  simp only [h1, h2, Pi.zero_apply, zero_mul]

theorem g35_P_sum_right (u : PhysicalL2) (hu : physicalSobolev 1 u) (s : Finset ℕ)
    (f : ℕ → PhysicalL2) :
    physicalProduct u (∑ i ∈ s, f i) = ∑ i ∈ s, physicalProduct u (f i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact physicalProduct_zero' u
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, g35_P_add_right u _ _ hu, ih]

theorem g35_P_sum_left (z : PhysicalL2) (s : Finset ℕ) (f : ℕ → PhysicalL2)
    (hf : ∀ i ∈ s, physicalSobolev 1 (f i)) :
    physicalProduct (∑ i ∈ s, f i) z = ∑ i ∈ s, physicalProduct (f i) z := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact g35_P_zero_left z
  | insert a s ha ih =>
    have hfa : physicalSobolev 1 (f a) := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ j ∈ s, physicalSobolev 1 (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      g35_P_add_left (f a) _ z hfa (g35_H1_sum s f hfs), ih hfs]

theorem g35_P_sum_smul_self (s : Finset ℕ) (c : ℕ → ℂ) (r : ℕ → PhysicalL2)
    (hr : ∀ i ∈ s, physicalSobolev 1 (r i)) :
    physicalProduct (∑ i ∈ s, c i • r i) (∑ i ∈ s, c i • r i) =
      ∑ i ∈ s, ∑ j ∈ s, (c i * c j) • physicalProduct (r i) (r j) := by
  rw [g35_P_sum_left _ s (fun i => c i • r i) (fun i hi => g35_H1_smul _ (hr i hi))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [g35_P_smul_left _ _ _ (hr i hi), g35_P_sum_right _ (hr i hi), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [g35_P_smul_right _ _ _ (hr i hi), smul_smul]

/-! ### Finite combinatorics -/

theorem g35_telescope {V : Type*} [AddCommGroup V] [Module ℂ V] (e : ℕ → ℂ) (r : ℕ → V)
    (he0 : e 0 = 1) (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, e n • r (n + 1) = ∑ n ∈ Finset.Icc 1 (M + 1), e (n - 1) • r n - r 1 := by
  induction M with
  | zero => simp [he0]
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1 + 1)]
    simp only [Nat.add_sub_cancel]
    abel

theorem g35_pair_succ {V : Type*} [AddCommGroup V] (H : ℕ → ℕ → V) (K : ℕ)
    (h1 : ∀ i ∈ Finset.Icc 1 K, H i (K + 1) = 0) (h2 : ∀ j ∈ Finset.Icc 1 (K + 1), H (K + 1) j = 0) :
    ∑ i ∈ Finset.Icc 1 (K + 1), ∑ j ∈ Finset.Icc 1 (K + 1), H i j =
      ∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K, H i j := by
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), Finset.sum_eq_zero (fun j hj => h2 j hj),
    add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), h1 i hi, add_zero]

theorem g35_antidiag {V : Type*} [AddCommGroup V] (F : ℕ → ℕ → V) (K : ℕ) :
    ∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K, (if i + j = K + 1 then F i j else 0) =
      ∑ i ∈ Finset.Icc 1 K, F i (K + 1 - i) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [Finset.sum_eq_single (K + 1 - i)]
  · rw [if_pos (show i + (K + 1 - i) = K + 1 by omega)]
  · intro b _ hne
    rw [if_neg (show ¬(i + b = K + 1) by intro h; apply hne; omega)]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_Icc]
    omega

theorem g35_reindex {V : Type*} [AddCommGroup V] (F : ℕ → ℕ → V) (K : ℕ) :
    ∑ n ∈ Finset.Icc 1 K, ∑ k ∈ Finset.Icc 1 (n - 1), F k (n - k) =
      ∑ i ∈ Finset.Icc 1 K, ∑ j ∈ Finset.Icc 1 K, (if i + j ≤ K then F i j else 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1), ih, Nat.add_sub_cancel]
    have h1 : ∀ i ∈ Finset.Icc 1 K, (if i + (K + 1) ≤ K + 1 then F i (K + 1) else 0) = 0 := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [if_neg (show ¬(i + (K + 1) ≤ K + 1) by omega)]
    have h2 : ∀ j ∈ Finset.Icc 1 (K + 1), (if K + 1 + j ≤ K + 1 then F (K + 1) j else 0) = 0 := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [if_neg (show ¬(K + 1 + j ≤ K + 1) by omega)]
    rw [g35_pair_succ (fun i j => if i + j ≤ K + 1 then F i j else 0) K h1 h2]
    have pt : ∀ i j : ℕ, (if i + j ≤ K + 1 then F i j else 0) =
        (if i + j ≤ K then F i j else 0) + (if i + j = K + 1 then F i j else 0) := by
      intro i j
      split_ifs <;> first | omega | simp
    simp only [pt, Finset.sum_add_distrib]
    rw [g35_antidiag F K]

theorem g35_split {V : Type*} [AddCommGroup V] (G : ℕ → ℕ → V) (M : ℕ) :
    ∑ i ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1), G i j =
      ∑ i ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (if i + j ≤ M then G i j else 0) +
      ∑ i ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
        (if M + 1 ≤ i + j then G i j else 0) := by
  have ext : ∀ i j : ℕ, G i j = (if i + j ≤ M then G i j else 0) +
      (if M + 1 ≤ i + j then G i j else 0) := by
    intro i j
    by_cases h : i + j ≤ M
    · rw [if_pos h, if_neg (show ¬(M + 1 ≤ i + j) by omega), add_zero]
    · rw [if_neg h, if_pos (show M + 1 ≤ i + j by omega), zero_add]
  have h1 : ∀ i ∈ Finset.Icc 1 M, (if i + (M + 1) ≤ M then G i (M + 1) else 0) = 0 := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [if_neg (show ¬(i + (M + 1) ≤ M) by omega)]
  have h2 : ∀ j ∈ Finset.Icc 1 (M + 1), (if M + 1 + j ≤ M then G (M + 1) j else 0) = 0 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [if_neg (show ¬(M + 1 + j ≤ M) by omega)]
  calc ∑ i ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1), G i j
      = ∑ i ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
          ((if i + j ≤ M then G i j else 0) + (if M + 1 ≤ i + j then G i j else 0)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ext i j))
    _ = ∑ i ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1), (if i + j ≤ M then G i j else 0) +
          ∑ i ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
            (if M + 1 ≤ i + j then G i j else 0) := by
        simp only [Finset.sum_add_distrib]
    _ = _ := by
        rw [g35_pair_succ (fun i j => if i + j ≤ M then G i j else 0) M h1 h2]

/-! ### Concrete identity -/

theorem g35_algebra {V : Type*} [AddCommGroup V] [Module ℂ V] (M : ℕ) (e : ℕ → ℂ) (h : ℂ)
    (r Dr : ℕ → V) (Q : ℕ → ℕ → V) (φ2 : V)
    (he0 : e 0 = 1) (he_mul : ∀ n j, e n * e j = e (n + j))
    (hh : ∀ n, 1 ≤ n → h * e n = e (n - 1))
    (hr1 : r 1 = -φ2)
    (hDr : ∀ n, 1 ≤ n → n ≤ M →
      Dr n = r (n + 1) - ∑ k ∈ Finset.Icc 1 (n - 1), Q k (n - k)) :
    (∑ n ∈ Finset.Icc 1 (M + 1), e n • Dr n) - h • (∑ n ∈ Finset.Icc 1 (M + 1), e n • r n) +
      (∑ n ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1), (e n * e j) • Q n j) - φ2 =
    e (M + 1) • Dr (M + 1) +
      ∑ n ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
        (if M + 1 ≤ n + j then e (n + j) • Q n j else 0) := by
  have A1 : ∑ n ∈ Finset.Icc 1 (M + 1), e n • Dr n =
      ∑ n ∈ Finset.Icc 1 M, e n • Dr n + e (M + 1) • Dr (M + 1) :=
    Finset.sum_Icc_succ_top (by omega) _
  have A2 : ∑ n ∈ Finset.Icc 1 M, e n • Dr n =
      ∑ n ∈ Finset.Icc 1 M, e n • r (n + 1) -
        ∑ n ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 (n - 1), e n • Q k (n - k) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [hDr n hn.1 hn.2, smul_sub, Finset.smul_sum]
  have A3 : ∑ n ∈ Finset.Icc 1 M, ∑ k ∈ Finset.Icc 1 (n - 1), e n • Q k (n - k) =
      ∑ i ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M,
        (if i + j ≤ M then e (i + j) • Q i j else 0) := by
    refine (Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun k hk => ?_))).trans
      (g35_reindex (fun i j => e (i + j) • Q i j) M)
    rw [Finset.mem_Icc] at hn hk
    have hen : e n = e (k + (n - k)) := by
      congr 1
      omega
    rw [hen]
  have A5 : ∑ n ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1), (e n * e j) • Q n j =
      ∑ i ∈ Finset.Icc 1 M, ∑ j ∈ Finset.Icc 1 M, (if i + j ≤ M then e (i + j) • Q i j else 0) +
        ∑ n ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
          (if M + 1 ≤ n + j then e (n + j) • Q n j else 0) := by
    simp only [he_mul]
    exact g35_split (fun i j => e (i + j) • Q i j) M
  have A6 : ∑ n ∈ Finset.Icc 1 M, e n • r (n + 1) =
      ∑ n ∈ Finset.Icc 1 (M + 1), e (n - 1) • r n - r 1 := g35_telescope e r he0 M
  have A7 : h • (∑ n ∈ Finset.Icc 1 (M + 1), e n • r n) =
      ∑ n ∈ Finset.Icc 1 (M + 1), e (n - 1) • r n := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [smul_smul, hh n hn.1]
  rw [A1, A2, A3, A5, A7, A6, hr1]
  abel

theorem g35_identity (M : ℕ) (φ : PotPair) (l : ℂ) (hl : 1 ≤ ‖l‖)
    (hr : ∀ k, 1 ≤ k → k ≤ M + 1 → physicalSobolev 1 (wkbR φ k))
    (hφ : physicalSobolev 1 φ.1) :
    wkbResidual (M + 1) l φ = wkbResidualTail (M + 1) l φ := by
  have hlne : l ≠ 0 := by
    intro h
    rw [h, norm_zero] at hl
    norm_num at hl
  have hl0 : (2 * Complex.I * l) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hlne
  have he0 : ((2 * Complex.I * l) ^ 0)⁻¹ = (1 : ℂ) := by simp
  have he_mul : ∀ n j : ℕ, ((2 * Complex.I * l) ^ n)⁻¹ * ((2 * Complex.I * l) ^ j)⁻¹ =
      ((2 * Complex.I * l) ^ (n + j))⁻¹ := by
    intro n j
    rw [← mul_inv, ← pow_add]
  have hh : ∀ n : ℕ, 1 ≤ n → (2 * Complex.I * l) * ((2 * Complex.I * l) ^ n)⁻¹ =
      ((2 * Complex.I * l) ^ (n - 1))⁻¹ := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, mul_inv]
    field_simp
  have hr1 : wkbR φ 1 = -φ.2 := wkbR_one φ
  have hDr : ∀ n : ℕ, 1 ≤ n → n ≤ M →
      weakDerivative (wkbR φ n) = wkbR φ (n + 1) -
        ∑ k ∈ Finset.Icc 1 (n - 1), physicalProduct φ.1 (physicalProduct (wkbR φ k) (wkbR φ (n - k))) := by
    intro n hn _
    have h := wkbR_succ φ n hn
    rw [g35_P_sum_right φ.1 hφ] at h
    exact eq_sub_of_add_eq h.symm
  have hfs : ∀ i ∈ Finset.Icc 1 (M + 1), physicalSobolev 1 (wkbR φ i) := fun i hi =>
    hr i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2
  have hW : weakDerivative (∑ n ∈ Finset.Icc 1 (M + 1), ((2 * Complex.I * l) ^ n)⁻¹ • wkbR φ n) =
      ∑ n ∈ Finset.Icc 1 (M + 1), ((2 * Complex.I * l) ^ n)⁻¹ • weakDerivative (wkbR φ n) :=
    g35_D_sum _ _ _ hfs
  have hP : physicalProduct φ.1
      (physicalProduct (∑ n ∈ Finset.Icc 1 (M + 1), ((2 * Complex.I * l) ^ n)⁻¹ • wkbR φ n)
        (∑ n ∈ Finset.Icc 1 (M + 1), ((2 * Complex.I * l) ^ n)⁻¹ • wkbR φ n)) =
      ∑ n ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
        (((2 * Complex.I * l) ^ n)⁻¹ * ((2 * Complex.I * l) ^ j)⁻¹) •
          physicalProduct φ.1 (physicalProduct (wkbR φ n) (wkbR φ j)) := by
    rw [g35_P_sum_smul_self _ _ _ hfs, g35_P_sum_right φ.1 hφ]
    apply Finset.sum_congr rfl
    intro n _
    rw [g35_P_sum_right φ.1 hφ]
    apply Finset.sum_congr rfl
    intro j _
    rw [g35_P_smul_right _ _ _ hφ]
  unfold wkbResidual wkbResidualTail
  unfold wkbPartial
  rw [hW, hP]
  exact g35_algebra M (fun n => ((2 * Complex.I * l) ^ n)⁻¹) (2 * Complex.I * l)
    (fun n => wkbR φ n) (fun n => weakDerivative (wkbR φ n))
    (fun k j => physicalProduct φ.1 (physicalProduct (wkbR φ k) (wkbR φ j))) φ.2
    he0 he_mul hh hr1 hDr

end NlsGge.GKDefinitionDesign
end
