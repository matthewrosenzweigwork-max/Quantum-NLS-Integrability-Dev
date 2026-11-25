import Mathlib
import NlsGge.Atomic.M.M054
import NlsGge.Atomic.M.M055
import NlsGge.Atomic.M.M056
import NlsGge.Atomic.DM.DM046
import NlsGge.ThirdConsultation.M.M021Real
import NlsGge.ThirdConsultation.M.M022Kernel

                                                                                                          
                                                                                                                               
                                                                                                     
                                                                                                               
                                                                                            

set_option autoImplicit false

open NlsGge.ThirdConsultation.MTwoMode.Real21 (cs_sq young_real)
open NlsGge.Atomic.M.M054 (indexWeight)

namespace NlsGge.ThirdConsultation.M.M022
noncomputable section

/-- Abbreviations (explicit definitions, unfolded only in the local identities). -/
def kern (s : ℤ) (α β : ℤ → ℂ) (m l : ℤ) : ℝ :=
  ‖α m‖ * ((1 + |((m + s : ℤ) : ℝ)|) / (1 + |((m - l : ℤ) : ℝ)|)) *
    (‖β l‖ / (1 + |((l + s : ℤ) : ℝ)|))

def aw (w : ℤ → ℝ) (pI : ℤ → ℂ) (j : ℤ) : ℝ := w j * ‖pI j‖

def bw (w : ℤ → ℝ) (s : ℤ) (x : ℤ → ℂ) (l : ℤ) : ℝ := w (l + s) * ‖x l‖

def cw (s : ℤ) (β : ℤ → ℂ) (l : ℤ) : ℝ := ‖β l‖ ^ 2 / (1 + |((l + s : ℤ) : ℝ)|) ^ 2

theorem one_le_small (t : ℤ) :
    (if t = 0 then (0 : ℝ) else 1 / |((t : ℤ) : ℝ)|) ≤ 1 := by
  split_ifs with ht
  · norm_num
  · have h1 : (1 : ℝ) ≤ |((t : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs ht
    exact div_le_one_of_le₀ h1 (by linarith)

theorem amgm2 (x y : ℝ) : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by
  nlinarith [sq_nonneg (x - y)]

theorem w_ge_one (w v : ℤ → ℝ) (hw : ∀ k : ℤ, w k = indexWeight k * v k)
    (hv1 : ∀ k : ℤ, 1 ≤ v k) (j : ℤ) : 1 ≤ w j := by
  rw [hw j]
  have h1 : (1 : ℝ) ≤ indexWeight j := by
    unfold indexWeight
    have := abs_nonneg ((j : ℝ))
    linarith
  calc (1 : ℝ) ≤ indexWeight j := h1
    _ = indexWeight j * 1 := (mul_one _).symm
    _ ≤ indexWeight j * v j := mul_le_mul_of_nonneg_left (hv1 j) (le_trans zero_le_one h1)

theorem F1_of (w v : ℤ → ℝ) (hw : ∀ k : ℤ, w k = indexWeight k * v k)
    (hv1 : ∀ k : ℤ, 1 ≤ v k) (hsub : NlsGge.Atomic.DM046.SubmultiplicativeWeight v)
    (s k m : ℤ) : w (k + s) ≤ w (k - m) * w (m + s) := by
  have hsub' : v (k + s) ≤ v (k - m) * v (m + s) := by
    have h := hsub (k - m) (m + s)
    rwa [show k - m + (m + s) = k + s by ring] at h
  have hρ' : indexWeight (k + s) ≤ indexWeight (k - m) * indexWeight (m + s) := by
    have h := NlsGge.ThirdConsultation.M.M022.indexWeight_add_le (k - m) (m + s)
    rwa [show k - m + (m + s) = k + s by ring] at h
  have hv0 : 0 ≤ v (k + s) := le_trans zero_le_one (hv1 _)
  have hρ0 : 0 < indexWeight (k - m) * indexWeight (m + s) := by
    have h1 : (0 : ℝ) < indexWeight (k - m) := by unfold indexWeight; positivity
    have h2 : (0 : ℝ) < indexWeight (m + s) := by unfold indexWeight; positivity
    exact mul_pos h1 h2
  rw [hw (k + s), hw (k - m), hw (m + s)]
  calc indexWeight (k + s) * v (k + s)
      ≤ (indexWeight (k - m) * indexWeight (m + s)) * (v (k - m) * v (m + s)) :=
        mul_le_mul hρ' hsub' hv0 hρ0.le
    _ = indexWeight (k - m) * v (k - m) * (indexWeight (m + s) * v (m + s)) := by ring

theorem F2_of (w v : ℤ → ℝ) (hw : ∀ k : ℤ, w k = indexWeight k * v k)
    (heven : ∀ k : ℤ, v (-k) = v k) (hsub : NlsGge.Atomic.DM046.SubmultiplicativeWeight v)
    (s m l : ℤ) : w (m + s) ≤
      indexWeight (m + s) * w (m - l) * w (l + s) /
        (indexWeight (m - l) * indexWeight (l + s)) := by
  have h := NlsGge.Atomic.M.M054.two_resolvent_weight_factor heven hsub m (-l) (-s)
  have e : ∀ j : ℤ, NlsGge.Atomic.M.M054.w v j = w j := fun j => (hw j).symm
  simp only [e] at h
  have e1 : m - -s = m + s := by ring
  have e2 : m + -l = m - l := by ring
  have e3 : -(-l) - -s = l + s := by ring
  have e4 : -l + -s = -(l + s) := by ring
  rw [e1, e2, e3, e4, NlsGge.ThirdConsultation.M.M022.indexWeight_neg] at h
  exact h

theorem aw_nonneg (w : ℤ → ℝ) (pI : ℤ → ℂ) (hw1 : ∀ j, 1 ≤ w j) (j : ℤ) :
    0 ≤ aw w pI j :=
  mul_nonneg (le_trans zero_le_one (hw1 j)) (norm_nonneg _)

theorem bw_nonneg (w : ℤ → ℝ) (s : ℤ) (x : ℤ → ℂ) (hw1 : ∀ j, 1 ≤ w j) (l : ℤ) :
    0 ≤ bw w s x l :=
  mul_nonneg (le_trans zero_le_one (hw1 _)) (norm_nonneg _)

theorem kern_nonneg (s : ℤ) (α β : ℤ → ℂ) (m l : ℤ) : 0 ≤ kern s α β m l := by
  unfold kern
  positivity

theorem kern_sq (s : ℤ) (α β : ℤ → ℂ) (m l : ℤ) :
    kern s α β m l ^ 2 = ‖α m‖ ^ 2 *
      ((1 + |((m + s : ℤ) : ℝ)|) ^ 2 / (1 + |((m - l : ℤ) : ℝ)|) ^ 2) * cw s β l := by
  unfold kern cw
  rw [mul_pow, mul_pow, div_pow, div_pow]

theorem kern_le (s : ℤ) (α β : ℤ → ℂ) (m l : ℤ) (hβ1 : ‖β l‖ ≤ 1) :
    kern s α β m l ≤ ‖α m‖ * (1 + |((m + s : ℤ) : ℝ)|) := by
  unfold kern
  have h1 : (1 + |((m + s : ℤ) : ℝ)|) / (1 + |((m - l : ℤ) : ℝ)|) ≤ 1 + |((m + s : ℤ) : ℝ)| :=
    div_le_self (by positivity) (by linarith [abs_nonneg ((m - l : ℤ) : ℝ)])
  have h2 : ‖β l‖ / (1 + |((l + s : ℤ) : ℝ)|) ≤ 1 :=
    div_le_one_of_le₀ (by linarith [abs_nonneg ((l + s : ℤ) : ℝ)]) (by positivity)
  have h3 : ‖α m‖ * ((1 + |((m + s : ℤ) : ℝ)|) / (1 + |((m - l : ℤ) : ℝ)|)) ≤
      ‖α m‖ * (1 + |((m + s : ℤ) : ℝ)|) :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have h4 : 0 ≤ ‖β l‖ / (1 + |((l + s : ℤ) : ℝ)|) := by positivity
  calc ‖α m‖ * ((1 + |((m + s : ℤ) : ℝ)|) / (1 + |((m - l : ℤ) : ℝ)|)) *
        (‖β l‖ / (1 + |((l + s : ℤ) : ℝ)|))
      ≤ ‖α m‖ * (1 + |((m + s : ℤ) : ℝ)|) * 1 :=
        mul_le_mul h3 h2 h4 (by positivity)
    _ = ‖α m‖ * (1 + |((m + s : ℤ) : ℝ)|) := mul_one _

/-- Column sums: for each l, sum_m kern(m,l)^2 <= (32/5) cw(l), summable. -/
theorem kern_colsum (s : ℤ) (α β : ℤ → ℂ)
    (hα : ∀ m : ℤ, ‖α m‖ ≤ if m + s = 0 then 0 else 1 / |((m + s : ℤ) : ℝ)|) (l : ℤ) :
    Summable (fun m : ℤ => kern s α β m l ^ 2) ∧
      ∑' m : ℤ, kern s α β m l ^ 2 ≤ 32 / 5 * cw s β l := by
  obtain ⟨h1, h2⟩ := NlsGge.ThirdConsultation.M.M022.outer_col s α hα l
  have e : (fun m : ℤ => kern s α β m l ^ 2) = fun m : ℤ =>
      ‖α m‖ ^ 2 * ((1 + |((m + s : ℤ) : ℝ)|) ^ 2 / (1 + |((m - l : ℤ) : ℝ)|) ^ 2) * cw s β l :=
    funext fun m => kern_sq s α β m l
  refine ⟨?_, ?_⟩
  · rw [e]
    exact h1.mul_right _
  · rw [e, tsum_mul_right]
    exact mul_le_mul_of_nonneg_right h2 (by unfold cw; positivity)

theorem norm_term_bound (w : ℤ → ℝ) (s : ℤ) (pI x β : ℤ → ℂ) (m l : ℤ)
    (hw1 : ∀ j, 1 ≤ w j) (hβ1 : ‖β l‖ ≤ 1) :
    ‖pI (m - l) * (β l * x l)‖ ≤ (aw w pI (m - l) ^ 2 + bw w s x l ^ 2) / 2 := by
  have hpI : ‖pI (m - l)‖ ≤ aw w pI (m - l) := by
    unfold aw
    exact le_mul_of_one_le_left (norm_nonneg _) (hw1 _)
  have hxb : ‖x l‖ ≤ bw w s x l := by
    unfold bw
    exact le_mul_of_one_le_left (norm_nonneg _) (hw1 _)
  have hprod' : ‖β l‖ * ‖x l‖ ≤ 1 * bw w s x l :=
    mul_le_mul hβ1 hxb (norm_nonneg _) zero_le_one
  have h1 : ‖pI (m - l) * (β l * x l)‖ ≤ aw w pI (m - l) * bw w s x l := by
    rw [norm_mul, norm_mul]
    calc ‖pI (m - l)‖ * (‖β l‖ * ‖x l‖) ≤ aw w pI (m - l) * (1 * bw w s x l) :=
          mul_le_mul hpI hprod' (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (aw_nonneg w pI hw1 _)
      _ = aw w pI (m - l) * bw w s x l := by rw [one_mul]
  exact le_trans h1 (amgm2 _ _)

theorem l1_term (w : ℤ → ℝ) (s : ℤ) (α β pI x : ℤ → ℂ) (m l : ℤ)
    (F2ml : w (m + s) ≤ indexWeight (m + s) * w (m - l) * w (l + s) /
        (indexWeight (m - l) * indexWeight (l + s))) :
    w (m + s) * ‖α m‖ * ‖pI (m - l) * (β l * x l)‖ ≤
      kern s α β m l * aw w pI (m - l) * bw w s x l := by
  have nn : 0 ≤ ‖α m‖ * ‖pI (m - l)‖ * (‖β l‖ * ‖x l‖) := by positivity
  calc w (m + s) * ‖α m‖ * ‖pI (m - l) * (β l * x l)‖
      = w (m + s) * (‖α m‖ * ‖pI (m - l)‖ * (‖β l‖ * ‖x l‖)) := by
        rw [norm_mul, norm_mul]
        ring
    _ ≤ (indexWeight (m + s) * w (m - l) * w (l + s) /
          (indexWeight (m - l) * indexWeight (l + s))) *
          (‖α m‖ * ‖pI (m - l)‖ * (‖β l‖ * ‖x l‖)) :=
        mul_le_mul_of_nonneg_right F2ml nn
    _ = kern s α β m l * aw w pI (m - l) * bw w s x l := by
        unfold kern aw bw indexWeight
        generalize (1 + |((m - l : ℤ) : ℝ)|) = U
        generalize (1 + |((l + s : ℤ) : ℝ)|) = V
        generalize (1 + |((m + s : ℤ) : ℝ)|) = T
        ring

theorem row_summable (w : ℤ → ℝ) (s : ℤ) (α β pI x : ℤ → ℂ) (m : ℤ)
    (hw1 : ∀ j, 1 ≤ w j) (hβ1 : ∀ l, ‖β l‖ ≤ 1)
    (hsh : Summable fun l : ℤ => aw w pI (m - l) ^ 2)
    (hb2 : Summable fun l : ℤ => bw w s x l ^ 2) :
    Summable fun l : ℤ => kern s α β m l * aw w pI (m - l) * bw w s x l := by
  have hC : 0 ≤ ‖α m‖ * (1 + |((m + s : ℤ) : ℝ)|) := by positivity
  refine Summable.of_nonneg_of_le (fun l => ?_) (fun l => ?_)
    ((((hsh.add hb2).mul_left (‖α m‖ * (1 + |((m + s : ℤ) : ℝ)|))).div_const 2))
  · exact mul_nonneg (mul_nonneg (kern_nonneg s α β m l) (aw_nonneg w pI hw1 _))
      (bw_nonneg w s x hw1 l)
  · have hk := kern_le s α β m l (hβ1 l)
    have hab : 0 ≤ aw w pI (m - l) * bw w s x l :=
      mul_nonneg (aw_nonneg w pI hw1 _) (bw_nonneg w s x hw1 l)
    have e1 : kern s α β m l * aw w pI (m - l) * bw w s x l =
        kern s α β m l * (aw w pI (m - l) * bw w s x l) := mul_assoc _ _ _
    rw [e1]
    have h2 := mul_le_mul_of_nonneg_right hk hab
    have h3 := amgm2 (aw w pI (m - l)) (bw w s x l)
    have h4 := mul_le_mul_of_nonneg_left h3 hC
    have h5 : ‖α m‖ * (1 + |((m + s : ℤ) : ℝ)|) * (aw w pI (m - l) * bw w s x l) ≤
        ‖α m‖ * (1 + |((m + s : ℤ) : ℝ)|) * ((aw w pI (m - l) ^ 2 + bw w s x l ^ 2) / 2) := h4
    have h6 : ‖α m‖ * (1 + |((m + s : ℤ) : ℝ)|) * ((aw w pI (m - l) ^ 2 + bw w s x l ^ 2) / 2) =
        ‖α m‖ * (1 + |((m + s : ℤ) : ℝ)|) * (aw w pI (m - l) ^ 2 + bw w s x l ^ 2) / 2 := by ring
    linarith


theorem inner_row_sum_bound (s : ℤ) (β : ℤ → ℂ)
    (hβ : ∀ l : ℤ, ‖β l‖ ≤ if l - s = 0 then 0 else 1 / |((l - s : ℤ) : ℝ)|) :
    Summable (cw s β) ∧ ∑' l : ℤ, cw s β l ≤ (5 / 2 : ℝ) / (1 + |(s : ℝ)|) ^ 2 :=
  NlsGge.ThirdConsultation.M.M022.inner_row s β hβ

theorem chain_bound
    (w v : ℤ → ℝ)
    (hw : ∀ k : ℤ, w k = indexWeight k * v k)
    (hv1 : ∀ k : ℤ, 1 ≤ v k)
    (heven : ∀ k : ℤ, v (-k) = v k)
    (hsub : NlsGge.Atomic.DM046.SubmultiplicativeWeight v)
    (s : ℤ) (pO pI x α β : ℤ → ℂ)
    (hα : ∀ m : ℤ, ‖α m‖ ≤ if m + s = 0 then 0 else 1 / |((m + s : ℤ) : ℝ)|)
    (hβ : ∀ l : ℤ, ‖β l‖ ≤ if l - s = 0 then 0 else 1 / |((l - s : ℤ) : ℝ)|)
    (hPo : Summable fun j : ℤ => w j ^ 2 * ‖pO j‖ ^ 2)
    (hPi : Summable fun j : ℤ => w j ^ 2 * ‖pI j‖ ^ 2)
    (hX : Summable fun l : ℤ => w (l + s) ^ 2 * ‖x l‖ ^ 2) :
    Summable (fun k : ℤ =>
      (w (k + s) * ‖∑' m : ℤ, pO (k - m) * (α m * ∑' l : ℤ, pI (m - l) * (β l * x l))‖) ^ 2) ∧
    ∑' k : ℤ, (w (k + s) * ‖∑' m : ℤ, pO (k - m) * (α m * ∑' l : ℤ, pI (m - l) * (β l * x l))‖) ^ 2 ≤
      16 / (1 + |(s : ℝ)|) ^ 2 * (∑' j : ℤ, w j ^ 2 * ‖pO j‖ ^ 2) *
        (∑' j : ℤ, w j ^ 2 * ‖pI j‖ ^ 2) * (∑' l : ℤ, w (l + s) ^ 2 * ‖x l‖ ^ 2) := by
  have hw1 : ∀ j : ℤ, (1 : ℝ) ≤ w j := w_ge_one w v hw hv1
  have hw0 : ∀ j : ℤ, (0 : ℝ) ≤ w j := fun j => le_trans zero_le_one (hw1 j)
  have F1 : ∀ k m : ℤ, w (k + s) ≤ w (k - m) * w (m + s) := F1_of w v hw hv1 hsub s
  have F2 : ∀ m l : ℤ, w (m + s) ≤ indexWeight (m + s) * w (m - l) * w (l + s) /
      (indexWeight (m - l) * indexWeight (l + s)) := F2_of w v hw heven hsub s
  have hα1 : ∀ m : ℤ, ‖α m‖ ≤ 1 := fun m => le_trans (hα m) (one_le_small (m + s))
  have hβ1 : ∀ l : ℤ, ‖β l‖ ≤ 1 := fun l => le_trans (hβ l) (one_le_small (l - s))
  have hA2 : Summable fun j : ℤ => aw w pO j ^ 2 :=
    hPo.congr fun j => by unfold aw; rw [mul_pow]
  have ha2 : Summable fun j : ℤ => aw w pI j ^ 2 :=
    hPi.congr fun j => by unfold aw; rw [mul_pow]
  have hb2 : Summable fun l : ℤ => bw w s x l ^ 2 :=
    hX.congr fun l => by unfold bw; rw [mul_pow]
  obtain ⟨hcs_c, hcb⟩ := inner_row_sum_bound s β hβ
  have hshift : ∀ l : ℤ, Summable (fun m : ℤ => aw w pI (m - l) ^ 2) := fun l =>
    ha2.comp_injective (i := fun m : ℤ => m - l) (fun m m' h => by simpa using h)
  have hshift' : ∀ m : ℤ, Summable (fun l : ℤ => aw w pI (m - l) ^ 2) := fun m =>
    ha2.comp_injective (i := fun l : ℤ => m - l) (fun l l' h => by simpa using h)
  have hshiftEq : ∀ l : ℤ, ∑' m : ℤ, aw w pI (m - l) ^ 2 = ∑' j : ℤ, aw w pI j ^ 2 := fun l =>
    (Equiv.subRight l).tsum_eq (fun j => aw w pI j ^ 2)
  -- inner sums G(l) = sum_m kern(m,l) aw(m-l)
  obtain ⟨G, hG⟩ : ∃ G : ℤ → ℝ, ∀ l, G l = ∑' m : ℤ, kern s α β m l * aw w pI (m - l) :=
    ⟨fun l => ∑' m : ℤ, kern s α β m l * aw w pI (m - l), fun l => rfl⟩
  have hG0 : ∀ l : ℤ, 0 ≤ G l := fun l => by
    rw [hG]
    exact tsum_nonneg fun m => mul_nonneg (kern_nonneg s α β m l) (aw_nonneg w pI hw1 _)
  have hcsG : ∀ l : ℤ, Summable (fun m : ℤ => kern s α β m l * aw w pI (m - l)) ∧
      (∑' m : ℤ, kern s α β m l * aw w pI (m - l)) ^ 2 ≤
        (∑' m : ℤ, kern s α β m l ^ 2) * (∑' m : ℤ, aw w pI (m - l) ^ 2) := fun l =>
    cs_sq (fun m => kern s α β m l) (fun m => aw w pI (m - l))
      (fun m => kern_nonneg s α β m l) (fun m => aw_nonneg w pI hw1 _)
      (kern_colsum s α β hα l).1 (hshift l)
  have hGsq : ∀ l : ℤ, G l ^ 2 ≤ (32 / 5 * ∑' j : ℤ, aw w pI j ^ 2) * cw s β l := by
    intro l
    calc G l ^ 2 = (∑' m : ℤ, kern s α β m l * aw w pI (m - l)) ^ 2 := by rw [hG]
      _ ≤ (∑' m : ℤ, kern s α β m l ^ 2) * (∑' m : ℤ, aw w pI (m - l) ^ 2) := (hcsG l).2
      _ = (∑' m : ℤ, kern s α β m l ^ 2) * (∑' j : ℤ, aw w pI j ^ 2) := by rw [hshiftEq l]
      _ ≤ (32 / 5 * cw s β l) * (∑' j : ℤ, aw w pI j ^ 2) :=
          mul_le_mul_of_nonneg_right (kern_colsum s α β hα l).2 (tsum_nonneg fun j => sq_nonneg _)
      _ = (32 / 5 * ∑' j : ℤ, aw w pI j ^ 2) * cw s β l := by ring
  have hG2 : Summable fun l : ℤ => G l ^ 2 :=
    Summable.of_nonneg_of_le (fun l => sq_nonneg _) hGsq (hcs_c.mul_left _)
  have hGb : Summable fun l : ℤ => G l * bw w s x l :=
    Summable.of_nonneg_of_le (fun l => mul_nonneg (hG0 l) (bw_nonneg w s x hw1 l))
      (fun l => amgm2 (G l) (bw w s x l)) ((hG2.add hb2).div_const 2)
  have hFcol : ∀ l : ℤ, Summable (fun m : ℤ => kern s α β m l * aw w pI (m - l) * bw w s x l) :=
    fun l => (hcsG l).1.mul_right _
  have hFrow : ∀ m : ℤ, Summable (fun l : ℤ => kern s α β m l * aw w pI (m - l) * bw w s x l) :=
    fun m => row_summable w s α β pI x m hw1 hβ1 (hshift' m) hb2
  -- summability on the product and the Tonelli swap
  have hnnP : (0 : ℤ × ℤ → ℝ) ≤ fun p : ℤ × ℤ =>
      kern s α β p.2 p.1 * aw w pI (p.2 - p.1) * bw w s x p.1 :=
    fun p => mul_nonneg (mul_nonneg (kern_nonneg _ _ _ _ _) (aw_nonneg w pI hw1 _))
      (bw_nonneg w s x hw1 _)
  have hprodsum : Summable (fun p : ℤ × ℤ =>
      kern s α β p.2 p.1 * aw w pI (p.2 - p.1) * bw w s x p.1) :=
    (summable_prod_of_nonneg hnnP).2 ⟨fun l => hFcol l, hGb.congr fun l =>
      (show ∑' y : ℤ, kern s α β y l * aw w pI (y - l) * bw w s x l = G l * bw w s x l by
        rw [hG, tsum_mul_right]).symm⟩
  have hU : Summable (Function.uncurry fun m l : ℤ => kern s α β m l * aw w pI (m - l) * bw w s x l) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr hprodsum
  have hswap : ∑' l : ℤ, ∑' m : ℤ, kern s α β m l * aw w pI (m - l) * bw w s x l =
      ∑' m : ℤ, ∑' l : ℤ, kern s α β m l * aw w pI (m - l) * bw w s x l :=
    Summable.tsum_comm' hU (fun m => hU.prod_factor m) (fun l => hFcol l)
  have hRsum : Summable fun m : ℤ => ∑' l : ℤ, kern s α β m l * aw w pI (m - l) * bw w s x l :=
    hU.prod
  -- the l1 function Y(m) = w(m+s) |alpha m| |g m|
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℂ, ∀ m, g m = ∑' l : ℤ, pI (m - l) * (β l * x l) :=
    ⟨fun m => ∑' l : ℤ, pI (m - l) * (β l * x l), fun m => rfl⟩
  simp only [← hg]
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ → ℝ, ∀ m, Y m = w (m + s) * ‖α m‖ * ‖g m‖ :=
    ⟨fun m => w (m + s) * ‖α m‖ * ‖g m‖, fun m => rfl⟩
  have hY0 : ∀ m, 0 ≤ Y m := fun m => by
    rw [hY]
    exact mul_nonneg (mul_nonneg (hw0 _) (norm_nonneg _)) (norm_nonneg _)
  have hnormsum : ∀ m : ℤ, Summable fun l : ℤ => ‖pI (m - l) * (β l * x l)‖ := fun m =>
    Summable.of_nonneg_of_le (fun l => norm_nonneg _)
      (fun l => norm_term_bound w s pI x β m l hw1 (hβ1 l))
      (((hshift' m).add hb2).div_const 2)
  have hgnorm : ∀ m : ℤ, ‖g m‖ ≤ ∑' l : ℤ, ‖pI (m - l) * (β l * x l)‖ := fun m => by
    rw [hg]
    exact norm_tsum_le_tsum_norm (hnormsum m)
  have hYF : ∀ m : ℤ, Y m ≤ ∑' l : ℤ, kern s α β m l * aw w pI (m - l) * bw w s x l := by
    intro m
    rw [hY]
    have hwα : 0 ≤ w (m + s) * ‖α m‖ := mul_nonneg (hw0 _) (norm_nonneg _)
    calc w (m + s) * ‖α m‖ * ‖g m‖
        ≤ w (m + s) * ‖α m‖ * ∑' l : ℤ, ‖pI (m - l) * (β l * x l)‖ :=
          mul_le_mul_of_nonneg_left (hgnorm m) hwα
      _ = ∑' l : ℤ, w (m + s) * ‖α m‖ * ‖pI (m - l) * (β l * x l)‖ := tsum_mul_left.symm
      _ ≤ ∑' l : ℤ, kern s α β m l * aw w pI (m - l) * bw w s x l :=
          Summable.tsum_le_tsum (fun l => l1_term w s α β pI x m l (F2 m l))
            ((hnormsum m).mul_left (w (m + s) * ‖α m‖)) (hFrow m)
  have hYsum : Summable Y := Summable.of_nonneg_of_le hY0 hYF hRsum
  have hYle : ∀ m : ℤ, Y m ≤ ∑' j : ℤ, Y j := fun m =>
    le_hasSum hYsum.hasSum m (fun j _ => hY0 j)
  have hY2 : Summable fun m : ℤ => Y m ^ 2 :=
    Summable.of_nonneg_of_le (fun m => sq_nonneg _)
      (fun m => by
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hYle m) (hY0 m))
      (hYsum.mul_left (∑' j : ℤ, Y j))
  have hsumAY : ∀ k : ℤ, Summable fun m : ℤ => aw w pO (k - m) * Y m := fun k =>
    (cs_sq (fun m => aw w pO (k - m)) Y (fun m => aw_nonneg w pO hw1 _) hY0
      (hA2.comp_injective (i := fun m : ℤ => k - m) (fun m m' h => by simpa using h)) hY2).1
  have hterm : ∀ k m : ℤ, w (k + s) * ‖pO (k - m) * (α m * g m)‖ ≤ aw w pO (k - m) * Y m := by
    intro k m
    have h1 := F1 k m
    have nn : 0 ≤ ‖pO (k - m)‖ * (‖α m‖ * ‖g m‖) := by positivity
    calc w (k + s) * ‖pO (k - m) * (α m * g m)‖
        = w (k + s) * (‖pO (k - m)‖ * (‖α m‖ * ‖g m‖)) := by rw [norm_mul, norm_mul]
      _ ≤ (w (k - m) * w (m + s)) * (‖pO (k - m)‖ * (‖α m‖ * ‖g m‖)) :=
          mul_le_mul_of_nonneg_right h1 nn
      _ = aw w pO (k - m) * Y m := by
          unfold aw
          rw [hY]
          ring
  have hbound : ∀ k : ℤ, w (k + s) * ‖∑' m : ℤ, pO (k - m) * (α m * g m)‖ ≤
      ∑' m : ℤ, aw w pO (k - m) * Y m := by
    intro k
    have hsumn : Summable fun m : ℤ => ‖pO (k - m) * (α m * g m)‖ :=
      Summable.of_nonneg_of_le (fun m => norm_nonneg _)
        (fun m => le_trans (le_mul_of_one_le_left (norm_nonneg _) (hw1 (k + s))) (hterm k m))
        (hsumAY k)
    calc w (k + s) * ‖∑' m : ℤ, pO (k - m) * (α m * g m)‖
        ≤ w (k + s) * ∑' m : ℤ, ‖pO (k - m) * (α m * g m)‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsumn) (hw0 _)
      _ = ∑' m : ℤ, w (k + s) * ‖pO (k - m) * (α m * g m)‖ := tsum_mul_left.symm
      _ ≤ ∑' m : ℤ, aw w pO (k - m) * Y m :=
          Summable.tsum_le_tsum (fun m => hterm k m) (hsumn.mul_left _) (hsumAY k)
  -- Young in squared form
  obtain ⟨hYs, hYt⟩ := young_real (aw w pO) Y (fun j => aw_nonneg w pO hw1 j) hY0 hA2 hYsum
  have hsq_bd : ∀ k : ℤ, (w (k + s) * ‖∑' m : ℤ, pO (k - m) * (α m * g m)‖) ^ 2 ≤
      (∑' m : ℤ, aw w pO (k - m) * Y m) ^ 2 := fun k =>
    pow_le_pow_left₀ (mul_nonneg (hw0 _) (norm_nonneg _)) (hbound k) 2
  have hmain1 : Summable (fun k : ℤ =>
      (w (k + s) * ‖∑' m : ℤ, pO (k - m) * (α m * g m)‖) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hsq_bd hYs
  have hmain2 : ∑' k : ℤ, (w (k + s) * ‖∑' m : ℤ, pO (k - m) * (α m * g m)‖) ^ 2 ≤
      (∑' l : ℤ, Y l) ^ 2 * ∑' m : ℤ, aw w pO m ^ 2 :=
    le_trans (Summable.tsum_le_tsum hsq_bd hmain1 hYs) hYt
  -- l1 bound by Cauchy-Schwarz in the outer index
  have hSY : ∑' m : ℤ, Y m ≤ ∑' l : ℤ, bw w s x l * G l := by
    calc ∑' m : ℤ, Y m ≤ ∑' m : ℤ, ∑' l : ℤ, kern s α β m l * aw w pI (m - l) * bw w s x l :=
          Summable.tsum_le_tsum hYF hYsum hRsum
      _ = ∑' l : ℤ, ∑' m : ℤ, kern s α β m l * aw w pI (m - l) * bw w s x l := hswap.symm
      _ = ∑' l : ℤ, G l * bw w s x l := tsum_congr fun l => by rw [hG, tsum_mul_right]
      _ = ∑' l : ℤ, bw w s x l * G l := tsum_congr fun l => mul_comm _ _
  have hEb : ∑' l : ℤ, bw w s x l ^ 2 = ∑' l : ℤ, w (l + s) ^ 2 * ‖x l‖ ^ 2 :=
    tsum_congr fun l => by unfold bw; rw [mul_pow]
  have hPin : ∑' j : ℤ, aw w pI j ^ 2 = ∑' j : ℤ, w j ^ 2 * ‖pI j‖ ^ 2 :=
    tsum_congr fun j => by unfold aw; rw [mul_pow]
  have hPout : ∑' j : ℤ, aw w pO j ^ 2 = ∑' j : ℤ, w j ^ 2 * ‖pO j‖ ^ 2 :=
    tsum_congr fun j => by unfold aw; rw [mul_pow]
  have hGsum : ∑' l : ℤ, G l ^ 2 ≤ 16 / (1 + |(s : ℝ)|) ^ 2 * ∑' j : ℤ, aw w pI j ^ 2 := by
    calc ∑' l : ℤ, G l ^ 2 ≤ ∑' l : ℤ, (32 / 5 * ∑' j : ℤ, aw w pI j ^ 2) * cw s β l :=
          Summable.tsum_le_tsum hGsq hG2 (hcs_c.mul_left _)
      _ = (32 / 5 * ∑' j : ℤ, aw w pI j ^ 2) * ∑' l : ℤ, cw s β l := tsum_mul_left
      _ ≤ (32 / 5 * ∑' j : ℤ, aw w pI j ^ 2) * ((5 / 2 : ℝ) / (1 + |(s : ℝ)|) ^ 2) :=
          mul_le_mul_of_nonneg_left hcb
            (mul_nonneg (by norm_num) (tsum_nonneg fun j => sq_nonneg _))
      _ = 16 / (1 + |(s : ℝ)|) ^ 2 * ∑' j : ℤ, aw w pI j ^ 2 := by ring
  have hS2 : (∑' l : ℤ, bw w s x l * G l) ^ 2 ≤
      (∑' l : ℤ, bw w s x l ^ 2) * (16 / (1 + |(s : ℝ)|) ^ 2 * ∑' j : ℤ, aw w pI j ^ 2) := by
    obtain ⟨_, hcs⟩ := cs_sq (bw w s x) G (fun l => bw_nonneg w s x hw1 l) hG0 hb2 hG2
    exact le_trans hcs (mul_le_mul_of_nonneg_left hGsum (tsum_nonneg fun l => sq_nonneg _))
  have hYS2 : (∑' l : ℤ, Y l) ^ 2 ≤
      (∑' l : ℤ, bw w s x l ^ 2) * (16 / (1 + |(s : ℝ)|) ^ 2 * ∑' j : ℤ, aw w pI j ^ 2) :=
    le_trans (pow_le_pow_left₀ (tsum_nonneg fun l => hY0 l) hSY 2) hS2
  refine ⟨hmain1, ?_⟩
  calc ∑' k : ℤ, (w (k + s) * ‖∑' m : ℤ, pO (k - m) * (α m * g m)‖) ^ 2
      ≤ (∑' l : ℤ, Y l) ^ 2 * ∑' m : ℤ, aw w pO m ^ 2 := hmain2
    _ ≤ ((∑' l : ℤ, bw w s x l ^ 2) * (16 / (1 + |(s : ℝ)|) ^ 2 * ∑' j : ℤ, aw w pI j ^ 2)) *
          ∑' m : ℤ, aw w pO m ^ 2 :=
        mul_le_mul_of_nonneg_right hYS2 (tsum_nonneg fun m => sq_nonneg _)
    _ = 16 / (1 + |(s : ℝ)|) ^ 2 * (∑' j : ℤ, w j ^ 2 * ‖pO j‖ ^ 2) *
          (∑' j : ℤ, w j ^ 2 * ‖pI j‖ ^ 2) * (∑' l : ℤ, w (l + s) ^ 2 * ‖x l‖ ^ 2) := by
        rw [hPout, hPin, hEb]
        ring

end
end NlsGge.ThirdConsultation.M.M022
