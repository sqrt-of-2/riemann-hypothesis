module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.BlockPermutation

open Formalism.MainNotions.S Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj

variable {K : Type*} [Field K]

theorem pval_pperm : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    pval bs (pperm bs i) = pval bs i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · simp only [pperm, pval, hi, ite_true]
      rw [ite_eq_left (by omega)]
    · simp only [pperm, pval, hi, ite_false]
      rw [ite_eq_right (by omega), show s + pperm bs (i - s) - s = pperm bs (i - s) by omega]
      exact pval_pperm bs (i - s) (by omega)

omit [Field K] in
theorem blkOf_pperm [Field K] : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    blkOf bs (pperm bs i) = blkOf bs i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · simp only [pperm, blkOf, hi, ite_true]
      rw [ite_eq_left (by omega)]
    · simp only [pperm, blkOf, hi, ite_false]
      rw [ite_eq_right (by omega), show s + pperm bs (i - s) - s = pperm bs (i - s) by omega]
      rw [blkOf_pperm bs (i - s) (by omega)]

omit [Field K] in
theorem pperm_lt_iff [Field K] : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → (i < j ↔ pperm bs j < pperm bs i)
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pperm, h1, h2, ite_true]; omega
    · simp only [blkOf, h1, h2, ite_true, ite_false] at hb; omega
    · simp only [blkOf, h1, h2, ite_true, ite_false] at hb; omega
    · simp only [blkOf, h1, h2, ite_false, add_left_inj] at hb
      simp only [pperm, h1, h2, ite_false]
      have := pperm_lt_iff bs (i - s) (j - s) (by omega) (by omega) hb
      omega

omit [Field K] in
theorem lt_of_blkOf_lt [Field K] : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i < blkOf bs j → i < j ∧ pperm bs i < pperm bs j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [blkOf, h1, h2, ite_true] at hb; omega
    · simp only [pperm, h1, h2, ite_true, ite_false]; omega
    · simp only [blkOf, h1, h2, ite_true, ite_false] at hb; omega
    · simp only [blkOf, h1, h2, ite_false, add_lt_add_iff_right] at hb
      simp only [pperm, h1, h2, ite_false]
      have := lt_of_blkOf_lt bs (i - s) (j - s) (by omega) (by omega) hb
      omega

omit [Field K] in
theorem pperm_add [Field K] : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → pperm bs i + i = pperm bs j + j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pperm, h1, h2, ite_true]; omega
    · simp only [blkOf, h1, h2, ite_true, ite_false] at hb; omega
    · simp only [blkOf, h1, h2, ite_true, ite_false] at hb; omega
    · simp only [blkOf, h1, h2, ite_false, add_left_inj] at hb
      simp only [pperm, h1, h2, ite_false]
      have := pperm_add bs (i - s) (j - s) (by omega) (by omega) hb
      omega

omit [Field K] in
theorem blkOf_mono [Field K] : ∀ (bs : List (K × ℕ)) (i j : ℕ), i ≤ j → blkOf bs i ≤ blkOf bs j
  | [], i, j, _ => by simp [blkOf]
  | (t, s) :: bs, i, j, hij => by
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp [blkOf, h1, h2]
    · simp [blkOf, h1, h2]
    · omega
    · simp only [blkOf, h1, h2, ite_false, add_le_add_iff_right]
      exact blkOf_mono bs (i - s) (j - s) (by omega)

theorem pval_eq_of_blk : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → pval bs i = pval bs j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pval, h1, h2, ite_true]
    · simp only [blkOf, h1, h2, ite_true, ite_false] at hb; omega
    · simp only [blkOf, h1, h2, ite_true, ite_false] at hb; omega
    · simp only [blkOf, h1, h2, ite_false, add_left_inj] at hb
      simp only [pval, h1, h2, ite_false]
      exact pval_eq_of_blk bs (i - s) (j - s) (by omega) (by omega) hb

section Pt

variable {N : ℕ} (p : Point K N)

theorem pval_pinv (a : Fin N) : pval p.1 (pinv p a).val = pval p.1 a.val :=
  pval_pperm p.1 a.val (by rw [p.2.2]; exact a.isLt)

theorem blkOf_pinv (a : Fin N) : blkOf p.1 (pinv p a).val = blkOf p.1 a.val :=
  blkOf_pperm p.1 a.val (by rw [p.2.2]; exact a.isLt)

theorem pinv_lt_iff (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) : a < b ↔ pinv p b < pinv p a :=
  pperm_lt_iff p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem lt_of_blk_lt (a b : Fin N) (hb : blkOf p.1 a.val < blkOf p.1 b.val) : a < b ∧ pinv p a < pinv p b :=
  lt_of_blkOf_lt p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem pinv_add (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) :
    (pinv p a).val + a.val = (pinv p b).val + b.val :=
  pperm_add p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem pval_eq_blk (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) : pval p.1 a.val = pval p.1 b.val :=
  pval_eq_of_blk p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

end Pt

end Formalism.L2.SG.Pf.BlockPermutation
