module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.PtEntryNeZeroImp
public import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.FlagMatLower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix

noncomputable section

namespace PI.AmpRootCommon

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem pt_spec (p : Point ℂ (r + 1)) (i : Fin (r + 1)) :
    pv p.1 i.val < r + 1 ∧ pv p.1 (pv p.1 i.val) = i.val ∧ ptEntry p.1 i.val (pv p.1 i.val) ≠ 0 := by
  let rec pv_spec : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i < (bs.map Prod.snd).sum →
      pv bs i < (bs.map Prod.snd).sum ∧ pv bs (pv bs i) = i ∧ ptEntry bs i (pv bs i) ≠ 0
    | [], _, i, hi => by simp at hi
    | (t, s) :: bs, hb, i, hi => by
      have ht : t ≠ 0 := (hb (t, s) (by simp)).1
      have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (by simp [h])
      simp only [List.map_cons, List.sum_cons] at hi ⊢
      by_cases h1 : i < s
      · have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, h1]
        have e2 : pv ((t, s) :: bs) (s - 1 - i) = i := by
          simp only [pv]; rw [ite_eq_left (by omega)]; omega
        refine ⟨by omega, by rw [e1, e2], ?_⟩
        rw [e1]; unfold ptEntry
        rw [ite_eq_left ⟨h1, by omega⟩, ite_eq_left (by omega)]; exact ht
      · obtain ⟨ih1, ih2, ih3⟩ := pv_spec bs hb' (i - s) (by omega)
        have e1 : pv ((t, s) :: bs) i = s + pv bs (i - s) := by simp [pv, h1]
        have e2 : pv ((t, s) :: bs) (s + pv bs (i - s)) = i := by
          simp only [pv]; rw [ite_eq_right (by omega), Nat.add_sub_cancel_left, ih2]; omega
        refine ⟨by omega, by rw [e1, e2], ?_⟩
        rw [e1]; unfold ptEntry
        rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]; exact ih3
  have h := pv_spec p.1 p.2.1 i.val (by rw [p.2.2]; exact i.isLt)
  rw [p.2.2] at h
  exact h

def ptσ (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : Fin (r + 1) := ⟨pv p.1 i.val, (pt_spec p i).1⟩

def ptζ (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ℂ :=
  (-1 : ℂ) ^ (r - (ptσ p i).val) * ptMat p i (ptσ p i)

theorem ptσ_invol (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ptσ p (ptσ p i) = i := Fin.ext (pt_spec p i).2.1

theorem ptζ_ne (p : Point ℂ (r + 1)) (i : Fin (r + 1)) : ptζ p i ≠ 0 := by
  unfold ptζ
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pt_spec p i).2.2

theorem neg_one_pow_mul_self (m : ℕ) : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
  rw [← mul_pow]
  norm_num

theorem zhat_pt {z z' : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : Point ℂ (r + 1)} (hP : ZhatO k r z z' g = ptMat p) (i j : Fin (r + 1)) :
    Zhat k r z z' g i j = if j = ptσ p i then ptζ p i else 0 := by
  let rec ptEntry_ne_zero_imp : ∀ (bs : List (ℂ × ℕ)) (i j : ℕ), ptEntry bs i j ≠ 0 → j = pv bs i
    | [], i, j, h => by simp [ptEntry] at h
    | (t, s) :: bs, i, j, h => by
      unfold ptEntry at h
      unfold pv
      by_cases h1 : i < s ∧ j < s
      · rw [ite_eq_left h1] at h
        by_cases h2 : i + j + 1 = s
        · rw [ite_eq_left h1.1]; omega
        · rw [ite_eq_right h2] at h; exact absurd rfl h
      · rw [ite_eq_right h1] at h
        by_cases h3 : s ≤ i ∧ s ≤ j
        · rw [ite_eq_left h3] at h
          have := ptEntry_ne_zero_imp bs (i - s) (j - s) h
          rw [ite_eq_right (by omega)]; omega
        · rw [ite_eq_right h3] at h; exact absurd rfl h
  have hZ : Zhat k r z z' g i j = (-1 : ℂ) ^ (r - j.val) * ptMat p i j := by
    have h := congrFun (congrFun hP i) j
    simp only [ZhatO] at h
    rw [← h, ← mul_assoc, neg_one_pow_mul_self, one_mul]
  rw [hZ]
  split_ifs with hj
  · subst hj
    rfl
  · have : ptEntry p.1 i.val j.val = 0 := by
      by_contra hne
      exact hj (Fin.ext (ptEntry_ne_zero_imp p.1 i.val j.val hne))
    show (-1 : ℂ) ^ (r - j.val) * ptEntry p.1 i.val j.val = 0
    rw [this, mul_zero]

theorem pt_adj (p : Point ℂ (r + 1)) (i i1 : Fin (r + 1)) (hi1 : i1.val = i.val + 1) :
    ((ptσ p i1).val + 1 = (ptσ p i).val ∧ ptζ p (ptσ p i1) = - ptζ p (ptσ p i)) ∨
      (ptσ p i).val < (ptσ p i1).val := by
  let rec pv_adj : ∀ (bs : List (ℂ × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → ∀ i, i + 1 < (bs.map Prod.snd).sum →
      (pv bs (i + 1) + 1 = pv bs i ∧ ptEntry bs (pv bs (i + 1)) (i + 1) = ptEntry bs (pv bs i) i) ∨
        pv bs i < pv bs (i + 1)
    | [], _, i, hi => by simp at hi
    | (t, s) :: bs, hb, i, hi => by
      have hb' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b h => hb b (by simp [h])
      simp only [List.map_cons, List.sum_cons] at hi
      by_cases h1 : i + 1 < s
      · left
        have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, show i < s by omega]
        have e2 : pv ((t, s) :: bs) (i + 1) = s - 1 - (i + 1) := by simp [pv, h1]
        rw [e1, e2]
        refine ⟨by omega, ?_⟩
        unfold ptEntry
        rw [ite_eq_left ⟨by omega, h1⟩, ite_eq_left (by omega), ite_eq_left ⟨by omega, by omega⟩, ite_eq_left (by omega)]
      · by_cases h2 : i + 1 = s
        · right
          have e1 : pv ((t, s) :: bs) i = s - 1 - i := by simp [pv, show i < s by omega]
          have e2 : pv ((t, s) :: bs) (i + 1) = s + pv bs (i + 1 - s) := by simp [pv, h1]
          rw [e1, e2]; omega
        · have e1 : pv ((t, s) :: bs) i = s + pv bs (i - s) := by simp [pv, show ¬ i < s by omega]
          have e2 : pv ((t, s) :: bs) (i + 1) = s + pv bs (i - s + 1) := by
            simp only [pv]; rw [ite_eq_right h1, show i + 1 - s = i - s + 1 by omega]
          rw [e1, e2]
          rcases pv_adj bs hb' (i - s) (by omega) with ⟨h3, h4⟩ | h3
          · left
            refine ⟨by omega, ?_⟩
            have hA : ¬ (s + pv bs (i - s + 1) < s ∧ i + 1 < s) := by omega
            have hB : s ≤ s + pv bs (i - s + 1) ∧ s ≤ i + 1 := by omega
            have hC : ¬ (s + pv bs (i - s) < s ∧ i < s) := by omega
            have hD : s ≤ s + pv bs (i - s) ∧ s ≤ i := by omega
            unfold ptEntry
            rw [ite_eq_right hA, ite_eq_left hB, ite_eq_right hC, ite_eq_left hD, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left,
              show i + 1 - s = i - s + 1 by omega]
            exact h4
          · right; omega
  have hs := p.2.2
  have hi1lt := i1.isLt
  rcases pv_adj p.1 p.2.1 i.val (by rw [hs]; omega) with ⟨h1, h2⟩ | h1
  · left
    have hv : pv p.1 i1.val = pv p.1 (i.val + 1) := by rw [hi1]
    refine ⟨by show pv p.1 i1.val + 1 = pv p.1 i.val; rw [hv]; exact h1, ?_⟩
    unfold ptζ
    rw [ptσ_invol p i1, ptσ_invol p i]
    show (-1 : ℂ) ^ (r - i1.val) * ptEntry p.1 (pv p.1 i1.val) i1.val =
      -((-1 : ℂ) ^ (r - i.val) * ptEntry p.1 (pv p.1 i.val) i.val)
    rw [hv, hi1, h2]
    have hr : r - i.val = (r - (i.val + 1)) + 1 := by omega
    rw [hr, pow_succ]
    ring
  · right
    show pv p.1 i.val < pv p.1 i1.val
    rw [hi1]
    exact h1

theorem flag_rel_Rset {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z')
    {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r))
    (hx : x ∈ Formalism.MainNotions.S.Rset k r g) :
    (flagMat k r z (g * x * g⁻¹))ᴴ * Zhat k r z z' g * flagMat k r z' x = Zhat k r z z' g := by
  have hgi : g⁻¹ * g = 1 := uh_inv_mul hg
  have hxe : g⁻¹ * (g * x * g⁻¹) * g = x := by
    calc g⁻¹ * (g * x * g⁻¹) * g = (g⁻¹ * g) * x * (g⁻¹ * g) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hgi, Matrix.one_mul, Matrix.mul_one]
  have ha : g * x * g⁻¹ ∈ RStab k r g := ⟨hx.2, by rw [hxe]; exact hx.1⟩
  have h := flag_rel hz hz' hg ha
  rw [hxe] at h
  exact h

section AtPt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {g a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
  {p : Point ℂ (r + 1)}

private theorem isUnit_det_of_unitriangular {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u.BlockTriangular id)
    (hd : ∀ i, u i i = 1) : IsUnit u.det := by
  rw [Matrix.det_of_isUpperTriangular hu, Finset.prod_eq_one fun i _ => hd i]
  exact isUnit_one

theorem flag_entry (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (i j : Fin (r + 1)) :
    ptζ p i * flagMat k r z' (g⁻¹ * a * g) (ptσ p i) j =
      star ((flagMat k r z a)⁻¹ (ptσ p j) i) * ptζ p (ptσ p j) := by
  have hU := isUnit_det_of_unitriangular (flagMat k r z a) (flagMat_upper ha.1) (flagMat_diag ha.1)
  have hrel := flag_rel hz hz' hg ha
  have hkey : Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g) =
      ((flagMat k r z a)⁻¹)ᴴ * Zhat k r z z' g := by
    calc Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g)
        = ((flagMat k r z a)⁻¹)ᴴ *
            ((flagMat k r z a)ᴴ * Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g)) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
            Matrix.mul_nonsing_inv _ hU, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = ((flagMat k r z a)⁻¹)ᴴ * Zhat k r z z' g := by rw [hrel]
  have hσ : ∀ l, (j = ptσ p l) ↔ (l = ptσ p j) := by
    intro l
    constructor
    · rintro rfl
      exact (ptσ_invol p l).symm
    · rintro rfl
      exact (ptσ_invol p j).symm
  have h := congrFun (congrFun hkey i) j
  simp only [Matrix.mul_apply, zhat_pt hP, hσ, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.conjTranspose_apply] at h
  exact h

private theorem blockTriangular_inv_of_unitriangular {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u.BlockTriangular id)
    (hd : ∀ i, u i i = 1) : u⁻¹.BlockTriangular id := by
  have hU := isUnit_det_of_unitriangular u hu hd
  let : Invertible u := ⟨u⁻¹, Matrix.nonsing_inv_mul u hU, Matrix.mul_nonsing_inv u hU⟩
  exact Matrix.blockTriangular_inv_of_blockTriangular hu

private theorem star_flagMat_mul_ptZeta_eq (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (m n : Fin (r + 1)) :
    star (flagMat k r z a (ptσ p n) m) * ptζ p (ptσ p n) =
      ptζ p m * (flagMat k r z' (g⁻¹ * a * g))⁻¹ (ptσ p m) n := by
  have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
  have hU := isUnit_det_of_unitriangular (flagMat k r z' (g⁻¹ * a * g)) (flagMat_upper hx) (flagMat_diag hx)
  have hrel := flag_rel hz hz' hg ha
  have hkey : (flagMat k r z a)ᴴ * Zhat k r z z' g =
      Zhat k r z z' g * (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by
    calc (flagMat k r z a)ᴴ * Zhat k r z z' g
        = (flagMat k r z a)ᴴ * Zhat k r z z' g * flagMat k r z' (g⁻¹ * a * g) *
            (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by
          rw [Matrix.mul_assoc _ (flagMat k r z' (g⁻¹ * a * g)), Matrix.mul_nonsing_inv _ hU,
            Matrix.mul_one]
      _ = Zhat k r z z' g * (flagMat k r z' (g⁻¹ * a * g))⁻¹ := by rw [hrel]
  have hσ : ∀ l, (n = ptσ p l) ↔ (l = ptσ p n) := by
    intro l
    constructor
    · rintro rfl
      exact (ptσ_invol p l).symm
    · rintro rfl
      exact (ptσ_invol p n).symm
  have h := congrFun (congrFun hkey m) n
  simp only [Matrix.mul_apply, zhat_pt hP, hσ, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.conjTranspose_apply] at h
  exact h

theorem flag_offblock (hz : inWb k r z) (hz' : inWb k r z') (hg : g ∈ UH (Hpk k r))
    (hP : ZhatO k r z z' g = ptMat p) (ha : a ∈ RStab k r g) (i j : Fin (r + 1))
    (hlt : (ptσ p i).val < (ptσ p j).val) :
    flagMat k r z' (g⁻¹ * a * g) i j = 0 ∧ flagMat k r z a i j = 0 := by
  have hlt' : ptσ p i < ptσ p j := hlt
  refine ⟨?_, ?_⟩
  · have h := flag_entry hz hz' hg hP ha (ptσ p i) j
    rw [ptσ_invol] at h
    have hv := blockTriangular_inv_of_unitriangular (flagMat k r z a) (flagMat_upper ha.1) (flagMat_diag ha.1)
    have h0 : (flagMat k r z a)⁻¹ (ptσ p j) (ptσ p i) = 0 := hv hlt'
    rw [h0, star_zero, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (ptζ_ne p _)
  · have h := star_flagMat_mul_ptZeta_eq hz hz' hg hP ha j (ptσ p i)
    rw [ptσ_invol] at h
    have hx : g⁻¹ * a * g ∈ Nset k r := ha.2
    have hv := blockTriangular_inv_of_unitriangular (flagMat k r z' (g⁻¹ * a * g)) (flagMat_upper hx) (flagMat_diag hx)
    have h0 : (flagMat k r z' (g⁻¹ * a * g))⁻¹ (ptσ p j) (ptσ p i) = 0 := hv hlt'
    rw [h0, mul_zero] at h
    exact star_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (ptζ_ne p i))

end AtPt

end PI.AmpRootCommon
