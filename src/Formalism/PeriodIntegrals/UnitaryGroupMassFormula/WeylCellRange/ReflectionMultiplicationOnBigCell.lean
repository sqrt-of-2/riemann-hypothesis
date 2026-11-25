module

public import Formalism.HermitianCurvature.StatementQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix Finset

namespace PI.QnWCellW

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable def cN (r : ℕ) (c : Fin r → ℂ) (j : ℕ) : ℂ := if h : j < r then c ⟨j, h⟩ else 0

@[simp] theorem cN_val (r : ℕ) (c : Fin r → ℂ) (a : Fin r) : cN r c a.val = c a := by
  simp [cN, a.isLt]

theorem cN_mk (r : ℕ) (c : Fin r → ℂ) (j : ℕ) (h : j < r) : c ⟨j, h⟩ = cN r c j := by
  unfold cN
  rw [dite_eq_left h]

def swp (k r : ℕ) (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ p.val ∧ p.val ≤ r + k then p else ⟨2 * r + k - p.val, by omega⟩

theorem swp_val (k r : ℕ) (p : Fin (2 * r + k + 1)) :
    (swp k r p).val = if r ≤ p.val ∧ p.val ≤ r + k then p.val else 2 * r + k - p.val := by
  unfold swp
  split_ifs <;> rfl

theorem swp_swp (k r : ℕ) (p : Fin (2 * r + k + 1)) : swp k r (swp k r p) = p := by
  have hp := p.isLt
  apply Fin.ext
  rw [swp_val, swp_val]
  split_ifs <;> omega

noncomputable def cf (k r : ℕ) (c : Fin r → ℂ) (p : Fin (2 * r + k + 1)) : ℂ :=
  if p.val < r then (star (cN r c p.val))⁻¹
  else if p.val ≤ r + k then 1 else cN r c (2 * r + k - p.val)

noncomputable def Wm (k r : ℕ) (S : Finset ℕ) (c : Fin r → ℂ) : Mx k r := fun p q =>
  if q.val < r then
    (if q.val ∈ S then (if p.val = 2 * r + k - q.val then cN r c q.val else 0)
     else if p.val = q.val then 1 else 0)
  else if q.val ≤ r + k then (if p.val = q.val then 1 else 0)
  else if 2 * r + k - q.val ∈ S then
    (if p.val = 2 * r + k - q.val then (star (cN r c (2 * r + k - q.val)))⁻¹ else 0)
  else if p.val = q.val then 1 else 0

theorem eI_ne_esI (k r : ℕ) (l : Fin r) : eI k r l ≠ esI k r l := by
  intro h
  have hl := l.isLt
  rw [Fin.ext_iff] at h
  change l.val = 2 * r + k - l.val at h
  omega

theorem weyl_cell_mul_apply (k r : ℕ) (l : Fin r) (d : ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (w1 k r l d * M) p q =
      if p = esI k r l then d * M (eI k r l) q
      else if p = eI k r l then (star d)⁻¹ * M (esI k r l) q else M p q := by
  have hne := eI_ne_esI k r l
  rw [Matrix.mul_apply]
  by_cases h1 : p = esI k r l
  · subst h1
    rw [ite_eq_left rfl, Finset.sum_eq_single (eI k r l)]
    · simp [w1]
    · intro x _ hx
      simp [w1, hx, Ne.symm hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · by_cases h2 : p = eI k r l
    · subst h2
      rw [ite_eq_right h1, ite_eq_left rfl, Finset.sum_eq_single (esI k r l)]
      · simp [w1, hne]
      · intro x _ hx
        simp [w1, hx, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [ite_eq_right h1, ite_eq_right h2, Finset.sum_eq_single p]
      · simp [w1, h1, h2]
      · intro x _ hx
        simp [w1, h1, h2, Ne.symm hx]
      · intro h; exact absurd (Finset.mem_univ _) h

theorem Wm_empty (k r : ℕ) (c : Fin r → ℂ) : Wm k r ∅ c = 1 := by
  ext p q
  simp [Wm, Matrix.one_apply, Fin.val_inj]



theorem reflection_mul_weyl_cell (k r : ℕ) (S : Finset ℕ) (c : Fin r → ℂ) (a : Fin r) (ha : a.val ∉ S) :
    w1 k r a (c a) * Wm k r S c = Wm k r (insert a.val S) c := by
  ext p q
  rw [weyl_cell_mul_apply]
  have hA := a.isLt
  have hp := p.isLt
  have hq := q.isLt
  have vE : (eI k r a).val = a.val := rfl
  have vS : (esI k r a).val = 2 * r + k - a.val := rfl
  simp only [Wm, Finset.mem_insert]
  by_cases h1 : q.val = a.val
  · simp only [h1, ha, or_false, ite_true, ite_false]
    split_ifs <;> (try simp only [Fin.ext_iff, vE, vS] at *) <;> first | (exfalso; omega) | (simp)
  · by_cases h2 : q.val = 2 * r + k - a.val
    · have e2 : 2 * r + k - (2 * r + k - a.val) = a.val := by omega
      simp only [h2, e2, ha, or_false, ite_true, ite_false]
      split_ifs <;> (try simp only [Fin.ext_iff, vE, vS] at *) <;> first | (exfalso; omega) | (simp)
    · have h3 : 2 * r + k - q.val ≠ a.val := by omega
      simp only [h1, h3, false_or]
      split_ifs <;> (try simp only [Fin.ext_iff, vE, vS] at *) <;> first | (exfalso; omega) | (simp)

theorem prod_eq_Wm (k r : ℕ) (c : Fin r → ℂ) : ∀ L : List (Fin r), L.Nodup →
    (L.map fun a => w1 k r a (c a)).prod = Wm k r (L.map Fin.val).toFinset c
  | [], _ => by simpa using (Wm_empty k r c).symm
  | a :: L, h => by
      rw [List.map_cons, List.prod_cons, prod_eq_Wm k r c L (List.nodup_cons.1 h).2, List.map_cons,
        List.toFinset_cons]
      apply reflection_mul_weyl_cell
      intro hm
      rw [List.mem_toFinset, List.mem_map_of_injective Fin.val_injective] at hm
      exact (List.nodup_cons.1 h).1 hm

theorem wCell_last (k r : ℕ) (c : Fin r → ℂ) : wCell k r (Fin.last r) c = Wm k r (Finset.range r) c := by
  unfold wCell
  rw [List.filter_eq_self.mpr (fun a _ => by simp [a.isLt]), prod_eq_Wm k r c _ (List.nodup_finRange r)]
  congr 1
  ext j
  simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and, Finset.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.isLt
  · intro hj
    exact ⟨⟨j, hj⟩, rfl⟩



theorem Wm_range_apply (k r : ℕ) (c : Fin r → ℂ) (p x : Fin (2 * r + k + 1)) :
    Wm k r (Finset.range r) c p x = if x = swp k r p then cf k r c p else 0 := by
  have hp := p.isLt
  have hx := x.isLt
  simp only [Wm, Finset.mem_range, cf, Fin.ext_iff, swp_val]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1 <;> omega) | (congr 1; congr 1; congr 1; omega)

theorem Wm_mul_apply (k r : ℕ) (c : Fin r → ℂ) (M : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Wm k r (Finset.range r) c * M) p q = cf k r c p * M (swp k r p) q := by
  rw [Matrix.mul_apply]
  simp_rw [Wm_range_apply]
  simp [ite_mul]

def μE {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : ℕ) : ℂ :=
  if h : i < k + 1 ∧ j < k + 1 then μ ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

theorem μE_mk {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : ℕ) (hi : i < k + 1) (hj : j < k + 1) :
    μ ⟨i, hi⟩ ⟨j, hj⟩ = μE μ i j := by
  unfold μE
  rw [dite_eq_left ⟨hi, hj⟩]

theorem bigCell_apply (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (p q : Fin (2 * r + k + 1)) :
    bigCell k r c μ p q =
      if q.val < r then (if p.val = 2 * r + k - q.val then cN r c q.val else 0)
      else if q.val ≤ r + k then
        (if r ≤ p.val ∧ p.val ≤ r + k then μE μ (p.val - r) (q.val - r) else 0)
      else (if p.val = 2 * r + k - q.val then (star (cN r c (2 * r + k - q.val)))⁻¹ else 0) := by
  have hq := q.isLt
  simp only [bigCell]
  by_cases h1 : q.val < r
  · rw [dite_eq_left h1, ite_eq_left h1, cN_mk r c q.val h1]
    have e : (p = esI k r ⟨q.val, h1⟩) ↔ p.val = 2 * r + k - q.val := by
      rw [Fin.ext_iff]
      rfl
    by_cases h : p.val = 2 * r + k - q.val
    · rw [ite_eq_left (e.mpr h), ite_eq_left h]
    · rw [ite_eq_right (mt e.mp h), ite_eq_right h]
  · rw [dite_eq_right h1, ite_eq_right h1]
    by_cases h2 : q.val ≤ r + k
    · rw [dite_eq_left h2, ite_eq_left h2]
      by_cases h3 : r ≤ p.val ∧ p.val ≤ r + k
      · rw [dite_eq_left h3, ite_eq_left h3]
        exact μE_mk μ _ _ _ _
      · rw [dite_eq_right h3, ite_eq_right h3]
    · rw [dite_eq_right h2, ite_eq_right h2]
      have h4 : 2 * r + k - q.val < r := by omega
      rw [cN_mk r c _ h4]


end PI.QnWCellW
