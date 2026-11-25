module

public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ColOKOfPath
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

open Formalism.MainNotions.G Formalism.MainNotions.LemmaBAlt

theorem strip_count {n : ℕ} (nu mu : Fin n → ℤ) (b : ℕ) (h : HStrip nu mu b) (S : Finset ℤ)
    (hS : ∀ a c, nu a < c → c ≤ mu a → c ∈ S) :
    (S.filter fun c => colH nu c ≠ colH mu c).card = b := by
  classical
  have h1 : ∀ c, ((if colH nu c ≠ colH mu c then 1 else 0 : ℕ) : ℤ) =
      ∑ a : Fin n, (if nu a < c ∧ c ≤ mu a then (1 : ℤ) else 0) := by
    intro c
    obtain ⟨l1, l2⟩ := colH_strip nu mu b h c
    have e : (colH mu c : ℤ) - colH nu c = ∑ a : Fin n, (if nu a < c ∧ c ≤ mu a then (1 : ℤ) else 0) := by
      unfold colH
      rw [Finset.card_filter, Finset.card_filter]
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have := h.1 a
      by_cases c1 : c ≤ mu a <;> by_cases c2 : c ≤ nu a
      · rw [ite_eq_left c1, ite_eq_left c2, ite_eq_right (by omega)]; ring
      · rw [ite_eq_left c1, ite_eq_right c2, ite_eq_left (by omega)]; ring
      · omega
      · rw [ite_eq_right c1, ite_eq_right c2, ite_eq_right (by omega)]; ring
    rw [← e]
    split_ifs with hne
    · push_cast; omega
    · push_cast; omega
  have h2 : ((S.filter fun c => colH nu c ≠ colH mu c).card : ℤ) = b := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_comm, ← h.2.2]
    refine Finset.sum_congr rfl fun a _ => ?_
    have e : S.filter (fun c => nu a < c ∧ c ≤ mu a) = Finset.Ioc (nu a) (mu a) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨fun x => x.2, fun x => ⟨hS a c x.1 x.2, x⟩⟩
    have e2 : (∑ c ∈ S, (if nu a < c ∧ c ≤ mu a then (1 : ℤ) else 0)) =
        ((S.filter (fun c => nu a < c ∧ c ≤ mu a)).card : ℤ) := by
      rw [Finset.card_filter]; push_cast; rfl
    rw [e2, e, Int.card_Ioc]
    have := h.1 a
    omega
  exact_mod_cast h2

theorem sum_range_odd {M : Type*} [AddCommMonoid M] (G : ℕ → M) (s : ℕ) :
    ∑ a ∈ Finset.range (2 * s + 1), G a = (∑ l ∈ Finset.range s, (G (2 * l) + G (2 * l + 1))) + G (2 * s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have e : 2 * (s + 1) + 1 = (2 * s + 1) + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have e2 : 2 * (s + 1) = 2 * s + 1 + 1 := by ring
    rw [e2]
    abel

theorem sum_fin_odd {M : Type*} [AddCommMonoid M] (s : ℕ) (F : Fin (2 * s + 1) → M) :
    ∑ a, F a = (∑ l : Fin s, (F ⟨2 * l.val, by have := l.2; omega⟩ + F ⟨2 * l.val + 1, by have := l.2; omega⟩)) +
      F ⟨2 * s, by omega⟩ := by
  classical
  set G : ℕ → M := fun a => if h : a < 2 * s + 1 then F ⟨a, h⟩ else 0 with hG
  have e1 : ∑ a, F a = ∑ a ∈ Finset.range (2 * s + 1), G a := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hG]; simp only [a.2, dite_eq_left]
  rw [e1, sum_range_odd, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    have := l.2
    rw [hG]
    simp only
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
  · rw [hG]; simp only; rw [dite_eq_left (by omega)]

end Formalism.MainNotions.ColumnSystems.Pf.GenusGluing
