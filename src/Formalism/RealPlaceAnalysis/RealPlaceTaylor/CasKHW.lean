module

public import Formalism.RealPlaceAnalysis.StatementA
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Finset

noncomputable section

namespace Formalism.REAL

lemma casKHW_two_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    2 * rhoC ε a = ∑ b, ((if a < b ∧ ε b = ε a then (1:ℝ) else 0) -
      (if b < a ∧ ε b = ε a then (1:ℝ) else 0)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
  unfold rhoC; ring

def casKHW_coef {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) (a b : Fin n) : ℝ :=
  if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0) else 0

lemma casKHW_term (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ) (w : V)
    (hG : GlRel E) (hK : KHighest ε E μ w) (a b : Fin n) :
    (if ε a = ε b then E a b * E b a else 0) w = ((casKHW_coef ε μ a b : ℝ) : ℂ) • w := by
  unfold casKHW_coef
  by_cases h : ε a = ε b
  · simp only [h, ite_true]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have hne : a ≠ b := ne_of_lt hab
      simp only [hne, ite_false, hab, ite_true]
      have h1 := congrArg (fun T : Module.End ℂ V => T w) (hG a b b a)
      simp only [ite_true, LinearMap.sub_apply, mul_apply_eq_comp] at h1
      have h0 : E a b w = 0 := hK.2 a b hab h
      rw [h0, map_zero, sub_zero, hK.1 a, hK.1 b] at h1
      rw [mul_apply_eq_comp, h1]
      push_cast
      rw [sub_smul]
    · simp only [ite_true, mul_apply_eq_comp, hK.1 a, map_smul, smul_smul]
      push_cast; ring_nf
    · have hne : a ≠ b := ne_of_gt hab
      have hnl : ¬ a < b := not_lt_of_gt hab
      simp only [hne, ite_false, hnl]
      rw [mul_apply_eq_comp, hK.2 b a hab h.symm, map_zero]
      simp
  · simp [h]

lemma casKHW_arith {n : ℕ} (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    ∑ a, ∑ b, casKHW_coef ε μ a b = nsq (μ + rhoC ε) - nsq (rhoC ε) := by
  have hpt : ∀ a b, casKHW_coef ε μ a b =
      (if a = b then μ a ^ 2 else 0) + (if a < b ∧ ε b = ε a then μ a else 0) -
        (if a < b ∧ ε a = ε b then μ b else 0) := by
    intro a b
    unfold casKHW_coef
    by_cases h : ε a = ε b
    · rcases lt_trichotomy a b with hab | rfl | hab
      · simp [h, hab, ne_of_lt hab]
      · simp
      · simp [h, ne_of_gt hab, not_lt_of_gt hab]
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      by_cases hab : a = b
      · exact absurd (congrArg ε hab) h
      · simp [h, h', hab]
  simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have e1 : ∑ a : Fin n, ∑ b : Fin n, (if a = b then μ a ^ 2 else 0) = ∑ a, μ a ^ 2 := by
    simp
  have e2 : ∑ a : Fin n, ∑ b : Fin n, (if a < b ∧ ε a = ε b then μ b else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) := by
    rw [Finset.sum_comm]
  have e3 : ∀ a, ∑ b : Fin n, (if a < b ∧ ε b = ε a then μ a else 0) -
      ∑ b : Fin n, (if b < a ∧ ε b = ε a then μ a else 0) = μ a * (2 * rhoC ε a) := by
    intro a
    rw [casKHW_two_rhoC, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [e1, e2, add_sub_assoc, ← Finset.sum_sub_distrib]
  simp_rw [e3]
  unfold nsq dot
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.add_apply]; ring

theorem compactCasimirOnHighestWeight_holds : CasKHighest := by
  intro V _ _ n ε E μ w hG hK
  unfold CasK
  simp only [LinearMap.sum_apply]
  simp_rw [casKHW_term V n ε E μ w hG hK]
  rw [← casKHW_arith ε μ]
  simp_rw [← Finset.sum_smul]
  push_cast
  rfl

end Formalism.REAL
