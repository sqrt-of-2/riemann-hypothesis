module

public import Formalism.LocalRingCardinality.DataKap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions




private theorem eventually_abs_le_half_add_of_doubling_bounds (x y w : ℚ) (hx : ∃ z : ℤ, x = z) (hy : ∃ z : ℤ, y = z + 1 / 2)
    (hw : ∃ z : ℤ, w = z) (h1 : x < y) (h2 : y < w) : x + 1 ≤ w := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  obtain ⟨c, rfl⟩ := hw
  have h1' : (a : ℚ) < ((b + 1 : ℤ) : ℚ) := by push_cast; linarith
  have h2' : (b : ℚ) < (c : ℚ) := by linarith
  have h1'' : a < b + 1 := by exact_mod_cast h1'
  have h2'' : b < c := by exact_mod_cast h2'
  have h3 : a + 1 ≤ c := by omega
  exact_mod_cast h3

theorem sigPar_step (D : D7) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.sigPar D τ (i + 1) + 1 ≤ DV.sigPar D τ i := by
  unfold DV.sigPar
  by_cases h1 : i + 1 < D.R.k - 1
  · have h0 : i < D.R.k - 1 := by omega
    rw [dite_eq_left h1, dite_eq_left h0]
    exact eventually_abs_le_half_add_of_doubling_bounds ((D.hc τ).v ⟨i + 1, h1⟩) ((D.hc τ).u ⟨i + 1, by omega⟩) ((D.hc τ).v ⟨i, h0⟩)
      ((D.hc τ).v_int ⟨i + 1, h1⟩) ((D.hc τ).u_half ⟨i + 1, by omega⟩) ((D.hc τ).v_int ⟨i, h0⟩)
      ((D.hc τ).u_gt_v ⟨i + 1, h1⟩) ((D.hc τ).v_gt_u ⟨i, h0⟩)
  · by_cases h0 : i < D.R.k - 1
    · have hb : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hk : 0 < D.R.k := by omega
      have hm : 0 < D.R.m := by omega
      rw [dite_eq_right h1, dite_eq_left hb, dite_eq_left h0]
      have e1 : (⟨i + 1 - (D.R.k - 1), hb⟩ : Fin D.R.m) = ⟨0, hm⟩ :=
        Fin.ext (show i + 1 - (D.R.k - 1) = 0 by omega)
      rw [e1]
      have hu2 : (D.hc τ).u ⟨D.R.k - 1, by omega⟩ < (D.hc τ).v ⟨i, h0⟩ := by
        have h5 := (D.hc τ).v_gt_u ⟨i, h0⟩
        have e2 : (⟨D.R.k - 1, by omega⟩ : Fin D.R.k) = ⟨i + 1, by omega⟩ :=
          Fin.ext (show D.R.k - 1 = i + 1 by omega)
        rw [e2]
        exact h5
      obtain ⟨zb, hzb⟩ := (D.hc τ).b_int ⟨0, hm⟩
      exact eventually_abs_le_half_add_of_doubling_bounds (-(D.hc τ).b ⟨0, hm⟩) ((D.hc τ).u ⟨D.R.k - 1, by omega⟩) ((D.hc τ).v ⟨i, h0⟩)
        ⟨-zb, by rw [hzb, Int.cast_neg]⟩ ((D.hc τ).u_half ⟨D.R.k - 1, by omega⟩) ((D.hc τ).v_int ⟨i, h0⟩)
        ((D.hc τ).u_last_gt hk hm) hu2
    · have hb1 : i + 1 - (D.R.k - 1) < D.R.m := by omega
      have hb0 : i - (D.R.k - 1) < D.R.m := by omega
      rw [dite_eq_right h1, dite_eq_left hb1, dite_eq_right h0, dite_eq_left hb0]
      have g1 := (D.hc τ).gap_be ⟨i - (D.R.k - 1), hb0⟩
      have g2 : ((D.R.t : ℚ) + 3) / 2 ≤
          (D.hc τ).b ⟨i - (D.R.k - 1) + 1, by omega⟩ - (D.hc τ).e ⟨i - (D.R.k - 1), hb0⟩ :=
        (D.hc τ).gap_eb ⟨i - (D.R.k - 1), hb0⟩ (show i - (D.R.k - 1) + 1 < D.R.m by omega)
      have e : (⟨i + 1 - (D.R.k - 1), hb1⟩ : Fin D.R.m) = ⟨i - (D.R.k - 1) + 1, by omega⟩ :=
        Fin.ext (show i + 1 - (D.R.k - 1) = i - (D.R.k - 1) + 1 by omega)
      rw [e]
      have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
      linarith

theorem aPlusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ (i + 1) ≤ DV.aPlusQ D j τ i := by
  have h := sigPar_step D τ i hi
  unfold DV.aPlusQ
  push_cast
  linarith

theorem aPlusQ_anti (D : D7) (j : ℕ) (τ : D.what₂.Tau) {a b : ℕ} (hab : a ≤ b) (hb : b < D.R.k - 1 + D.R.m) :
    DV.aPlusQ D j τ b ≤ DV.aPlusQ D j τ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    exact (aPlusQ_step D j τ (a + d) (by omega)).trans (ih (by omega))

theorem aMinusQ_step (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c : ℕ) (hc : j + (c + 1) < D.R.m) :
    DV.aMinusQ D j τ c ≤ DV.aMinusQ D j τ (c + 1) := by
  have h0 : j + c < D.R.m := by omega
  unfold DV.aMinusQ
  rw [dite_eq_left h0, dite_eq_left hc]
  have g1 := (D.hc τ).gap_be ⟨j + c, h0⟩
  have g2 : ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨j + (c + 1), hc⟩ - (D.hc τ).e ⟨j + c, h0⟩ :=
    (D.hc τ).gap_eb ⟨j + c, h0⟩ (show j + c + 1 < D.R.m by omega)
  have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
  push_cast
  linarith

theorem aMinusQ_mono (D : D7) (j : ℕ) (τ : D.what₂.Tau) {a b : ℕ} (hab : a ≤ b) (hb : j + b < D.R.m) :
    DV.aMinusQ D j τ a ≤ DV.aMinusQ D j τ b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  clear hab
  induction d with
  | zero => simp
  | succ d ih =>
    exact (ih (by omega)).trans (aMinusQ_step D j τ (a + d) (by omega))

end Formalism.MainNotions.DIV.Inh

end
