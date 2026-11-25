module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
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

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA.LastEnt

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem eT_zero (τ : D.what₂.Tau) : eT X D pos 0 τ =
    lamAt (X.G.P.lam0 (pos.symm τ).1) (pos.symm τ).2 (Fin.last X.G.P.m) := rfl

theorem eT_succ (l : ℕ) (τ : D.what₂.Tau) : eT X D pos (l + 1) τ =
    lamAt (fun s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 (pos.symm τ).1 s) (fun i => X.Fl.w (pos.symm τ).1 i s) (l + 1))
      (pos.symm τ).2 (Fin.last (X.G.P.m + (l + 1) * (X.Fl.t + 1))) := rfl

theorem lamAt_last0 (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamAt (X.G.P.lam0 v) s (Fin.last X.G.P.m) =
      if IsOddPos s then -(X.G.P.lam0 v s 0) else X.G.P.lam0 v s (Fin.last X.G.P.m) := by
  unfold lamAt
  by_cases h : Even s.val
  · rw [ite_eq_left h, ite_eq_right (fun ho : IsOddPos s => by unfold IsOddPos at ho; rw [Nat.even_iff] at h; omega)]
  · rw [ite_eq_right h, ite_eq_left (show IsOddPos s by unfold IsOddPos; rw [Nat.even_iff] at h; omega), Fin.rev_last]

theorem lamAt_lastS (l : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamAt (fun s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (l + 1)) s
        (Fin.last (X.G.P.m + (l + 1) * (X.Fl.t + 1))) =
      if IsOddPos s then -(X.G.P.lam0 v s 0) else -(X.Fl.w v (l + 1) s) := by
  unfold lamAt
  by_cases h : Even s.val
  · rw [ite_eq_left h, ite_eq_right (fun ho : IsOddPos s => by unfold IsOddPos at ho; rw [Nat.even_iff] at h; omega)]
    unfold liftWt
    beta_reduce
    have h1 : 1 ≤ (l + 1) * (X.Fl.t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    rw [dite_eq_right (by simp only [Fin.val_last]; omega)]
    simp only [Fin.val_last]
    have h2 : X.G.P.m + (l + 1) * (X.Fl.t + 1) - (X.G.P.m + 1) = (l + 1) * (X.Fl.t + 1) - 1 := by omega
    rw [h2, _root_.Formalism.L2.G.Pend.succ_mul_succ_sub_one_div_succ]
  · rw [ite_eq_right h, ite_eq_left (show IsOddPos s by unfold IsOddPos; rw [Nat.even_iff] at h; omega), Fin.rev_last]
    unfold liftWt
    beta_reduce
    rw [dite_eq_left (by simp)]
    rfl

theorem nuv_one (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v (j + 1) s 1 = X.G.P.lam0 v s 0 + X.w v (j + 1) s := by
  unfold Sys.nuv nu
  rw [ite_eq_left ⟨le_refl 1, by omega⟩]
  unfold lamI
  rw [dite_eq_left ⟨le_refl 1, by omega⟩]
  rfl

theorem nuv_one_at_firstLevelIndex (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v 1 s (NN X.G.P.m X.t 0) = X.G.P.lam0 v s (Fin.last X.G.P.m) + X.w v 1 s := by
  unfold Sys.nuv nu NN
  rw [ite_eq_left ⟨by omega, by omega⟩]
  unfold lamI
  rw [dite_eq_left ⟨by omega, by omega⟩]
  congr 2
  ext
  simp

theorem nuv_NNS (l : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v (l + 1 + 1) s (NN X.G.P.m X.t (l + 1)) = -X.w v (l + 1) s + X.w v (l + 1 + 1) s := by
  have h1 : 1 ≤ (l + 1) * (X.t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h3 : (l + 1) * (X.t + 1) + (X.t + 1) = (l + 1 + 1) * (X.t + 1) := by ring
  unfold Sys.nuv nu
  rw [ite_eq_right (by unfold NN; omega), ite_eq_left ⟨by unfold NN; omega, by unfold NN; omega⟩]
  have h2 : NN X.G.P.m X.t (l + 1) - (X.G.P.m + 2) = (l + 1) * (X.t + 1) - 1 := by unfold NN; omega
  rw [h2, _root_.Formalism.L2.G.Pend.succ_mul_succ_sub_one_div_succ]

end GlobalTheory.TwV.DelA.LastEnt


open GlobalTheory.TwV.DelA.LastEnt in
theorem GlobalTheory.TwV.DelA.eT_last_pair : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (τ : D.what₂.Tau), (eT X D pos j τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) - wT X D pos j τ) ∧ (eT X D pos (j + 1) τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else -wT X D pos j τ) := by
  intro p _ X D pos j τ
  have hc1 : cT1 X D pos j τ = X.G.P.lam0 (pos.symm τ).1 (pos.symm τ).2 0 + wT X D pos j τ :=
    nuv_one X j (pos.symm τ).1 (pos.symm τ).2
  have hw : wT X D pos j τ = X.w (pos.symm τ).1 (j + 1) (pos.symm τ).2 := rfl
  rw [hc1, eT_succ X D pos j τ, lamAt_lastS X j]
  cases j with
  | zero =>
    rw [eT_zero, lamAt_last0, nuv_one_at_firstLevelIndex, hw]
    constructor <;> split_ifs <;> ring
  | succ l =>
    rw [eT_succ X D pos l τ, lamAt_lastS X l, nuv_NNS, hw]
    constructor <;> split_ifs <;> ring
