module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.HaveILetI
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

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem blockDiagPart_mul {L : Type} [Field L] {n : ℕ} (β : Fin n → ℕ) (A B : Matrix (Fin n) (Fin n) L)
    (hA : A.BlockTriangular β) (hB : B.BlockTriangular β) (hAB : A * B = 1) :
    (Matrix.of fun a b => if β a = β b then A a b else 0) *
      (Matrix.of fun a b => if β a = β b then B a b else 0) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  by_cases h : β i = β j
  · rw [← hAB, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (β l) (β i) with h1 | h1 | h1
    · rw [hA h1]; simp
    · rw [ite_eq_left h1.symm, ite_eq_left (h1.trans h)]
    · rw [hB (h ▸ h1 : β j < β l)]; simp
  · rw [Matrix.one_apply_ne (fun e => h (by rw [e]))]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : β i = β l
    · rw [ite_eq_right (hl ▸ h : ¬ β l = β j), mul_zero]
    · rw [ite_eq_right hl, zero_mul]

theorem leviPart : LeviPart := by
  intro L _ _ σ n β hβ g hg
  have hβ' : ∀ a b, β a = β b ↔ β a.rev = β b.rev := fun a b =>
    ⟨hβ a b, fun h => by simpa using hβ _ _ h⟩
  have h0 : (mat g⁻¹).BlockTriangular β := by
    let : Invertible (mat g) := (g : GL (Fin n) L).invertible
    have e : mat g⁻¹ = (mat g)⁻¹ := by simp [mat]
    rw [e]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg
  have h1 := blockDiagPart_mul β _ _ h0 hg (mat_inv_mul g)
  set M : Matrix (Fin n) (Fin n) L := Matrix.of fun a b => if β a = β b then mat g a b else 0 with hM
  have h2 : antiJ L n * (cT σ M * antiJ L n) =
      Matrix.of fun a b => if β a = β b then mat g⁻¹ a b else 0 := by
    ext a b
    rw [antiJ_mul_apply, P.fSatake_cTJ, Matrix.of_apply, mat_inv_apply, hM, Matrix.of_apply]
    by_cases h : β a = β b
    · rw [ite_eq_left h, ite_eq_left ((hβ' _ _).1 h.symm)]
    · rw [ite_eq_right h, ite_eq_right (fun e => h ((hβ' _ _).2 e).symm), map_zero]
  have h3 : cT σ M * antiJ L n * M = antiJ L n := by
    rw [← h2] at h1
    calc cT σ M * antiJ L n * M
        = antiJ L n * (antiJ L n * (cT σ M * antiJ L n) * M) := by
          rw [← Matrix.mul_assoc (antiJ L n), ← Matrix.mul_assoc (antiJ L n),
            GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.one_mul]
      _ = antiJ L n := by rw [h1, Matrix.mul_one]
  obtain ⟨m, hm⟩ := exists_mat M h3
  have hmL : m ∈ leviU σ β := fun i j h => by rw [hm, hM, Matrix.of_apply, ite_eq_right h]
  refine ⟨m, hmL, fun a b h => by rw [hm, hM, Matrix.of_apply, ite_eq_left h], fun i j h => ?_⟩
  rw [← mat_inv_mul m, mat_mul, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : β i = β l
  · rw [hm, hM, Matrix.of_apply]
    split_ifs with h4
    · rfl
    · rw [hg (lt_of_le_of_ne (hl ▸ h) (Ne.symm h4) : β j < β l)]
  · rw [(leviU σ β).inv_mem hmL i l hl, zero_mul, zero_mul]

end GlobalTheory.SatakeWeyl
