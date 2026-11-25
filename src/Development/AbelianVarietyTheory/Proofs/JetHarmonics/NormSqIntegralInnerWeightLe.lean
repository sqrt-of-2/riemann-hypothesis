module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem norm_sq_integral_inner_smul_le (Ω V : Type) [MeasurableSpace Ω] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (ν : Measure Ω) (f g : Ω → V) (ph : Ω → ℂ)
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν)
    (hp : AEStronglyMeasurable ph ν) :
    ENNReal.ofReal (‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ ^ 2) ≤
      (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) *
        ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν := by
  set F : Ω → ℝ≥0∞ := fun x => ‖ph x‖ₑ * ‖f x‖ₑ with hF
  set G : Ω → ℝ≥0∞ := fun x => ‖g x‖ₑ with hG
  have hFm : AEMeasurable F ν := hp.eNorm.mul hf.eNorm
  have hGm : AEMeasurable G ν := hg.eNorm
  have h1 : ‖∫ x, ⟪f x, ph x • g x⟫_ℂ ∂ν‖ₑ ≤ ∫⁻ x, (F * G) x ∂ν := by
    refine (MeasureTheory.eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun x => ?_)
    have h : ‖⟪f x, ph x • g x⟫_ℂ‖ ≤ ‖ph x‖ * ‖f x‖ * ‖g x‖ := by
      refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
      rw [norm_smul]; ring
    have := ENNReal.ofReal_le_ofReal h
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_norm, ofReal_norm, ofReal_norm,
      ofReal_norm] at this
    exact this
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hFm hGm
  have e1 : (∫⁻ x, ENNReal.ofReal (‖ph x‖ ^ 2 * ‖f x‖ ^ 2) ∂ν) = ∫⁻ x, F x ^ (2 : ℝ) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [← mul_pow, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by positivity),
      ofReal_norm, ofReal_norm, ENNReal.rpow_two]
  have e2 : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂ν) = ∫⁻ x, G x ^ (2 : ℝ) ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (by positivity), ofReal_norm, ENNReal.rpow_two]
  rw [e1, e2, ENNReal.ofReal_pow (by positivity), ofReal_norm]
  refine (pow_le_pow_left' (h1.trans h2) 2).trans (le_of_eq ?_)
  have k : ∀ a : ℝ≥0∞, (a ^ (1 / 2 : ℝ)) ^ 2 = a := fun a => by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  rw [mul_pow, k, k]

end GlobalTheory
