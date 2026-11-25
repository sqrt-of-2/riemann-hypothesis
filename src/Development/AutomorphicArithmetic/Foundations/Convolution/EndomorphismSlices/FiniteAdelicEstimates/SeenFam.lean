module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintTranslate
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical



namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
private theorem heckeFunction_mul (a b : ℕ) (w : Pl E) (x y : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (x.mul y) = PositivityTheory.Rg.BcN.F2.mconv (fn2 a b w x) (fn2 a b w y) := rfl

omit [IsCMField E] in
private theorem heckeFunction_one (a b : ℕ) (w : Pl E) :
    fn2 a b w (.one : Ex (Fin (a + 1) × Fin (b + 1))) = (K2 a b w : Set _).indicator 1 := rfl

private theorem hecke_unit (a b : ℕ) (w : Pl E) :
    IsHecke (K2 a b w) (((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)).indicator (1 : GLw a w × GLw b w → ℂ)) :=
  UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w .one

private theorem mconv_unit (a b : ℕ) (w : Pl E) {f : LF a b w} (hf : IsHecke (K2 a b w) f) :
    PositivityTheory.Rg.BcN.F2.mconv f ((K2 a b w : Set _).indicator 1) = f := by
  have L : Lv a b (∅ : Finset (Pl E)) := ⟨fun w => KGL w (n := a), fun w => KGL w (n := b),
    fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
    fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, fun _ => le_rfl, fun _ => le_rfl,
    fun _ _ => ⟨rfl, rfl⟩⟩
  exact ((locAlg E a b ∅ L w).2.2.2.2 f hf).1

private theorem heckeFunction_one_pow (a b : ℕ) (w : Pl E) (k : ℕ) :
    fn2 a b w ((.one : Ex (Fin (a + 1) × Fin (b + 1))).pow k) = (K2 a b w : Set _).indicator 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show fn2 a b w (((.one : Ex (Fin (a + 1) × Fin (b + 1))).pow k).mul .one) = _
    rw [heckeFunction_mul, ih, heckeFunction_one]
    exact mconv_unit a b w (hecke_unit a b w)

theorem seenFam : SeenFam := by
  intro E _ _ _ a b S Z L hZ φ T e₁ e₂ hφ hT
  have hposition := positionTest E a b S Z L hZ
  have hZw : ∀ w ∈ Z, seen φ L.ln w = φ w := by
    intro w hw
    funext y
    have h := ((locAlg E a b Z L w).2.2.2.1 (φ w) (hφ w hw)).1
    simp only [seen, ite_eq_left (hZ w hw).2]
    exact congrFun h y
  refine ⟨hZw, fun k => ⟨⟨hT.1, fun w hw hs x => ?_⟩, ?_, ?_, ?_⟩⟩
  · rw [Ex.ev_pow, hT.2 w hw hs]
    simp [Ex.ev]
  · funext w
    by_cases hwZ : w ∈ Z
    · have h := hZw w hwZ
      funext y
      have h' := congrFun h y
      simp only [seen, ite_eq_left (hZ w hwZ).2, intersection_update_fsHerm_neg_one, fam, ite_eq_left hwZ] at h' ⊢
      exact h'
    · by_cases hwT : w ∈ T
      · by_cases hs : IsSplitAt w
        · funext y
          simp only [seen, ite_eq_left hs, intersection_update_fsHerm_neg_one, fam, ite_eq_right hwZ, ite_eq_left hwT]
          rfl
        · funext y
          simp only [seen, ite_eq_right hs, intersection_update_fsHerm_neg_one, fam, ite_eq_right hwZ, ite_eq_left hwT]
          rw [heckeFunction_mul, hT.2 w hwT hs, heckeFunction_one_pow, mconv_unit a b w (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w _)]
      · by_cases hs : IsSplitAt w
        · funext y
          simp only [seen, ite_eq_left hs, intersection_update_fsHerm_neg_one, fam, ite_eq_right hwZ, ite_eq_right hwT]
          exact congrFun (mconv_unit a b w (hecke_unit a b w)) y
        · funext y
          simp only [seen, ite_eq_right hs, intersection_update_fsHerm_neg_one, fam, ite_eq_right hwZ, ite_eq_right hwT]
  · have h : fam Z T φ e₁ e₂ k = intersection_update_fsHerm_neg_one Z T φ fun w => ((e₁ w).pow k).mul ((e₂ w).pow k) := by
      funext w
      simp only [fam, intersection_update_fsHerm_neg_one]
    rw [h]
    exact (hposition.2.2 φ hφ).2 T _
  · funext B₁ B₂
    simp only [UpperTheory.V.Z.Tf.GlobalTraceComparison.val, ev2, Ex.ev_pow, ← Finset.prod_pow, mul_pow]

end UpperTheory.Zero.ConvolutionTheory.EB
