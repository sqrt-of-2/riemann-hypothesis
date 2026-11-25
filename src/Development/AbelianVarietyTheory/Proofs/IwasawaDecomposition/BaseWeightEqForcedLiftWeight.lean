module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Formalism.LocalToGlobal.Columns.BaseLemmas
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2



noncomputable section

open Formalism.L2.Col

namespace GlobalTheory.Mem.LiftWt

theorem lamLdef_eq_lamV (X : Stages) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ X.B.R.m) (τ) (i : Fin (X.toD7.sp.V j).rank)
    (i' : Fin X.B.R.nV) (e : (i : ℕ) = i') :
    (Bridge.lamLdef (D := X.toD7) (X.toD7.sp.V j).rank j τ).w i = (X.B.wts.lamV j τ).w i' := by
  obtain ⟨hj, W, hk, hm, ht, hjj, he, hv, hb, hw⟩ := GlobalTheory.ForcedWeights.lamLForced X.toD7 j h1 h2 τ
  have hk : W.k = X.B.R.k := hk
  have hm : W.m = X.B.R.m := hm
  have ht : W.t = X.B.R.t := ht
  have he : (W.e : ℚ) = (X.B.hc τ).e ⟨j - 1, hj.2⟩ := he
  have hv : ∀ a : Fin (X.B.R.k - 1), (W.v (a + 2) : ℚ) = (X.B.hc τ).v a := hv
  have hb : ∀ a : Fin X.B.R.m, (W.b (a + 1) : ℚ) = (X.B.hc τ).b a := hb
  have hkm := X.B.R.m_add_three_le_k
  have q := RowPar.lamV_eq (X.B.hc τ) h1 h2 i'
  have hi := i'.2
  have hE : (RowPar.of (X.B.hc τ)).eAt (j - 1) = W.e := by
    rw [he]; exact dite_eq_left hj.2
  have hB : ∀ n, n < X.B.R.m → (RowPar.of (X.B.hc τ)).bAt n = W.b (n + 1) := fun n hn => by
    rw [hb ⟨n, hn⟩]; exact dite_eq_left hn
  have key : W.lamPrime (i'.1 + 1) = (RowPar.of (X.B.hc τ)).lamVQ j i' := by
    unfold Ranks.nV Ranks.r at hi
    unfold IndefiniteWeightData.WeightData.lamPrime IndefiniteWeightData.WeightData.thetaWt IndefiniteWeightData.WeightData.dTau IndefiniteWeightData.WeightData.aPlus IndefiniteWeightData.WeightData.aMinus
      IndefiniteWeightData.WeightData.lam IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r IndefiniteWeightData.WeightData.p IndefiniteWeightData.WeightData.q
      RowPar.lamVQ RowPar.aPlus RowPar.aMinusRev RowPar.dV RowPar.vb RowPar.pOf RowPar.qOf
    rw [hk, hm, ht, hjj, hE]
    congr 1
    by_cases a : i'.1 < X.B.R.k + j - 1
    · rw [ite_eq_left a, ite_eq_left (show i'.1 + 1 ≤ _ from a), Nat.add_sub_cancel]
      by_cases b : i'.1 < X.B.R.k - 1
      · rw [dite_eq_left b, ite_eq_left (show i'.1 + 1 ≤ _ from b), hv ⟨_, b⟩]
        rfl
      · rw [dite_eq_right b, ite_eq_right (show ¬ i'.1 + 1 ≤ _ from b), hB _ (by omega), Int.cast_neg,
          show i'.1 + 1 - (X.B.R.k - 1) = i'.1 - (X.B.R.k - 1) + 1 by omega]
        rfl
    · rw [ite_eq_right a, ite_eq_right (show ¬ i'.1 + 1 ≤ _ from a)]
      by_cases b : i'.1 < X.B.R.k + j - 1 + X.B.R.t
      · rw [ite_eq_left b, ite_eq_left (show i'.1 + 1 ≤ _ from b)]
      · rw [ite_eq_right b, ite_eq_right (show ¬ i'.1 + 1 ≤ _ from b), hB _ (by omega),
          show X.B.R.m - j + 1 - (X.B.R.m - j + 1 - (i'.1 + 1 - (X.B.R.k + j - 1) - X.B.R.t)) =
            i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1 by omega,
          show j + (i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1) - 1 + 1 = j + (i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1) by omega]
  have := (hw i).trans ((e ▸ key).trans q.symm)
  exact_mod_cast this

theorem lamV_eq_lamLdef : ∀ (X : Stages) (i : Fin X.toD7.R.m) (τ : X.B.fields.Tau) (a : Fin X.B.R.nV),
    (X.B.wts.lamV ((i : ℕ) + 1) τ).w a =
      (Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ).w (Fin.cast (LiftBrg.rkEq X i) a) := by
  intro X i τ a
  exact (lamLdef_eq_lamV X ((i : ℕ) + 1) (by omega) i.2 τ _ a rfl).symm

end GlobalTheory.Mem.LiftWt
