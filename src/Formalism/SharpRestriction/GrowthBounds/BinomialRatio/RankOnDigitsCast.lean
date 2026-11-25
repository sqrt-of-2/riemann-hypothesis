module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountDefs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem cast_finsum {α : Sort*} (f : α → ℕ) : ((∑ᶠ a, f a : ℕ) : ℚ) = ∑ᶠ a, (f a : ℚ) :=
  AddMonoidHom.map_finsum_of_injective (Nat.castAddMonoidHom ℚ) Nat.cast_injective f

theorem segTies_J_le {s r : ℕ} (p : ℕ) (S : SegData s) (b : SegBlock s r) (k : Fin (segTies p S b).q) :
    (segTies p S b).J k ≤ 2 * s + 1 := by
  unfold segTies
  dsimp only
  split_ifs with h
  · have := (uTop S ⟨k, h⟩).2
    omega
  · exact le_rfl

theorem blockRank_cast (hB : BlockRankAt) (hY : DimYAt) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Sd : UniformizedDVR p O) {s r : ℕ} [NeZero r] (S : SegData s) (aTop : Fin s → ℕ)
    (aPlus : ℕ) (m : ℝ) (b : SegBlock s r) :
    (blockRank O p r S aTop aPlus m b : ℚ) =
      (let D := blockData p S aTop aPlus m b
       open Classical in
       ∑ᶠ x : (Fin D.T.t → ℕ) × ℕ, if D.LevelOK x.1 x.2 then
        chainSum (r := r) (D.lettersAt x.1 x.2) D.T.J D.T.thr * (sdXi r (D.B - x.2) : ℚ) else 0) := by
  classical
  have h1 := hB O (2 * s + 1) r (blockData p S aTop aPlus m b)
  have h2 : blockRank O p r S aTop aPlus m b =
      Module.finrank (KK O) (Submodule.span (KK O)
        (((blockData p S aTop aPlus m b).SSZ O (r := r) :
            Submodule O (MvPolynomial (BVar (2 * s + 1) r (blockData p S aTop aPlus m b).T.t) (KK O))) :
          Set (MvPolynomial (BVar (2 * s + 1) r (blockData p S aTop aPlus m b).T.t) (KK O)))) := rfl
  rw [h2, h1, cast_finsum]
  dsimp only
  refine finsum_congr fun x => ?_
  by_cases hx : (blockData p S aTop aPlus m b).LevelOK x.1 x.2
  · rw [ite_eq_left hx, ite_eq_left hx]
    push_cast
    congr 1
    exact hY p O Sd (2 * s + 1) r _ _ _ _ (fun k => segTies_J_le p S b k)
  · rw [ite_eq_right hx, ite_eq_right hx]
    simp

theorem rankOnDigits_cast (hB : BlockRankAt) (hY : DimYAt) (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Sd : UniformizedDVR X.p O)
    (j : Fin (numSeg X.TT)) (m : ℝ) (rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ) :
    (rankOnDigits O C0 CE1 CE2 X j m rz ry : ℚ) = chainCount C0 CE1 CE2 X j m rz ry := by
  classical
  unfold rankOnDigits chainCount
  rw [cast_finsum]
  refine finsum_congr fun b => ?_
  by_cases hb : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b ∧ b.rz = rz ∧ b.ry = ry
  · rw [ite_eq_left hb, ite_eq_left hb]
    exact blockRank_cast hB hY X.p O Sd _ _ _ m b
  · rw [ite_eq_right hb, ite_eq_right hb]
    simp

theorem restUp_of (hB : BlockRankAt) (hY : DimYAt) (hC : RestCountUp) : RestUp := by
  refine TransportedAlt.mono ?_ hC
  intro C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc h X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc j m hm rz ry hd
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have : Fact X.p.Prime := ⟨hS.1.prime⟩
  have h1 := h X hD1 hH hc j m hm rz ry hd
  rw [← rankOnDigits_cast hB hY C0 CE1 CE2 X O (dvrOfStd hS) j m rz ry] at h1
  exact_mod_cast h1

theorem restLow_of (hB : BlockRankAt) (hY : DimYAt) (hC : RestCountLow) : RestLow := by
  refine TransportedAlt.mono ?_ hC
  intro C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc h X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc j m hm hm2 rz ry hd
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have : Fact X.p.Prime := ⟨hS.1.prime⟩
  have h1 := h X hD1 hH hc j m hm hm2 rz ry hd
  rw [← rankOnDigits_cast hB hY C0 CE1 CE2 X O (dvrOfStd hS) j m rz ry] at h1
  simpa using h1

end Formalism.MainNotions.ColumnSystems.Pf
