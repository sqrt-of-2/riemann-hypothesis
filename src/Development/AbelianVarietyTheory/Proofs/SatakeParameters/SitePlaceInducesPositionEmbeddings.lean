module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosBridge
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosOfPosEmb, Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosOfPosEmb =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosOfPosEmb", "h": "module\n\npublic import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace\nimport Formalism.LocalRingCardinality.RankBoundMonotoneInDimension\npublic import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosBridge\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot\nimport Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel\nimport Formalism.LocalToGlobal.InertKernelTheory.StatementInt\nimport Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms\nimport Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.PlaceAbove

theorem involution_conj (D : D7) (x : D.host.E) : sigD D (D.host.conj x) = x := by
  have h3 : ∀ y : D.host.E, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  rw [h3, ← Formalism.L2.Herm.star_conj, ← Formalism.L2.Herm.star_conj, star_star]

theorem posArg_eq_self (D : D7) {n : ℕ} (s : Fin n) (x : D.host.E) :
    (if Even s.val then (if IsOddPos s then D.host.conj x else x)
      else sigD D (if IsOddPos s then D.host.conj x else x)) = x := by
  by_cases hs : s.val % 2 = 1
  · have hodd : IsOddPos s := hs
    have hne : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
    rw [ite_eq_right hne, ite_eq_left hodd, involution_conj]
  · have hodd : ¬ IsOddPos s := hs
    have hev : Even s.val := by rw [Nat.even_iff]; omega
    rw [ite_eq_left hev, ite_eq_right hodd]

end GlobalTheory.TwU.PlaceAbove


open GlobalTheory.TwU.PlaceAbove in
theorem GlobalTheory.TwU.lamPos_of_posEmb : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (e : D.what₂.LL →+* X.G.Kf), (∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (e z) = lam ⟨D.what₂.embLL z, hz⟩) → (∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : D.host.E), e (tEL D (pos ⟨v, s⟩) (if Even s.val then x else sigD D x)) = X.G.P.ι v ((X.G.P.σ v ^ s.val) (ρ v x))) → LamPos X E pos lam ρ := by
  intro p _ X E D pos lam ρ e hK hpos
  intro v s x
  have h1 := hpos v s (if IsOddPos s then D.host.conj x else x)
  rw [posArg_eq_self D s x] at h1
  have hz := embLL_mem_alg D (tEL D (pos ⟨v, s⟩) x)
  have h2 := hK (tEL D (pos ⟨v, s⟩) x) hz
  have he : Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x = D.what₂.embLL (tEL D (pos ⟨v, s⟩) x) := (tEL_emb D (pos ⟨v, s⟩) x).symm
  have hL : Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = lam ⟨D.what₂.embLL (tEL D (pos ⟨v, s⟩) x), hz⟩ := by
    unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dite_eq_left (he ▸ hz)]
    congr 1
    exact Subtype.ext he
  show Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = _
  rw [hL, ← h2, h1]
  rfl
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosOfPosEmb =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosOfPosEmb\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem pos_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  exact GlobalTheory.TwU.lamPos_of_posEmb (sysS H X std) S.E.toCEmb D _ S.lam _ (ex.cmp.embW u w hg) S.hK (J.Gd.cmp.tie u w hg).pos_emb

end GlobalTheory.TwV
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SitePlaceInducesPositionEmbeddings =====
