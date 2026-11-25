module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Formalism.LocalToGlobal.Columns.ChainInst
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

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwist, Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwistStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwist =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwist", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\nimport Formalism.LocalToGlobal.Columns.ChainInst\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) {w : Pr.Word}


open Classical in
theorem cplCoset_frsF_mem {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  split_ifs with h
  · have h1 : p.deco.1.HasLift ⟨P.1, h⟩ := Deco.Ok.hasLift p.deco.2 ⟨P.1, h⟩
    exact (Deco.liftFr_spec h1).1 x
  · exact Subtype.property p ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

theorem cplCoset_sameCoset_of_common {cst : LocCst X (rowSG Pr sel mu)} {n : ℕ} {P : rowSG Pr sel mu} {x y z : Sp X.E n}
    (h : SameCoset sel mu cst P x z) (h' : SameCoset sel mu cst P y z) : SameCoset sel mu cst P x y := fun l => by
  have h1 := (h l).add (ciIntAt_neg (h' l))
  rwa [← mul_neg, ← Pi.neg_apply, ← mul_add, ← Pi.add_apply, neg_sub, sub_add_sub_cancel] at h1

end Gen

end GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem cplCoset_bound : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ)
  (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
  (P.1 ∈ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y l)) ∧
  (P.1 ∉ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y l))) := by
  classical
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hP H hi β P y hy
  obtain ⟨⟨c, rfl⟩, -⟩ := ((St (t.m2 + 1) hi).K β).y_bij.2 (Quotient.mk'' 1)
  obtain ⟨y1, hy1, hY⟩ := H.chain.2.1 c
  have hmem : y1 ∈ A.yb c := by rw [hY]; simp
  have h0 := H.coset c y1 hmem P
  have hy' : SameCoset t.sel (t.tup μ) (t.cst μ) P y (A.y0 ((St _ (cpl_lt t μ).le).chOf c) P) := by
    unfold y0At at hy
    rwa [dite_eq_left rfl] at hy
  have hyw := cplCoset_sameCoset_of_common t.sel (t.tup μ) hy' h0
  set p := A.pt (t.m2 + 1) (cpl_lt t μ).le c with hp
  set w := (frsF t.sel (t.tup μ) p P).symm y1 with hw
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  have hloc := (mem_locLat _ _ _ _).1 hy1 P
  have hw1 : ∀ l, IntAt P.1 ((((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then (-1 : ℤ) else -((t.cst μ).M : ℤ)))⁻¹) * w l) := by
    have h2 : frsF t.sel (t.tup μ) p P ((((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then (-1 : ℤ) else -((t.cst μ).M : ℤ)))⁻¹) • w) ∈ p.deco.1.at P.1 := by
      rw [map_smul, hw, LinearEquiv.apply_symm_apply]
      exact hloc
    have h3 := (ciMem_stdAt _ _).1 ((cplCoset_frsF_mem t.sel (t.tup μ) p P _).1 h2)
    intro l
    simpa using h3 l
  refine ⟨fun hG l => ?_, fun hG l => ?_⟩
  · have h1 := hw1 l
    have h2 := hyw l
    simp only [hG, ite_true, pow_zero, inv_one, one_mul, _root_.zpow_neg, zpow_one, inv_inv, Pi.sub_apply] at h1 h2
    have e : (qOf P.1 : t.X.E) * y l = (qOf P.1 : t.X.E) * (y l - w l) + (qOf P.1 : t.X.E) * w l := by ring
    rw [e]
    exact (ciIntAt_q.mul h2).add h1
  · have h1 := hw1 l
    have h2 := hyw l
    simp only [hG, ite_false, _root_.zpow_neg, zpow_natCast, inv_inv, Pi.sub_apply] at h1 h2
    have hqM : IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M) := by
      have := IntAt.coe P.1 (((qOf P.1 ^ (t.cst μ).M : ℕ)) : 𝓞 t.X.E)
      rwa [map_natCast, Nat.cast_pow] at this
    have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * y l = (qOf P.1 : t.X.E) ^ (t.cst μ).M * (qOf P.1 : t.X.E) ^ (t.cst μ).M *
        (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (y l - w l)) + (qOf P.1 : t.X.E) ^ (t.cst μ).M * w l := by
      field_simp
      ring
    rw [e]
    exact ((hqM.mul hqM).mul h2).add h1

end GlobalTheory.TwV
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwist =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwistStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwistStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwist\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ)
  (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
  (P.1 ∈ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y l)) ∧
  (P.1 ∉ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y l))) := by
  first | exact @GlobalTheory.TwV.cplCoset_bound
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwistStatement =====
