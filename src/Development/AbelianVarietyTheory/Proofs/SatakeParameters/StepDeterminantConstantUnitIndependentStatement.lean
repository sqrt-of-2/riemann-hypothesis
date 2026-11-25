module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitNatCastOfCoprimeLocal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpCompanEq
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatricesStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDerivationGeneratorsEqOneAtSiteStatement
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOne, Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOneStatement, Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOne, Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOneStatement, Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnit, Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnitStatement, Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOne, Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOneStatement, Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransform, Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransformStatement, Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOne, Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOneStatement, Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependent, Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependentStatement

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOne =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOne", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\nimport Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe\nimport Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies\nimport Formalism.LocalToGlobal.InertKernelTheory.SubBSplit\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.NormOne

variable {p : ℕ} [Fact p.Prime]

theorem norm_alg_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x))‖ ≤ 1 := by
  rw [(X.G.P.setting v).ι_comp]
  exact E.int _

theorem norm_sigma_alg_le (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := (X.G.P.setting v).frob x
  rw [hy]
  exact norm_alg_le X E v _

theorem norm_unit (X : Sys p) (E : CEmb X.G) (v : X.Pl) (u : (X.G.P.W v)ˣ) :
    ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))‖ = 1 ∧
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))‖ = 1 := by
  have h1 : ((u : X.G.P.W v) * ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := Units.mul_inv u
  have e1 : ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))‖ *
      ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, ← map_mul, h1, map_one, map_one, map_one, norm_one]
  have e2 : ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))‖ *
      ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, h1, map_one, map_one, map_one, map_one, norm_one]
  have a1 := norm_alg_le X E v (u : X.G.P.W v)
  have a2 := norm_alg_le X E v ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have b1 := norm_sigma_alg_le X E v (u : X.G.P.W v)
  have b2 := norm_sigma_alg_le X E v ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have n1 := norm_nonneg (E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v))))
  have n2 := norm_nonneg (E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))))
  have n3 := norm_nonneg (E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) (u : X.G.P.W v)))))
  have n4 := norm_nonneg (E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((u⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)))))
  constructor <;> nlinarith

theorem norm_sigma_alg (X : Sys p) (E : CEmb X.G) (v : X.Pl) (x : X.G.P.W v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x)))‖ =
      ‖E.iK (X.G.P.ι v (algebraMap (X.G.P.W v) (X.G.P.Qq v) x))‖ := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx (X.G.P.setting v).p_unif
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, (norm_unit X E v u).1, (norm_unit X E v u).2]

theorem norm_sigma (X : Sys p) (E : CEmb X.G) (v : X.Pl) (y : X.G.P.Qq v) :
    ‖E.iK (X.G.P.ι v (X.G.P.σ v y))‖ = ‖E.iK (X.G.P.ι v y)‖ := by
  have := (X.G.P.setting v).frac_alt
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := X.G.P.W v) y
  simp only [map_div₀, norm_div, norm_sigma_alg]

theorem norm_twG (X : Sys p) (E : CEmb X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : X.G.P.Qq v) :
    ‖twG X E v s y‖ = ‖E.iK (X.G.P.ι v y)‖ := by
  simp only [twG, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  generalize s.val = n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : ((X.G.P.σ v) ^ (n + 1)) y = X.G.P.σ v (((X.G.P.σ v) ^ n) y) := by rw [pow_succ']; rfl
    rw [e, norm_sigma, ih]

theorem prod_parity {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) (hn : Even n) :
    ∏ s : Fin n, (if s.val % 2 = 1 then b else a) = (a * b) ^ (n / 2) := by
  obtain ⟨m, rfl⟩ := hn
  rw [Fin.prod_univ_eq_prod_range (fun i => if i % 2 = 1 then b else a) (m + m)]
  have : m + m = 2 * m := by ring
  rw [this, Nat.mul_div_cancel_left m (by norm_num)]
  clear this
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih, pow_succ]
    have h1 : (2 * m + 1) % 2 = 1 := by omega
    have h0 : ¬ (2 * m) % 2 = 1 := by omega
    simp only [h1, h0, ite_true, ite_false]
    rw [mul_assoc]

theorem prod_parity_pos {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) (hn : Even n) :
    ∏ s : Fin n, (if IsOddPos s then b else a) = (a * b) ^ (n / 2) := by
  rw [← prod_parity a b n hn]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases h : s.val % 2 = 1
  · rw [ite_eq_left h, ite_eq_left (show IsOddPos s from h)]
  · rw [ite_eq_right h, ite_eq_right (show ¬ IsOddPos s from h)]

end GlobalTheory.TwU.NormOne

namespace GlobalTheory.TwU.NormOne

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  have h : IsIntegral ℚ (TaylorLogMetric.embT D τ x) := (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom
  exact mem_algebraicClosure_iff.2 h.isAlgebraic

end GlobalTheory.TwU.NormOne


open GlobalTheory.TwU.NormOne in
theorem GlobalTheory.TwV.prod_embT_norm_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ z : D.host.E, z * D.host.conj z = 1 → ‖ι (∏ τ, TaylorLogMetric.embT D τ z)‖ = 1) := by
  intro D _ hT _ _ _ _ _ _ u _ w hg _ _ H X _ std _ J S hPos ι hι z hz
  have hl : ∀ τ, ι (TaylorLogMetric.embT D τ z) = TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D τ z) := by
    intro τ
    rw [TaylorLogMetric.lamC, dite_eq_left (embT_mem_qbar D τ z)]
    exact hι ⟨_, embT_mem_qbar D τ z⟩
  rw [map_prod, norm_prod]
  simp only [hl]
  rw [← Fintype.prod_equiv (hT.gat_pos u w hg) (fun σ => ‖TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg σ) z)‖) _ (fun _ => rfl)]
  rw [Fintype.prod_sigma]
  have hP : ∀ v s x, TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x) =
      twG (sysS H X std) S.E.toCEmb v s (J.rho std v (if IsOddPos s then D.host.conj x else x)) := hPos
  refine Finset.prod_eq_one fun v _ => ?_
  have hs : ∀ s : Fin ((sysS H X std).G.P.n' v),
      ‖twG (sysS H X std) S.E.toCEmb v s (J.rho std v (if IsOddPos s then D.host.conj z else z))‖ =
        if IsOddPos s then ‖S.E.toCEmb.iK ((sysS H X std).G.P.ι v (J.rho std v (D.host.conj z)))‖
        else ‖S.E.toCEmb.iK ((sysS H X std).G.P.ι v (J.rho std v z))‖ := by
    intro s
    split_ifs <;> exact norm_twG _ _ _ _ _
  simp only [hP]
  refine (Finset.prod_congr rfl fun s _ => hs s).trans ?_
  rw [prod_parity_pos _ _ _ ((sysS H X std).G.P.setting v).even, ← norm_mul, ← map_mul, ← map_mul, ← map_mul, hz,
    map_one, map_one, map_one, norm_one, one_pow]
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOne =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOneStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOneStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe\nimport Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies\nimport Formalism.LocalToGlobal.InertKernelTheory.SubBSplit\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_prod_cmType_embeddings_norm_one_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ z : D.host.E, z * D.host.conj z = 1 → ‖ι (∏ τ, TaylorLogMetric.embT D τ z)‖ = 1) := by
  first | exact @GlobalTheory.TwV.prod_embT_norm_one
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOneStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOne =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOne", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel\npublic import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe\nimport Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies\nimport Formalism.LocalToGlobal.InertKernelTheory.SubBSplit\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.ScaleUnit

theorem norm_ltC_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ‖ltC S.g S.hLT‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  obtain ⟨-, hAt, -⟩ := S.curve
  obtain ⟨h1, h2, h3, hLam, hOk⟩ := hAt
  have hU : GL3Theta.IsModelU S.g.lam (TaylorLogMetric.lamOf D t.cc t.δ) S.g.C := hLam ▸ hOk.1
  have hu := (GlobalTheory.UnitModel.modelEx_holds D _ S.g.lam t.cc t.δ h1 h2 h3).2.2 S.g.C hU
  unfold ltC
  rw [norm_inv, norm_mul, hu, norm_wToC_unit, mul_one, inv_one]

end GlobalTheory.TwU.ScaleUnit
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOne =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOneStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOneStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe\nimport Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies\nimport Formalism.LocalToGlobal.InertKernelTheory.SubBSplit\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_site_coordinate_scale_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ‖ltC S.g S.hLT‖ = 1) := by
  first | exact @GlobalTheory.TwU.ScaleUnit.norm_ltC_eq_one
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOneStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnit =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnit", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitNatCastOfCoprimeLocal\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpCompanEq\npublic import Formalism.LocalToGlobal.GlobalTheory.BlockActions.FiniteAdeleRingNontrivial\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe\nimport Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies\nimport Formalism.LocalToGlobal.InertKernelTheory.SubBSplit\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.TwV.LatDet

theorem det_isUnit_of_colSpan {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]
    (hinj : Function.Injective (algebraMap W Qq)) {N : ℕ} (M : Matrix (Fin N) (Fin N) Qq)
    (h1 : ∀ i c, M i c ∈ (algebraMap W Qq).range) (h2 : ∀ i, Pi.single i (1 : Qq) ∈ colSpan W M) :
    ∃ y : Wˣ, M.det = algebraMap W Qq y := by
  choose M0' hM0 using h1
  let M0 : Matrix (Fin N) (Fin N) W := fun i c => M0' i c
  have hM : M = M0.map (algebraMap W Qq) := by
    ext i c; rw [Matrix.map_apply]; exact (hM0 i c).symm
  have h2' : ∀ i, ∃ c : Fin N → W, ∑ k, c k • (fun r => M r k) = Pi.single i (1 : Qq) := fun i =>
    (Submodule.mem_span_range_iff_exists_fun W).1 (h2 i)
  choose C hC using h2'
  let C0 : Matrix (Fin N) (Fin N) W := fun k i => C i k
  have hMC : M * C0.map (algebraMap W Qq) = 1 := by
    ext r i
    have := congrFun (hC i) r
    simp only [Finset.sum_apply, Pi.smul_apply] at this
    simp only [Algebra.smul_def] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h3 : ∑ k, M r k * (C0.map (algebraMap W Qq)) k i = ∑ k, algebraMap W Qq (C i k) * M r k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.map_apply, mul_comm]
    rw [h3, this, Pi.single_apply]
  have h4 : (M0 * C0).map (algebraMap W Qq) = (1 : Matrix (Fin N) (Fin N) W).map (algebraMap W Qq) := by
    rw [Matrix.map_mul, ← hM, hMC, Matrix.map_one _ (map_zero _) (map_one _)]
  have h5 : M0 * C0 = 1 := by
    ext i c
    have := congrFun (congrFun h4 i) c
    exact hinj (by simpa using this)
  have h6 : M0.det * C0.det = 1 := by rw [← Matrix.det_mul, h5, Matrix.det_one]
  refine ⟨⟨M0.det, C0.det, h6, by rw [mul_comm, h6]⟩, ?_⟩
  show M.det = algebraMap W Qq M0.det
  rw [hM]
  exact (RingHom.map_det (algebraMap W Qq) M0).symm

theorem rho_int_mem {E W Qq : Type} [Field E] [NumberField E] [CommRing W] [IsDomain W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] [IsIntegrallyClosed W] (ρ : E →+* Qq) (x : 𝓞 E) : ρ x ∈ (algebraMap W Qq).range := by
  have hx : IsIntegral ℤ (x : E) := NumberField.RingOfIntegers.isIntegral_coe x
  have h1 : IsIntegral ℤ (ρ x) := hx.map ρ.toIntAlgHom
  have h2 : IsIntegral W (ρ x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  exact ⟨y, hy⟩

theorem mulVec_mem_locSp_mvL {E W Qq : Type} [Field E] [NumberField E] [StarRing E] [CommRing W] [Field Qq] [Algebra W Qq]
    (ρ : E →+* Qq) {N : ℕ} (g : GL (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) {z : Fin N → Qq}
    (hz : z ∈ locSp W ρ L) : (g.1.map ρ) *ᵥ z ∈ locSp W ρ (mvL g L) := by
  let f : (Fin N → Qq) →ₗ[W] (Fin N → Qq) := ((g.1.map ρ).mulVecLin).restrictScalars W
  have hle : locSp W ρ L ≤ (locSp W ρ (mvL g L)).comap f := by
    unfold locSp
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    change (g.1.map ρ) *ᵥ (fun k => ρ (x k)) ∈ locSp W ρ (mvL g L)
    have h1 : (g.1.map ρ) *ᵥ (fun k => ρ (x k)) = fun k => ρ ((g.1 *ᵥ x) k) := by
      funext k
      exact (RingHom.map_mulVec ρ g.1 x k).symm
    rw [h1]
    refine Submodule.subset_span ⟨g.1 *ᵥ x, ?_, rfl⟩
    exact Submodule.mem_map.2 ⟨x, hx, by simp [toLE_apply]⟩
  exact hle hz

end GlobalTheory.TwV.LatDet

namespace GlobalTheory.TwV.LatDet

theorem locSp_std_int {E W Qq : Type} [Field E] [NumberField E] [CommRing W] [IsDomain W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] [IsIntegrallyClosed W] (ρ : E →+* Qq) {N : ℕ} {z : Fin N → Qq}
    (hz : z ∈ locSp W ρ (Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E)))) (i : Fin N) :
    z i ∈ (algebraMap W Qq).range := by
  let P : Submodule W (Fin N → Qq) := Submodule.pi Set.univ (fun _ => LinearMap.range (Algebra.linearMap W Qq))
  have hle : locSp W ρ (Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E))) ≤ P := by
    unfold locSp
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩ k -
    have hk : x k ∈ (1 : Submodule (𝓞 E) E) := hx k trivial
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 hk
    obtain ⟨w', hw⟩ := rho_int_mem (W := W) ρ y
    refine ⟨w', ?_⟩
    rw [Algebra.linearMap_apply, hw]
    show ρ ↑y = ρ (x k)
    rw [← hy]
  obtain ⟨w', hw⟩ := hle hz i trivial
  exact ⟨w', hw⟩

theorem det_unit_of_base {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [IsFractionRing W Qq] (ρ : E →+* Qq) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (T : ℕ)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hT : IsUnit (T : W))
    (hdual : ∀ z ∈ dualSet (sp.cm.sig : E →+* E) J Lb, (T : E) • z ∈ Lb) (crd B : GL (Fin N) E)
    (hbase : mvL crd (compan (sp := sp) J a Lb) = Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E)))
    (hB : locSp W ρ Lb = colSpan W (B.1.map ρ)) :
    ∃ y : Wˣ, ρ (crd.1.det * B.1.det) = algebraMap W Qq y := by
  have hc := CompSp.locSp_compan_eq sp W Qq ρ J a T Lb hT hdual
  rw [hB] at hc
  let M : Matrix (Fin N) (Fin N) Qq := crd.1.map ρ * B.1.map ρ
  have hdet : ρ (crd.1.det * B.1.det) = M.det := by
    rw [map_mul, RingHom.map_det, RingHom.map_det, Matrix.det_mul]
    rfl
  rw [hdet]
  have hcolM : ∀ c, (crd.1.map ρ) *ᵥ (fun r => (B.1.map ρ) r c) = fun r => M r c := fun c => by
    funext r
    rfl
  apply det_isUnit_of_colSpan (IsFractionRing.injective W Qq) M
  · intro i c
    have hcol : (fun r => (B.1.map ρ) r c) ∈ colSpan W (B.1.map ρ) := Submodule.subset_span ⟨c, rfl⟩
    rw [← hc] at hcol
    have h1 := mulVec_mem_locSp_mvL ρ crd _ hcol
    rw [hbase, hcolM] at h1
    exact locSp_std_int ρ h1 i
  · intro i
    have hei : Pi.single i (1 : E) ∈ Submodule.pi Set.univ (fun _ : Fin N => (1 : Submodule (𝓞 E) E)) := by
      intro k _
      rw [Pi.single_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact zero_mem _
    rw [← hbase] at hei
    obtain ⟨x, hx, hx'⟩ := Submodule.mem_map.1 hei
    have hx2 : crd.1 *ᵥ x = Pi.single i (1 : E) := by
      rw [← hx']
      simp [toLE_apply]
    have hρx : (fun k => ρ (x k)) ∈ colSpan W (B.1.map ρ) := hc ▸ Submodule.subset_span ⟨x, hx, rfl⟩
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun W).1 hρx
    unfold colSpan
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨cc, ?_⟩
    let f : (Fin N → Qq) →ₗ[W] (Fin N → Qq) := ((crd.1.map ρ).mulVecLin).restrictScalars W
    have hf : ∀ c, f (fun r => (B.1.map ρ) r c) = fun r => M r c := hcolM
    have h3 : f (fun k => ρ (x k)) = Pi.single i (1 : Qq) := by
      show (crd.1.map ρ) *ᵥ (fun k => ρ (x k)) = _
      funext r
      have h4 := RingHom.map_mulVec ρ crd.1 x r
      rw [hx2] at h4
      rw [show (fun k => ρ (x k)) = ⇑ρ ∘ x from rfl, ← h4, Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp

    rw [← h3, ← hcc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hf]

end GlobalTheory.TwV.LatDet

namespace GlobalTheory.TwV.LatDet

theorem latAd_one_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb) :
    latAd (1 : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) Lb = Lb := by
  apply le_antisymm
  · rw [latAd, Submodule.span_le]
    intro x hx
    apply Formalism.L2.GlobalTheoryTheory.Br.latLocGlob_main (F := F) Lb hfin x
    simp only [Set.mem_ofPred_eq, inv_one, Units.val_one, Matrix.one_mulVec] at hx
    exact hx
  · intro x hx
    apply Submodule.subset_span
    show _ ∈ {x | _}
    simp only [Set.mem_ofPred_eq, inv_one, Units.val_one, Matrix.one_mulVec]
    exact (Submodule.subset_span ⟨x, hx, rfl⟩ : (fun i => inclE (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb)

theorem crd_mul_det_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v)) → ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v ((J.A.crd j hj).1.det * B.1.det) = algebraMap _ _ (y : (sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj β B v hB
  have hbase := J.base j hj β
  unfold latCo at hbase
  rw [latAd_one_eq _ ((J.St j hj).K β).lev.Lb_fin] at hbase
  have hTe := J.tie.T_eq j hj
  have hdual := ((J.St j hj).K β).lev.Lb_dual
  have hset := ((sysS H X std).G.P.setting v)
  have := hset.frac_alt
  have hcop : Nat.Coprime (D.mem u).A.T (D.what₂.places.resChar w) :=
    (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hg.1).2 hg.2.2.2.2.2)
  have hTu : IsUnit (((D.mem u).A.T : ℕ) : (sysS H X std).G.P.W v) := natCast_isUnit_localRing (sysS H X std) v _ hcop
  rw [← hTe] at hTu
  exact det_unit_of_base D.sp (J.rho std v) (gramN D j hj) J.a (J.St j hj).T _ hTu hdual (J.A.crd j hj) B hbase hB

end GlobalTheory.TwV.LatDet
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnit =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnitStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnitStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnit\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe\nimport Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies\nimport Formalism.LocalToGlobal.InertKernelTheory.SubBSplit\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.det_orthonormalCoords_mul_basis_localUnit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v)) → ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v ((J.A.crd j hj).1.det * B.1.det) = algebraMap _ _ (y : (sysS H X std).G.P.W v)) := by
  first | exact @GlobalTheory.TwV.LatDet.crd_mul_det_unit
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnitStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOne =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOne", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\nimport Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe\nimport Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies\nimport Formalism.LocalToGlobal.InertKernelTheory.SubBSplit\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.UnitPos

theorem norm_twG_le {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmbC X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : X.G.P.W v) :
    ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) y)‖ ≤ 1 := by
  have h := E.compat v s.val y
  have e : twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) y) =
      E.iK (X.G.P.ι v ((X.G.P.σ v ^ s.val) (algebraMap (X.G.P.W v) (X.G.P.Qq v) y))) := rfl
  rw [e, h, Formalism.L2.G.Pend.witt_fraction_to_Cp_algebraMap]
  exact Formalism.L2.G.Pend.norm_wToC_le p _

theorem norm_twG_unit {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmbC X.G) (v : X.Pl) (s : Fin (X.G.P.n' v)) (y : (X.G.P.W v)ˣ) :
    ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v))‖ = 1 := by
  have h1 := norm_twG_le X E v s (y : X.G.P.W v)
  have h2 := norm_twG_le X E v s ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)
  have hm : twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v)) *
      twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have hn := congrArg norm hm
  rw [norm_mul, norm_one] at hn
  have h0 : 0 ≤ ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) (y : X.G.P.W v))‖ := norm_nonneg _
  have h0' : 0 ≤ ‖twG X E.toCEmb v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) ((y⁻¹ : (X.G.P.W v)ˣ) : X.G.P.W v))‖ := norm_nonneg _
  nlinarith

end GlobalTheory.TwV.UnitPos

namespace GlobalTheory.TwV.UnitPos

theorem embT_mem_qbar (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom

end GlobalTheory.TwV.UnitPos


open GlobalTheory.TwV.UnitPos in
theorem GlobalTheory.TwV.UnitPos.norm_embT_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ b : D.host.E, b * D.host.conj b = 1 → (∀ v, ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v b = algebraMap _ _ (y : (sysS H X std).G.P.W v)) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ b)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hS ι hι b hb hloc τ
  obtain ⟨⟨v, s⟩, rfl⟩ := (hT.gat_pos u w hg).surjective τ
  have hq := embT_mem_qbar D ((hT.gat_pos u w hg) ⟨v, s⟩) b
  have e1 : ι (TaylorLogMetric.embT D ((hT.gat_pos u w hg) ⟨v, s⟩) b) = TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D ((hT.gat_pos u w hg) ⟨v, s⟩) b) := by
    rw [TaylorLogMetric.lamC, dite_eq_left hq]
    exact hι ⟨_, hq⟩
  rw [e1, hS v s b]
  obtain ⟨y, hy⟩ := hloc v
  split_ifs with ho
  · have hc : J.rho std v (D.host.conj b) = algebraMap _ _ (((y⁻¹ : ((sysS H X std).G.P.W v)ˣ)) : (sysS H X std).G.P.W v) := by
      have h1 : J.rho std v (D.host.conj b) * J.rho std v b = 1 := by
        rw [← map_mul, mul_comm, hb, map_one]
      have h2 : algebraMap ((sysS H X std).G.P.W v) ((sysS H X std).G.P.Qq v) (((y⁻¹ : ((sysS H X std).G.P.W v)ˣ)) : (sysS H X std).G.P.W v) *
          J.rho std v b = 1 := by
        rw [hy, ← map_mul, Units.inv_mul, map_one]
      have hne : J.rho std v b ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h1; exact zero_ne_one h1
      exact mul_right_cancel₀ hne (h1.trans h2.symm)
    rw [hc]
    exact norm_twG_unit _ S.E v s _
  · rw [hy]
    exact norm_twG_unit _ S.E v s y
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOne =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOneStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOneStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe\nimport Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies\nimport Formalism.LocalToGlobal.InertKernelTheory.SubBSplit\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.norm_cmEmbedding_normOne_localUnit_eq_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ b : D.host.E, b * D.host.conj b = 1 → (∀ v, ∃ y : ((sysS H X std).G.P.W v)ˣ, J.rho std v b = algebraMap _ _ (y : (sysS H X std).G.P.W v)) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ b)‖ = 1) := by
  first | exact @GlobalTheory.TwV.UnitPos.norm_embT_unit
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOneStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransform =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransform", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetOrthonormalCoordsMulBasisLocalUnitStatement\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCmEmbeddingNormOneLocalUnitEqOneStatement\nimport Formalism.LocalRingCardinality.RankBoundMonotoneInDimension\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe\nimport Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies\nimport Formalism.LocalToGlobal.InertKernelTheory.SubBSplit\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.TwV.DelB.UnitB

theorem det_map_transpose {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (M : Matrix (Fin N) (Fin N) E) :
    ((M.map σ)ᵀ).det = σ M.det := by
  rw [Matrix.det_transpose, RingHom.map_det]
  rfl

theorem det_unitary_prod {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (J c B : Matrix (Fin N) (Fin N) E)
    (hc : (c.map σ)ᵀ * c = J) (hB : (B.map σ)ᵀ * J * B = 1) :
    σ (c.det * B.det) * (c.det * B.det) = 1 := by
  have h : ((c * B).map σ)ᵀ * (c * B) = 1 := by
    rw [Matrix.map_mul, Matrix.transpose_mul]
    calc (B.map σ)ᵀ * (c.map σ)ᵀ * (c * B) = (B.map σ)ᵀ * ((c.map σ)ᵀ * c) * B := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc, hB]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, det_map_transpose, Matrix.det_one, Matrix.det_mul] at hd
  exact hd

end GlobalTheory.TwV.DelB.UnitB


open GlobalTheory.TwV.DelB.UnitB in
theorem GlobalTheory.TwV.DelB.detCrdB_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) B.1 * gramN D j hj * B.1 = 1 → (∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v))) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ ((J.A.crd j hj).1.det * B.1.det))‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj β B hB hL τ
  refine GlobalTheory.T.norm_cmEmbedding_normOne_localUnit_eq_one S hPos ι hι _ ?_ (fun v => GlobalTheory.T.det_orthonormalCoords_mul_basis_localUnit S j hj β B v (hL v)) τ
  have hc := J.pins.crd_orth j hj
  have h1 := det_unitary_prod (sigD D : D.host.E →+* D.host.E) (gramN D j hj) (J.A.crd j hj).1 B.1 hc hB
  have hconj : ∀ y : D.host.E, D.host.conj y = (sigD D : D.host.E →+* D.host.E) y := fun y => (bridge_star_holds D.R D.host y).symm
  rw [hconj, mul_comm]
  exact h1
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransform =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransformStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransformStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransform\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe\nimport Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies\nimport Formalism.LocalToGlobal.InertKernelTheory.SubBSplit\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_space_gram_transform : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) B.1 * gramN D j hj * B.1 = 1 → (∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v))) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ ((J.A.crd j hj).1.det * B.1.det))‖ = 1) := by
  first | exact @GlobalTheory.TwV.DelB.detCrdB_unit
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransformStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOne =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOne", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependent\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransformStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem castSt_lb {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (β : S.Ch) (T : GlobalTheory.TwU.StepCharts C' i hi) (hT : T = castSt h S) :
    ∃ β' : T.Ch, (T.K β').lev.Lb = (S.K β).lev.Lb := by
  subst hT
  subst h
  exact ⟨β, rfl⟩

theorem uB_det_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j) τ, ‖ι (embT D τ (uB J j hj a).1.det)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a τ
  have hU := GlobalTheory.T.local_space_gram_transform S hPos ι hι j hj
  have hO := (bAt_orth_lev S j hj a).1
  have e : (uB J j hj a).1.det = (J.A.crd j hj).1.det * (bAt J j hj a).1.det := by
    simp [uB, Matrix.det_mul]
  rw [e]
  cases j with
  | zero =>
    obtain ⟨c⟩ := Formalism.MainNotions.G.KAat.cl_nonempty J.one a
    refine hU ((J.St 0 hj).chOf (J.e0 c)) (bAt J 0 hj a) hO (fun v => ?_) τ
    rw [(J.lev0 _).1]
    exact J.lb0 v
  | succ j =>
    obtain ⟨β, hβ⟩ := castSt_lb (X.onCh j hj) (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st) ((I.at' j hj).st.eC.symm a).1 _ (J.st j hj)
    refine hU β (bAt J (j + 1) hj a) hO (fun v => ?_) τ
    rw [hβ]
    have h1 := J.lbB j hj ((I.at' j hj).st.eC.symm a).1 v
    rw [J.iw j hj _ v] at h1
    exact h1

end GlobalTheory.TwV.DelA
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOne =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOneStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOneStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orthonormalChartBasis_det_norm_one : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j) τ, ‖ι (embT D τ (uB J j hj a).1.det)‖ = 1) := by
  first | exact @GlobalTheory.TwV.DelA.uB_det_unit
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOneStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependent =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependent", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetRationalUnitaryOrthonormalChangeMatricesStatement\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependent\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormDerivationGeneratorsEqOneAtSiteStatement\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmTypeEmbeddingsNormOneEqOneStatement\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSiteCoordinateScaleEqOneStatement\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChartBasisDetNormOneStatement\nimport Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem cKs_unit_indep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j + 1 ≤ D.R.m) (a : Lv.comp j) (a' : Lv.comp (j + 1)), ‖cKs S ι j hj a a'‖ = 1 ∧ ι (kS J j (Nat.le_of_succ_le hj) a * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 ∧ ∀ b b', cKs S ι j hj b b' = cKs S ι j hj a a') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a a'
  have hB := GlobalTheory.T.orthonormalChartBasis_det_norm_one S hPos ι hι
  have hG := GlobalTheory.T.norm_derivation_generators_eq_one_at_site S ι hι
  have hD := GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S
  have hL := GlobalTheory.T.norm_site_coordinate_scale_eq_one S
  have hN := GlobalTheory.T.norm_prod_cmType_embeddings_norm_one_eq_one S hPos ι hι
  have hBas := bAt_orth_lev S
  beta_reduce at hD hL hBas
  have hdPow : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (e : D.what₂.Tau → ℤ),
      (∀ τ, ‖ι (embT D τ M.det)‖ = 1) → ‖ι (dPow M e)‖ = 1 := by
    intro n M e hM
    unfold dPow
    rw [map_prod, norm_prod]
    exact Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hM τ, one_zpow])
  have hdPowC : ∀ (k : ℕ) (hk : k ≤ D.R.m) (c : ℤ), ‖ι (dPow (gMat J k hk 1) (fun _ => c))‖ = 1 := by
    intro k hk c
    unfold dPow
    rw [Finset.prod_zpow, map_zpow₀, norm_zpow]
    rw [show (∏ τ, embT D τ (gMat J k hk 1).det) = ∏ τ, TaylorLogMetric.embT D τ (gMat J k hk 1).det from rfl]
    rw [hN _ (hD k hk).1, one_zpow]
  have hsg : ∀ n, ‖ι (sgRev n)‖ = 1 := by
    intro n
    unfold sgRev
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]
  have hcOp : ‖ι (cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1 := by
    have h1 : ‖ι (sgO (sysS H X std) D (hT.gat_pos u w hg) j)‖ = 1 := by
      unfold sgO
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one (fun τ _ => ?_)
      split_ifs
      · simp [hsg]
      · simp
    have h2 : ‖ι (∏ τ, (t.O u μ).dgen τ ^ (-(szT (sysS H X std) D (hT.gat_pos u w hg) j τ)))‖ = 1 := by
      rw [map_prod, norm_prod]
      exact Finset.prod_eq_one (fun τ _ => by rw [map_zpow₀, norm_zpow, hG τ, one_zpow])
    unfold cOp
    rw [map_mul, norm_mul, h1, h2, one_mul]
  have hkS : ∀ b : Lv.comp j, ‖ι (kS J j (Nat.le_of_succ_le hj) b)‖ = 1 := by
    intro b
    unfold kS
    rw [map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]
  have hkT : ∀ b : Lv.comp (j + 1), ‖ι (kT J j hj b)‖ = 1 := by
    intro b
    unfold kT
    rw [map_mul, norm_mul, hdPow _ _ (hB _ _ b), hdPowC, one_mul]
  have hkSc : ∀ b : Lv.comp j,
      ‖ι (kS J j (Nat.le_of_succ_le hj) b * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)‖ = 1 := by
    intro b
    rw [map_mul, norm_mul, hkS, hcOp, one_mul]
  have hkSeq : ∀ b : Lv.comp j, kS J j (Nat.le_of_succ_le hj) b = kS J j (Nat.le_of_succ_le hj) a := by
    intro b
    simp only [kS, uB, (hBas j (Nat.le_of_succ_le hj) a).2 b]
  have hkTeq : ∀ b : Lv.comp (j + 1), kT J j hj b = kT J j hj a' := by
    intro b
    simp only [kT, uB, (hBas (j + 1) hj a').2 b]
  refine ⟨?_, ?_, ?_⟩
  · unfold cKs
    rw [norm_mul, norm_zpow, hL, one_zpow, mul_one, map_mul, norm_mul, map_inv₀, norm_inv, hkT, hkSc, inv_one, mul_one]
  · intro h
    have h1 := hkSc a
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  · intro b b'
    unfold cKs
    rw [hkSeq b, hkTeq b']

end GlobalTheory.TwV.DelA
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependent =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependentStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependentStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependent\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepDeterminantConstant_unit_independent : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j + 1 ≤ D.R.m) (a : Lv.comp j) (a' : Lv.comp (j + 1)), ‖cKs S ι j hj a a'‖ = 1 ∧ ι (kS J j (Nat.le_of_succ_le hj) a * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 ∧ ∀ b b', cKs S ι j hj b b' = cKs S ι j hj a a') := by
  first | exact @GlobalTheory.TwV.DelA.cKs_unit_indep
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepDeterminantConstantUnitIndependentStatement =====
