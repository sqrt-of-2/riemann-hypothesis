module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrystallineLogarithm.MemAcris0OfFactorialMul
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

@[expose] public section

noncomputable section
namespace GlobalTheory.RingIface
open Formalism Reformulated.AutPerF
open scoped Formalism.Per

namespace X
end X

variable (l : ℕ) [Fact l.Prime]

theorem phiA_teich (y : Per.Fl l) : Per.φA l (WittVector.teichmuller l y) = WittVector.teichmuller l (y ^ l) := by
  first | exact FrobeniusTeichmuller.Bridge.phiA_teich ..

theorem sigA_teich (g : Per.Gq l) (y : Per.Fl l) :
    Per.σA g (WittVector.teichmuller l y) = WittVector.teichmuller l (Per.σF g y) := by
  first | exact TeichmullerAction.Bridge.sigA_teich ..

theorem sigA_coeff (g : Per.Gq l) (w : Per.Ainf l) (n : ℕ) : (Per.σA g w).coeff n = Per.σF g (w.coeff n) := by
  first | exact SigmaCoeffA.Bridge.sigA_coeff ..

theorem sigO_coe (g : Per.Gq l) (y : Per.OC l) : ((Per.σO g y : Per.OC l) : ℂ_[l]) = Per.σC g (y : ℂ_[l]) := by
  first | exact IntegralActionCoe.Bridge.sigO_coe ..

theorem sigC_cont (g : Per.Gq l) : Continuous (Per.σC g) := by
  first | exact ContinuousGalois.Bridge.sigC_cont ..

theorem tower (x : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) x =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) := by
  first | exact ScalarTowerAlt.Bridge.tower ..

theorem sigD_alg (g : Per.Gq l) (b : Per.BdRp l) : Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) b) =
    algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g b) := by
  first | exact DeRhamSigmaAlgebra.Bridge.sigD_alg ..

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a := by
  first | exact EvaluationAlgebra.Bridge.ev_alg ..

theorem ev_ext (y y' : Per.BdRp l) (h : ∀ n, Per.ev l n y = Per.ev l n y') : y = y' := by
  first | (intros; apply EvaluationExt.Bridge.ev_ext; assumption)

theorem phiA_coeff (w : Per.Ainf l) (n : ℕ) : (Per.φA l w).coeff n = w.coeff n ^ l := by
  first | exact FrobeniusCoeffA.Bridge.phiA_coeff ..

theorem fontaineTheta_algebraMap (a : Per.Ainf l) :
    Per.θP l (algebraMap (Per.Ainf l) (Per.AinfP l) a) = ((Per.θ l a : Per.OC l) : ℂ_[l]) := by
  first | exact ThetaAlgebraMap.Bridge.fontaineTheta_algebraMap ..

theorem alg_mem_kerP {a : Per.Ainf l} (h : Per.θ l a = 0) : algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := by
  first | (intros; apply AlgebraMemThetaKernel.Bridge.alg_mem_kerP; assumption)

theorem ev_surj (n : ℕ) : Function.Surjective (Per.ev l n) := by
  first | (intros; apply EvaluationSurjective.Bridge.ev_surj)

theorem thetaD_alg (a : Per.AinfP l) : Per.θD l (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Per.θP l a := by
  first | exact ThetaDeRhamAlgebra.Bridge.thetaD_alg ..

theorem thetaD_of_mem_FilP {y : Per.BdRp l} (h : y ∈ Per.FilP l 1) : Per.θD l y = 0 := by
  first | (intros; apply ThetaOfFiltration.Bridge.thetaD_of_mem_FilP; assumption)

theorem sigDp_alg (g : Per.Gq l) (a : Per.AinfP l) : Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) a) =
    algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) a) := by
  first | exact DividedPowerAlgebraMap.Bridge.sigDp_alg ..

theorem isUnit_of_generator {a : Per.AinfP l} (h : Per.kerP l = Ideal.span {a}) : IsUnit (Per.pD l a) := by
  first | (intros; apply IsUnitOfGenerator.Bridge.isUnit_of_generator; assumption)

theorem exists_bdRp_equiv : ∃ e : Per.BdRp l ≃+* AdicCompletion (Per.kerP l) (Per.AinfP l),
    (∀ a, e (algebraMap (Per.AinfP l) (Per.BdRp l) a) = algebraMap _ _ a) ∧
      ∀ n y, AdicCompletion.evalₐ (Per.kerP l) n (e y) = Per.ev l n y := by
  first | exact DeRhamPlusEquivExists.Bridge.exists_bdRp_equiv ..

theorem bcris_ext {R : Type} [CommRing R] {f g : Per.Bcris l →+* R}
    (h : ∀ x, f (algebraMap (Per.Acris l) (Per.Bcris l) x) = g (algebraMap (Per.Acris l) (Per.Bcris l) x)) : f = g := by
  first | (intros; apply PeriodRingExt.Bridge.bcris_ext; assumption)

theorem alg_mem_FilD_nat {n : ℕ} {z : Per.BdRp l} (h : z ∈ Per.FilP l n) :
    algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l (n : ℤ) := by
  first | (intros; apply DeRhamFiltrationNat.Bridge.alg_mem_FilD_nat; assumption)

theorem exists_of_mem_FilD_nat {n : ℕ} {x : Per.BdR l} (h : x ∈ Per.FilD l (n : ℤ)) :
    ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  first | (intros; apply FiltrationNatExists.Bridge.exists_of_mem_FilD_nat; assumption)

theorem zB_eq_aB_zA : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zB l z = Formalism.Per.aB l (Formalism.Per.zA l z) := by
  first | exact @GeneratorRelation.Bridge.zB_eq_aB_zA

theorem mem_filtration_iff_mem_kerTheta_pow : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (y : Formalism.Per.BdRp l), y ∈ Formalism.Per.FilP l n ↔ Formalism.Per.ev l n y = 0 := by
  first | exact @DividedPowerFiltrationIff.Bridge.mem_filtration_iff_mem_kerTheta_pow

theorem padicIntMap_eq_algebraMap_comp : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zP l z = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z) := by
  first | exact @GeneratorAlgebraRelation.Bridge.padicIntMap_eq_algebraMap_comp

theorem dividedPower_mem_Acris0 : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Ainf l) (n : ℕ) (y : Formalism.Per.AinfP l), Formalism.Per.θ l x = 0 → ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ Formalism.Per.Acris0 l := by
  first | exact @DividedPowerInCrisZero.Bridge.dividedPower_mem_Acris0

theorem Acris0_le_of_dividedPowers : ∀ (l : ℕ) [Fact l.Prime] (S : Subalgebra (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)), (∀ (x : Formalism.Per.Ainf l) (n : ℕ) (y : Formalism.Per.AinfP l), Formalism.Per.θ l x = 0 → ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ S) → Formalism.Per.Acris0 l ≤ S := by
  first | exact @CrisZeroDividedPowersLe.Bridge.Acris0_le_of_dividedPowers

theorem aB_algebraMap_padicInt : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.aB l (algebraMap ℤ_[l] (Formalism.BasicNotions.Loc.Ainf l) z) = Formalism.Per.zB l z := by
  first | exact @GeneratorRelation.Bridge.zB_eq_aB_zA

theorem zD_eq_alg : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zD l z = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z))) := by
  first | exact @DeRhamGeneratorAlgebra.Bridge.zD_eq_alg

theorem aB_eq_alg : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.Ainf l), Formalism.Per.aB l a = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) := by
  first | exact @PeriodMapApply.Bridge.aB_apply

theorem mem_Acris0_of_factorial_mul : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Ainf l), Formalism.Per.θ l x = 0 → ∀ (n : ℕ) (y : Formalism.Per.AinfP l), ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ Formalism.Per.Acris0 l := by
  first | exact @CrisZeroFactorialMul.Bridge.mem_Acris0_of_factorial_mul

alias aB_apply := _root_.GlobalTheory.RingIface.aB_eq_alg

alias aB_alg := _root_.GlobalTheory.RingIface.aB_eq_alg

theorem pD_eq_alg : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.AinfP l), Formalism.Per.pD l a = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) a) := by
  first | exact @DividedPowerApply.Bridge.pD_apply

theorem alg_mem_FilD_zero : ∀ (l : ℕ) [Fact l.Prime] (y : Formalism.Per.BdRp l), algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) y ∈ Formalism.Per.FilD l 0 := by
  first | exact @DeRhamFiltrationZero.Bridge.alg_mem_FilD_zero

theorem zB_alg : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zB l z = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (Formalism.Per.zA l z)) := by
  first | exact @CrisGeneratorAlgebra.Bridge.zB_alg

theorem acris0_le : ∀ (l : ℕ) [Fact l.Prime] (S : Subalgebra (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)), (∀ x : Formalism.Per.Ainf l, Formalism.Per.θ l x = 0 → ∀ (n : ℕ) (y : Formalism.Per.AinfP l), ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ S) → Formalism.Per.Acris0 l ≤ S := by
  first | exact @CrisZeroLeAlt.Bridge.acris0_le

theorem acris0_le_3 : ∀ (l : ℕ) [Fact l.Prime] (S : Subalgebra (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)), (∀ x : Formalism.Per.Ainf l, Formalism.Per.θ l x = 0 → ∀ (n : ℕ) (y : Formalism.Per.AinfP l), y ∈ Formalism.Per.Acris0 l → ((n.factorial : ℕ) : Formalism.Per.AinfP l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n → y ∈ S) → Formalism.Per.Acris0 l ≤ S := by
  first | exact @CrisZeroLeThird.Bridge.acris0_le_3

theorem ev_sigDp : ∀ (l : ℕ) [Fact l.Prime] (g : Formalism.Per.Gq l) (n : ℕ) (y : Formalism.Per.BdRp l) (a : Formalism.Per.AinfP l), Formalism.Per.ev l n y = Ideal.Quotient.mk _ a → Formalism.Per.ev l n (Formalism.Per.σDp g y) = Ideal.Quotient.mk _ (Formalism.Per.extP (Formalism.Per.σA g) a) := by
  first | exact @EvaluationDividedPower.Bridge.ev_sigDp

end GlobalTheory.RingIface
