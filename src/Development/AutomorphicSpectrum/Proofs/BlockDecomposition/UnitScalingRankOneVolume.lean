module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharMulVecArtinianReduced
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarModulusOfUnitCompletionsAtPlacesEqProdNorm
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem GlobalTheory.CompanionTheory.SW.coordW_image_unit_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (u : (Fv F v ⊗[F] E)ˣ) (S : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)), MeasurableSet S → coordW (Fv F v) b lam 1 M ((fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) '' S) = ((‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ : ℝ≥0∞)) ^ M * coordW (Fv F v) b lam 1 M S := by
  intro F E _ _ _ _ _ σ hσ M d b v lam hlam u S hS
  have hR := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hR
  have := h1
  have := h2
  have := h3
  have := h4
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  have := a1
  have := a2
  have := a3
  have := a4
  have := a8 1 M
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam hlam.1
  have := hW 1 M
  have : (coordW (Fv F v) b lam 1 M).Regular := by
    let K : TopologicalSpace.PositiveCompacts (Fin 1 → Fin M → Fv F v ⊗[F] E) := Classical.choice inferInstance
    exact Measure.regular_of_isAddLeftInvariant K.isCompact K.interior_nonempty K.isCompact.measure_ne_top
  have hchar : distribHaarChar (Fv F v ⊗[F] E) u = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ := by
    have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    let bE := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
    let e : (Fv F v ⊗[F] E) ≃ₜ+ (Fin (Module.finrank F E) → Fv F v) :=
      { bE.equivFun.toAddEquiv with
        continuous_toFun := IsModuleTopology.continuous_of_linearMap bE.equivFun.toLinearMap
        continuous_invFun := IsModuleTopology.continuous_of_linearMap bE.equivFun.symm.toLinearMap }
    borelize (Fv F v ⊗[F] E)
    set A := Algebra.leftMulMatrix bE (u : Fv F v ⊗[F] E)
    have hdet : A.det = Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) := (Algebra.norm_eq_matrix_det bE _).symm
    have hA : IsUnit A.det := hdet ▸ u.isUnit.map (Algebra.norm (Fv F v))
    have hN : Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E) ≠ 0 := (hdet ▸ hA).ne_zero
    rw [GlobalTheory.ModuNorm.distribHaarChar_eq_addEquivAddHaarChar]
    have ht := GlobalTheory.ModuLR.addEquivAddHaarChar_transport e.symm (GlobalTheory.ModuLR.mulVecCE A hA)
    have hext : ((e.symm.symm.trans (GlobalTheory.ModuLR.mulVecCE A hA)).trans e.symm) = GlobalTheory.ModuNorm.mulUnitCE u := by
      ext x
      show bE.equivFun.symm (Matrix.mulVec A (bE.equivFun x)) = (u : Fv F v ⊗[F] E) * x
      rw [show Matrix.mulVec A (bE.equivFun x) = bE.equivFun ((u : Fv F v ⊗[F] E) * x) from Algebra.leftMulMatrix_mulVec_repr bE _ x, LinearEquiv.symm_apply_apply]
    rw [hext] at ht
    rw [ht, GlobalTheory.ModuArtin.addEquivAddHaarChar_mulVecCE _ inferInstance inferInstance, hdet, GlobalTheory.GaugeEx.modu, dite_eq_left (hdet ▸ hA)]
    convert GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v _ hN using 2
    exact Units.ext rfl
  let U1 : (Fin M → Fv F v ⊗[F] E)ˣ := Units.map (Pi.constRingHom (Fin M) (Fv F v ⊗[F] E)).toMonoidHom u
  let U : (Fin 1 → Fin M → Fv F v ⊗[F] E)ˣ :=
    Units.map (Pi.constRingHom (Fin 1) (Fin M → Fv F v ⊗[F] E)).toMonoidHom U1
  have hc1 : distribHaarChar (Fin M → Fv F v ⊗[F] E) U1 = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ M := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin M => Fv F v ⊗[F] E) U1]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin M => Fv F v ⊗[F] E) i).toMonoidHom U1 = u :=
      fun i => Units.ext rfl
    simp only [hU, hchar, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc : distribHaarChar (Fin 1 → Fin M → Fv F v ⊗[F] E) U = ‖Algebra.norm (Fv F v) (u : Fv F v ⊗[F] E)‖₊ ^ M := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : Fin 1 => Fin M → Fv F v ⊗[F] E) U]
    have hU : ∀ i, Units.map (Pi.evalRingHom (fun _ : Fin 1 => Fin M → Fv F v ⊗[F] E) i).toMonoidHom U = U1 :=
      fun i => Units.ext rfl
    simp only [hU, hc1, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  have hm : coordW (Fv F v) b lam 1 M ((fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => U • X) '' S) =
      distribHaarChar (Fin 1 → Fin M → Fv F v ⊗[F] E) U * coordW (Fv F v) b lam 1 M S := by
    open scoped Pointwise in
    exact (distribHaarChar_mul (coordW (Fv F v) b lam 1 M) U S).symm
  have himg : (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) => (u : Fv F v ⊗[F] E) * X p k) =
      fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => U • X := rfl
  rw [himg, hm, hc]
  push_cast
  rfl
