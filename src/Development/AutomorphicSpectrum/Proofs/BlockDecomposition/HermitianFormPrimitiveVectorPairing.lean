module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreePartner

theorem isReduced_tens (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] [IsReduced R] : IsReduced (R ⊗[F] E) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E
  have : Algebra.FormallySmooth F E := inferInstance
  have : Algebra.FinitePresentation F E := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Smooth F E := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth R (R ⊗[F] E) := inferInstance
  exact GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R (R ⊗[F] E)

theorem isUnit_det_JR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (h : J.det ≠ 0) :
    IsUnit (JR (F := F) R J).det := by
  have e : (JR (F := F) R J).det = inclR (F := F) R J.det := by
    rw [RingHom.map_det]
    rfl
  rw [e]
  exact (IsUnit.mk0 _ h).map _

theorem exists_partner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => x) → ∃ y : Fin M → R ⊗[F] E, hR R σ J x y = 1 := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hloc x hx
  obtain ⟨-, -, -, -, hA, hRed, -, -⟩ := hloc
  have := hA
  have := hRed
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  have : IsReduced (R ⊗[F] E) := isReduced_tens F E R
  have hinv : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z :=
    HermTop.sigR_sigR R (HermTop.sigma_sigma hσ)
  have hlip := FreeOpen.lip_of_artinian_reduced (R ⊗[F] E)
  obtain ⟨P, hP⟩ := hlip (Fin M) (Fin 1)
    (Matrix.of fun i (_ : Fin 1) => sigR R σ (x i)) (by
      intro c hc
      have h1 : ∀ i, sigR R σ (x i) * c 0 = 0 := by
        intro i
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct] using this
      have h2 : sigR R σ (c 0) • x = 0 := by
        funext i
        have := congrArg (sigR R σ) (h1 i)
        rw [map_mul, hinv, map_zero] at this
        simpa [mul_comm] using this
      have h3 := Fintype.linearIndependent_iff.mp hx (fun _ => sigR R σ (c 0)) (by simpa using h2) 0
      have h4 : c 0 = 0 := by
        have := congrArg (sigR R σ) h3
        simpa [hinv] using this
      funext j
      rw [Subsingleton.elim j 0]
      simpa using h4)
  have hu := isUnit_det_JR (F := F) R hJ.2
  refine ⟨(JR R J)⁻¹ *ᵥ (fun j => P 0 j), ?_⟩
  have hv : JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) = fun j => P 0 j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h00 := congrFun (congrFun hP 0) 0
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply_eq] at h00
  have hform' : hR R σ J x ((JR R J)⁻¹ *ᵥ (fun j => P 0 j)) =
      ∑ i, sigR R σ (x i) * (JR R J *ᵥ ((JR R J)⁻¹ *ᵥ (fun j => P 0 j))) i := by
    simp only [hR, hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [hform', hv, ← h00]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.CompanionTheory.WeilSiegel.FreePartner
