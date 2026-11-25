module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchimedeanUnitaryL2

open scoped ENNReal
open GlobalTheory.WeilAdm.HaarSplit

private theorem opensMeasurableSpace_pi_mixedSpace (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := by
  have : SecondCountableTopology (mixedEmbedding.mixedSpace F) := inferInstance
  have : BorelSpace (mixedEmbedding.mixedSpace F) := inferInstance
  infer_instance

theorem exists_haar (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (μ : Measure (κ → mixedEmbedding.mixedSpace F)) [μ.IsAddHaarMeasure]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hg0 : g 0 ≠ 0) :
    ∃ μA : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μA ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μA = c * ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ := by
  classical
  have := opensMeasurableSpace_pi_mixedSpace F κ
  let : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  have : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  have : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  let : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
  have : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  let mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  have : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (κ → FiniteAdeleRing (𝓞 F) F), ν = Measure.addHaar := ⟨_, rfl⟩
  have : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  have : SFinite ν := by rw [hν]; infer_instance
  have : SFinite μ := inferInstance
  have : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := inferInstance
  have : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := inferInstance
  let h : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ₜ (κ → AdeleRing (𝓞 F) F) :=
    { toEquiv := (splitE F κ).toEquiv
      continuous_toFun := continuous_splitE F κ
      continuous_invFun := continuous_splitE_symm F κ }
  let m := h.toMeasurableEquiv
  have hm : (m : _ → _) = splitE F κ := rfl
  have hgc : Continuous g := hg.1.continuous
  refine ⟨(μ.prod ν).map m, ?_, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν, ?_, ?_, ?_⟩
  · rw [hm]
    exact AddEquiv.isAddHaarMeasure_map (μ.prod ν) (splitE F κ) (continuous_splitE F κ) (continuous_splitE_symm F κ)
  · apply ne_of_gt
    have hU : IsOpen {y | g y = g 0} := hg.1.isOpen_fiber _
    have hpos : 0 < ν {y | g y = g 0} := hU.measure_pos ν ⟨0, rfl⟩
    calc (0 : ℝ≥0∞) < ‖g 0‖ₑ ^ 2 * ν {y | g y = g 0} :=
          ENNReal.mul_pos (pow_ne_zero _ (eNorm_ne_zero.2 hg0)) hpos.ne'
      _ = ∫⁻ y, {y | g y = g 0}.indicator (fun _ => ‖g 0‖ₑ ^ 2) y ∂ν :=
          (lintegral_indicator_const hU.measurableSet _).symm
      _ ≤ ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := by
          refine lintegral_mono fun y => ?_
          by_cases hy : g y = g 0
          · simp [Set.indicator, hy]
          · simp [Set.indicator, hy]
  · have hs : HasCompactSupport fun y => ‖g y‖ ^ 2 := hg.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have hint : Integrable (fun y => ‖g y‖ ^ 2) ν := (hgc.norm.pow 2).integrable_of_hasCompactSupport hs
    have h2 := hint.2
    unfold HasFiniteIntegral at h2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h2)
    refine lintegral_congr fun y => ?_
    rw [eNorm_pow, eNorm_norm]
  · intro f
    rw [lintegral_map_equiv, hm]
    have hpt : ∀ p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F),
        ‖GlobalTheory.WeilM.pureA F f g (splitE F κ p)‖ₑ ^ 2 = ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, eNorm_mul, mul_pow]
    simp_rw [hpt]
    rw [mul_comm]
    exact lintegral_prod_mul (μ := μ) (ν := ν) (f := fun z => ‖f z‖ₑ ^ 2) (g := fun y => ‖g y‖ₑ ^ 2)
      (f.continuous.measurable.eNorm.pow_const 2).aemeasurable (hgc.measurable.eNorm.pow_const 2).aemeasurable

theorem integral_sq_eq {V : Type} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V] (μ : Measure V)
    {f : V → ℂ} (hf : Continuous f) : ∫ x, ‖f x‖ ^ 2 ∂μ = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ).toReal := by
  have hc : Continuous fun x => ‖f x‖ ^ 2 := hf.norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x‖ ^ 2)
    (Filter.Eventually.of_forall fun x => by positivity) hc.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

alias opensMeasurable := _root_.GlobalTheory.ArchimedeanUnitaryL2.opensMeasurableSpace_pi_mixedSpace

theorem snd_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have h := hz (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _)
  have h2 : (((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) * ((z i).1, (z i).2)).2 =
      (0 : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 := congrArg Prod.snd (congrFun h i)
  simpa using h2

theorem integral_norm_sq_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W,
    ∀ T : ℝ → SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
    (∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
    ∀ (μ : Measure (Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
    ∀ (t : ℝ) (f : SInf F (Fin a × Fin (a + a'))), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ σ a a' B G X om om' hT γ _ T hAct μ hμ t f
  classical
  have := hμ
  have := opensMeasurable F (Fin a × Fin (a + a'))
  set g : (Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (GlobalTheory.SchANonzero.intPts F (Fin a × Fin (a + a'))).indicator 1 with hgdef
  have hgSB : g ∈ GlobalTheory.WeilM.SB _ := GlobalTheory.SchANonzero.indicator_intPts_mem_SB F _
  have h0mem : (0 : Fin a × Fin (a + a') → FiniteAdeleRing (𝓞 F) F) ∈ GlobalTheory.SchANonzero.intPts F _ := by
    intro i _ v
    exact zero_mem (v.adicCompletionIntegers F)
  have hg0 : g 0 ≠ 0 := by
    rw [hgdef, Set.indicator_of_mem h0mem]
    simp
  obtain ⟨μA, hμA, c, hc0, hctop, hc⟩ := exists_haar F (Fin a × Fin (a + a')) μ g hgSB hg0
  have hU := (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil).unit
  let r : (Fin a × Fin (a + a') → AF F) → ℂ := fun x => g (fun i => (x i).2)
  have htens : ∀ φ : SInf F (Fin a × Fin (a + a')), tens (evI F) (φ : _ → ℂ) r = GlobalTheory.WeilM.pureA F φ g :=
    fun φ => rfl
  have hRest : Rest (evI F) (f : _ → ℂ) r := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · show g _ = g _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero hz i, add_zero]
    · rw [htens]
      exact Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hA := hAct t f r hRest
  rw [htens, htens] at hA
  have hmem : GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) :=
    Submodule.subset_span ⟨f, g, hgSB, rfl⟩
  have hu := hU μA hμA (1, γ (Multiplicative.ofAdd t)) _ hmem
  rw [hA, hc, hc] at hu
  have hl := (ENNReal.mul_right_inj hc0 hctop).1 hu
  rw [integral_sq_eq μ (T t f).continuous, integral_sq_eq μ f.continuous, hl]

end GlobalTheory.ArchimedeanUnitaryL2

end
