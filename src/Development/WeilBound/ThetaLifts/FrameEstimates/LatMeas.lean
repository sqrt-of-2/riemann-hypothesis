module

import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LatticeQuotientMeasure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (F) in
def e0 : AF F := ((0 : Ainf F), (1 : Af F))

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] (z : M) : At (evI F) z ↔ e0 F • z = 0 := by
  constructor
  · intro h
    apply h
    show (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : Ainf F) = 0
    exact map_zero _
  · intro h u hu
    have hu1 : u.1 = 0 := by
      have hu' : (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
      exact (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu'.trans (map_zero _).symm)
    have hue : u = u * e0 F := by
      refine Prod.ext ?_ ?_
      · show u.1 = u.1 * (0 : Ainf F)
        rw [hu1, zero_mul]
      · show u.2 = u.2 * (1 : Af F)
        rw [mul_one]
    rw [hue, mul_smul, h, smul_zero]

variable (F) in
theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  have : T2Space (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
    T2Space.of_injective_continuous DFunLike.coe_injective RestrictedProduct.continuous_coe
  have : T2Space (NumberField.InfiniteAdeleRing F) :=
    show T2Space ((v : InfinitePlace F) → v.Completion) from inferInstance
  show T2Space (NumberField.InfiniteAdeleRing F × IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
  infer_instance

variable (F E) in
theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  have := t2Space_adeleRing_of_numberField F
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  exact T2Space.of_injective_continuous (X := AE F E) b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (A := AE F E) b.equivFun.toLinearMap)

variable (F E) in
theorem ring_AE : IsTopologicalRing (AE F E) := by
  exact IsModuleTopology.isTopologicalRing (AF F) (AE F E)

omit [NumberField E] in
theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  apply PositivityTheory.RL.continuous_piInf

variable {n d : ℕ}

theorem continuous_sz (τ : ∀ w : InfinitePlace F, EmbOver E w) : Continuous (sz τ : Ten F E n d → ℝ) := by
  exact continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_piInf (τ w)).comp (continuous_id.matrix_elem i j)).norm

theorem isClosed_supp {C : Set (Ten F E n d)} (hC : IsCompact C) :
    IsClosed {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} := by
  have := t2Space_cm_host_adeles F E
  have hset : {z : Ten F E n d | ∃ c ∈ C, At (evI F) (z - c)} =
      (fun z : Ten F E n d => e0 F • z) ⁻¹' ((fun c : Ten F E n d => e0 F • c) '' C) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image, at_iff, smul_sub, sub_eq_zero]
    constructor
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
    · rintro ⟨c, hc, hzc⟩
      exact ⟨c, hc, hzc.symm⟩
  rw [hset]
  exact (hC.image (continuous_const_smul (e0 F))).isClosed.preimage (continuous_const_smul (e0 F))

theorem measurable_maj {G : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {C : Set (Ten F E n d)} (hC : IsCompact C) (N : ℕ)
    {f : G → Ten F E n d} (hf : Continuous f) : Measurable fun g => maj τ C N (f g) := by
  have hcl := isClosed_supp (F := F) (E := E) (n := n) (d := d) hC
  delta maj
  refine Measurable.ite (hcl.preimage hf).measurableSet ?_ measurable_const
  exact ((continuous_const.add ((continuous_sz τ).comp hf)).measurable.pow_const N).inv

omit [NumberField E] in
theorem continuous_mat_inv {J : Matrix (Fin n) (Fin n) E} : Continuous fun g : UA σ J => mat g⁻¹ := by
  exact Units.continuous_coe_inv.comp continuous_subtypeVal

end LatticeQuotientMeasure


open LatticeQuotientMeasure in
theorem latMeas : LatMeas := by
  intro F E _ _ _ _ _ σ _ τ n d J J' _ _ C N S hC h
  have := ring_AE F E
  have := t2Space_cm_host_adeles F E
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  have : Countable (Matrix (Fin n) (Fin d) E) := show Countable (Fin n → Fin d → E) from inferInstance
  have : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ J) := ⟨rfl⟩
  delta latSum
  refine Measurable.tsum fun x => ENNReal.measurable_ofReal.comp ?_
  exact measurable_maj τ hC N ((continuous_mat_inv.matrix_mul continuous_const).matrix_mul continuous_const)

end PositivityTheory.ThKEst

end
