module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
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
import Mathlib.RingTheory.TotallySplit
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
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowSplit

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.WeilContF

open Formalism.IndefR.DatumF

theorem continuous_mixed (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  first

  | (apply _root_.PositivityTheory.ThKF0.Split.continuous_toMixed)

theorem continuous_mixed_symm (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  first

  | (apply _root_.PositivityTheory.ThKF0.Split.continuous_ofMixed)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem modTop : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩

theorem finiteFE : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E

theorem topRing : IsTopologicalRing (AEF F E) := by
  have := finiteFE (F := F) (E := E)
  have := modTop (F := F) (E := E)
  exact IsModuleTopology.isTopologicalRing (AF F) (AEF F E)

def sigLin (σ : E →ₐ[F] E) : AEF F E →ₗ[AF F] AEF F E :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : AF F →ₗ[AF F] AF F) σ.toLinearMap

theorem continuous_cAF (σ : E →ₐ[F] E) : Continuous (cAF σ) := by
  have := finiteFE (F := F) (E := E)
  haveI := modTop (F := F) (E := E)
  haveI := topRing (F := F) (E := E)
  have h := IsModuleTopology.continuous_of_linearMap (sigLin σ)
  have e : (sigLin σ : AEF F E → AEF F E) = cAF σ := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show (TensorProduct.AlgebraTensorModule.map (LinearMap.id : AF F →ₗ[AF F] AF F) σ.toLinearMap)
        (a ⊗ₜ[F] b) = Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ (a ⊗ₜ[F] b)
      rw [TensorProduct.AlgebraTensorModule.map_tmul, Algebra.TensorProduct.map_tmul]
      rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [e] at h
  exact h

theorem continuous_symplOHF (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ : E) {X : Type} [TopologicalSpace X] {x y : X → WOF F E nS nT}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun t => symplOHF σ JS JT ξ (x t) (y t) := by
  haveI := finiteFE (F := F) (E := E)
  haveI := modTop (F := F) (E := E)
  haveI := topRing (F := F) (E := E)
  have hy' : ∀ i j, Continuous fun t => cAF σ (y t i j) := fun i j =>
    (continuous_cAF σ).comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hx' : ∀ i j, Continuous fun t => x t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hx)
  have hh : Continuous fun t => hOF σ JS JT (x t) (y t) :=
    continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

def eInf (F : Type) [Field F] [NumberField F] : AF F := pairA F 1 0

theorem finPartF_eInf_smul (z : AEF F E) : finPartF F E (eInf F • z) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have : finPartF F E (algebraMap (AF F) (AEF F E) (eInf F)) = 0 := by
    show (sndA F (eInf F)) ⊗ₜ[F] (1 : E) = 0
    have : sndA F (eInf F) = 0 := rfl
    rw [this, TensorProduct.zero_tmul]
  rw [this, zero_mul]

theorem infPartF_sub_eInf_smul (z : AEF F E) : infPartF F E (z - eInf F • z) = 0 := by
  have e : z - eInf F • z = (1 - eInf F) • z := by rw [sub_smul, one_smul]
  rw [e, Algebra.smul_def, map_mul]
  have : infPartF F E (algebraMap (AF F) (AEF F E) (1 - eInf F)) = 0 := by
    show (fstA F (1 - eInf F)) ⊗ₜ[F] (1 : E) = 0
    have : fstA F (1 - eInf F) = 0 := by
      rw [map_sub, map_one]
      show (1 : Ainf F) - 1 = 0
      exact sub_self _
    rw [this, TensorProduct.zero_tmul]
  rw [this, zero_mul]

end GlobalTheory.WeilContF

end

noncomputable section

namespace GlobalTheory.WeilContF

open Formalism.IndefR.DatumF
open scoped Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] finiteFE modTop topRing


variable (F E) in
def crd : AEF F E ≃ₗ[AF F] (Fin (Module.finrank F E) → AF F) :=
  (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun

theorem continuous_crd : Continuous (crd F E) :=
  IsModuleTopology.continuous_of_linearMap (crd F E).toLinearMap

theorem continuous_crd_symm : Continuous (crd F E).symm :=
  IsModuleTopology.continuous_of_linearMap (crd F E).symm.toLinearMap

theorem eInf_mul_pair (x : Ainf F) : eInf F * pairA F x 0 = pairA F x 0 :=
  Prod.ext (one_mul x) (zero_mul (0 : Af F))

theorem pair_fst_eInf_mul (a : AF F) : pairA F (eInf F * a).1 0 = eInf F * a :=
  Prod.ext rfl (zero_mul a.2).symm


variable (F E) in
def realCh (nS nT : ℕ) : (Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F) →+ WOF F E nS nT where
  toFun t := fun i j => (crd F E).symm fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0
  map_zero' := by
    funext i j
    show (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0) 0) = 0
    rw [map_zero]
    exact (crd F E).symm.map_zero
  map_add' x y := by
    funext i j
    show (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x (i, j, l) + y (i, j, l))) 0) =
      (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x (i, j, l))) 0) +
      (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y (i, j, l))) 0)
    rw [← map_add (f := _)]
    congr 1
    funext l
    rw [map_add (f := _)]
    exact Prod.ext rfl (add_zero (0 : Af F)).symm


variable (F E) in
def realCo (nS nT : ℕ) (y : WOF F E nS nT) : Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F :=
  fun p => InfiniteAdeleRing.ringEquiv_mixedSpace F ((crd F E (y p.1 p.2.1)) p.2.2).1

theorem continuous_realCh (nS nT : ℕ) : Continuous (realCh F E nS nT) := by
  refine continuous_pi fun i => continuous_pi fun j => continuous_crd_symm.comp (continuous_pi fun l => ?_)
  show Continuous fun t : Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l)), (0 : Af F)) : Ainf F × Af F)
  exact ((continuous_mixed_symm F).comp (continuous_apply (i, j, l))).prodMk continuous_const

theorem continuous_realCo (nS nT : ℕ) : Continuous (realCo F E nS nT) := by
  refine continuous_pi fun p => ?_
  exact (continuous_mixed F).comp (continuous_fst.comp ((continuous_apply p.2.2).comp
    (continuous_crd.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))))

theorem realCh_fin (nS nT : ℕ) (t) (i j) : finPartF F E (realCh F E nS nT t i j) = 0 := by
  show finPartF F E ((crd F E).symm fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0) = 0
  have e : (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0) =
      eInf F • fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0 := by
    funext l
    exact (eInf_mul_pair _).symm
  rw [e, LinearEquiv.map_smul]
  exact finPartF_eInf_smul _

theorem realCh_realCo (nS nT : ℕ) (y : WOF F E nS nT) :
    realCh F E nS nT (realCo F E nS nT (eInf F • y)) = eInf F • y := by
  funext i j
  show (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (InfiniteAdeleRing.ringEquiv_mixedSpace F ((crd F E ((eInf F • y) i j)) l).1)) 0) = (eInf F • y) i j
  have e : (eInf F • y) i j = eInf F • y i j := rfl
  rw [e, LinearEquiv.map_smul]
  conv_rhs => rw [← (crd F E).symm_apply_apply (eInf F • y i j), LinearEquiv.map_smul]
  congr 1
  funext l
  rw [RingEquiv.symm_apply_apply]
  exact pair_fst_eInf_mul _

end GlobalTheory.WeilContF
