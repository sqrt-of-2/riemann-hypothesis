module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {T L : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def zcol (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y : WO L T) : n → k :=
  β.b' *ᵥ fun i => p.pr ((y *ᵥ fun j => incA D (ζ j)) i)


open Classical in
def colFun (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (a : (n → k) → ℂ) (y : WO L T) : ℂ :=
  if IsHalf p.e y then a (zcol β ζ y) else 0

def zrow (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (x : WO T L) : n → k :=
  (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)))⁻¹ •
    ((fun i => p.pr (((fun j => incA D ((star ζ ᵥ* L.gram) j)) ᵥ* x) i)) ᵥ* β.b)


open Classical in
def rowFun (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (b : (n → k) → ℂ) (x : WO T L) : ℂ :=
  if IsHalf p.e x then b (zrow β ζ x) else 0

def restrModel {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m'' n'' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (y : Mx D m'' n'') :
    (Mx D m' n' → ℂ) →ₗ[ℂ] (Mx D m' n' → ℂ) where
  toFun Φ := fun w => T' (fun t => Φ (r t).1 * h (r t).2) (r.symm (w, y))
  map_add' Φ Φ' := by
    funext w
    have : (fun t => (Φ + Φ') (r t).1 * h (r t).2) = (fun t => Φ (r t).1 * h (r t).2) + fun t => Φ' (r t).1 * h (r t).2 := by
      funext t; simp [add_mul]
    rw [this, map_add (f := _)]; rfl
  map_smul' c Φ := by
    funext w
    have : (fun t => (c • Φ) (r t).1 * h (r t).2) = c • fun t => Φ (r t).1 * h (r t).2 := by
      funext t; simp [mul_assoc]
    rw [this, map_smul]; rfl

theorem restrModel_apply {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m'' n'' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (y : Mx D m'' n'') (Φ : Mx D m' n' → ℂ) (w : Mx D m' n') :
    restrModel r h T' y Φ w = T' (fun t => Φ (r t).1 * h (r t).2) (r.symm (w, y)) := rfl

theorem heisO_resS_symm (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (a : WO A T)
    (F : WO S T → ℂ) (w : WO A T) (y : WO L T) :
    heisO ψ S T ((o.resS T).symm (a, 0)) F ((o.resS T).symm (w, y)) =
      heisO ψ A T a (fun w' => F ((o.resS T).symm (w', y))) w := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h0 : symplOH L T y 0 = 0 := by simp [symplOH, symplO, hO]
  rw [h0, add_zero, ← map_add (f := _)]
  simp

theorem heisO_resT_symm (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (a : WO T A)
    (F : WO T S → ℂ) (w : WO T A) (y : WO T L) :
    heisO ψ T S ((o.resT T).symm (a, 0)) F ((o.resT T).symm (w, y)) =
      heisO ψ T A a (fun w' => F ((o.resT T).symm (w', y))) w := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h0 : symplOH T L y 0 = 0 := by simp [symplOH, symplO, hO]
  rw [h0, add_zero, ← map_add (f := _)]
  simp

theorem symplO_resS_symm {S A L T : HSp D} (o : OrthDec S A L) (t : WO S T) (a : WO A T) :
    symplO S T t ((o.resS T).symm (a, 0)) = symplO A T ((o.resS T) t).1 a := by
  rw [o.symplO_resS, AddEquiv.apply_symm_apply]
  simp [symplO, hO]

theorem symplO_resT_symm {S A L T : HSp D} (o : OrthDec S A L) (t : WO T S) (a : WO T A) :
    symplO T S t ((o.resT T).symm (a, 0)) = symplO T A ((o.resT T) t).1 a := by
  rw [o.symplO_resT, AddEquiv.apply_symm_apply]
  simp [symplO, hO]

theorem half_resS_symm {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {a : WO A T} (ha : IsHalf e a) :
    IsHalf e ((o.resS T).symm (a, 0)) := by
  intro i j
  rw [OrthDec.resS_symm_apply]
  simp only [Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, ha]

theorem half_resT_symm {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {a : WO T A} (ha : IsHalf e a) :
    IsHalf e ((o.resT T).symm (a, 0)) := by
  intro i j
  rw [OrthDec.resT_symm_apply]
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, ha]

section Lat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [Fintype n']

omit [Fintype n] [Fintype n'] in
theorem latInd_lastKer [Fintype n] [Fintype n'] (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)) :
    latInd (lastKer ΛA) ΛT = tensCol (latInd ΛA ΛT) (vecInd ΛT) := by
  classical
  funext x
  have hmv : ∀ y : n' ⊕ Fin 1 → k, x *ᵥ y = x.submatrix id Sum.inl *ᵥ (y ∘ Sum.inl) +
      y (Sum.inr 0) • fun i => x i (Sum.inr 0) := by
    intro y; funext i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
  have key : (∀ y ∈ lastKer ΛA, x *ᵥ y ∈ ΛT) ↔
      (∀ y ∈ ΛA, x.submatrix id Sum.inl *ᵥ y ∈ ΛT) ∧ (fun i => x i (Sum.inr 0)) ∈ ΛT := by
    constructor
    · intro h
      refine ⟨fun y hy => ?_, ?_⟩
      · have hm : Sum.elim y 0 ∈ lastKer ΛA := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using hy, by simp⟩
        have := h _ hm
        rw [hmv] at this
        simpa using this
      · have hm : (Sum.elim 0 1 : n' ⊕ Fin 1 → k) ∈ lastKer ΛA :=
          GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using ΛA.zero_mem, by simp⟩
        have := h _ hm
        rw [hmv] at this
        simpa using this
    · rintro ⟨h1, h2⟩ y hy
      obtain ⟨hy1, hy2⟩ := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy
      rw [hmv]
      refine ΛT.add_mem (h1 _ hy1) ?_
      have := ΛT.smul_mem (⟨y (Sum.inr 0), hy2⟩ : 𝒪[k]) h2
      exact this
  simp only [latInd, tensCol, vecInd]
  by_cases h : ∀ y ∈ lastKer ΛA, x *ᵥ y ∈ ΛT
  · rw [ite_eq_left h, ite_eq_left (key.1 h).1, ite_eq_left (key.1 h).2, mul_one]
  · rw [ite_eq_right h]
    by_cases h1 : ∀ y ∈ ΛA, x.submatrix id Sum.inl *ᵥ y ∈ ΛT
    · rw [ite_eq_left h1, ite_eq_right fun h2 => h (key.2 ⟨h1, h2⟩), mul_zero]
    · rw [ite_eq_right h1, zero_mul]

omit [Fintype n'] in
theorem latInd_lastKer_row [Fintype n'] (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)) :
    latInd ΛT (lastKer ΛA) = tensRow (latInd ΛT ΛA) (dualInd ΛT) := by
  classical
  funext x
  have key : (∀ y ∈ ΛT, x *ᵥ y ∈ lastKer ΛA) ↔
      (∀ y ∈ ΛT, x.submatrix Sum.inl id *ᵥ y ∈ ΛA) ∧ InDual ΛT (x (Sum.inr 0)) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, InDual]
    exact ⟨fun h => ⟨fun y hy => (h y hy).1, fun y hy => (h y hy).2⟩, fun h y hy => ⟨h.1 y hy, h.2 y hy⟩⟩
  simp only [latInd, tensRow, dualInd]
  by_cases h : ∀ y ∈ ΛT, x *ᵥ y ∈ lastKer ΛA
  · rw [ite_eq_left h, ite_eq_left (key.1 h).1, ite_eq_left (key.1 h).2, mul_one]
  · rw [ite_eq_right h]
    by_cases h1 : ∀ y ∈ ΛT, x.submatrix Sum.inl id *ᵥ y ∈ ΛA
    · rw [ite_eq_left h1, ite_eq_right fun h2 => h (key.2 ⟨h1, h2⟩), mul_zero]
    · rw [ite_eq_right h1, zero_mul]

end Lat

end GlobalTheory.FinPl.ExtZero

end
