module

public import Formalism.FormalDegreeBessel.StatementWR
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped ContDiff

noncomputable section

namespace Formalism.QuantumDeterminants

namespace WRPres

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isOpen_omX (m : ℕ) : IsOpen (OmX m) := by
  unfold OmX
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const

theorem coord_contDiff (l : Fin m) : ContDiff ℝ ∞ (fun x : Fin m → ℂ => x l) := contDiff_apply ℝ (fun _ => ℂ) l

theorem conjCoord_contDiff (l : Fin m) : ContDiff ℝ ∞ (fun x : Fin m → ℂ => star (x l)) := by
  first
  | exact (Complex.conjCLE.contDiff).comp (contDiff_apply ℝ (fun _ => ℂ) l)

theorem fderiv_apply_contDiffOn {f : (Fin m → ℂ) → E} (hf : ContDiffOn ℝ ∞ f (OmX m))
    (v : Fin m → ℂ) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) (OmX m) := by
  exact ((contDiffOn_infty_iff_fderiv_of_isOpen (isOpen_omX m)).1 hf).2.clm_apply contDiffOn_const

theorem wirt_contDiffOn {f : (Fin m → ℂ) → E} (hf : ContDiffOn ℝ ∞ f (OmX m)) (l : Fin m) :
    ContDiffOn ℝ ∞ (wirt l f) (OmX m) := by
  unfold wirt
  exact ((fderiv_apply_contDiffOn hf _).sub ((fderiv_apply_contDiffOn hf _).const_smul _)).const_smul _

theorem wirtBar_contDiffOn {f : (Fin m → ℂ) → E} (hf : ContDiffOn ℝ ∞ f (OmX m)) (l : Fin m) :
    ContDiffOn ℝ ∞ (wirtBar l f) (OmX m) := by
  unfold wirtBar
  first
  | exact ((fderiv_apply_contDiffOn hf _).add ((fderiv_apply_contDiffOn hf _).const_smul _)).const_smul _

theorem differentiableAt_of_mem {f : (Fin m → ℂ) → E} (hf : f ∈ WSm m E) {x : Fin m → ℂ}
    (hx : x ∈ OmX m) : DifferentiableAt ℝ f x := by
  have h1 : ContDiffOn ℝ ∞ f (OmX m) := hf.1
  exact (h1.differentiableOn (by simp)).differentiableAt ((isOpen_omX m).mem_nhds hx)

end WRPres

open WRPres

theorem preserved_operators_holds : PresOps := by
  intro m E _ _ l i f hf
  have hc : ContDiffOn ℝ ∞ f (OmX m) := hf.1
  have hz : ∀ x ∉ OmX m, f x = 0 := hf.2
  have hcoord : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => x l) (OmX m) := (coord_contDiff l).contDiffOn
  have hconj : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => star (x l)) (OmX m) :=
    (conjCoord_contDiff l).contDiffOn
  have hne : ∀ x ∈ OmX m, x l ≠ 0 := fun x hx => hx l
  have hinv : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (x l)⁻¹) (OmX m) := hcoord.inv hne
  have hinvc : ContDiffOn ℝ ∞ (fun x : Fin m → ℂ => (star (x l))⁻¹) (OmX m) :=
    hconj.inv fun x hx => by simpa using hne x hx
  show ContDiffOn ℝ ∞ (opL l i f) (OmX m) ∧ ∀ x ∉ OmX m, opL l i f x = 0
  fin_cases i
  · exact ⟨(hcoord.smul (wirt_contDiffOn hc l)).congr fun x hx => by simp [opL, pOp, hx],
      fun x hx => by simp [opL, pOp, hx]⟩
  · exact ⟨(hcoord.smul hc).congr fun x hx => by simp [opL, cOp],
      fun x hx => by simp [opL, cOp, hz x hx]⟩
  · exact ⟨(hinv.smul hc).congr fun x hx => by simp [opL, ciOp],
      fun x hx => by simp [opL, ciOp, hz x hx]⟩
  · exact ⟨(hconj.smul (wirtBar_contDiffOn hc l)).congr fun x hx => by simp [opL, pbOp, hx],
      fun x hx => by simp [opL, pbOp, hx]⟩
  · exact ⟨(hconj.smul hc).congr fun x hx => by simp [opL, cbOp],
      fun x hx => by simp [opL, cbOp, hz x hx]⟩
  · exact ⟨(hinvc.smul hc).congr fun x hx => by simp [opL, cbiOp],
      fun x hx => by simp [opL, cbiOp, hz x hx]⟩

theorem linear_operators_holds : LinOps := by
  intro m E _ _ l i f g a hf hg
  have hd : ∀ x ∈ OmX m, DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ g x :=
    fun x hx => ⟨differentiableAt_of_mem hf hx, differentiableAt_of_mem hg hx⟩
  fin_cases i <;> refine ⟨funext fun x => ?_, funext fun x => ?_⟩ <;>
    simp only [opL, pOp, cOp, ciOp, pbOp, cbOp, cbiOp, wirt, wirtBar, Pi.add_apply, Pi.smul_apply] <;>
    (try split_ifs with hx) <;>
    (try (have e1 : fderiv ℝ (f + g) x = fderiv ℝ f x + fderiv ℝ g x :=
            fderiv_add (hd x hx).1 (hd x hx).2
          rw [e1])) <;>
    (try (have e2 : fderiv ℝ (a • f) x = a • fderiv ℝ f x := by
            first
            | exact fderiv_const_smul (hd x hx).1 a

          rw [e2])) <;>
    (try simp only [add_apply, smul_apply, smul_zero, add_zero]) <;>
    module

end Formalism.QuantumDeterminants
