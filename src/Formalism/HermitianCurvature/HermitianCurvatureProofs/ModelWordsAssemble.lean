module

public import Formalism.HermitianCurvature.StatementM
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.FourierDecayAlt.P

open Matrix Finset Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.M

namespace Mx9

theorem eq_ofReal {z : ℂ} (h : z.im = 0) : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h])

theorem star_eq {z : ℂ} (h : z.im = 0) : star z = z := by
  exact Complex.conj_eq_iff_im.mpr h

theorem far {z z' : ℂ} (h : 2 < |z.re - z'.re|) (n : ℤ) (hn : |n| ≤ 2) : z - z' ≠ (n : ℂ) := by
  intro heq
  have h1 := congrArg Complex.re heq
  simp only [Complex.sub_re, Complex.intCast_re] at h1
  rw [h1] at h
  have h2 : ((|n| : ℤ) : ℝ) ≤ 2 := by exact_mod_cast hn
  rw [Int.cast_abs] at h2
  linarith

noncomputable def ty0 (P : Par) : Ty P := fun _ => 0

theorem xC_ne (hR : RealPoints) (P : Par) (π : Ty P) (n : ℕ) (Y : ℝ)
    (h : 0 < (-1 : ℝ) ^ n * I.xpoly P.k (rho P π) Y) : xC P π (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P π Y).1] at h0
  have h1 : I.xpoly P.k (rho P π) Y = 0 := by exact_mod_cast h0
  rw [h1, mul_zero] at h
  exact lt_irrefl _ h

theorem qC_ne (hR : RealPoints) (P : Par) (Y : ℝ)
    (h : 0 < I.qpoly P.k P.T P.T' P.u P.u' Y) : qC P (Y : ℂ) ≠ 0 := by
  intro h0
  rw [(hR P (ty0 P) Y).2] at h0
  have h1 : I.qpoly P.k P.T P.T' P.u P.u' Y = 0 := by exact_mod_cast h0
  rw [h1] at h
  exact lt_irrefl _ h

end Mx9

open Mx9

theorem cut_admissible : Formalism.FourierDecayAlt.M.CutAdm := by
  intro hIS hQP hQS hTy hR P hP l hl1 hlk S _ _ w hw
  obtain ⟨hnd, hpt, hpw⟩ := hw
  have key : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → ∀ e ∈ ({-1, 0, 1} : Finset ℝ),
      ((Y + e : ℝ) : ℂ) ∈ (startM P l).inv := by
    intro Y hY e he
    show ∀ π, xC P π _ ≠ 0
    intro π
    exact xC_ne hR P π (P.k - l) (Y + e) (hIS P.k P.u P.u' (rho P π) l Y hl1 hlk (hTy P hP π) hY e he)
  have qpos : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q (Y : ℂ) ≠ 0 := by
    intro Y hY
    exact qC_ne hR P Y (hQP P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
  have qsh : ∀ (Y : ℝ), I.OnCut P.u P.u' l Y → (startM P l).q ((Y : ℂ) - 1) ≠ 0 := by
    intro Y hY
    have h := qC_ne hR P (Y - 1) (hQS P.k P.u P.u' (rho P (ty0 P)) l Y P.T P.T' hl1 hlk (hTy P hP (ty0 P)) hY
      hP.T_pos hP.T'_pos)
    push_cast at h
    exact h
  refine ⟨hnd, fun a ha => star_eq (hpt a ha).1, fun a ha => ?_, hpw.imp fun h n hn => far h n hn⟩
  obtain ⟨him, hcut⟩ := hpt a ha
  have hz : a.pt = ((a.pt.re : ℝ) : ℂ) := eq_ofReal him
  rw [hz]
  refine ⟨?_, ?_, ?_, qpos _ hcut, qsh _ hcut⟩
  · convert key _ hcut 0 (by norm_num) using 1; push_cast; ring
  · convert key _ hcut 1 (by norm_num) using 1; push_cast; ring
  · convert key _ hcut (-1) (by norm_num) using 1; push_cast; ring

end Formalism.FourierDecayAlt.P
