module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane

variable {N : ℕ}

theorem minorIJ_image_of_tri {R : Type} [CommRing R] (M : Matrix (Fin N) (Fin N) R) (S : Finset (Fin N))
    (σ : Fin N → Fin N) (hσ : StrictMonoOn σ S)
    (hT : ∀ x ∈ S, ∀ y ∈ S, y < x → M (σ x) y = 0) :
    minorIJ M (S.image σ) S = ∏ c ∈ S, M (σ c) c := by
  have e : (S.image σ).card = S.card := Finset.card_image_of_injOn hσ.injOn
  unfold minorIJ
  rw [dite_eq_left e]
  have hf : (fun i => σ (S.orderEmbOfFin rfl i)) = ⇑((S.image σ).orderEmbOfFin e) := by
    apply Finset.orderEmbOfFin_unique e
    · intro i
      exact Finset.mem_image_of_mem σ (Finset.orderEmbOfFin_mem S rfl i)
    · intro i i' hii
      exact hσ (Finset.orderEmbOfFin_mem S rfl i) (Finset.orderEmbOfFin_mem S rfl i')
        ((S.orderEmbOfFin rfl).strictMono hii)
  rw [← hf, Matrix.det_of_isUpperTriangular]
  · simp only [Matrix.submatrix_apply]
    conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]
    rw [Finset.prod_map]
    rfl
  · intro i i' hii
    exact hT _ (Finset.orderEmbOfFin_mem S rfl i) _ (Finset.orderEmbOfFin_mem S rfl i')
      ((S.orderEmbOfFin rfl).strictMono hii)

theorem mul_entry (B : Matrix (Fin N) (Fin N) ℂ) (ca cb x y : Fin N) (s : ℂ) :
    (B * (1 + Matrix.single cb ca s)) x y = B x y + if y = ca then s * B x cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hy : y = ca
  · subst hy
    simp [Matrix.mul_single_apply_same, mul_comm]
  · simp [Matrix.mul_single_apply_of_ne, hy]

theorem one_entry (ca cb x y : Fin N) (s : ℂ) :
    (1 + Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) x y =
      (if x = y then 1 else 0) + if cb = x ∧ ca = y then s else 0 := by
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem param_core (S : Finset (Fin N)) (ca cb : Fin N) (hca : ca ∈ S) (hmax : ∀ c ∈ S, c ≤ ca) (hlt : ca < cb)
    (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.BlockTriangular id) (t t' μ : ℂ)
    (H : ∀ J, minorIJ (B * (1 + Matrix.single cb ca t')) J S = μ * minorIJ (1 + Matrix.single cb ca t) J S) :
    μ = (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb) ∧
      μ * t = (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb) := by
  have hne : ∀ c ∈ S, c ≠ cb := fun c hc => ne_of_lt ((hmax c hc).trans_lt hlt)
  have hcaNe : ca ≠ cb := ne_of_lt hlt
  let σ : Fin N → Fin N := fun c => if c = ca then cb else c
  have hσca : σ ca = cb := ite_eq_left rfl
  have hσne : ∀ c, c ≠ ca → σ c = c := fun c hc => ite_eq_right hc
  have hσ : StrictMonoOn σ S := by
    intro x _ y hy hxy
    have hx' : x ≠ ca := ne_of_lt (hxy.trans_le (hmax y hy))
    rw [hσne x hx']
    by_cases hy' : y = ca
    · rw [hy', hσca]
      exact (hxy.trans_le (hmax y hy)).trans hlt
    · rw [hσne y hy']
      exact hxy
  have hge : ∀ x ∈ S, x ≤ σ x := by
    intro x hx
    by_cases hx' : x = ca
    · rw [hx', hσca]
      exact hlt.le
    · rw [hσne x hx']
  have hyne : ∀ x ∈ S, ∀ y, y < x → y ≠ ca := fun x hx y hy => ne_of_lt (hy.trans_le (hmax x hx))

  have L1 : minorIJ (B * (1 + Matrix.single cb ca t')) S S =
      (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb) := by
    have h0 := minorIJ_image_of_tri (B * (1 + Matrix.single cb ca t')) S id strictMonoOn_id (by
      intro x hx y _ hy
      rw [mul_entry, ite_eq_right (hyne x hx y hy), add_zero]
      exact hB hy)
    rw [Finset.image_id] at h0
    rw [h0, ← Finset.prod_erase_mul S _ hca]
    congr 1
    · refine Finset.prod_congr rfl fun c hc => ?_
      rw [id, mul_entry, ite_eq_right (Finset.ne_of_mem_erase hc), add_zero]
    · rw [id, mul_entry, ite_eq_left rfl]
  have R1 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
    have h0 := minorIJ_image_of_tri (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S id strictMonoOn_id (by
      intro x hx y _ hy
      rw [id, one_entry, ite_eq_right (ne_of_gt hy), ite_eq_right (fun h => hne x hx h.1.symm), add_zero])
    rw [Finset.image_id] at h0
    rw [h0]
    refine Finset.prod_eq_one fun c hc => ?_
    rw [id, one_entry, ite_eq_left rfl, ite_eq_right (fun h => hne c hc h.1.symm), add_zero]

  have L2 : minorIJ (B * (1 + Matrix.single cb ca t')) (S.image σ) S =
      (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb) := by
    rw [minorIJ_image_of_tri _ S σ hσ (by
      intro x hx y _ hy
      rw [mul_entry, ite_eq_right (hyne x hx y hy), add_zero]
      exact hB (hy.trans_le (hge x hx))), ← Finset.prod_erase_mul S _ hca]
    congr 1
    · refine Finset.prod_congr rfl fun c hc => ?_
      have hc' := Finset.ne_of_mem_erase hc
      rw [hσne c hc', mul_entry, ite_eq_right hc', add_zero]
    · have h0 : B cb ca = 0 := hB hlt
      rw [hσca, mul_entry, ite_eq_left rfl, h0, zero_add]
  have R2 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (S.image σ) S = t := by
    rw [minorIJ_image_of_tri _ S σ hσ (by
      intro x hx y _ hy
      rw [one_entry, ite_eq_right (ne_of_gt (hy.trans_le (hge x hx))),
        ite_eq_right (fun h => hyne x hx y hy h.2.symm), add_zero]), ← Finset.prod_erase_mul S _ hca]
    have h1 : ∏ c ∈ S.erase ca, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (σ c) c = 1 := by
      refine Finset.prod_eq_one fun c hc => ?_
      have hc' := Finset.ne_of_mem_erase hc
      rw [hσne c hc', one_entry, ite_eq_left rfl,
        ite_eq_right (fun h => hne c (Finset.mem_of_mem_erase hc) h.1.symm), add_zero]
    rw [h1, one_mul, hσca, one_entry, ite_eq_right (Ne.symm hcaNe), ite_eq_left ⟨rfl, rfl⟩, zero_add]
  have e1 := H S
  have e2 := H (S.image σ)
  rw [L1, R1, mul_one] at e1
  rw [L2, R2] at e2
  exact ⟨e1.symm, e2.symm⟩

theorem param_relation : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h B : Matrix (Fin N) (Fin N) ℂ) (t t' μ : ℂ), h.det ≠ 0 → IsBlockDiag j B → B.BlockTriangular id → (∀ I, minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) = μ * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a)) → μ = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (B ca ca + t' * B ca cb) ∧ μ * t = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (t' * B cb cb) := by
  intro N j a b ca cb hj hb hab hca hcb h B t t' μ hdet _ hBt hyp
  have hinv : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h (isUnit_iff_ne_zero.2 hdet)
  have hcaS : ca ∈ stepCols N j a := by
    unfold lastCol at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  have hmax : ∀ c ∈ stepCols N j a, c ≤ ca := by
    intro c hc
    unfold lastCol at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Fin.le_def]
    split_ifs at hca hc <;> omega
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  refine param_core _ ca cb hcaS hmax hlt B hBt t t' μ fun J => ?_
  calc minorIJ (B * (1 + Matrix.single cb ca t')) J (stepCols N j a)
      = minorIJ (h⁻¹ * (h * B * (1 + Matrix.single cb ca t'))) J (stepCols N j a) := by
        rw [Matrix.mul_assoc h, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    _ = ∑ I, minorIJ h⁻¹ J I * minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) :=
        minorIJ_mul_sum _ _ _ _
    _ = μ * ∑ I, minorIJ h⁻¹ J I * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [hyp I]
        ring
    _ = μ * minorIJ (h⁻¹ * (h * (1 + Matrix.single cb ca t))) J (stepCols N j a) := by
        rw [minorIJ_mul_sum]
    _ = μ * minorIJ (1 + Matrix.single cb ca t) J (stepCols N j a) := by
        rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane
