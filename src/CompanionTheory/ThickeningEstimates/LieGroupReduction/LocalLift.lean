module

public import CompanionTheory.ThickeningEstimates.LieGroupReduction.NormExpSubLe
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import CompanionTheory.ThickeningEstimates.InnerProductFactorization.EqOfInner

@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform

namespace CompanionTheory.ThKR.LL

variable {l : Type} [Fintype l] [DecidableEq l]

def bl (i j : l → l ⊕ l) : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] (Eu l →L[ℝ] Eu l) where
  toFun g := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (g.submatrix i j)
  map_add' g h := by rw [← map_add (f := _)]; rfl
  map_smul' c g := by rw [RingHom.id_apply, ← map_smul]; rfl

theorem bl_apply (i j : l → l ⊕ l) (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (x : Eu l) (a : l) :
    bl i j g x a = ∑ b, g (i a) (j b) * x b := rfl

theorem pPart_mulVec (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (w : l ⊕ l → ℝ) :
    pPart (g *ᵥ w) = bl Sum.inl Sum.inl g (pPart w) + bl Sum.inl Sum.inr g (qPart w) := by
  ext a
  simp [bl_apply, pPart, qPart, mulVec, dotProduct]

theorem qPart_mulVec (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) (w : l ⊕ l → ℝ) :
    qPart (g *ᵥ w) = bl Sum.inr Sum.inl g (pPart w) + bl Sum.inr Sum.inr g (qPart w) := by
  ext a
  simp [bl_apply, pPart, qPart, mulVec, dotProduct]

theorem det_bl (i j : l → l ⊕ l) (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) : (bl i j g).det = (g.submatrix i j).det :=
  LinearMap.det_toLin (EuclideanSpace.basisFun l ℝ).toBasis _

theorem block_inl_inl_one : bl Sum.inl Sum.inl (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := by
  ext x a
  simp [bl_apply, Matrix.one_apply]

theorem block_inl_inr_one : bl Sum.inl Sum.inr (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 0 := by
  ext x a
  simp [bl_apply]

theorem block_inr_inl_one : bl Sum.inr Sum.inl (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 0 := by
  ext x a
  simp [bl_apply]

theorem hasDerivAt_lin_exp {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Matrix (l ⊕ l) (l ⊕ l) ℝ →ₗ[ℝ] F)
    (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • X))) (L (NormedSpace.exp (t • X) * X)) t := by
  let := Matrix.linftyOpNormedRing (n := l ⊕ l) (α := ℝ)
  let := Matrix.linftyOpNormedAlgebra (n := l ⊕ l) (R := ℝ) (α := ℝ)
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t)

theorem exp_mul_exp_neg (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right, add_neg_cancel, NormedSpace.exp_zero]

theorem intw_of_sympl {g : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hg : ∀ w w', sympl (g *ᵥ w) (g *ᵥ w') = sympl w w')
    (h : IsUnit (bl Sum.inl Sum.inl g)) (c : ℝ) (w : l ⊕ l → ℝ) :
    Intw (big (Ring.inverse (bl Sum.inl Sum.inl g)) (bl Sum.inl Sum.inr g) (bl Sum.inr Sum.inl g) c) (pPart w) (qPart w)
      (pPart (g *ᵥ w)) (qPart (g *ᵥ w)) := by
  have key : ∀ p q p' q' : Eu l, ⟪bl Sum.inl Sum.inl g p + bl Sum.inl Sum.inr g q,
      bl Sum.inr Sum.inl g p' + bl Sum.inr Sum.inr g q'⟫ - ⟪bl Sum.inr Sum.inl g p + bl Sum.inr Sum.inr g q,
      bl Sum.inl Sum.inl g p' + bl Sum.inl Sum.inr g q'⟫ = ⟪p, q'⟫ - ⟪q, p'⟫ := fun p q p' q' => by
    have := hg (Sum.elim (fun i => p i) fun i => q i) (Sum.elim (fun i => p' i) fun i => q' i)
    simp only [sympl, pPart_mulVec, qPart_mulVec] at this
    exact this
  rw [pPart_mulVec, qPart_mulVec]
  refine intw_big h.ringInverse (fun x => ?_) (fun x => ?_) (fun y z => ?_) (fun y z => ?_) (fun y z => ?_) c _ _
  · rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ h, one_apply_eq_self]
  · rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ h, one_apply_eq_self]
  · simpa [sub_eq_zero] using key y 0 z 0
  · simpa [sub_eq_zero] using key 0 y 0 z
  · simpa using key y 0 0 z

theorem fou_mq_fouInv (B : Matrix l l ℝ) (f : Sch l) :
    fou l (mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) B)) (fouInv l f)) =
      (4 * π * I : ℂ)⁻¹ • ∑ j, ∑ k, (B j k : ℂ) • (∂_{(EuclideanSpace.single j 1 : Eu l)}
        (∂_{(EuclideanSpace.single k 1 : Eu l)} f)) := by
  have e : ∀ u : Sch l, fou l (fouInv l u) = u := fun u => by
    rw [← mul_apply_eq_comp, fou_mul_fouInv, one_apply_eq_self]
  rw [← e (_ • _)]
  congr 1
  have h : ∀ j (u : Sch l), fouInv l (dRho (Pi.single (Sum.inl j) 1) u) = -dRho (Pi.single (Sum.inr j) 1) (fouInv l u) :=
    fourierInv_dRho_inl

  simp only [← dRho_single_inl, map_smul, map_sum, h, map_neg, neg_neg]
  ext x
  have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  simp only [mq_apply, smul_apply, sum_apply, dRho_single_inr, smul_eq_mul,
    neg_apply, inner_neg_right, inner_toEuclideanCLM, dotProduct, mulVec, Finset.mul_sum]
  push_cast
  simp only [mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [← Finset.sum_neg_distrib, neg_neg]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp
  ring

theorem quad_eq {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) (f : Sch l) :
    quad X f = mq (bl Sum.inr Sum.inl X) f + vf (-bl Sum.inl Sum.inl X) f +
      fou l (mq (-bl Sum.inl Sum.inr X) (fouInv l f)) - ((X.toBlocks₁₁.trace / 2 : ℝ) : ℂ) • f := by
  ext x
  have h := quad_fromBlocks (A := X.toBlocks₁₁) (B := X.toBlocks₁₂) (C := X.toBlocks₂₁) (D := X.toBlocks₂₂)
    (by rwa [fromBlocks_toBlocks]) f x
  rw [fromBlocks_toBlocks] at h
  have h2 := fou_mq_fouInv X.toBlocks₁₂ f
  have h3 : vf (-bl Sum.inl Sum.inl X) f x =
      -∑ j, ∑ k, (X.toBlocks₁₁ j k : ℂ) * x k * (∂_{(EuclideanSpace.single j 1 : Eu l)} f) x := by
    have : bl Sum.inl Sum.inl X x = ∑ j, ∑ k, (X.toBlocks₁₁ j k * x k) • (EuclideanSpace.single j 1 : Eu l) := by
      ext a
      simp [bl_apply, Pi.single_apply, toBlocks₁₁, Finset.sum_apply]
    rw [vf_apply, neg_apply, this]
    simp [lineDerivOp_apply_eq_fderiv]
  have h4 : mq (bl Sum.inr Sum.inl X) f x = -(π * I * ∑ j, ∑ k, (X.toBlocks₂₁ j k : ℂ) * x j * x k * f x) := by
    have : ⟪x, bl Sum.inr Sum.inl X x⟫ = x ⬝ᵥ X.toBlocks₂₁ *ᵥ x := inner_toEuclideanCLM _ _ _
    rw [mq_apply, this]
    simp only [dotProduct, mulVec]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  simp only [sub_apply, add_apply]
  rw [h, h3, h4]
  erw [h2]
  simp only [smul_apply, sum_apply, smul_eq_mul]
  push_cast
  ring

end CompanionTheory.ThKR.LL

namespace CompanionTheory.ThKR

open LL

end CompanionTheory.ThKR
