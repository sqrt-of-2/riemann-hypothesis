module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.DimF

open Ideal

theorem height_polynomial_of_isMaximal {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsJacobsonRing R] {c : ℕ∞} (hR : ∀ m : Ideal R, m.IsMaximal → m.height = c)
    (M : Ideal (Polynomial R)) (hM : M.IsMaximal) : M.height = c + 1 := by
  have := hM
  have hp : (M.under R).IsMaximal := by
    rw [Ideal.under, Polynomial.algebraMap_eq]
    exact Polynomial.isMaximal_comap_C_of_isJacobsonRing M
  have : M.LiesOver (M.under R) := ⟨rfl⟩
  rw [Polynomial.height_eq_height_add_one (M.under R) M, hR _ hp]

theorem height_mvPolynomial_fin_of_isMaximal {k : Type*} [Field k] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = n
  := by
    intro n
    induction n with
    | zero =>
      intro M hM
      have h := Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
      rw [ringKrullDim_mvPolynomial_of_isEmpty, ringKrullDim_eq_zero_of_field] at h
      rw [Nat.cast_zero]
      exact le_antisymm (WithBot.coe_le_coe.mp h) zero_le
    | succ n ih =>
      intro M hM
      let e := (MvPolynomial.finSuccEquiv k n).toRingEquiv
      have hM' : (M.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
      rw [← e.height_map M, height_polynomial_of_isMaximal ih _ hM']
      simp

theorem height_map_under_eq_zero {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] (M : Ideal B) [M.IsPrime] :
    (M.map (Ideal.Quotient.mk ((M.under R).map (algebraMap R B)))).height = 0 := by
  classical
  have hIM : (M.under R).map (algebraMap R B) ≤ M := Ideal.map_comap_le
  set I := (M.under R).map (algebraMap R B) with hIdef
  have hp : (M.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIM)
  have hMc : (M.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = M := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hIM]
  have h0 : M.map (Ideal.Quotient.mk I) ∈ minimalPrimes (B ⧸ I) := by
    refine ⟨⟨hp, bot_le⟩, ?_⟩
    intro Q hQ hQM
    have hQp : Q.IsPrime := hQ.1
    set Q' := Q.comap (Ideal.Quotient.mk I) with hQ'def
    have hQ'M : Q' ≤ M := by
      rw [← hMc]
      exact Ideal.comap_mono hQM
    have hIQ' : I ≤ Q' := by
      intro x hx
      rw [hQ'def, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact Q.zero_mem
    have hQ'eq : Q' = M := by
      by_contra hne
      have hlt : Q' < M := lt_of_le_of_ne hQ'M hne
      obtain ⟨x, hxM, hxQ⟩ := IsConcreteLE.exists_of_lt hlt
      have hcl := Ideal.under_lt_under_of_integral_mem_sdiff (R := R) hQ'M ⟨hxM, hxQ⟩
        (Algebra.IsIntegral.isIntegral x)
      have hge : M.under R ≤ Q'.comap (algebraMap R B) :=
        (Ideal.le_comap_map).trans (Ideal.comap_mono hIQ')
      exact absurd (lt_of_le_of_lt hge hcl) (lt_irrefl _)
    have hmq : M.map (Ideal.Quotient.mk I) = Q := by
      rw [← hQ'eq, hQ'def, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact hmq.le
  exact Ideal.height_eq_zero_iff.mpr h0

theorem exists_height_of_isMaximal_of_field (k B : Type*) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] :
    ∃ s : ℕ, ∀ M : Ideal B, M.IsMaximal → M.height = s := by
  classical
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  let : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin s) k) B := hfin
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := Algebra.IsIntegral.of_finite _ _
  have : FaithfulSMul (MvPolynomial (Fin s) k) B := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  refine ⟨s, fun M hM => ?_⟩
  have := hM
  have hmax : (M.under (MvPolynomial (Fin s) k)).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
  have : M.LiesOver (M.under (MvPolynomial (Fin s) k)) := ⟨rfl⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (M.under (MvPolynomial (Fin s) k)) M,
    height_mvPolynomial_fin_of_isMaximal s _ hmax, height_map_under_eq_zero M, add_zero]

end ReciprocityTheory.ChartRestriction.G.Geo.DimF
