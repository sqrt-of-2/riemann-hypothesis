module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.LevAlg

variable {S : Scheme.{0}}

section Hom

variable {G H : Over S} [GrpObj G] [GrpObj H]

alias isMonHom_of_mulComp := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul

alias isMonHom_one := _root_.GlobalTheory.Serre.isMonHom_one

end Hom

section Obj

variable (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

omit [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] in
theorem mkZ_pa [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  unfold mkZ pa
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

omit [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] in
theorem mkZ_pb [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  unfold mkZ pb
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

omit [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] in
theorem zob_ext [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S} (f g : T ⟶ Zob A B) (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance isMonHom_pa (i : Fin 4) : IsMonHom (pa A B i) := by
  unfold pa; infer_instance

instance isMonHom_pb (j : Fin 4) : IsMonHom (pb A B j) := by
  unfold pb; infer_instance

theorem isMonHom_mkZ {T : Over S} [GrpObj T] (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B))
    (hu : ∀ i, IsMonHom (u i)) (hv : ∀ j, IsMonHom (v j)) : IsMonHom (mkZ A B u v) :=
  isMonHom_of_mulComp _ fun T' x y ↦ by
    apply zob_ext
    · intro i
      have := hu i
      simp only [Category.assoc, mkZ_pa, MonObj.mul_comp]
    · intro j
      have := hv j
      simp only [Category.assoc, mkZ_pb, MonObj.mul_comp]

theorem isMonHom_incZ : IsMonHom (incZ A B) := by
  unfold incZ
  apply isMonHom_mkZ
  · intro i
    split_ifs
    · infer_instance
    · exact isMonHom_one
  · intro j
    exact isMonHom_one

theorem isMonHom_actZ (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A) [IsMonHom la] [IsMonHom mu] (N : ord d) :
    IsMonHom (actZ A B d la mu N) := by
  unfold actZ
  apply isMonHom_mkZ
  · intro i
    apply _root_.GlobalTheory.SharpExt.isMonHom_prod
    intro j
    have := _root_.GlobalTheory.Serre.isMonHom_zpow (pa A B j) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inl i))
    have := _root_.GlobalTheory.Serre.isMonHom_zpow (pb A B j ≫ mu)
      ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inl i) / (d : ℤ))
    exact _root_.GlobalTheory.Serre.isMonHom_mul _ _
  · intro i
    apply _root_.GlobalTheory.SharpExt.isMonHom_prod
    intro j
    have := _root_.GlobalTheory.Serre.isMonHom_zpow (pa A B j ≫ la) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inl j) (Sum.inr i))
    have := _root_.GlobalTheory.Serre.isMonHom_zpow (pb A B j) ((N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) (Sum.inr j) (Sum.inr i))
    exact _root_.GlobalTheory.Serre.isMonHom_mul _ _

end Obj

end GlobalTheory.ZarhinFam.LevAlg

namespace GlobalTheory.ZarhinFam.LevAlg

theorem levZ_add_tors : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a b, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (a + b) = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a * (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) ∧ ∀ a, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a ^ M = 1 := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _ κ _
  have : IsMonHom la := hZ.2.2.2.1
  have : IsMonHom mu := hZ.2.2.2.2.1
  have hg : ∀ k, IsMonHom (incZ c.A B ≫ actZ c.A B d la mu (oMat d k)) := fun k => by
    have := isMonHom_incZ c.A B
    have := isMonHom_actZ c.A B d la mu (oMat d k)
    infer_instance
  constructor
  · intro a b
    simp only [levZ, List.prod_ofFn]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have := hg k
    rw [map_add (f := _), c.lev_add, MonObj.mul_comp]
  · intro a
    simp only [levZ, List.prod_ofFn]
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one fun k _ => ?_
    have := hg k
    rw [← MonObj.pow_comp, c.lev_tors]
    simp

end GlobalTheory.ZarhinFam.LevAlg
