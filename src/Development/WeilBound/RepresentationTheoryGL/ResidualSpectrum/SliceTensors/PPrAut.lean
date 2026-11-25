module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGrowthOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspStab

namespace PositivityTheory.Rg.Rs.PrAut

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem isAutForm_act (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (o : Op E N) {φ : Sm E N} (h : IsAutForm φ) :
    IsAutForm (act o φ) := by
  cases o with
  | fin k =>
    refine ⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩
    · change φ.1 (ratGL E N γ * g * finGL E N k) = φ.1 (g * finGL E N k)
      rw [mul_assoc, h.left]
    · have e : {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ} =
          (fun k' => k⁻¹ * k' * k) ⁻¹' {k' | finRep E N k' φ = φ} := by
        ext k'
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, map_mul]
        constructor
        · intro e
          rw [mul_apply_eq_comp, mul_apply_eq_comp, e, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
            map_one, one_apply_eq_self]
        · intro e
          have := congrArg (finRep E N k) e
          rwa [mul_apply_eq_comp, mul_apply_eq_comp, ← mul_apply_eq_comp (finRep E N k), ← map_mul,
            mul_inv_cancel, map_one, one_apply_eq_self] at this
      change IsOpen {k' | finRep E N k' (finRep E N k φ) = finRep E N k φ}
      rw [e]
      exact h.level.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun c => cptRep E N c φ)).map
        (finRep E N k)) (Submodule.span_le.2 ?_)
      rintro _ ⟨c, rfl⟩
      exact ⟨_, Submodule.subset_span ⟨c, rfl⟩, (LinearMap.congr_fun (fin_cpt_comm k c) φ)⟩
    · exact zfin_of_comm _ (fun z hz => zalg_comm_fin k hz) h.zfin
    · obtain ⟨C, M, h1⟩ := h.growth (g * finGL E N k)
      refine ⟨C, M, fun y => ?_⟩
      change ‖φ.1 (g * infGL E N y * finGL E N k)‖ ≤ _
      rw [mul_assoc, infGL_comm, ← mul_assoc]
      exact h1 y
  | cpt c =>
    refine ⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩
    · change φ.1 (ratGL E N γ * g * infGL E N (Unitary.toUnits c)) = φ.1 (g * infGL E N (Unitary.toUnits c))
      rw [mul_assoc, h.left]
    · exact level_of_le h.level fun k hk => by
        change finRep E N k (cptRep E N c φ) = cptRep E N c φ
        rw [← mul_apply_eq_comp, fin_cpt_comm, mul_apply_eq_comp, hk]
    · have := h.kfin
      refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun c => cptRep E N c φ))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨c', rfl⟩
      refine Submodule.subset_span ⟨c' * c, ?_⟩
      change _ = (cptRep E N c' * cptRep E N c) φ
      rw [← map_mul]
    · exact zfin_of_comm _ (fun z hz => GlobalTheory.ZalgCpt.zalg_comm_cptRep E N c z hz) h.zfin
    · obtain ⟨C, M, h1⟩ := growth_mul (Unitary.toUnits c) (h.growth g)
      refine ⟨C, M, fun y => ?_⟩
      change ‖φ.1 (g * infGL E N y * infGL E N (Unitary.toUnits c))‖ ≤ _
      rw [mul_assoc, ← map_mul]
      exact h1 y
  | lie X =>
    refine ⟨fun γ g => ?_, ?_, GlobalTheory.CuspRep.KFin.kfin_lie E N X φ h.kfin,
      zfin_of_comm _ (fun z hz => GlobalTheory.CuspRep.Zalg_mul_lie E N X z hz) h.zfin,
      _root_.GlobalTheory.AutGrowth.lie_growth_of_finite hF E N X φ h⟩
    · change lieD X φ.1 (ratGL E N γ * g) = lieD X φ.1 g
      have e : chart φ.1 (ratGL E N γ * g) = chart φ.1 g := by
        funext x
        unfold chart
        split_ifs
        · rw [mul_assoc, h.left]
        · rfl
      unfold lieD
      rw [e]
    · exact level_of_le h.level fun k hk => by
        change finRep E N k (lie E N X φ) = lie E N X φ
        change (rt E N (finGL E N k) * lie E N X) φ = _
        rw [← lie_rt_fin, mul_apply_eq_comp]
        exact congrArg (lie E N X) hk

end PositivityTheory.Rg.Rs.PrAut

end
