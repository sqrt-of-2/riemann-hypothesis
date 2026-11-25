module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OtherInstanceCharacterEqPsiSymmetricArgument
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section


open GlobalTheory.Mem.SymFrame GlobalTheory.Mem.SymChar in
theorem GlobalTheory.Mem.SymChar.Resid.hA_bw_symVec_not_ewAt : ∀ (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2) → sigA X.B.I X.ew - 1 ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) → ∀ (m : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bw m) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2) j) - (if j.val = D.R.rS + D.R.k - 1 - m.val then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  intro D X kv hg hEw hs m j
  have hm := m.2
  have hZ : ∀ c, ZMod' X.B.I X.B.g c → c ∈ wInt X (D.naut.plGw kv.1 kv.2) :=
    fun c hc => wInt_of_zmod X kv.1 hg hc
  have hS : ∀ v, ZMod' X.B.I X.B.g (hA X.B.I v (X.bw m)) → hA X.B.I (X.bw m) v ∈ wInt X (D.naut.plGw kv.1 kv.2) := by
    intro v hv
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I v (X.bw m)]
    exact hZ _ (Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ hv)
  have hB : ∀ l : Fin D.R.k, hA X.B.I (X.bw m) (X.bwd l) - (if l = m then 1 else 0) ∈
      wInt X (D.naut.plGw kv.1 kv.2) := by
    intro l
    have h := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig _ _ (X.bw_dual l m)
    rw [map_sub, apply_ite (sigA X.B.I), map_zero] at h
    rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_symm X.B.I (X.bwd l) (X.bw m)]
    by_cases hl : l = m
    · simp only [hl, ite_true] at h ⊢
      have := add_mem (hZ _ h) hs
      convert this using 1
      ring
    · simp only [hl, ite_false] at h ⊢
      simpa using hZ _ h
  unfold symVec epsW
  rw [ite_eq_right hEw]
  unfold GlobalTheory.SeeConjRead.flagV
  by_cases h1 : j.1 < D.R.rS
  · rw [dite_eq_left h1, ite_eq_right (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 ⟨j.1, h1⟩).1
  rw [dite_eq_right h1]
  by_cases h2 : j.1 < D.R.rS + D.R.k
  · rw [dite_eq_left h2]
    have e : ((Fin.rev (⟨j.1 - D.R.rS, by omega⟩ : Fin D.R.k)) = m) ↔ j.val = D.R.rS + D.R.k - 1 - m.val := by
      rw [Fin.ext_iff, Fin.val_rev]; simp only; constructor <;> intro h <;> omega
    have := hB (Fin.rev ⟨j.1 - D.R.rS, by omega⟩)
    by_cases h' : j.val = D.R.rS + D.R.k - 1 - m.val
    · rw [ite_eq_left h']; rwa [ite_eq_left (e.2 h')] at this
    · rw [ite_eq_right h']; rwa [ite_eq_right (fun hh => h' (e.1 hh))] at this
  rw [dite_eq_right h2]
  by_cases h4 : j.1 = D.R.rS + D.R.k
  · rw [dite_eq_left h4, ite_eq_right (by omega), sub_zero]
    exact hS _ (X.weightVectorsIntegral m).1
  rw [dite_eq_right h4]
  by_cases h3 : j.1 < 2 * D.R.rS + D.R.k + 1
  · rw [dite_eq_left h3, ite_eq_right (by omega), sub_zero]
    exact hS _ ((X.weightVectorsIntegral m).2.2 _).2.1
  · rw [dite_eq_right h3, ite_eq_right (by omega), sub_zero, hA_zero_right']
    exact zero_mem _

end
