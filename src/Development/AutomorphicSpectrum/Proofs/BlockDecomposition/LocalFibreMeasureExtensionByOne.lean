module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.ToOld

theorem linearIndependent_of_isUnit_gram {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E)
    (h : IsUnit (gramR R σ J X).det) : LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hj : ∀ j, ∑ b, w b * X b j = 0 := fun j => by
    have := congrFun hw j
    simpa [Finset.sum_apply] using this
  have hmul : (gramR R σ J X).mulVec w = 0 := by
    funext a
    show ∑ b, hform (sigR R σ) (JR R J) (X a) (X b) * w b = 0
    simp only [hform, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ∑ b, sigR R σ (X a i) * JR R J i j * X b j * w b =
        sigR R σ (X a i) * JR R J i j * ∑ b, w b * X b j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, hj j, mul_zero]
  have h1 := congrArg (Matrix.mulVec (gramR R σ J X)⁻¹) hmul
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  exact fun i => congrFun h1 i


open Classical in
theorem isFibreFamily_restrict {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (U W : Set V) (ν : Measure X)
    (B : Set X) (fib : X → Measure V) (hUW : U ⊆ W) (hU : MeasurableSet U)
    (hUB : ∀ v b, f v = ι b → (v ∈ U ↔ b ∈ B))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι W ν Set.univ fib) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B (fun b => if b ∈ B then fib b else 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hs ht => ?_⟩
  · by_cases hb : b ∈ B
    · simp only [hb, ite_true]
      refine measure_mono_null (Set.compl_subset_compl.2 fun v (hv : v ∈ f ⁻¹' {ι b} ∩ W) => ⟨hv.1, ?_⟩) (h1 b)
      exact (hUB v b hv.1).2 hb
    · simp [hb]
  · have key := h2 (U.indicator φ) (hφ.indicator hU)
    rw [lintegral_indicator hU, Measure.restrict_restrict hU, Set.inter_eq_left.2 hUW] at key
    rw [key]
    refine lintegral_congr fun b => ?_
    have hae : ∀ᵐ v ∂(fib b), f v = ι b := by
      have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ W := mem_ae_iff.2 (h1 b)
      filter_upwards [this] with v hv using hv.1
    by_cases hb : b ∈ B
    · simp only [hb, ite_true]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with v hv
      exact Set.indicator_of_mem ((hUB v b hv).2 hb) φ
    · simp only [hb, ite_false, lintegral_zero_measure]
      refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
      filter_upwards [hae] with v hv
      exact Set.indicator_of_notMem (fun hvU => hb ((hUB v b hv).1 hvU)) φ
  · obtain ⟨k1, k2⟩ := h3 φ hc hs (ht.trans hUW)
    refine ⟨fun b hb => ?_, ?_⟩
    · simpa only [hb, ite_true] using k1 b (Set.mem_univ b)
    · exact (k2.mono (Set.subset_univ B)).congr fun b hb => by simp only [hb, ite_true]

theorem stageData_of_stageDataF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∃ m₀ : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E), StageData σ J t n b lam m₁ m₀ s B₀ a κ₁ cm := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨iTR, iLC, iSC, iT2, -⟩ := id D.hR
  have := iTR; have := iLC; have := iSC; have := iT2
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  have := kTR; have := kLC; have := kSC; have := kT2
  have := kB n M
  obtain ⟨-, -, -, -, hg⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ D.hCM R n
  obtain ⟨g, gc, hgg⟩ := hg M J D.hJ
  have hopen : IsOpen (Unt σ R n) := by
    have hu : IsOpen {x : R ⊗[F] E | IsUnit x} := by
      have := (_root_.GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ D.hCM R D.hR).isOpen_range
      convert this using 1
      ext x
      simp [IsUnit]
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      continuous_subtypeVal.matrix_det
    exact hu.preimage hc
  have hset : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' (Unt σ R n) := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Unt, hgg X]
  have hmeas : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
    rw [hset]
    exact (hopen.preimage gc).measurableSet
  have hfam := isFibreFamily_restrict (coordW R b lam n M) (gramR R σ J) Subtype.val
    {X | IsUnit (gramR R σ J X).det} {X | LinearIndependent (R ⊗[F] E) X} (coordHerm R σ b lam n)
    {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m'
    (fun X hX => linearIndependent_of_isUnit_gram R σ J X hX) hmeas
    (fun X S hX => by simp only [Set.mem_ofPred_eq, hX]) D.hm'
  exact ⟨_, { hCM := D.hCM, hJ := D.hJ, ht := D.ht, hR := D.hR, hlam := D.hlam, hm₁ := D.hm₁, hm' := hfam,
              hs := D.hs, hsec := D.hsec, hcpt := D.hcpt, hB₀ := D.hB₀, htB := D.htB, hac := D.hac,
              hoff := D.hoff, hsq := D.hsq, ha1 := D.ha1, hκc := D.hκc, hκ1 := D.hκ1, hscale := D.hscale,
              hcmc := D.hcmc, hmod := D.hmod }⟩

end GlobalTheory.CompanionTheory.SW.StageF.ToOld
