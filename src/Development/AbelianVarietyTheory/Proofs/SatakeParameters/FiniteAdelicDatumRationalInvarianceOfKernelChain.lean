module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPDivOfUnit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtFormOfMemStdAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAut
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
public import Formalism.LocalToGlobal.Columns.ChainTopTilQK
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryAutColumnFieldOfStandardUnitaryMatr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalCoordsConjUnitaryStandardForm
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveRationalIsometry, Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartBaseRepresentativePenultimateStep, Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariant, Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitary, Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometry, Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixStepDatumEquivariantRationalUnitary, Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChangeIntertwinesRationalIsometries, Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometry, Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometryStatement, Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry, Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChain

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveRationalIsometry =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveRationalIsometry", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\npublic import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPDivOfUnit\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelFrameLiftUnitaryAutNearAdelicMatrixDepthOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.RatFrame



theorem frame_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P)
        (ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P))) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i hi β x x₁ γ hγ h₁ g hg p hp P
  have hx : ratA D.host.F (A.crd i hi) * x₁.1 * ratA D.host.F (A.fb i hi β P) =
      ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) := by
    rw [h₁, hg, map_mul, map_mul, map_inv]
    group
  rw [hx]
  have h0 := hp.frame P
  by_cases hP : P.1 ∈ t.Pr.vGs
  · have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
    have hq := GlobalTheory.TopStep.qOf_notMem_sq hPin.fields.ok t.pr_ok hP
    have e1 : frsF t.sel (t.tup μ) p P = p.deco.1.liftFr ⟨P.1, hP⟩ := by
      unfold frsF
      rw [dite_eq_left hP]
    have h1 : NearAt (seamP t.seam P.1) 1 (ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P)) (seamGL t.seam (p.deco.1.liftFr ⟨P.1, hP⟩)) := by
      rw [← e1, ← hD]; exact h0
    have e2 : frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) ×
        GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P =
        (((g, (1 : GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs))) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs)) • p.deco).1.liftFr ⟨P.1, hP⟩ := by
      unfold frsF
      rw [dite_eq_left hP]
      rfl
    have key := GlobalTheory.FrameRat.nearAt_liftFr_smul t.seam p.deco ⟨P.1, hP⟩ g hq _ h1
    rw [e2, hD]
    exact key
  · have e : frsF t.sel (t.tup μ) (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) ×
        GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p) P = g.1 * frsF t.sel (t.tup μ) p P := by
      unfold frsF
      rw [dite_eq_right hP, dite_eq_right hP]
      show g.1 * _ * _ = _
      simp
      rfl
    rw [e, map_mul, nearAt_rat_mul]
    exact h0

end GlobalTheory.RatFrame

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveRationalIsometry =====

-- ===== clump member: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartBaseRepresentativePenultimateStep =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartBaseRepresentativePenultimateStep", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.TwV.Model

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {w : Pr.Word}


open Classical in
theorem frsF_mem {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  split_ifs with h
  · exact (Deco.liftFr_spec (p.deco.2.hasLift ⟨P.1, h⟩)).1 x
  · exact p.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

private theorem mem_stdAt_iff_forall_intAt {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (w : Sp X.E n) :
    w ∈ stdAt X.E n P ↔ ∀ l, IntAt P (w l) := by
  show (∃ s ∈ P.asIdeal.primeCompl, s • w ∈ _) ↔ _
  constructor
  · rintro ⟨s, hs, hsw⟩ l
    obtain ⟨r, hr⟩ := (Submodule.mem_one).1 (hsw l (Set.mem_univ l))
    refine ⟨r, s, hs, ?_⟩
    rw [hr]
    simp [Algebra.smul_def]
  · intro h
    choose r s hs e using h
    refine ⟨∏ l, s l, Submonoid.prod_mem _ fun l _ => hs l, fun l _ => ?_⟩
    change ((∏ l, s l) • w) l ∈ (1 : Submodule (𝓞 X.E) X.E)
    rw [Submodule.mem_one]
    refine ⟨r l * ∏ k ∈ Finset.univ.erase l, s k, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ l)]
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, map_prod]
    rw [← e l]
    ring


open Classical in
theorem sameCoset_iff {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (z y : Sp X.E (R.N j)) :
    SameCoset sel mu cst P ((frsF sel mu p P).symm z) ((frsF sel mu p P).symm y) ↔
      (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • (z - y)) ∈ p.deco.1.at P.1 := by
  have hc : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ =
      ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ := by
    split_ifs <;> simp
  have e : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • (z - y) =
      frsF sel mu p P (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ •
        ((frsF sel mu p P).symm z - (frsF sel mu p P).symm y)) := by
    rw [map_smul, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [e, frsF_mem, mem_stdAt_iff_forall_intAt]
  unfold SameCoset
  simp only [hc, Pi.smul_apply, smul_eq_mul]

theorem sameCoset_trans {n : ℕ} {P : rowSG Pr sel mu} {x y z : Sp X.E n} (h : SameCoset sel mu cst P x y) (h' : SameCoset sel mu cst P y z) :
    SameCoset sel mu cst P x z := by
  intro l
  obtain ⟨r₁, s₁, hs₁, e₁⟩ := h l
  obtain ⟨r₂, s₂, hs₂, e₂⟩ := h' l
  refine ⟨r₁ * s₂ + r₂ * s₁, s₁ * s₂, fun hm => (P.1.isPrime.mem_or_mem hm).elim hs₁ hs₂, ?_⟩
  simp only [Pi.sub_apply] at e₁ e₂ ⊢
  rw [map_add (f := _), map_mul, map_mul, map_mul, ← e₁, ← e₂]
  ring

theorem sameCoset_symm {n : ℕ} {P : rowSG Pr sel mu} {x y : Sp X.E n} (h : SameCoset sel mu cst P x y) :
    SameCoset sel mu cst P y x := by
  intro l
  obtain ⟨r, s, hs, e⟩ := h l
  refine ⟨-r, s, hs, ?_⟩
  simp only [Pi.sub_apply] at e ⊢
  rw [map_neg, ← e]
  ring

end Gen

end GlobalTheory.TwV.Model

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartBaseRepresentativePenultimateStep =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariant =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariant", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartBaseRepresentativePenultimateStep\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeOneAddPrimeSmulEqOne\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrime\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplRat

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}


open Classical in
theorem exists_pass_rat (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) :
    ∃ κ : GLQ X.E (R.N j) (rowSG Pr sel mu),
      (∀ P, frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * (frsF sel mu p P * ((κ P)⁻¹).1)) ∧
      (∀ P : rowSG Pr sel mu, GlobalTheory.TopStep.redGL (R.N j) P.1 (κ P) = 1) ∧ (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → κ P = 1) := by
  have h : ∀ P : rowSG Pr sel mu, ∃ k : GLint X.E (R.N j) P.1,
      frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * (frsF sel mu p P * (k⁻¹).1) ∧ GlobalTheory.TopStep.redGL (R.N j) P.1 k = 1 ∧ (P.1 ∉ Pr.vGs → k = 1) := by
    intro P
    by_cases hP : P.1 ∈ Pr.vGs
    · obtain ⟨κ0, h1, h2⟩ := liftFr_smul p.deco ((g, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs)) ⟨P.1, hP⟩
      have hr : GlobalTheory.TopStep.redGL (R.N j) P.1 κ0 = 1 := GlobalTheory.TopStep.redGL_eq κ0 fun x hx => by
        rw [h2 x hx]
        simp
      refine ⟨κ0⁻¹, ?_, by rw [map_inv, hr, inv_one], fun h => absurd hP h⟩
      unfold frsF
      rw [dite_eq_left hP, dite_eq_left hP, inv_inv]
      exact h1.trans (mul_assoc _ _ _)
    · refine ⟨1, ?_, map_one _, fun _ => rfl⟩
      unfold frsF
      rw [dite_eq_right hP, dite_eq_right hP]
      show g.1 * _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
      simp
      rfl
  choose κ hκ using h
  exact ⟨κ, fun P => (hκ P).1, fun P => (hκ P).2.1, fun P => (hκ P).2.2⟩

theorem levAt_one {n : ℕ} (Λ : LevFam X.E X.K n Pr.vGs) (Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K))) (P : rowSG Pr sel mu)
    (k : GLint X.E n P.1) (hr : GlobalTheory.TopStep.redGL n P.1 k = 1) (h1 : P.1 ∉ Pr.vGs → k = 1) : GlobalTheory.TopLaw.LevAt Λ Θ P k 1 := by
  refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
  · have hm : GlobalTheory.TopStep.redGL n P.1 k ∈ (Λ ⟨P.1, hP⟩).H := by rw [hr]; exact one_mem _
    refine ⟨hm, ?_⟩
    rw [show (⟨_, hm⟩ : (Λ ⟨P.1, hP⟩).H) = 1 from Subtype.ext hr, map_one]
  · obtain rfl := h1 hP
    exact ⟨one_mem _, (map_one _).symm⟩

end Gen

section Cos

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}


open Classical in
theorem sameCoset_pass (hX : X.Ok) (hPr : Pr.Ok) {n : ℕ} (P : rowSG Pr sel mu) (k : GLint X.E n P.1)
    (hr : GlobalTheory.TopStep.redGL n P.1 k = 1) (h1 : P.1 ∉ Pr.vGs → k = 1) (y0 : Sp X.E n)
    (hy0 : P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ 1 * y0 l)) (v : Sp X.E n) :
    SameCoset sel mu cst P (k.1 v) y0 ↔ SameCoset sel mu cst P v y0 := by
  by_cases hP : P.1 ∈ Pr.vGs
  · unfold SameCoset
    simp only [ite_eq_left hP]
    have hk : k⁻¹ ∈ GlobalTheory.TopStep.prinCong n P.1 1 :=
      GlobalTheory.CplCosetPt.mem_prinCong_one_of_redGL (GlobalTheory.TopStep.qOf_notMem_sq hX hPr hP) _ (by rw [map_inv, hr, inv_one])
    exact GlobalTheory.CplCosetPt.sameCoset_loc P.1 0 1 1 k.1 1 k⁻¹ k.2 (one_mem _) hk (by simp) (by omega) y0 (hy0 hP)
      (fun l => by simpa using GlobalTheory.TopStep.intAt_zero) v
  · obtain rfl := h1 hP
    exact Iff.rfl


open Classical in
theorem coset_image (hX : X.Ok) (hPr : Pr.Ok) {n : ℕ} (fp fq : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) (κ : GLQ X.E n (rowSG Pr sel mu)) (hκ : ∀ P, fq P = g * (fp P * ((κ P)⁻¹).1))
    (hr : ∀ P : rowSG Pr sel mu, GlobalTheory.TopStep.redGL n P.1 (κ P) = 1) (h1 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → κ P = 1)
    (y0 : rowSG Pr sel mu → Sp X.E n) (hy0 : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : X.E) ^ 1 * y0 P l)) :
    {y | ∀ P, SameCoset sel mu cst P ((fq P).symm y) (y0 P)} =
      (fun v => g v) '' {y | ∀ P, SameCoset sel mu cst P ((fp P).symm y) (y0 P)} := by
  have e : ∀ P y, (fq P).symm y = (κ P).1 ((fp P).symm (g.symm y)) := by
    intro P y
    apply (fq P).injective
    rw [LinearEquiv.apply_symm_apply, hκ P]
    show y = g (fp P (((κ P)⁻¹).1 ((κ P).1 ((fp P).symm (g.symm y)))))
    rw [Subgroup.coe_inv]
    show y = g (fp P ((κ P).1.symm ((κ P).1 ((fp P).symm (g.symm y)))))
    simp
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_image, e]
  constructor
  · intro h
    refine ⟨g.symm y, fun P => (sameCoset_pass hX hPr P (κ P) (hr P) (h1 P) (y0 P) (hy0 P) _).1 (h P), by simp⟩
  · rintro ⟨z, hz, rfl⟩ P
    rw [LinearEquiv.symm_apply_apply]
    exact (sameCoset_pass hX hPr P (κ P) (hr P) (h1 P) (y0 P) (hy0 P) _).2 (hz P)


open Classical in
theorem coset_mem_ybSet (p : ChPt (R := R) sel mu u j) (y0 : rowSG Pr sel mu → Sp X.E (R.N j))
    (hy0 : ∀ (P : rowSG Pr sel mu) l, IntAt P.1 ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M) * y0 P l)) :
    {y | ∀ P, SameCoset sel mu cst P ((frsF sel mu p P).symm y) (y0 P)} ∈ ybSet sel mu cst p.deco.1.N := by
  obtain ⟨y, hy⟩ := GlobalTheory.CplCosetPt.exists_sameCoset_frames sel mu cst (frsF sel mu p) y0
  refine ⟨y, ?_, ?_⟩
  · rw [mem_locLat]
    intro P
    have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
      have : qOf P.1 ≠ 0 := fun h0 => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
      exact_mod_cast this
    have hqI : IntAt P.1 ((qOf P.1 : ℕ) : X.E) := by simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 X.E)
    rw [← (frsF sel mu p P).apply_symm_apply (_ • y), GlobalTheory.TwV.Model.frsF_mem, GlobalTheory.TopStep.mem_stdAt]
    intro l
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    have hs := hy P l
    have h0 := hy0 P l
    by_cases hP : P.1 ∈ Pr.vGs
    · simp only [ite_eq_left hP, pow_zero, inv_one, one_mul, pow_one] at hs h0 ⊢
      simp only [_root_.zpow_neg, zpow_one, inv_inv]
      have e : ((qOf P.1 : ℕ) : X.E) * (frsF sel mu p P).symm y l =
          ((qOf P.1 : ℕ) : X.E) * ((frsF sel mu p P).symm y - y0 P) l + ((qOf P.1 : ℕ) : X.E) * y0 P l := by
        simp only [Pi.sub_apply]; ring
      rw [e]
      exact (hqI.mul hs).add h0
    · simp only [ite_eq_right hP] at hs h0 ⊢
      simp only [_root_.zpow_neg, zpow_natCast, inv_inv]
      have e : ((qOf P.1 : ℕ) : X.E) ^ cst.M * (frsF sel mu p P).symm y l =
          (((qOf P.1 : ℕ) : X.E) ^ cst.M * ((qOf P.1 : ℕ) : X.E) ^ cst.M) *
            ((((qOf P.1 : ℕ) : X.E) ^ cst.M)⁻¹ * ((frsF sel mu p P).symm y - y0 P) l) + ((qOf P.1 : ℕ) : X.E) ^ cst.M * y0 P l := by
        simp only [Pi.sub_apply]
        field_simp
        ring
      rw [e]
      exact (((GlobalTheory.TopStep.intAt_pow hqI _).mul (GlobalTheory.TopStep.intAt_pow hqI _)).mul hs).add h0
  · ext z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, mem_locLat]
    refine forall_congr' fun P => ?_
    rw [← GlobalTheory.TwV.Model.sameCoset_iff sel mu cst p P z y]
    exact ⟨fun h => GlobalTheory.TwV.Model.sameCoset_trans _ _ _ h (GlobalTheory.TwV.Model.sameCoset_symm _ _ _ (hy P)),
      fun h => GlobalTheory.TwV.Model.sameCoset_trans _ _ _ h (hy P)⟩

end Cos

section Main

theorem unitV_det_one {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k : GLint E n P) (hr : GlobalTheory.TopStep.redGL n P k = 1) :
    LocE.unitV χ ((LinearEquiv.det k.1 : Eˣ) : E) = 1 := by
  rw [GlobalTheory.TopStep.unitV_congr χ (b := 1) ?_, GlobalTheory.Mem.Col2.IdxEx.Cong.unitV_one]
  rw [(GlobalTheory.TopStep.det_glint k).2, GlobalTheory.TopStep.reduction_one₂, ← GlobalTheory.TopStep.redGL_val, hr]
  simp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiPt_cpl_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i = t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi hm β β' x x' p p' _ _ g g' w
  classical
  subst hm
  have hX : t.X.Ok := hPins.fields.ok
  have hPr := t.pr_ok
  have hL := t.idx_ok μ
  obtain ⟨κ, hκ, hr, h1⟩ := exists_pass_rat (R := D.R) p g
  obtain ⟨κ', hκ', hr', h1'⟩ := exists_pass_rat (R := D.R) p' g'
  have hy0 : ∀ (P : SB t μ) l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) *
      y0At A (t.m2 + 1) hi β' P l) := by
    intro P l
    have e : y0At A (t.m2 + 1) hi β' P = A.y0 β' P := by
      unfold y0At
      rw [dite_eq_left rfl]
    rw [e]
    exact GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie β' P l
  have hY : cosetOf A (t.m2 + 1) hi β' p' ∈ ybSet t.sel (t.tup μ) (t.cst μ) p'.deco.1.N := coset_mem_ybSet p' _ hy0
  have hC : cosetOf A (t.m2 + 1) hi β' (((g', 1, 1) : UF t.X.E (D.R.N (t.m2 + 1)) × GLG (E := t.X.E) (n := D.R.N (t.m2 + 1)) (SG := t.Pr.vGs) ×
      GLQ t.X.E (D.R.N (t.m2 + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p') =
      (fun v => g'.1 v) '' cosetOf A (t.m2 + 1) hi β' p' :=
    coset_image hX hPr _ _ g'.1 κ' hκ' hr' h1' _ (fun P hP l => by simpa [hP] using hy0 P l)
  have hY2 : (fun v => g'.1 v) '' cosetOf A (t.m2 + 1) hi β' p' ∈ ybSet t.sel (t.tup μ) (t.cst μ)
      ((((g', 1, 1) : UF t.X.E (D.R.N (t.m2 + 1)) × GLG (E := t.X.E) (n := D.R.N (t.m2 + 1)) (SG := t.Pr.vGs) ×
        GLQ t.X.E (D.R.N (t.m2 + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p').deco.1.N) :=
    (ybSet_gmap t.sel (t.tup μ) (t.cst μ) _ g'.1 _).2 hY
  have law := GlobalTheory.CoupledLaw.xiCpl1_law (Ch := t.Ch) (L := t.idx μ) (al := A.ib t.m2 hi β)
    (b := A.ib (t.m2 + 1) (cpl_lt t μ) β') hX hPr hL hY hY2 hκ hκ' (a := fun _ => 1) (a' := fun _ => 1)
    (fun P => levAt_one _ _ P _ (hr P) (h1 P)) (fun P => levAt_one _ _ P _ (hr' P) (h1' P)) w
    (Formalism.L2.Ker.phiT_smul t.X.K p.deco p'.deco g 1 g' 1 w)
  have hprod : ∀ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ⁻¹ P).1 : t.X.Eˣ) : t.X.E) *
      rhoT t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (κ'⁻¹ P).1 : t.X.Eˣ) : t.X.E) = 1 := by
    intro P
    unfold rhoS rhoT
    rw [Pi.inv_apply, Pi.inv_apply, unitV_det_one _ _ (by rw [map_inv, hr P, inv_one]),
      unitV_det_one _ _ (by rw [map_inv, hr' P, inv_one]), mul_one]
  rw [Finset.prod_eq_one fun P _ => hprod P, mul_one] at law
  simp only [Finset.prod_const_one, inv_one, mul_one, Units.val_one, one_mul] at law
  unfold xiPt
  rw [dite_eq_right (lt_irrefl _), ite_eq_left rfl, dite_eq_right (lt_irrefl _), ite_eq_left rfl, hC]
  exact law

end Main

end GlobalTheory.CplRat
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariant =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitary =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitary", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\npublic import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPDivOfUnit\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseCosetRepIntegralAfterScalingAtBadPrime\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtFormOfMemStdAt\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOn\npublic import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TopRat

section Frames
variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) {u : Pr.Word} {j : ℕ}

theorem frsF_rat_notG (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs) :
    frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
      g.1 * frsF sel mu p P := by
  unfold frsF
  rw [dite_eq_right hP, dite_eq_right hP]
  show g.1 * p.fr _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
  simp

theorem frsF_rat_G (hq : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (p : ChPt (R := R) sel mu u j) (g : UF X.E (R.N j)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    ∃ κ : ↥(GLint X.E (R.N j) P.1),
      frsF sel mu (((g, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • p) P =
        g.1 * frsF sel mu p P * κ.1 ∧
      ∀ x ∈ stdAt X.E (R.N j) P.1, ((qOf P.1 : X.E) ^ 1)⁻¹ • (κ.1 x - x) ∈ stdAt X.E (R.N j) P.1 := by
  obtain ⟨κ, he, hr⟩ := liftFr_smul p.deco (g, (1 : GLG (E := X.E) (n := R.N j) (SG := Pr.vGs))) ⟨P.1, hP⟩
  refine ⟨κ, ?_, fun x hx => ?_⟩
  · unfold frsF
    rw [dite_eq_left hP, dite_eq_left hP]
    exact he
  · rw [GlobalTheory.TopStep.mem_stdAt]
    intro i
    have hkx := GlobalTheory.TopStep.mem_stdAt.1 ((κ.2 x).2 hx) i
    have hxi := GlobalTheory.TopStep.mem_stdAt.1 hx i
    have h1 := congrFun (hr x hx) i
    simp only [Pi.one_apply, inv_one, Units.val_one, Matrix.one_mulVec] at h1
    have hred : redP P.1 (κ.1 x i - x i) = 0 := by
      rw [GlobalTheory.TopStep.reduction_sub hkx hxi]
      have h2 : redP P.1 (κ.1 x i) = redP P.1 (x i) := h1
      rw [h2, sub_self]
    have h := GlobalTheory.TopStep.intAt_div_of_redP (hq P hP) (GlobalTheory.TopStep.intAt_sub hkx hxi) hred
    have e : (((qOf P.1 : X.E) ^ 1)⁻¹ • (κ.1 x - x)) i = (κ.1 x i - x i) / (qOf P.1 : X.E) := by
      simp [div_eq_inv_mul]
    rw [e]
    exact h

end Frames

theorem xiPt_top_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), t.m2 < i → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie i hi hlt β β' x x' p p' _hp _hp' g g' w
  have hm := m_eq t μ
  obtain rfl : i = t.m2 + 1 := by omega
  have hn1 : ¬ (t.m2 + 1 < t.m2) := by omega
  have hn2 : t.m2 + 1 ≠ t.m2 := by omega
  unfold xiPt
  rw [dite_eq_right hn1, ite_eq_right hn2, dite_eq_right hn1, ite_eq_right hn2, XiTop_eq, XiTop_eq]
  congr 1
  · exact phiT_smul t.X.K p.deco p'.deco g 1 g' 1 w
  · have hX : t.X.Ok := hPin.fields.ok
    have hok := t.idx_ok μ
    have hc := hok.cst_ok
    have hrep : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
        repY (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q := by
      intro q
      obtain ⟨y, hy⟩ := GlobalTheory.CplCosetPt.exists_sameCoset_frames t.sel (t.tup μ) (t.cst μ) (fun P => frsF t.sel (t.tup μ) q P)
        (fun P => y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P)
      exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) ⟨y, hy⟩
    have hy0 := _root_.GlobalTheory.TwU.BaseCosetInt.baseCosetRep_integral_after_scaling_at_bad_prime D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie β
    refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 : (qOf P.1 : t.X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
    have hqI : IntAt P.1 (qOf P.1 : t.X.E) := by simpa using IntAt.coe P.1 ((qOf P.1 : ℕ) : 𝓞 t.X.E)
    have hyy : y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P = A.y0 β P := by
      unfold y0At
      rw [dite_eq_left rfl]
    by_cases hP : P.1 ∈ t.Pr.vGs
    · have hq2 : ∀ P : rowSG t.Pr t.sel (t.tup μ), P.1 ∈ t.Pr.vGs → ((qOf P.1 : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal ^ 2 :=
        fun P hP => GlobalTheory.TopStep.qOf_notMem_sq hX t.pr_ok hP
      obtain ⟨κ, hF, hκc⟩ := frsF_rat_G t.sel (t.tup μ) hq2 p g P hP
      obtain ⟨κ', hF', hκc'⟩ := frsF_rat_G t.sel (t.tup μ) hq2 p' g' P hP
      have hD1 : (t.cst μ).D P = 1 := hok.depthG P hP
      have hκD : ∀ z ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ.1 z - z) ∈ stdAt t.X.E _ P.1 := by
        rw [hD1]; exact hκc
      have hκD' : ∀ z ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ'.1 z - z) ∈ stdAt t.X.E _ P.1 := by
        rw [hD1]; exact hκc'
      have hy0P : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * A.y0 β P l) := by
        intro l
        have h := hy0 P l
        simpa only [hP, ite_true, pow_one] using h
      have key1 : ∀ (F1 : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))) (u1 u0 : Sp t.X.E (D.R.N (t.m2 + 1))),
          F1 = g.1 * frsF t.sel (t.tup μ) p P * κ.1 →
          SameCoset t.sel (t.tup μ) (t.cst μ) P (F1.symm u1) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm u0) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr F1 (g'.1 * frsF t.sel (t.tup μ) p' P * κ'.1) (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap)) (F1.symm u1) =
            topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w) ((frsF t.sel (t.tup μ) p P).symm u0) := by
        rintro F1 u1 u0 rfl h1 h2
        unfold SameCoset at h1 h2
        simp only [hP, ite_true, pow_zero, inv_one, one_mul, hyy] at h1 h2
        have e1 : inFr (g.1 * frsF t.sel (t.tup μ) p P * κ.1) (g'.1 * frsF t.sel (t.tup μ) p' P * κ'.1)
            (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) =
            κ'.1.symm.toLinearMap ∘ₗ inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w ∘ₗ κ.1.toLinearMap := by
          refine LinearMap.ext fun v => ?_
          show κ'.1.symm ((frsF t.sel (t.tup μ) p' P).symm (g'.1.symm (g'.1 (w (g.1.symm (g.1 ((frsF t.sel (t.tup μ) p P) (κ.1 v)))))))) = _
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
          rfl
        have e2 : (g.1 * frsF t.sel (t.tup μ) p P * κ.1).symm u1 = κ.1.symm ((frsF t.sel (t.tup μ) p P).symm (g.1.symm u1)) := rfl
        rw [e1, e2]
        rw [e2] at h1
        generalize (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) = v1 at h1 ⊢
        generalize (frsF t.sel (t.tup μ) p P).symm u0 = v at h2 ⊢
        generalize inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w = Yw
        have hbd : ∀ z : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 ((z - A.y0 β P) l)) →
            ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * z l) := by
          intro z hz l
          have e : (qOf P.1 : t.X.E) * z l = (qOf P.1 : t.X.E) * (z - A.y0 β P) l + (qOf P.1 : t.X.E) * A.y0 β P l := by
            simp only [Pi.sub_apply]; ring
          rw [e]
          exact (hqI.mul (hz l)).add (hy0P l)
        have hw : (qOf P.1 : t.X.E) • κ.1.symm v1 ∈ stdAt t.X.E _ P.1 :=
          GlobalTheory.TopStep.mem_stdAt.2 fun l => by simpa using hbd _ h1 l
        have hw1 : (qOf P.1 : t.X.E) • v1 ∈ stdAt t.X.E _ P.1 := by
          have h := (κ.2 ((qOf P.1 : t.X.E) • κ.1.symm v1)).2 hw
          rwa [map_smul, LinearEquiv.apply_symm_apply] at h
        have hv1 : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * v1 l) := fun l => by
          simpa using GlobalTheory.TopStep.mem_stdAt.1 hw1 l
        rw [GlobalTheory.TwV.AwayTopG.topDat_frames_vGs A dtU a hPin hTie P hP κ.1 κ'.1 κ.2 hκD κ'.2 hκD' Yw v1 hv1]
        have hs := GlobalTheory.TwV.AwayTopG.symm_near κ.2 hκc hw1
        rw [map_smul, ← smul_sub, smul_smul, pow_one, inv_mul_cancel₀ hq0, one_smul] at hs
        have hdiff : v1 - v ∈ stdAt t.X.E _ P.1 := by
          refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
          have e : (v1 - v) l = (κ.1.symm v1 - A.y0 β P) l - (κ.1.symm v1 - v1) l - (v - A.y0 β P) l := by
            simp only [Pi.sub_apply]; ring
          rw [e]
          exact GlobalTheory.TopStep.intAt_sub (GlobalTheory.TopStep.intAt_sub (h1 l) (GlobalTheory.TopStep.mem_stdAt.1 hs l)) (h2 l)
        unfold topDat
        congr 1
        have h := GlobalTheory.TopLaw.ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (hok.depthQ P) (κ := 1)
          (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ Yw) v v1 (fun _ => hbd _ h2)
          (fun h => absurd hP h) (fun _ => hdiff) (fun h => absurd hP h)
        exact h
      rw [hF']
      exact key1 _ _ _ hF (hrep _ P) (hrep _ P)
    · have hy0P : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * A.y0 β P l) := by
        intro l
        have h := hy0 P l
        simpa only [hP, ite_false] using h
      have hqM : (qOf P.1 : t.X.E) ^ (t.cst μ).M ≠ 0 := pow_ne_zero _ hq0
      have key2 : ∀ (F1 : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))) (u1 u0 : Sp t.X.E (D.R.N (t.m2 + 1))),
          F1 = g.1 * frsF t.sel (t.tup μ) p P →
          SameCoset t.sel (t.tup μ) (t.cst μ) P (F1.symm u1) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p P).symm u0) (y0At A (t.m2 + 1) (Nat.le_of_succ_le hi) β P) →
          topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr F1 (g'.1 * frsF t.sel (t.tup μ) p' P) (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap)) (F1.symm u1) =
            topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P
              (inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w) ((frsF t.sel (t.tup μ) p P).symm u0) := by
        rintro F1 u1 u0 rfl h1 h2
        unfold SameCoset at h1 h2
        simp only [hP, ite_false, hyy] at h1 h2
        have e1 : inFr (g.1 * frsF t.sel (t.tup μ) p P) (g'.1 * frsF t.sel (t.tup μ) p' P)
            (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w := by
          refine LinearMap.ext fun v => ?_
          show (frsF t.sel (t.tup μ) p' P).symm (g'.1.symm (g'.1 (w (g.1.symm (g.1 ((frsF t.sel (t.tup μ) p P) v)))))) = _
          rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
          rfl
        have e2 : (g.1 * frsF t.sel (t.tup μ) p P).symm u1 = (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) := rfl
        rw [e1, e2]
        rw [e2] at h1
        generalize (frsF t.sel (t.tup μ) p P).symm (g.1.symm u1) = v1 at h1 ⊢
        generalize (frsF t.sel (t.tup μ) p P).symm u0 = v at h2 ⊢
        generalize inFr (frsF t.sel (t.tup μ) p P) (frsF t.sel (t.tup μ) p' P) w = Yw
        have hv : ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * v l) := by
          intro l
          have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * v l = (qOf P.1 : t.X.E) ^ (t.cst μ).M * (qOf P.1 : t.X.E) ^ (t.cst μ).M *
              (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v - A.y0 β P) l) + (qOf P.1 : t.X.E) ^ (t.cst μ).M * A.y0 β P l := by
            simp only [Pi.sub_apply]
            field_simp
            ring
          rw [e]
          exact (((GlobalTheory.TopStep.intAt_pow hqI _).mul (GlobalTheory.TopStep.intAt_pow hqI _)).mul (h2 l)).add (hy0P l)
        have hdiff : ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • (v1 - v) ∈ stdAt t.X.E _ P.1 := by
          refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
          have e : (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • (v1 - v)) l =
              ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v1 - A.y0 β P) l - ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (v - A.y0 β P) l := by
            simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
          rw [e]
          exact GlobalTheory.TopStep.intAt_sub (h1 l) (h2 l)
        unfold topDat
        congr 1
        have h := GlobalTheory.TopLaw.ftY_comp_glint t.sel (t.tup μ) (t.cst μ) hc P (hok.depthQ P) (κ := 1)
          (atNL t.X.E (D.R.N (t.m2 + 1 + 1)) (D.R.N (t.m2 + 1 + 1) - 1) ∘ₗ Yw) v v1 (fun h => absurd h hP)
          (fun _ => hv) (fun h => absurd h hP) (fun _ => hdiff)
        exact h
      rw [frsF_rat_notG t.sel (t.tup μ) p' g' P hP]
      exact key2 _ _ _ (frsF_rat_notG t.sel (t.tup μ) p g P hP) (hrep _ P) (hrep _ P)

end GlobalTheory.TopRat
end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitary =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometry =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometry", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAut\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem funMoved_ptAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
        IsOver v (seamP t.seam P.1) →
        FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x₁.1) ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β x x₁ γ hγ hx g hg p hp P v h hv
  have H := funMoved_ratA_act t.seam _ P v h _ _ _ g.1 1 (hp.fnl P v h hv)
  have e : ratA D.host.F (A.crd i hi) * x₁.1 = ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * x.1) := by
    rw [hx, hg, map_mul, map_mul, map_inv]; group
  rw [e]
  exact H

end GlobalTheory.TwV
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometry =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixStepDatumEquivariantRationalUnitary =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixStepDatumEquivariantRationalUnitary", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\npublic import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant\npublic import Formalism.LocalToGlobal.Columns.ChainTopTilQK\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\npublic import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IntegralGLSuccEmbeddingMemParahoricTimesPrincipa\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open GlobalTheory.TopStep GlobalTheory.TopLaw

noncomputable section

namespace GlobalTheory.RatEntry

theorem unitV_det_red_one {X : Fields} {n : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (χ : (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ)
    (k : GLint X.E n P) (hk : redGL n P k = 1) : LocE.unitV χ ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 :=
  tqk_unitV_one χ (by rw [(det_glint k).2, ← redGL_val, hk, Units.val_one, Matrix.det_one])

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem red_pass_one {u : Pr.Word} {j : ℕ} {Λ : LevFam X.E X.K (R.N j) Pr.vGs} {Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}
    (g : UF X.E (R.N j)) (p : ChPt (R := R) sel mu u j) (κ : GLQ X.E (R.N j) (rowSG Pr sel mu))
    (hκ : ∀ P, frsF sel mu (((g, 1, 1) : FrmG Λ Θ) • p) P = g.1 * (frsF sel mu p P * ((κ P)⁻¹).1)) (P : rowSG Pr sel mu) :
    redGL (R.N j) P.1 (κ P) = 1 := by
  classical
  have h := hκ P
  by_cases hP : P.1 ∈ Pr.vGs
  · have e : κ P = passG ((g, 1, 1) : FrmG Λ Θ) p ⟨P.1, hP⟩ := by
      apply Subtype.ext
      unfold frsF at h
      simp only [dite_eq_left hP] at h
      show (κ P).1 = ((((g, 1, 1) : FrmG Λ Θ) • p).deco.1.liftFr ⟨P.1, hP⟩)⁻¹ * g.1 * p.deco.1.liftFr ⟨P.1, hP⟩
      rw [h, Subgroup.coe_inv]
      group
    rw [e]
    exact redGL_passG ((g, 1, 1) : FrmG Λ Θ) p ⟨P.1, hP⟩
  · unfold frsF at h
    simp only [dite_eq_right hP] at h
    have h1 : ((κ P)⁻¹).1 = 1 := by
      have h' : g.1 * (p.fr ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ * ((κ P)⁻¹).1) =
          g.1 * (p.fr ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ * 1) := by
        rw [← h]
        show g.1 * p.fr _ * (((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 = _
        simp
      exact mul_left_cancel (mul_left_cancel h')
    have h2 : κ P = 1 := inv_eq_one.1 (Subtype.ext h1)
    rw [h2, map_one]

theorem rho_pass_one (i : ℕ) (κ : GLQ X.E (R.N i) (rowSG Pr sel mu)) (κ' : GLQ X.E (R.N (i + 1)) (rowSG Pr sel mu))
    (hκ : ∀ P : rowSG Pr sel mu, redGL (R.N i) P.1 (κ P) = 1) (hκ' : ∀ P : rowSG Pr sel mu, redGL (R.N (i + 1)) P.1 (κ' P) = 1) :
    ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu i P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) *
      rhoT Ch sel mu i P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E)) = 1 := by
  refine Finset.prod_eq_one fun P _ => ?_
  have h1 : redGL _ P.1 ((κ P)⁻¹) = 1 := by rw [map_inv, hκ P, inv_one]
  have h2 : redGL _ P.1 ((κ' P)⁻¹) = 1 := by rw [map_inv, hκ' P, inv_one]
  rw [Pi.inv_apply, Pi.inv_apply]
  unfold rhoS rhoT
  rw [unitV_det_red_one _ ((κ P)⁻¹) h1, unitV_det_red_one _ ((κ' P)⁻¹) h2, mul_one]

theorem xiEntry_rat {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ k, Pr.g k ∈ S)
    (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1))
    (g : UF X.E (R.N i)) (g' : UF X.E (R.N (i + 1))) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiEntry Ch sel mu cst L i al be
        (((g, 1, 1) : UF X.E (R.N i) × GLG (E := X.E) (n := R.N i) (SG := Pr.vGs) × GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) • p)
        (((g', 1, 1) : UF X.E (R.N (i + 1)) × GLG (E := X.E) (n := R.N (i + 1)) (SG := Pr.vGs) × GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) • p')
        (g'.1.toLinearMap ∘ₗ x ∘ₗ g.1.symm.toLinearMap) = XiEntry Ch sel mu cst L i al be p p' x := by
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  have e1 : (((g, 1, 1) : UF X.E (R.N i) × GLG (E := X.E) (n := R.N i) (SG := Pr.vGs) × GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) • p) =
      ((g, 1, 1) : FrmG (L.levG i al) (L.levQ i al)) • p := rfl
  have e2 : (((g', 1, 1) : UF X.E (R.N (i + 1)) × GLG (E := X.E) (n := R.N (i + 1)) (SG := Pr.vGs) × GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) • p') =
      ((g', 1, 1) : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)) • p' := rfl
  rw [e1, e2]
  obtain ⟨κ, c, hκ, hc, ec⟩ := exists_pass hd ((g, 1, 1) : FrmG (L.levG i al) (L.levQ i al)) p
  obtain ⟨κ', c', hκ', hc', ec'⟩ := exists_pass hd ((g', 1, 1) : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)) p'
  have key := GlobalTheory.MatLaw.xiEntry_law hX hPr hsel hL hi hκ hκ' hc hc' x (phiT_act _ _ _ _ _ _ _)
  rw [rho_pass_one i κ κ' (red_pass_one g p κ hκ) (red_pass_one g' p' κ' hκ'), mul_one, ec, ec'] at key
  rw [key]
  simp

end GlobalTheory.RatEntry

namespace GlobalTheory.RatEntry

theorem xiPt_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i < t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _hT i hi hlt β β' x x' p p' _hp _hp' g g' w
  unfold xiPt
  rw [dite_eq_left hlt, dite_eq_left hlt]
  exact GlobalTheory.RatEntry.xiEntry_rat hP.fields.ok t.pr_ok hP.sel ⟨hP.avoid.2, hP.avoid.1⟩ (t.idx_ok μ) hlt _ _ g g' p p' w

end GlobalTheory.RatEntry
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixStepDatumEquivariantRationalUnitary =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChangeIntertwinesRationalIsometries =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChangeIntertwinesRationalIsometries", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\nimport Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Coalgebra.CoassocSimps\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV

open scoped TensorProduct

section Alg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem coordRat_toLE_mul (g k : GL (Fin N) E) (v : Fin N → E) : toLE (g * k) v = toLE g (toLE k v) := by
  rw [toLE_apply, toLE_apply, toLE_apply, Units.val_mul, Matrix.mulVec_mulVec]

theorem coordRat_toLE_inv_apply (g : GL (Fin N) E) (v : Fin N → E) : toLE g⁻¹ (toLE g v) = v := by
  rw [← coordRat_toLE_mul, inv_mul_cancel, toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem coordRat_toLE_apply_inv (g : GL (Fin N) E) (v : Fin N → E) : toLE g (toLE g⁻¹ v) = v := by
  rw [← coordRat_toLE_mul, mul_inv_cancel, toLE_apply, Units.val_one, Matrix.one_mulVec]

theorem coordRat_toLE_symm (g : GL (Fin N) E) (v : Fin N → E) : (toLE g).symm v = toLE g⁻¹ v := by
  apply (toLE g).injective
  rw [LinearEquiv.apply_symm_apply, coordRat_toLE_apply_inv]

theorem coordRat_inFr {a b : ℕ} (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (co γ : GL (Fin a) E) (co' γ' : GL (Fin b) E) (z : (Fin a → E) →ₗ[E] (Fin b → E)) (v : Fin a → E) :
    inFr (toStdCo σ J co) (toStdCo σ J' co') (inFr (stdG σ J γ) (stdG σ J' γ') z) v =
      toLE (co' * γ' * co'⁻¹)⁻¹ (inFr (toStdCo σ J co) (toStdCo σ J' co') z (toLE (co * γ * co⁻¹) v)) := by
  simp only [inFr, toStdCo, stdG, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, coordRat_toLE_symm, LinearEquiv.symm_apply_apply,
    _root_.mul_inv_rev, inv_inv, coordRat_toLE_mul, coordRat_toLE_inv_apply]

end Alg

theorem seamHom_inFr_stdG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E) (γ' : GL (Fin (D.R.N (i + 1))) D.host.E)
      (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))),
      seamGL t.seam g.1 = A.crd i (Nat.le_of_succ_le hi) * γ * (A.crd i (Nat.le_of_succ_le hi))⁻¹ →
      seamGL t.seam g'.1 = A.crd (i + 1) hi * γ' * (A.crd (i + 1) hi)⁻¹ → ∀ z : HomE D.host.E (D.R.N i) (D.R.N (i + 1)),
      seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z) =
      g'.1.toLinearMap ∘ₗ seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi))
        (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
          (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)) ∘ₗ g.1.symm.toLinearMap) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ _ i hi γ γ' g g' hg hg' z
  have hS : ∀ {p q : ℕ} (x : HomE D.host.E p q) (w : Sp t.X.E p),
      (fun l => t.seam.iE (seamHom t.seam x w l)) = x (fun k => t.seam.iE (w k)) :=
    fun x w => funext (seamHom_apply t.seam x w)
  have hG : ∀ {n : ℕ} (h : Sp t.X.E n ≃ₗ[t.X.E] Sp t.X.E n) (v : Sp t.X.E n),
      (fun l => t.seam.iE (h v l)) = toLE (seamGL t.seam h) (fun l => t.seam.iE (v l)) := by
    intro n h v
    rw [toLE_apply, seamGL_mulVec]
  have hw : ∀ {n : ℕ} (h : Sp t.X.E n ≃ₗ[t.X.E] Sp t.X.E n) (v : Sp t.X.E n),
      (fun l => t.seam.iE (h.symm v l)) = toLE (seamGL t.seam h)⁻¹ (fun l => t.seam.iE (v l)) := by
    intro n h v
    apply (toLE (seamGL t.seam h)).injective
    rw [← hG, LinearEquiv.apply_symm_apply, coordRat_toLE_apply_inv]
  refine LinearMap.ext fun w => funext fun l => ?_
  have key : (fun l => t.seam.iE (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z) w l)) =
      (fun l => t.seam.iE (g'.1 (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi))
        (inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)
          (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ') z)) (g.1.symm w)) l)) := by
    rw [hG, hS, hS, hw, hg, hg', coordRat_inFr, coordRat_toLE_apply_inv, coordRat_toLE_apply_inv]
  exact t.seam.iE.injective (congrFun key l)

end GlobalTheory.TwV

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChangeIntertwinesRationalIsometries =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometry =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometry", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\nimport Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwLatRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem seam_lat_gmap {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) : s.lat (Formalism.HermitianLatticesTheory.gmap g N) = mvL (seamGL s g) (s.lat N) := by
  ext y
  rw [s.mem_lat]
  unfold mvL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Formalism.L2.Col.mem_gmap] at hx
    refine ⟨s.vec (g.symm x), (s.mem_lat N _).2 ⟨_, hx, rfl⟩, ?_⟩
    show (seamGL s g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (g.symm x l)) = fun l => s.iE (x l)
    rw [seamGL_mulVec, LinearEquiv.apply_symm_apply]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨x0, hx0, rfl⟩ := (s.mem_lat N w).1 hw
    refine ⟨g x0, ?_, ?_⟩
    · rw [Formalism.L2.Col.mem_gmap, LinearEquiv.symm_apply_apply]; exact hx0
    · show (fun l => s.iE (g x0 l)) = (seamGL s g : Matrix (Fin n) (Fin n) D.host.E) *ᵥ (fun l => s.iE (x0 l))
      rw [seamGL_mulVec]



theorem lat_moved : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → t.seam.lat ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x₁.1 ((St i hi).K β).lev.Lb) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a _ _ i hi β x x₁ γ hγ hx g hg p hp
  have e1 : ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = Formalism.HermitianLatticesTheory.gmap g.1 p.deco.1.N := rfl
  rw [e1, seam_lat_gmap, hg, hp.lat, hx, latCo_rat _ _ _ hγ]

end GlobalTheory.TwLatRat

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometry =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometryStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometryStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometry\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.pointLattice_moved_rational_isometry : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → t.seam.lat ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1.N = latCo D.sp (gramN D i hi) (A.crd i hi) a x₁.1 ((St i hi).K β).lev.Lb) := by
  first | exact @GlobalTheory.TwLatRat.lat_moved
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometryStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryAutColumnFieldOfStandardUnitaryMatr\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalCoordsConjUnitaryStandardForm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwRat

theorem ratUnitCol : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (γ : GL (Fin (D.R.N i)) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) →
      ∃ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹) := by
  intro D _ _ _ _ _ _ _ _ t u μ St A dtU a hP _ i hi γ hγ
  exact _root_.GlobalTheory.TwU.UnitaryFrom.exists_uf_seamGL_eq t.seam t.seam_ok (A.crd i hi * γ * (A.crd i hi)⁻¹)
    (GlobalTheory.unitary_conj_orthonormal D _ _ _ (hP.crd_orth i hi) hγ)

end GlobalTheory.TwRat
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChain =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChain", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveRationalIsometry\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepDatumRationalUnitaryEquivariant\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumEquivariantRationalUnitary\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometry\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MatrixStepDatumEquivariantRationalUnitary\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalChangeIntertwinesRationalIsometries\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointLatticeMovedRationalIsometryStatement\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalUnitaryOrthonormalCoordsIsColumnIsometry\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.RatPt

theorem isPtAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) ×
          GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp
  exact ⟨GlobalTheory.T.pointLattice_moved_rational_isometry A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp, _root_.GlobalTheory.RatFrame.frame_rat A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp,
    _root_.GlobalTheory.TwV.funMoved_ptAd_rat A dtU a hP hTie i hi β x x₁ γ hγ h₁ g hg p hp⟩

theorem xiPt_smul : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m) β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie i hi
  rcases lt_trichotomy i t.m2 with h | h | h
  · exact _root_.GlobalTheory.RatEntry.xiPt_rat A dtU a hP hTie i hi h
  · exact _root_.GlobalTheory.CplRat.xiPt_cpl_smul A dtU a hP hTie i hi h
  · exact _root_.GlobalTheory.TopRat.xiPt_top_smul A dtU a hP hTie i hi h

theorem ratLaw_of_tie : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    PtEx A a → (∀ i hi, PtAway A a i hi) → RatLaw A a) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hEx hAw
  intro i hi β β' x x' x₁ x₁' γ hγ γ' hγ' h₁ h₁' z
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.TwRat.ratUnitCol A dtU a hP hTie i (Nat.le_of_succ_le hi) γ hγ
  obtain ⟨g', hg'⟩ := _root_.GlobalTheory.TwRat.ratUnitCol A dtU a hP hTie (i + 1) hi γ' hγ'
  obtain ⟨p, hp⟩ := hEx i (Nat.le_of_succ_le hi) β x
  obtain ⟨p', hp'⟩ := hEx (i + 1) hi β' x'
  have hq := isPtAd_rat A dtU a hP hTie i (Nat.le_of_succ_le hi) β x x₁ γ hγ h₁ g hg p hp
  have hq' := isPtAd_rat A dtU a hP hTie (i + 1) hi β' x' x₁' γ' hγ' h₁' g' hg' p' hp'
  have hE1 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x₁' p' := ⟨⟨_, hq⟩, ⟨_, hq'⟩⟩
  have hE0 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨_, hp⟩, ⟨_, hp'⟩⟩
  have a1 := hAw i hi β β' x₁ x₁' x₁ x₁' _ _ _ _ hq hq' hE1.1.choose_spec hE1.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  have a0 := hAw i hi β β' x x' x x' _ _ _ _ hp hp' hE0.1.choose_spec hE0.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)
  unfold xiAd
  rw [dite_eq_left hE1, dite_eq_left hE0, a1, a0, _root_.GlobalTheory.TwV.seamHom_inFr_stdG A dtU a hP hTie i hi γ γ' g g' hg hg' z]
  rw [xiPt_smul A dtU a hP hTie i hi β β' x x' p p' hp hp' g g']

end GlobalTheory.RatPt

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicDatumRationalInvarianceOfKernelChain =====
