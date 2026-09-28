import NoCompromise.Elliptic.Caccioppoli
import NoCompromise.Elliptic.SobolevChainHarmonic
import NoCompromise.Elliptic.HarmonicMeanValue
import NoCompromise.Elliptic.WeakMaximumCore

/-!
# The weak Laplace equation for a continuous harmonic function

A continuous distributionally harmonic function on an open set satisfies the weak Laplace
equation `div(∇u) = 0` against C¹ compactly supported tests (`IsWeakDivergenceEquationOn` with
identity coefficient). The boundary Caccioppoli bound for the capacitary potential built on it is
in `HullPotentialCaccioppoliBound.lean`.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A product of a function continuous on an open set with a compactly supported continuous
function supported in that set is integrable. -/
private lemma hull_caccioppoli_integrable_mul {V : Set (EuclideanSpace ℝ (Fin 3))}
    (hV : IsOpen V) {a b : EuclideanSpace ℝ (Fin 3) → ℝ} (ha : ContinuousOn a V)
    (hb : Continuous b) (hcb : HasCompactSupport b) (hsb : tsupport b ⊆ V) :
    Integrable (fun x => a x * b x) :=
  ((ha.mul hb.continuousOn).continuous_of_tsupport_subset hV
    (tsupport_mul_subset_right.trans hsb)).integrable_of_hasCompactSupport hcb.mul_left

/-- For a C² function on an open set, the Dirichlet pairing against a C¹ test supported in the
set is minus the pairing of the test with the classical Laplacian. -/
private lemma hull_caccioppoli_integral_inner_gradient {V : Set (EuclideanSpace ℝ (Fin 3))}
    (hV : IsOpen V) {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : ContDiffOn ℝ 2 u V)
    {φ : EuclideanSpace ℝ (Fin 3) → ℝ} (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ V) :
    (∫ x in V, inner ℝ (gradient u x) (gradient φ x)) =
      -∫ x in V, φ x * laplacianN u x := by
  have hd : ∀ i : Fin 3, ContDiffOn ℝ 1 (poissonCoordinateDerivative i u) V := by
    intro i
    have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y) V := hu.fderiv_of_isOpen hV (by norm_num)
    exact h1.clm_apply contDiffOn_const
  have hdd : ∀ i : Fin 3, ContinuousOn
      (poissonCoordinateDerivative i (poissonCoordinateDerivative i u)) V := by
    intro i
    exact ((hd i).continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
  have hφd : ∀ i : Fin 3, Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    fun i => (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcφd : ∀ i : Fin 3, HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    fun i => HasCompactSupport.fderiv_apply ℝ hcφ _
  have hsφd : ∀ i : Fin 3, tsupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) ⊆ V :=
    fun i => (tsupport_fderiv_apply_subset ℝ _).trans hsφ
  have hi1 : ∀ i : Fin 3, Integrable (fun x => poissonCoordinateDerivative i u x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    fun i => hull_caccioppoli_integrable_mul hV (hd i).continuousOn (hφd i) (hcφd i) (hsφd i)
  have hi2 : ∀ i : Fin 3, Integrable (fun x => φ x *
      poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x) := by
    intro i
    have h := hull_caccioppoli_integrable_mul hV (hdd i) hφ.continuous hcφ hsφ
    simpa only [mul_comm] using h
  have hpt : ∀ x, inner ℝ (gradient u x) (gradient φ x) =
      ∑ i : Fin 3, poissonCoordinateDerivative i u x *
        fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    intro x
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      gradient_apply_eq_fderiv_single, poissonCoordinateDerivative]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hlap : ∀ x, φ x * laplacianN u x = ∑ i : Fin 3, φ x *
      poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x := by
    intro x
    rw [laplacianN, Finset.mul_sum]
  simp_rw [hpt, hlap]
  rw [integral_finsetSum _ (fun i _ => (hi1 i).integrableOn),
    integral_finsetSum _ (fun i _ => (hi2 i).integrableOn), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw := (hasWeakGradientOn_of_contDiffOn hV (hd i)).test_eq i φ hφ hcφ hsφ
  have he : ∀ x, gradient (poissonCoordinateDerivative i u) x i =
      poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x :=
    fun x => gradient_apply_eq_fderiv_single _ x i
  simp only [he] at hw
  linarith

/-- A continuous distributionally harmonic function solves the weak Laplace equation
`div(∇u) = 0` against C¹ tests. -/
theorem isWeakDivergenceEquationOn_id_of_harmonic {V : Set (EuclideanSpace ℝ (Fin 3))}
    (hV : IsOpen V) {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : ContinuousOn u V)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) V) :
    IsWeakDivergenceEquationOn (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)))
      (gradient u) (fun _ => 0) V := by
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u V := hh.contDiffOn_of_continuous (by norm_num) hV hu
  have hu2 : ContDiffOn ℝ 2 u V := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hlc : ContinuousOn (laplacianN u) V := by
    have hd : ∀ i : Fin 3, ContDiffOn ℝ 1 (poissonCoordinateDerivative i u) V := by
      intro i
      have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ u y) V := hu2.fderiv_of_isOpen hV (by norm_num)
      exact h1.clm_apply contDiffOn_const
    have hdd : ∀ i : Fin 3, ContinuousOn
        (poissonCoordinateDerivative i (poissonCoordinateDerivative i u)) V := by
      intro i
      exact ((hd i).continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
    have h : ContinuousOn (fun x => ∑ i : Fin 3,
        poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x) V :=
      continuousOn_finsetSum _ fun i _ => hdd i
    exact h
  -- the classical Laplacian vanishes almost everywhere on `V`
  have hae : ∀ᵐ x ∂volume, x ∈ V → laplacianN u x = 0 := by
    apply hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hlc.locallyIntegrableOn hV.measurableSet)
    intro ψ hψ hcψ hsψ
    have hw := (hasWeakGradientOn_of_contDiffOn hV
      (hu2.of_le (by norm_num))).integral_mul_laplacianN (hψ.of_le (by simp)) hcψ hsψ
    have ht := hh.test_eq ψ hψ hcψ hsψ
    have hI := hull_caccioppoli_integral_inner_gradient hV hu2 (hψ.of_le (by simp)) hcψ hsψ
    simp only [zero_mul, integral_zero] at ht
    have hV0 : (∫ x in V, ψ x * laplacianN u x) = 0 := by linarith
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := V) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsψ h)), zero_smul])]
    simpa only [smul_eq_mul] using hV0
  intro φ hφ hcφ hsφ
  have hI := hull_caccioppoli_integral_inner_gradient hV hu2 hφ hcφ hsφ
  have hz : (∫ x in V, φ x * laplacianN u x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [(ae_restrict_iff' hV.measurableSet).mpr hae] with x hx
    rw [hx, mul_zero, Pi.zero_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := V) (fun x hx => by
    rw [gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h)), inner_zero_right])]
  simp only [ContinuousLinearMap.id_apply, sub_zero]
  rw [hI, hz, neg_zero]

end LiquidDrop
