import NoCompromise.BV.TraceKernels

/-!
# Actual BV cut identities on flat interfaces

Smooth one-sided cutoffs are inserted into the original distributional pairing.
The boundary term converges to the constructed trace by the proved kernel
recovery theorem, including at hyperplanes carrying a derivative atom.
-/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def smoothLowerHalfspaceCutoff {n : ℕ} (j : ℕ) (a : ℝ)
    (z : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  Real.smoothTransition (((j : ℝ) + 1) * (a - z (Fin.last n)))

lemma contDiff_smoothLowerHalfspaceCutoff {n : ℕ} (j : ℕ) (a : ℝ) :
    ContDiff ℝ 1 (smoothLowerHalfspaceCutoff (n := n) j a) := by
  have hp : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z (Fin.last n)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).contDiff
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.mul (contDiff_const.sub hp))

lemma smoothLowerHalfspaceCutoff_bounds {n : ℕ} (j : ℕ) (a : ℝ)
    (z : EuclideanSpace ℝ (Fin (n + 1))) :
    0 ≤ smoothLowerHalfspaceCutoff j a z ∧ smoothLowerHalfspaceCutoff j a z ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma fderiv_smoothLowerHalfspaceCutoff {n : ℕ} (j : ℕ) (a : ℝ)
    (z v : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ (smoothLowerHalfspaceCutoff j a) z v =
      -smoothSuperlevelKernel ((j : ℝ) + 1) a (z (Fin.last n)) * v (Fin.last n) := by
  have hp := (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).hasFDerivAt (x := z)
  have hq := (hp.const_sub a).const_mul ((j : ℝ) + 1)
  have hd := (((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    (((j : ℝ) + 1) * (a - z (Fin.last n)))).hasDerivAt).comp_hasFDerivAt z hq
  change fderiv ℝ (Real.smoothTransition ∘ (fun z =>
    ((j : ℝ) + 1) * (a - (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)) z))) z v = _
  rw [hd.fderiv]
  simp only [smul_apply, neg_apply, smul_eq_mul, smoothSuperlevelKernel]
  change deriv Real.smoothTransition (((j : ℝ) + 1) * (a - z (Fin.last n))) *
    (((j : ℝ) + 1) * (-v (Fin.last n))) = _
  ring

lemma IsLocallyBVOn.flatBVLeftTrace_mul_continuous_ae {n : ℕ}
    {f φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : IsLocallyBVOn f univ)
    (hφ : Continuous φ) (a : ℝ) :
    flatBVLeftTrace (fun z => φ z * f z) a =ᵐ[volume]
      (fun x => φ (graphAppendN x a) * flatBVLeftTrace f a x) := by
  filter_upwards [hf.ae_line_oneSided_traces] with x hx
  have hc : Continuous (fun t : ℝ => φ (graphAppendN x t)) := by
    apply hφ.comp
    change Continuous (fun t : ℝ => graphBaseN n x + t • EuclideanSpace.single (Fin.last n) 1)
    fun_prop
  have ht : HasBVLeftTrace (fun t => φ (graphAppendN x t) * f (graphAppendN x t)) a
      (φ (graphAppendN x a) * flatBVLeftTrace f a x) :=
    ((hc.tendsto a).mono_left (inf_le_left.trans nhdsWithin_le_nhds)).mul (hx a).1
  exact ht.eq_bvLeftTrace

lemma tendsto_integral_smoothLowerHalfspaceCutoff {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))}
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hw : Integrable w μ) (a : ℝ) :
    Tendsto (fun j : ℕ => ∫ z, smoothLowerHalfspaceCutoff j a z * w z ∂μ) atTop
      (𝓝 (∫ z in {z | z (Fin.last n) < a}, w z ∂μ)) := by
  classical
  have hS : MeasurableSet {z : EuclideanSpace ℝ (Fin (n + 1)) | z (Fin.last n) < a} :=
    measurableSet_lt (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).measurable measurable_const
  rw [← integral_indicator hS]
  apply tendsto_integral_filter_of_dominated_convergence (fun z => |w z|)
  · exact Eventually.of_forall fun j =>
      ((contDiff_smoothLowerHalfspaceCutoff j a).continuous.aestronglyMeasurable.mul
        hw.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro j
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (smoothLowerHalfspaceCutoff_bounds j a z).1]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (smoothLowerHalfspaceCutoff_bounds j a z).2 (abs_nonneg (w z))
  · exact hw.abs
  · apply ae_of_all
    intro z
    have ht := (tendsto_smoothTransition_nat_mul_sub a (z (Fin.last n))).mul_const (w z)
    simpa only [smoothLowerHalfspaceCutoff, Set.indicator_apply, mem_ofPred_eq,
      ite_mul, one_mul, zero_mul] using ht

lemma fderiv_smoothLowerHalfspaceCutoff_mul {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (j : ℕ) (a : ℝ) (z v : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ (fun z => smoothLowerHalfspaceCutoff j a z * φ z) z v =
      smoothLowerHalfspaceCutoff j a z * fderiv ℝ φ z v -
        smoothSuperlevelKernel ((j : ℝ) + 1) a (z (Fin.last n)) * v (Fin.last n) * φ z := by
  have ht := (((contDiff_smoothLowerHalfspaceCutoff j a).differentiable one_ne_zero z).hasFDerivAt
    ).mul (hφ.differentiable one_ne_zero z).hasFDerivAt
  change fderiv ℝ (smoothLowerHalfspaceCutoff j a * φ) z v = _
  rw [ht.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [fderiv_smoothLowerHalfspaceCutoff]
  ring

/-- Cutting a genuine locally BV scalar function on a halfspace adds its actual one-sided trace.
The hypothesis is the original compact-C¹ distributional pairing, not a cut or trace identity. -/
theorem IsLocallyBVOn.flat_cut_directional_pairing {n : ℕ}
    {f w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))} (hf : IsLocallyBVOn f univ)
    (hw : LocallyIntegrable w μ) (v : EuclideanSpace ℝ (Fin (n + 1)))
    (hpair : ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        -(∫ z, f z * fderiv ℝ ψ z v) = ∫ z, ψ z * w z ∂μ)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (a : ℝ) :
    (∫ z in {z | z (Fin.last n) < a}, f z * fderiv ℝ φ z v) =
      -(∫ z in {z | z (Fin.last n) < a}, φ z * w z ∂μ) +
        v (Fin.last n) * ∫ x, φ (graphAppendN x a) * flatBVLeftTrace f a x := by
  have hfl : LocallyIntegrable f volume := locallyIntegrableOn_univ.mp hf.1
  have hcD : HasCompactSupport (fun z => fderiv ℝ φ z v) := hcφ.fderiv_apply ℝ v
  have hcontD : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hiA : Integrable (fun z => f z * fderiv ℝ φ z v) volume := by
    simpa only [smul_eq_mul] using
      hfl.integrable_smul_right_of_hasCompactSupport hcontD hcD
  have hiB : Integrable (fun z => φ z * w z) μ := by
    simpa only [smul_eq_mul, mul_comm] using
      hw.integrable_smul_right_of_hasCompactSupport hφ.continuous hcφ
  let A : ℕ → ℝ := fun j => ∫ z,
    smoothLowerHalfspaceCutoff j a z * (f z * fderiv ℝ φ z v)
  let B : ℕ → ℝ := fun j => ∫ z, smoothLowerHalfspaceCutoff j a z * (φ z * w z) ∂μ
  let C : ℕ → ℝ := fun j => ∫ z,
    smoothSuperlevelKernel ((j : ℝ) + 1) a (z (Fin.last n)) * (φ z * f z)
  have htA := tendsto_integral_smoothLowerHalfspaceCutoff hiA a
  have htB := tendsto_integral_smoothLowerHalfspaceCutoff hiB a
  have hg : IsBVOn (fun z => φ z * f z) univ :=
    hf.isBVOn_mul_compact_factor isOpen_univ hφ hcφ (subset_univ _)
  have htC := hg.tendsto_integral_smooth_normal_kernel a
  have htrace : (∫ x, flatBVLeftTrace (fun z => φ z * f z) a x) =
      ∫ x, φ (graphAppendN x a) * flatBVLeftTrace f a x :=
    integral_congr_ae (hf.flatBVLeftTrace_mul_continuous_ae hφ.continuous a)
  rw [htrace] at htC
  have hidentity (j : ℕ) : -(A j - v (Fin.last n) * C j) = B j := by
    have hiAj : Integrable (fun z => smoothLowerHalfspaceCutoff j a z *
        (f z * fderiv ℝ φ z v)) volume := by
      apply hiA.bdd_mul (contDiff_smoothLowerHalfspaceCutoff j a).continuous.aestronglyMeasurable
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (smoothLowerHalfspaceCutoff_bounds j a z).1]
        exact (smoothLowerHalfspaceCutoff_bounds j a z).2
    have hcK : Continuous (fun z : EuclideanSpace ℝ (Fin (n + 1)) =>
        smoothSuperlevelKernel ((j : ℝ) + 1) a (z (Fin.last n))) :=
      continuous_const.mul (continuous_deriv_smoothTransition.comp
        (continuous_const.mul (continuous_const.sub
          (EuclideanSpace.proj (𝕜 := ℝ) (Fin.last n)).continuous)))
    have hiCj : Integrable (fun z =>
        smoothSuperlevelKernel ((j : ℝ) + 1) a (z (Fin.last n)) * (φ z * f z)) volume := by
      have hcprod : HasCompactSupport (fun z =>
          smoothSuperlevelKernel ((j : ℝ) + 1) a (z (Fin.last n)) * φ z) := hcφ.mul_left
      simpa only [smul_eq_mul, Pi.mul_def, mul_assoc, mul_left_comm, mul_comm] using!
        hfl.integrable_smul_right_of_hasCompactSupport (hcK.mul hφ.continuous) hcprod
    have htest : ContDiff ℝ 1 (fun z => smoothLowerHalfspaceCutoff j a z * φ z) :=
      (contDiff_smoothLowerHalfspaceCutoff j a).mul hφ
    have hctest : HasCompactSupport (fun z => smoothLowerHalfspaceCutoff j a z * φ z) :=
      hcφ.mul_left
    have hi : (∫ z, f z *
        fderiv ℝ (fun z => smoothLowerHalfspaceCutoff j a z * φ z) z v) =
        A j - v (Fin.last n) * C j := by
      calc
        _ = ∫ z, smoothLowerHalfspaceCutoff j a z * (f z * fderiv ℝ φ z v) -
            v (Fin.last n) *
              (smoothSuperlevelKernel ((j : ℝ) + 1) a (z (Fin.last n)) * (φ z * f z)) := by
          apply integral_congr_ae
          exact ae_of_all _ fun z => by
            dsimp only
            rw [fderiv_smoothLowerHalfspaceCutoff_mul hφ]
            ring
        _ = _ := by rw [integral_sub hiAj (hiCj.const_mul _), integral_const_mul]
    calc
      _ = -(∫ z, f z * fderiv ℝ (fun z => smoothLowerHalfspaceCutoff j a z * φ z) z v) :=
        congrArg Neg.neg hi.symm
      _ = ∫ z, (smoothLowerHalfspaceCutoff j a z * φ z) * w z ∂μ := hpair _ htest hctest
      _ = B j := by simp only [B, mul_assoc]
  have hlim : Tendsto (fun j => -(A j - v (Fin.last n) * C j)) atTop
      (𝓝 (-((∫ z in {z | z (Fin.last n) < a}, f z * fderiv ℝ φ z v) -
        v (Fin.last n) * ∫ x, φ (graphAppendN x a) * flatBVLeftTrace f a x))) :=
    (htA.sub (htC.const_mul (v (Fin.last n)))).neg
  have hlim' : Tendsto B atTop
      (𝓝 (-((∫ z in {z | z (Fin.last n) < a}, f z * fderiv ℝ φ z v) -
        v (Fin.last n) * ∫ x, φ (graphAppendN x a) * flatBVLeftTrace f a x))) :=
    hlim.congr' (Eventually.of_forall hidentity)
  have he := tendsto_nhds_unique hlim' htB
  linarith

end LiquidDrop
