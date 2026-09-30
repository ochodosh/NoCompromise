module

public import NoCompromise.Sobolev.H1Zero
public import NoCompromise.Elliptic.Caccioppoli
public import NoCompromise.DeGiorgi.SmoothGraph

@[expose] public section

/-!
# Flat integration by parts for the actual H¹ trace

Strong H¹ mollification and strong L² trace convergence pass the classical
half-space identity to arbitrary H¹ functions. Zero trace removes the boundary
term and gives the weak gradient of the genuine zero extension.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology Gradient Convolution
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma tendsto_setIntegral_inner_of_eLpNorm_sub {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}
    {F : α → E} {g : ℕ → α → E} {G : α → E} {A : Set α}
    (hA : MeasurableSet A) (hF : MemLp F 2 μ) (hg : ∀ j, MemLp (g j) 2 μ)
    (hG : MemLp G 2 μ)
    (ht : Tendsto (fun j => eLpNorm (g j - G) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in A, inner ℝ (F x) (g j x) ∂μ) atTop
      (𝓝 (∫ x in A, inner ℝ (F x) (G x) ∂μ)) := by
  have h := tendsto_integral_inner_of_eLpNorm_sub (μ := μ)
    (F := A.indicator F) (g := g) (G := G) (hF.indicator hA) hg hG ht
  have heq (q : α → E) : (fun x => inner ℝ (A.indicator F x) (q x)) =
      A.indicator (fun x => inner ℝ (F x) (q x)) := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  simpa only [heq, integral_indicator hA] using h

lemma smooth_h1_lowerHalfspace_pairing {k : ℕ}
    {f φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hf : ContDiff ℝ 1 f) (hmf : MemLp f 2 volume)
    (hmg : MemLp (gradient f) 2 volume)
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (i : Fin (k + 1)) :
    (∫ z in smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)),
        f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) +
      (∫ z in smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)),
        inner ℝ (φ z • EuclideanSpace.single i 1) (gradient f z)) =
      (EuclideanSpace.single i (1 : ℝ) (Fin.last k)) *
        ∫ x, φ (graphAppendN x 0) * f (graphAppendN x 0) := by
  have hdφ : Continuous (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hmD := hdφ.memLp_of_hasCompactSupport (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1))
    (p := (2 : ℝ≥0∞)) (μ := volume)
  have hmX : MemLp (fun z => φ z • EuclideanSpace.single i (1 : ℝ)) 2 volume :=
    (hφ.continuous.smul continuous_const).memLp_of_hasCompactSupport hcφ.smul_right
  have hi1 := (hmf.integrable_mul hmD).integrableOn
    (s := smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)))
  change IntegrableOn (fun z => f z * fderiv ℝ φ z (EuclideanSpace.single i 1))
    (smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ))) volume at hi1
  have hi2 := (integrable_inner_of_memLp_two hmX hmg).integrableOn
    (s := smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)))
  have heq (z) : fderiv ℝ (fun y => f y * φ y) z (EuclideanSpace.single i 1) =
      f z * fderiv ℝ φ z (EuclideanSpace.single i 1) +
        inner ℝ (φ z • EuclideanSpace.single i 1) (gradient f z) := by
    rw [fderiv_fun_mul (hf.differentiable one_ne_zero z) (hφ.differentiable one_ne_zero z)]
    simp only [add_apply, smul_apply, smul_eq_mul, inner_smul_left,
      EuclideanSpace.inner_single_left, map_one, one_mul, gradient_apply_eq_fderiv_single,
      starRingEnd_apply, star_trivial]
  have h := smoothSubgraph_directional_pairing
    (f := fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)) contDiff_const
    (hf.mul hφ) hcφ.mul_left (EuclideanSpace.single i 1)
  simp_rw [heq] at h
  rw [integral_add hi1 hi2] at h
  simpa only [fderiv_const_apply, zero_apply, sub_zero, graphMapN, zero_smul,
    add_zero, graphAppendN, mul_comm, integral_const_mul] using h

/-- The exact half-space identity for the constructed L² trace, without smoothness
of the H¹ representative. -/
theorem HasH1GradientOn.lowerHalfspace_trace_pairing {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ)
    {φ : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hcφ : HasCompactSupport φ) (i : Fin (k + 1)) :
    (∫ z in smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)),
        f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) +
      (∫ z in smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)),
        inner ℝ (φ z • EuclideanSpace.single i 1) (G z)) =
      (EuclideanSpace.single i (1 : ℝ) (Fin.last k)) *
        ∫ x, φ (graphAppendN x 0) * flatTraceFunction f G x := by
  let A := smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ))
  have hA : MeasurableSet A := (isOpen_smoothSubgraph continuous_const).measurableSet
  let b (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin (k + 1))) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hb : Tendsto (fun j => (b j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let u (j : ℕ) := (b j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f
  have hu (j : ℕ) := hf.bump_convolution (b j)
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  have hmu (j : ℕ) : MemLp (u j) 2 volume := by
    simpa only [Measure.restrict_univ] using (hu j).2.2.1.memLp_function
  have hmgu (j : ℕ) : MemLp (gradient (u j)) 2 volume := by
    rw [funext (hu j).2.1]
    simpa only [Measure.restrict_univ] using (hu j).2.2.1.memLp_gradient
  have hconv := hf.tendsto_bump_convolution hb
  have hdφ : Continuous (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hmD : MemLp (fun z => fderiv ℝ φ z (EuclideanSpace.single i 1)) 2 volume :=
    hdφ.memLp_of_hasCompactSupport (hcφ.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hmX : MemLp (fun z => φ z • EuclideanSpace.single i (1 : ℝ)) 2 volume :=
    (hφ.continuous.smul continuous_const).memLp_of_hasCompactSupport hcφ.smul_right
  have hL : Tendsto (fun j => ∫ z in A, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1))
      atTop (𝓝 (∫ z in A, f z * fderiv ℝ φ z (EuclideanSpace.single i 1))) := by
    simpa only [Real.inner_apply, mul_comm] using
      (tendsto_setIntegral_inner_of_eLpNorm_sub (F := fun z =>
        fderiv ℝ φ z (EuclideanSpace.single i 1)) (g := u) (G := f)
        hA hmD hmu hmf hconv.1)
  have hR := tendsto_setIntegral_inner_of_eLpNorm_sub
    (F := fun z => φ z • EuclideanSpace.single i (1 : ℝ))
    (g := fun j => gradient (u j)) (G := G) hA hmX hmgu hmG hconv.2
  have hcφb : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin k) => φ (graphAppendN x 0)) := by
    change HasCompactSupport (φ ∘ graphMapN (fun _ => (0 : ℝ)))
    exact hcφ.comp_isClosedEmbedding (isClosedEmbedding_smoothGraphMap continuous_const)
  have hmφb : MemLp (fun x : EuclideanSpace ℝ (Fin k) => φ (graphAppendN x 0)) 2 volume := by
    have hc := hφ.continuous.comp (isClosedEmbedding_smoothGraphMap
      (f := fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)) continuous_const).continuous
    exact hc.memLp_of_hasCompactSupport hcφb
  have hmub (j : ℕ) : MemLp (fun x => u j (graphAppendN x 0)) 2 volume :=
    (memLp_restrict_plane_of_continuous_h1 (hu j).2.2.1 (hu j).1.continuous).1
  have hmT := (memLp_flatTraceFunction hmf hmG).1
  have ht : Tendsto (fun j => eLpNorm
      ((fun x => u j (graphAppendN x 0)) - flatTraceFunction f G) 2 volume)
      atTop (𝓝 0) := by
    have ht := (ENNReal.continuous_ofReal.tendsto 0).comp
      (hf.tendsto_flatTrace_bump_convolution hb)
    change Tendsto (fun j => ENNReal.ofReal (lpNorm
      ((fun x => u j (graphAppendN x 0)) - flatTraceFunction f G) 2 volume))
      atTop (𝓝 (ENNReal.ofReal 0)) at ht
    simpa only [ENNReal.ofReal_zero, ofReal_lpNorm ((hmub _).sub hmT)] using ht
  have hB : Tendsto (fun j => ∫ x, φ (graphAppendN x 0) * u j (graphAppendN x 0))
      atTop (𝓝 (∫ x, φ (graphAppendN x 0) * flatTraceFunction f G x)) := by
    simpa only [Real.inner_apply, mul_comm] using
      (tendsto_integral_inner_of_eLpNorm_sub (F := fun x => φ (graphAppendN x 0))
        (g := fun j x => u j (graphAppendN x 0)) (G := flatTraceFunction f G)
        hmφb hmub hmT ht)
  have hleft := hL.add hR
  have hright := hB.const_mul (EuclideanSpace.single i (1 : ℝ) (Fin.last k))
  have heq : (fun j => (∫ z in A, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)) +
      ∫ z in A, inner ℝ (φ z • EuclideanSpace.single i 1) (gradient (u j) z)) =
      (fun j => (EuclideanSpace.single i (1 : ℝ) (Fin.last k)) *
        ∫ x, φ (graphAppendN x 0) * u j (graphAppendN x 0)) := by
    funext j
    exact smooth_h1_lowerHalfspace_pairing ((hu j).1.of_le (by simp)) (hmu j) (hmgu j) hφ hcφ i
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- Zero actual flat trace makes the lower-half-space cut a genuine H¹ function,
with precisely the restricted original weak gradient. -/
theorem HasH1GradientOn.indicator_lowerHalfspace_of_flatTrace_zero {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hT : flatTraceFunction f G =ᵐ[volume] 0) :
    HasH1GradientOn
      ((smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ))).indicator f)
      ((smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ))).indicator G) univ := by
  let A := smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ))
  have hA : MeasurableSet A := (isOpen_smoothSubgraph continuous_const).measurableSet
  have hmf : MemLp f 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_function
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hf.memLp_gradient
  apply hasH1GradientOn_of_memLp_test
    (by simpa only [Measure.restrict_univ] using hmf.indicator hA)
    (by simpa only [Measure.restrict_univ] using hmG.indicator hA)
  intro i φ hφ hcφ _
  have hpair := hf.lowerHalfspace_trace_pairing hφ hcφ i
  have hzero : (∫ x, φ (graphAppendN x 0) * flatTraceFunction f G x) = 0 := by
    have heq : (fun x => φ (graphAppendN x 0) * flatTraceFunction f G x) =ᵐ[volume] 0 :=
      hT.mono fun x hx => by simp [hx]
    simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae heq
  rw [hzero, mul_zero] at hpair
  simp only [inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul,
    starRingEnd_apply, star_trivial] at hpair
  have hL (z) : A.indicator f z * fderiv ℝ φ z (EuclideanSpace.single i 1) =
      A.indicator (fun y => f y * fderiv ℝ φ y (EuclideanSpace.single i 1)) z := by
    by_cases hz : z ∈ A <;> simp [hz]
  have hR (z) : φ z * A.indicator G z i = A.indicator (fun y => φ y * G y i) z := by
    by_cases hz : z ∈ A <;> simp [hz]
  change -(∫ z in univ, A.indicator f z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
    ∫ z in univ, φ z * A.indicator G z i
  simp_rw [hL, hR]
  rw [setIntegral_univ, setIntegral_univ, integral_indicator hA, integral_indicator hA]
  linarith

/-- The corresponding zero extension from the open upper half-space. The plane
itself has zero ambient volume, so the representative there is immaterial. -/
theorem HasH1GradientOn.indicator_upperHalfspace_of_flatTrace_zero {k : ℕ}
    {f : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    (hf : HasH1GradientOn f G univ) (hT : flatTraceFunction f G =ᵐ[volume] 0) :
    HasH1GradientOn
      ((smoothEpigraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ))).indicator f)
      ((smoothEpigraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ))).indicator G) univ := by
  have h := hf.sub (hf.indicator_lowerHalfspace_of_flatTrace_zero hT)
  have hAE := smoothEpigraph_ae_compl
    (f := fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)) continuous_const
  apply h.congr_ae
  · filter_upwards [ae_restrict_of_ae hAE] with z hz
    have hu : z ∈ smoothEpigraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)) ↔
        z ∉ smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)) := Iff.of_eq hz
    by_cases hx : z ∈ smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ))
    · simp [hx, show z ∉ smoothEpigraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)) from
        fun hz' => (hu.mp hz') hx]
    · simp [hx, hu.mpr hx]
  · filter_upwards [ae_restrict_of_ae hAE] with z hz
    have hu : z ∈ smoothEpigraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)) ↔
        z ∉ smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)) := Iff.of_eq hz
    by_cases hx : z ∈ smoothSubgraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ))
    · simp [hx, show z ∉ smoothEpigraph (fun _ : EuclideanSpace ℝ (Fin k) => (0 : ℝ)) from
        fun hz' => (hu.mp hz') hx]
    · simp [hx, hu.mpr hx]

end LiquidDrop
