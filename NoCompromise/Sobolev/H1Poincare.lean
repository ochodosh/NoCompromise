module

public import NoCompromise.Sobolev.SpatialDomain
public import NoCompromise.Sobolev.H1Algebra

@[expose] public section

/-!
# The L² Poincaré inequality

Strong L² compactness and zero-gradient rigidity imply the mean-zero estimate.
This proves only the Poincaré clause of the blueprint's Poincaré-and-trace proposition.
-/

noncomputable section
open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Integration is continuous on L² over a finite measure space. -/
lemma continuous_integral_lp_two_finite {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    Continuous (fun u : Lp ℝ 2 μ => ∫ x, u x ∂μ) := by
  let one : Lp ℝ 2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) 1
  have heq (u : Lp ℝ 2 μ) : (∫ x, u x ∂μ) = inner ℝ one u := by
    simpa only [setIntegral_univ] using
      (L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top μ univ) u).symm
  simp_rw [heq]
  exact (innerSL ℝ one).continuous

/-- On a finite-volume connected open domain, zero weak gradient and zero mean force zero. -/
lemma HasH1GradientOn.ae_eq_zero_of_zero_gradient_integral {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hvol : volume D < ∞) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HasH1GradientOn f (fun _ => 0) D) (hmean : (∫ x in D, f x) = 0) :
    f =ᵐ[volume.restrict D] 0 := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  have hi : IntegrableOn f D := (hf.memLp_function.mono_exponent
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable (by norm_num)
  have hz : variation f D = 0 := by
    apply le_antisymm _ bot_le
    simpa using hf.toHasWeakGradientOn.variation_le
      (by simp : IntegrableOn (fun _ => (0 : EuclideanSpace ℝ (Fin n))) D)
  obtain ⟨c, hc⟩ := ae_eq_const_of_variation_eq_zero hD hcD
    hf.locallyIntegrable_function hz
  have heq : (∫ x in D, |f x|) = |∫ x in D, f x| := by
    have hcabs : (fun x => |f x|) =ᵐ[volume.restrict D] fun _ => |c| := hc.fun_comp abs
    rw [integral_congr_ae hcabs, integral_congr_ae hc]
    simp only [integral_const, smul_eq_mul, abs_mul, abs_of_nonneg measureReal_nonneg]
  rw [hmean, abs_zero] at heq
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg (f x)) hi.abs).mp heq
  filter_upwards [hae] with x hx
  exact abs_eq_zero.mp hx

/-- Strong L² sequential compactness of bounded H¹ sets gives mean-zero Poincaré. -/
theorem exists_h1_poincare_mean_zero_of_compactness {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hvol : volume D < ∞)
    (hcompact : ∀ u : ℕ → H1Space D, (∀ j, ‖u j‖ ≤ 2) →
      ∃ v : H1Space D, ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun j => (u (σ j)).toLp) atTop (𝓝 v.toLp)) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H1Space D, (∫ x in D, u x) = 0 →
      ‖u.toLp‖ ≤ C * ‖u.gradientLp‖ := by
  classical
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  by_contra! h
  have hbad (j : ℕ) := h ((j : ℝ) + 1) (by positivity)
  choose u hmean hbad using hbad
  let N (j : ℕ) := ‖(u j).toLp‖
  have hN (j) : 0 < N j :=
    (mul_nonneg (by positivity) (norm_nonneg _)).trans_lt (hbad j)
  let w (j : ℕ) := (N j)⁻¹ • u j
  have hmean' (j) : (∫ x in D, w j x) = 0 := by
    rw [integral_congr_ae (H1Space.coeFn_smul (N j)⁻¹ (u j)), integral_const_mul,
      hmean j, mul_zero]
  have hnorm (j) : ‖(w j).toLp‖ = 1 := by
    simp only [w, H1Space.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (hN j)]
    exact inv_mul_cancel₀ (hN j).ne'
  have hgrad (j) : ‖(w j).gradientLp‖ < 1 / ((j : ℝ) + 1) := by
    simp only [w, H1Space.gradientLp_smul, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (hN j)]
    rw [inv_mul_eq_div, div_lt_div_iff₀ (hN j) (by positivity)]
    simpa only [one_mul, mul_comm] using hbad j
  have hgradbound (j) : ‖(w j).gradientLp‖ ≤ 1 :=
    (hgrad j).le.trans (div_le_self (by norm_num) (by norm_num))
  have hgradlim : Tendsto (fun j => (w j).gradientLp) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun j => (hgrad j).le)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨v, σ, hσ, ht⟩ := hcompact w (fun j => by
    have h := (w j).norm_le_sum
    rw [hnorm j] at h
    linarith [hgradbound j])
  have hzero := hasH1GradientOn_of_tendsto_Lp
    (fun j => (w (σ j)).hasH1GradientOn) ht (hgradlim.comp hσ.tendsto_atTop)
  have hz : HasH1GradientOn v (fun _ => 0) D := hzero.congr_ae EventuallyEq.rfl
    (Lp.coeFn_zero (EuclideanSpace ℝ (Fin n)) 2 (volume.restrict D))
  have htmean :=
    (continuous_integral_lp_two_finite (volume.restrict D)).continuousAt.tendsto.comp ht
  change Tendsto (fun j => ∫ x in D, w (σ j) x) atTop (𝓝 (∫ x in D, v x)) at htmean
  simp_rw [hmean'] at htmean
  have hvmean : (∫ x in D, v x) = 0 := tendsto_nhds_unique htmean tendsto_const_nhds
  have hvzero := hz.ae_eq_zero_of_zero_gradient_integral hD hcD hvol hvmean
  have hvnorm : ‖v.toLp‖ = 0 := by
    rw [v.norm_toLp_eq_lpNorm]
    exact (lpNorm_eq_zero hz.memLp_function (by norm_num)).mpr hvzero
  have htnorm := ht.norm
  simp_rw [hnorm] at htnorm
  have hvone : ‖v.toLp‖ = 1 := tendsto_nhds_unique htnorm tendsto_const_nhds
  linarith

/-- Centering by the domain average gives the L² Poincaré estimate from compactness. -/
theorem exists_h1_poincare_of_compactness {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hcD : IsPreconnected D)
    (hvol : volume D < ∞)
    (hcompact : ∀ u : ℕ → H1Space D, (∀ j, ‖u j‖ ≤ 2) →
      ∃ v : H1Space D, ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun j => (u (σ j)).toLp) atTop (𝓝 v.toLp)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f G, HasH1GradientOn f G D →
      lpNorm (fun x => f x - ⨍ y in D, f y) 2 (volume.restrict D) ≤
        C * lpNorm G 2 (volume.restrict D) := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hvol⟩
  obtain ⟨C, hC, hb⟩ := exists_h1_poincare_mean_zero_of_compactness hD hcD hvol hcompact
  refine ⟨C, hC, fun f G hf => ?_⟩
  let c : ℝ := ⨍ y in D, f y
  have hc : HasH1GradientOn (fun _ => c) (fun _ => 0) D := by
    refine ⟨?_, memLp_const c, memLp_const (0 : EuclideanSpace ℝ (Fin n))⟩
    simpa only [gradient_fun_const'] using
      (hasWeakGradientOn_of_contDiffOn hD (contDiff_const (c := c)).contDiffOn)
  have hg : HasH1GradientOn (fun x => f x - c) G D := by
    simpa only [sub_zero] using hf.sub hc
  let u := H1Space.ofFunction (fun x => f x - c) G hg
  have hmean : (∫ x in D, u x) = 0 := by
    rw [integral_congr_ae (H1Space.coeFn_ofFunction _ _ hg)]
    exact setAverage_sub_setAverage hvol.ne f
  have hb' := hb u hmean
  have huf : ‖u.toLp‖ = lpNorm (fun x => f x - c) 2 (volume.restrict D) := by
    change ‖hg.memLp_function.toLp (fun x => f x - c)‖ = _
    rw [Lp.norm_toLp, toReal_eLpNorm]
  have huG : ‖u.gradientLp‖ = lpNorm G 2 (volume.restrict D) := by
    change ‖hg.memLp_gradient.toLp G‖ = _
    rw [Lp.norm_toLp, toReal_eLpNorm]
  rwa [huf, huG] at hb'

/-- L² Poincaré on every bounded connected open planar Lipschitz domain. -/
theorem h1_poincare_planar {D : Set (EuclideanSpace ℝ (Fin 2))}
    (hD : IsOpen D) (hcD : IsPreconnected D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f G, HasH1GradientOn f G D →
      lpNorm (fun x => f x - ⨍ y in D, f y) 2 (volume.restrict D) ≤
        C * lpNorm G 2 (volume.restrict D) := by
  apply exists_h1_poincare_of_compactness hD hcD hbD.measure_lt_top
  intro u hu
  obtain ⟨v, σ, hσ, _, _, ht⟩ := exists_subseq_weak_h1_strong_l2_planar hD hbD hL u hu
  exact ⟨v, σ, hσ, ht⟩

/-- The Poincaré clause of blueprint `prop:poincare-trace`, on every bounded
connected open spatial Lipschitz domain. No boundary-trace statement is asserted here. -/
theorem h1_poincare_spatial {D : Set (EuclideanSpace ℝ (Fin 3))}
    (hD : IsOpen D) (hcD : IsPreconnected D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ C : ℝ, 0 < C ∧ ∀ f G, HasH1GradientOn f G D →
      lpNorm (fun x => f x - ⨍ y in D, f y) 2 (volume.restrict D) ≤
        C * lpNorm G 2 (volume.restrict D) := by
  apply exists_h1_poincare_of_compactness hD hcD hbD.measure_lt_top
  intro u hu
  obtain ⟨v, σ, hσ, _, _, ht⟩ := exists_subseq_weak_h1_strong_l2_spatial hD hbD hL u hu
  exact ⟨v, σ, hσ, ht⟩

end LiquidDrop
