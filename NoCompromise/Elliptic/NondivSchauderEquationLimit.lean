module

public import NoCompromise.Elliptic.NondivSchauderWeakLimit
public import NoCompromise.Elliptic.NondivSchauderTests

@[expose] public section

/-!
# Passing variable-coefficient weak equations to the limit

The hypotheses record actual L² functions, bounded weak convergence of the
unknown fields, uniform coefficient convergence, and strong L² convergence of
the constructed data. The conclusion is the genuine compact-test equation.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma nondiv_lpNorm_le_mul_of_ae_bound {X E F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure X} {f : X → E} {g : X → F}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ C * ‖g x‖) : lpNorm f 2 μ ≤ C * lpNorm g 2 μ := by
  have hs : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖C • g x‖ := by
    simpa only [norm_smul, Real.norm_of_nonneg hC] using hb
  have ht := ENNReal.toReal_mono (hg.const_smul C).eLpNorm_ne_top
    (eLpNorm_mono_ae hf.aestronglyMeasurable hs)
  rw [toReal_eLpNorm, toReal_eLpNorm] at ht
  simpa only [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg hC] using ht

/-- Uniform coefficient convergence is strong convergence of every adjoint L²
test field. This holds on arbitrary measures, including unbounded domains. -/
lemma nondiv_tendsto_adjoint_testLp {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {A : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {A₀ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ∀ j, AEStronglyMeasurable (A j) μ) (hA₀ : AEStronglyMeasurable A₀ μ)
    (hP : MemLp P 2 μ) {cap : ℝ}
    (hbA : ∀ j, ∀ᵐ x ∂μ, ‖A j x‖ ≤ cap) (hbA₀ : ∀ᵐ x ∂μ, ‖A₀ x‖ ≤ cap)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 ≤ ε j) (htε : Tendsto ε atTop (𝓝 0))
    (he : ∀ j, ∀ᵐ x ∂μ, ‖A j x - A₀ x‖ ≤ ε j) :
    ∃ (hQ : ∀ j, MemLp (fun x => (A j x).adjoint (P x)) 2 μ)
      (hQ₀ : MemLp (fun x => (A₀ x).adjoint (P x)) 2 μ),
      Tendsto (fun j => (hQ j).toLp (fun x => (A j x).adjoint (P x))) atTop
        (𝓝 (hQ₀.toLp (fun x => (A₀ x).adjoint (P x)))) := by
  have hadj := (ContinuousLinearMap.adjoint (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin n)) (F := EuclideanSpace ℝ (Fin n))).continuous
  have hQ (j : ℕ) : MemLp (fun x => (A j x).adjoint (P x)) 2 μ :=
    campanato_memLp_apply_bounded (hadj.comp_aestronglyMeasurable (hA j)) hP
      (by simpa only [LinearIsometryEquiv.norm_map] using hbA j)
  have hQ₀ : MemLp (fun x => (A₀ x).adjoint (P x)) 2 μ :=
    campanato_memLp_apply_bounded (hadj.comp_aestronglyMeasurable hA₀) hP
      (by simpa only [LinearIsometryEquiv.norm_map] using hbA₀)
  refine ⟨hQ, hQ₀, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn (j : ℕ) : ‖(hQ j).toLp (fun x => (A j x).adjoint (P x)) -
      hQ₀.toLp (fun x => (A₀ x).adjoint (P x))‖ ≤ ε j * lpNorm P 2 μ := by
    rw [← MemLp.toLp_sub, Lp.norm_toLp, toReal_eLpNorm]
    apply nondiv_lpNorm_le_mul_of_ae_bound ((hQ j).sub hQ₀) hP (hε j)
    filter_upwards [he j] with x hx
    change ‖(A j x).adjoint (P x) - (A₀ x).adjoint (P x)‖ ≤ _
    rw [← sub_apply, ← map_sub]
    exact ((A j x - A₀ x).adjoint.le_opNorm (P x)).trans
      (by simpa only [LinearIsometryEquiv.norm_map] using
        mul_le_mul_of_nonneg_right hx (norm_nonneg (P x)))
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall hn)
  simpa only [zero_mul] using htε.mul_const (lpNorm P 2 μ)

/-- Weak convergence of the unknown fields passes through uniformly convergent
bounded coefficient fields in every actual L² integral pairing. -/
theorem nondiv_tendsto_integral_variable_flux {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {A : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {A₀ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {D₀ P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ∀ j, AEStronglyMeasurable (A j) μ) (hA₀ : AEStronglyMeasurable A₀ μ)
    (hD : ∀ j, MemLp (D j) 2 μ) (hP : MemLp P 2 μ)
    {cap M : ℝ} (hbA : ∀ j, ∀ᵐ x ∂μ, ‖A j x‖ ≤ cap)
    (hbA₀ : ∀ᵐ x ∂μ, ‖A₀ x‖ ≤ cap) (hbD : ∀ j, lpNorm (D j) 2 μ ≤ M)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 ≤ ε j) (htε : Tendsto ε atTop (𝓝 0))
    (he : ∀ j, ∀ᵐ x ∂μ, ‖A j x - A₀ x‖ ≤ ε j)
    (hw : ∀ Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), MemLp Q 2 μ →
      Tendsto (fun j => ∫ x, inner ℝ (Q x) (D j x) ∂μ) atTop
        (𝓝 (∫ x, inner ℝ (Q x) (D₀ x) ∂μ))) :
    Tendsto (fun j => ∫ x, inner ℝ (A j x (D j x)) (P x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (A₀ x (D₀ x)) (P x) ∂μ)) := by
  obtain ⟨hQ, hQ₀, htQ⟩ := nondiv_tendsto_adjoint_testLp hA hA₀ hP hbA hbA₀ hε htε he
  let u (j : ℕ) := (hD j).toLp (D j)
  let v (j : ℕ) := (hQ j).toLp (fun x => (A j x).adjoint (P x))
  let v₀ := hQ₀.toLp (fun x => (A₀ x).adjoint (P x))
  have hbu (j : ℕ) : ‖u j‖ ≤ M := by
    simpa only [u, Lp.norm_toLp, toReal_eLpNorm] using hbD j
  have herr : Tendsto (fun j => inner ℝ (v j - v₀) (u j)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun j => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hbu j) (norm_nonneg _)))
    simpa only [v, v₀, sub_self, norm_zero, zero_mul] using!
      ((htQ.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => v₀) atTop (𝓝 v₀))).norm.mul_const M)
  have hfixed : Tendsto (fun j => inner ℝ v₀ (u j)) atTop
      (𝓝 (∫ x, inner ℝ ((A₀ x).adjoint (P x)) (D₀ x) ∂μ)) := by
    simpa only [v₀, u, inner_toLp_eq_integral_inner] using hw _ hQ₀
  have ht := herr.add hfixed
  simp only [inner_sub_left, sub_add_cancel, zero_add, v, u,
    inner_toLp_eq_integral_inner, ContinuousLinearMap.adjoint_inner_left] at ht
  simpa only [real_inner_comm] using ht

/-- Restrict a compact-test integral to the test domain without any integrability
assumption on the field outside that domain. -/
lemma nondiv_integral_flux_restrict {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hsφ : tsupport φ ⊆ U) :
    (∫ x, inner ℝ (F x) (gradient φ x)) = ∫ x in U, inner ℝ (F x) (gradient φ x) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [gradient_eq_zero_of_notMem_tsupport (fun h => hx (hsφ h)), inner_zero_right]

/-- Stability of the actual divergence equation under weak L² convergence of
bounded gradients, uniform coefficient convergence, and strong L² source
convergence. All hypotheses concern the constructed functions themselves. -/
theorem nondiv_weakDivergenceEquation_limit {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {A : ℕ → EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {A₀ : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D G : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {D₀ G₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hA : ∀ j, AEStronglyMeasurable (A j) (volume.restrict U))
    (hA₀ : AEStronglyMeasurable A₀ (volume.restrict U))
    (hD : ∀ j, MemLp (D j) 2 (volume.restrict U))
    (hD₀ : MemLp D₀ 2 (volume.restrict U))
    (hG : ∀ j, MemLp (G j) 2 (volume.restrict U))
    (hG₀ : MemLp G₀ 2 (volume.restrict U))
    {cap M : ℝ} (hbA : ∀ j, ∀ᵐ x ∂volume.restrict U, ‖A j x‖ ≤ cap)
    (hbA₀ : ∀ᵐ x ∂volume.restrict U, ‖A₀ x‖ ≤ cap)
    (hbD : ∀ j, lpNorm (D j) 2 (volume.restrict U) ≤ M)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 ≤ ε j) (htε : Tendsto ε atTop (𝓝 0))
    (hcoeff : ∀ j, ∀ᵐ x ∂volume.restrict U, ‖A j x - A₀ x‖ ≤ ε j)
    (hw : ∀ P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      MemLp P 2 (volume.restrict U) →
      Tendsto (fun j => ∫ x in U, inner ℝ (P x) (D j x)) atTop
        (𝓝 (∫ x in U, inner ℝ (P x) (D₀ x))))
    (hstrong : Tendsto (fun j => eLpNorm (fun x => G j x - G₀ x) 2 (volume.restrict U))
      atTop (𝓝 0))
    (he : ∀ j, IsWeakDivergenceEquationOn (A j) (D j) (G j) U) :
    IsWeakDivergenceEquationOn A₀ D₀ G₀ U := by
  intro φ hφ hcφ hsφ
  have hP : MemLp (gradient φ) 2 (volume.restrict U) := by
    have hp := (nondiv_hasH1GradientOn_compact_test hφ hcφ).memLp_gradient
    rw [Measure.restrict_univ] at hp
    exact hp.mono_measure Measure.restrict_le_self
  have hL := nondiv_tendsto_integral_variable_flux hA hA₀ hD hP hbA hbA₀ hbD
    hε htε hcoeff hw
  have htG : Tendsto (fun j => (hG j).toLp (G j)) atTop (𝓝 (hG₀.toLp G₀)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' G hG G₀ hG₀).mpr
    simpa only [Pi.sub_apply] using! hstrong
  have hR : Tendsto (fun j => ∫ x in U, inner ℝ (G j x) (gradient φ x)) atTop
      (𝓝 (∫ x in U, inner ℝ (G₀ x) (gradient φ x))) := by
    have ht := ((innerSL ℝ (hP.toLp (gradient φ))).continuous.tendsto (hG₀.toLp G₀)).comp htG
    simpa only [Function.comp_def, innerSL_apply_apply, inner_toLp_eq_integral_inner,
      real_inner_comm] using! ht
  have hj (j : ℕ) : (∫ x in U, inner ℝ (A j x (D j x)) (gradient φ x)) =
      ∫ x in U, inner ℝ (G j x) (gradient φ x) := by
    have h := he j φ hφ hcφ hsφ
    rw [nondiv_integral_flux_restrict _ hsφ] at h
    simp_rw [inner_sub_left] at h
    rw [integral_sub
      (integrable_inner_of_memLp_two (campanato_memLp_apply_bounded (hA j) (hD j) (hbA j)) hP)
      (integrable_inner_of_memLp_two (hG j) hP)] at h
    exact sub_eq_zero.mp h
  have hlim := tendsto_nhds_unique (hL.congr' (Eventually.of_forall hj)) hR
  rw [nondiv_integral_flux_restrict _ hsφ]
  simp_rw [inner_sub_left]
  rw [integral_sub
    (integrable_inner_of_memLp_two (campanato_memLp_apply_bounded hA₀ hD₀ hbA₀) hP)
    (integrable_inner_of_memLp_two hG₀ hP), hlim, sub_self]

/-- Uniform convergence of a.e.-strongly measurable errors on a finite measure space gives
the actual strong L² convergence. -/
lemma nondiv_tendsto_eLpNorm_of_uniform_error {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X → F} {g : X → F} {ε : ℕ → ℝ}
    (ht : Tendsto ε atTop (𝓝 0))
    (hm : ∀ j, AEStronglyMeasurable (fun x => f j x - g x) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, ‖f j x - g x‖ ≤ ε j) :
    Tendsto (fun j => eLpNorm (fun x => f j x - g x) 2 μ) atTop (𝓝 0) := by
  have hof : Tendsto (fun j => ENNReal.ofReal (ε j)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ht
  have hfin : μ univ ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ)
  have hlim := ENNReal.Tendsto.const_mul hof (Or.inr hfin)
  simp only [mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro j
  simpa only [ENNReal.toReal_ofNat, one_div] using (eLpNorm_le_of_ae_bound (p := 2) (hm j) (hb j))

end LiquidDrop
