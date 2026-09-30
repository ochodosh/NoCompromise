module

public import NoCompromise.CapacitaryK.KelvinNormalization
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

@[expose] public section

/-!
# The normalized translated quadrupole

Chapter 31, `lem:K-normalization`: the translated quadrupole is a continuous,
homogeneous harmonic quadratic with zero spherical mean.
-/

noncomputable section

open Set Filter Metric InnerProductSpace MeasureTheory
open scoped Topology Gradient RealInnerProductSpace Pointwise

namespace LiquidDrop.CapacitaryK

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private def quadrupoleSphereEquiv (e : E₃ ≃ₗᵢ[ℝ] E₃) :
    sphere (0 : E₃) 1 ≃ₜ sphere (0 : E₃) 1 where
  toFun θ := ⟨e θ, by simpa only [mem_sphere_zero_iff_norm, e.norm_map] using θ.property⟩
  invFun θ := ⟨e.symm θ, by
    simpa only [mem_sphere_zero_iff_norm, e.symm.norm_map] using θ.property⟩
  left_inv θ := Subtype.ext (e.symm_apply_apply θ)
  right_inv θ := Subtype.ext (e.apply_symm_apply θ)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

private theorem quadrupoleSphereEquiv_measurePreserving (e : E₃ ≃ₗᵢ[ℝ] E₃) :
    MeasurePreserving (quadrupoleSphereEquiv e)
      (volume : Measure E₃).toSphere (volume : Measure E₃).toSphere := by
  refine ⟨(quadrupoleSphereEquiv e).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (quadrupoleSphereEquiv e).measurable hs,
    Measure.toSphere_apply' _ ((quadrupoleSphereEquiv e).measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hcone : Ioo (0 : ℝ) 1 • (Subtype.val '' (quadrupoleSphereEquiv e ⁻¹' s)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, _, ⟨θ, hθ, rfl⟩, rfl⟩
      exact ⟨r, hr, e θ, ⟨quadrupoleSphereEquiv e θ, hθ, rfl⟩, (e.map_smul r θ).symm⟩
    · rintro ⟨r, hr, _, ⟨θ, hθ, rfl⟩, hx⟩
      refine ⟨r, hr, e.symm θ, ⟨(quadrupoleSphereEquiv e).symm θ, ?_, rfl⟩, ?_⟩
      · simpa using hθ
      · apply e.injective
        simpa using hx
  rw [hcone]
  exact e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding _

private theorem quadrupoleSphere_mixed_moment (i j : Fin 3) (hij : i ≠ j) :
    ∫ θ : sphere (0 : E₃) 1, (θ : E₃) i * (θ : E₃) j
      ∂(volume : Measure E₃).toSphere = 0 := by
  let e : E₃ ≃ₗᵢ[ℝ] E₃ := LinearIsometryEquiv.piLpCongrRight 2
    (fun k : Fin 3 => if k = i then LinearIsometryEquiv.neg ℝ else .refl ℝ ℝ)
  have h := (quadrupoleSphereEquiv_measurePreserving e).integral_comp
    (quadrupoleSphereEquiv e).measurableEmbedding (fun θ => (θ : E₃) i * (θ : E₃) j)
  have he (θ : sphere (0 : E₃) 1) :
      (quadrupoleSphereEquiv e θ : E₃) i * (quadrupoleSphereEquiv e θ : E₃) j =
        -((θ : E₃) i * (θ : E₃) j) := by
    simp [quadrupoleSphereEquiv, e, hij.symm]
  simp_rw [he, integral_neg] at h
  linarith

private theorem quadrupoleSphere_diagonal_moment (i j : Fin 3) :
    (∫ θ : sphere (0 : E₃) 1, (θ : E₃) i * (θ : E₃) i
      ∂(volume : Measure E₃).toSphere) =
    ∫ θ : sphere (0 : E₃) 1, (θ : E₃) j * (θ : E₃) j
      ∂(volume : Measure E₃).toSphere := by
  let e : E₃ ≃ₗᵢ[ℝ] E₃ := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  have h := (quadrupoleSphereEquiv_measurePreserving e).integral_comp
    (quadrupoleSphereEquiv e).measurableEmbedding (fun θ => (θ : E₃) j * (θ : E₃) j)
  simpa [quadrupoleSphereEquiv, e, Equiv.piCongrLeft'] using h

private theorem quadrupole_bilinear_expansion
    (B : E₃ →L[ℝ] E₃ →L[ℝ] ℝ) (x : E₃) :
    B x x = ∑ i : Fin 3, ∑ j : Fin 3,
      B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * (x i * x j) := by
  have hx : (∑ i : Fin 3, x i • EuclideanSpace.single i 1) = x := by
    simpa using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  calc
    B x x = B (∑ i : Fin 3, x i • EuclideanSpace.single i 1)
        (∑ j : Fin 3, x j • EuclideanSpace.single j 1) := by rw [hx]
    _ = _ := by
      simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- A trace-free continuous bilinear form has zero spherical mean on the diagonal. -/
theorem integral_toSphere_bilinear_eq_zero (B : E₃ →L[ℝ] E₃ →L[ℝ] ℝ)
    (hB : ∑ i : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 0) :
    ∫ θ, B (θ : E₃) θ ∂(volume : Measure E₃).toSphere = 0 := by
  have hint (i j : Fin 3) : Integrable
      (fun θ : sphere (0 : E₃) 1 =>
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
          ((θ : E₃) i * (θ : E₃) j)) (volume : Measure E₃).toSphere := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact HasCompactSupport.of_compactSpace _
  simp_rw [quadrupole_bilinear_expansion]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j), integral_const_mul]
  have hmoment (i : Fin 3) :
      (∑ j : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
        ∫ θ : sphere (0 : E₃) 1, (θ : E₃) i * (θ : E₃) j
          ∂(volume : Measure E₃).toSphere) =
      B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) *
        ∫ θ : sphere (0 : E₃) 1, (θ : E₃) 0 * (θ : E₃) 0
          ∂(volume : Measure E₃).toSphere := by
    rw [Finset.sum_eq_single i]
    · rw [quadrupoleSphere_diagonal_moment i 0]
    · intro j _ hji
      rw [quadrupoleSphere_mixed_moment i j hji.symm, mul_zero]
    · simp
  simp_rw [hmoment]
  rw [← Finset.sum_mul, hB, zero_mul]

/-- The translated quadrupole is homogeneous of degree two, including when `v 0 = 0`. -/
theorem kelvinTranslatedQuadrupole_smul (v : E₃ → ℝ) (c : ℝ) (x : E₃) :
    kelvinTranslatedQuadrupole v (c • x) = c ^ 2 * kelvinTranslatedQuadrupole v x := by
  simp only [kelvinTranslatedQuadrupole, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, map_smul, smul_apply,
    smul_eq_mul]
  ring

/-- The translated quadrupole is continuous, without any regularity assumption on `v`. -/
theorem continuous_kelvinTranslatedQuadrupole (v : E₃ → ℝ) :
    Continuous (kelvinTranslatedQuadrupole v) := by
  unfold kelvinTranslatedQuadrupole
  fun_prop

private def quadrupoleBilinear (v : E₃ → ℝ) : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
  let innerB : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := innerSL ℝ
  (-(2 * v 0)⁻¹) •
    ((3 : ℝ) • (innerSL ℝ (gradient v 0)).smulRight (innerSL ℝ (gradient v 0)) -
      ‖gradient v 0‖ ^ 2 • innerB) +
    (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ v) 0

private theorem quadrupoleBilinear_diag (v : E₃ → ℝ) (x : E₃) :
    quadrupoleBilinear v x x = kelvinTranslatedQuadrupole v x := by
  change (-(2 * v 0)⁻¹) *
      (3 * (⟪gradient v 0, x⟫ * ⟪gradient v 0, x⟫) -
        ‖gradient v 0‖ ^ 2 * ⟪x, x⟫) +
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ v) 0 x x = kelvinTranslatedQuadrupole v x
  rw [real_inner_self_eq_norm_sq]
  unfold kelvinTranslatedQuadrupole
  ring

private theorem quadrupoleBilinear_trace {v : E₃ → ℝ}
    (htr : ∑ i : Fin 3, fderiv ℝ (fderiv ℝ v) 0
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 0) :
    ∑ i : Fin 3, quadrupoleBilinear v
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 0 := by
  have hnorm (i : Fin 3) : ‖(EuclideanSpace.single i 1 : E₃)‖ = 1 := by simp
  simp only [quadrupoleBilinear_diag, kelvinTranslatedQuadrupole,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, hnorm, one_pow, mul_one,
    Finset.sum_add_distrib, ← Finset.mul_sum, htr, mul_zero, add_zero,
    ← Finset.sum_div]
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← EuclideanSpace.real_norm_sq_eq]
  simp

/-- A trace-free Hessian gives a translated quadrupole with zero spherical mean. -/
theorem kelvinTranslatedQuadrupole_sphere_mean_zero {v : E₃ → ℝ}
    (htr : ∑ i : Fin 3, fderiv ℝ (fderiv ℝ v) 0
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 0) :
    ∫ θ, kelvinTranslatedQuadrupole v (θ : E₃) ∂(volume : Measure E₃).toSphere = 0 := by
  simpa only [quadrupoleBilinear_diag] using
    integral_toSphere_bilinear_eq_zero (quadrupoleBilinear v) (quadrupoleBilinear_trace htr)

private theorem quadrupole_bilinear_laplacian
    (B : E₃ →L[ℝ] E₃ →L[ℝ] ℝ) (x : E₃) :
    laplacianN (fun y => B y y) x =
      2 * ∑ i : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  have hd (i : Fin 3) : poissonCoordinateDerivative i (fun y => B y y) =
      fun y => B y (EuclideanSpace.single i 1) + B (EuclideanSpace.single i 1) y := by
    funext y
    unfold poissonCoordinateDerivative
    have h := B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
    simp only [id_eq] at h
    rw [h.fderiv]
    simp
  have hd2 (i : Fin 3) :
      poissonCoordinateDerivative i (poissonCoordinateDerivative i (fun y => B y y)) x =
        2 * B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    rw [hd]
    unfold poissonCoordinateDerivative
    change fderiv ℝ (fun y => B.flip (EuclideanSpace.single i 1) y +
      B (EuclideanSpace.single i 1) y) x _ = _
    rw [((B.flip (EuclideanSpace.single i 1)).hasFDerivAt.fun_add
      (B (EuclideanSpace.single i 1)).hasFDerivAt).fderiv]
    simp [two_mul]
  simp only [laplacianN, hd2, Finset.mul_sum]

/-- A trace-free Hessian gives a harmonic translated quadrupole everywhere. -/
theorem kelvinTranslatedQuadrupole_laplacian {v : E₃ → ℝ}
    (htr : ∑ i : Fin 3, fderiv ℝ (fderiv ℝ v) 0
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 0) (x : E₃) :
    laplacianN (kelvinTranslatedQuadrupole v) x = 0 := by
  have hQ : kelvinTranslatedQuadrupole v = fun y => quadrupoleBilinear v y y := by
    funext y
    exact (quadrupoleBilinear_diag v y).symm
  rw [hQ, quadrupole_bilinear_laplacian, quadrupoleBilinear_trace htr, mul_zero]

/-- `lem:K-normalization`: the translated capacitary expansion has a continuous,
two-homogeneous harmonic quadrupole with zero spherical mean. -/
theorem capacitary_translated_expansion_normalized
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ (v : E₃ → ℝ) (r : ℝ), 0 < r ∧ ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r) ∧
      EqOn v (kelvinTransform u) (ball 0 r \ {0}) ∧ (∀ y ∈ ball 0 r, laplacianN v y = 0) ∧
      0 < v 0 ∧
      Continuous (kelvinTranslatedQuadrupole v) ∧
      (∀ (c : ℝ) (x : E₃),
        kelvinTranslatedQuadrupole v (c • x) = c ^ 2 * kelvinTranslatedQuadrupole v x) ∧
      (∀ x : E₃, laplacianN (kelvinTranslatedQuadrupole v) x = 0) ∧
      (∫ θ, kelvinTranslatedQuadrupole v (θ : E₃) ∂(volume : Measure E₃).toSphere = 0) ∧
      ∃ R M : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
        |u (x + (v 0)⁻¹ • gradient v 0) - v 0 / ‖x‖ -
          kelvinTranslatedQuadrupole v x / ‖x‖ ^ 5| ≤ M / ‖x‖ ^ 4 := by
  obtain ⟨v, r, hr, hv, he, hharm, hC, hexp⟩ :=
    capacitary_translated_expansion hK hR₀ hKR hzero hu hh hb hinf
  have htr := kelvin_quadrupole_trace_zero
    ((hv.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).of_le (by simp))
    (hharm 0 (mem_ball_self hr))
  exact ⟨v, r, hr, hv, he, hharm, hC, continuous_kelvinTranslatedQuadrupole v,
    kelvinTranslatedQuadrupole_smul v, kelvinTranslatedQuadrupole_laplacian htr,
    kelvinTranslatedQuadrupole_sphere_mean_zero htr, hexp⟩

end LiquidDrop.CapacitaryK
