import NoCompromise.Surface.HeightMorse
import NoCompromise.Area.Sphere
import NoCompromise.Area.Cofactor

/-!
# Morse height functions

* `lem:morse-height` (PARTIAL): for every unit `v` such that `v` and `-v` are regular values of
  the Gauss map, the height `h_v` is Morse with finitely many critical points, all in
  `n⁻¹{v} ∪ n⁻¹{-v}` (`morse_height_of_regular`, proved). The almost-everywhere clause
  (`ae_morse_height_of_sard_charts`) takes the almost-everywhere regularity of the Gauss map
  (`cor:sard-charts`, proved for abstract manifolds but not yet bridged to embedded surfaces and
  `hausdorffMeasure2`) as a named hypothesis, and derives from it that almost every `v` has
  both `v` and `-v` regular, via the antipodal invariance of `H²` on the sphere.
* `lem:morse-distinct`: `exists_morse_distinct_critical_values`. The finiteness of the critical
  set used implicitly by the blueprint ("write the critical points as `p₁,…,p_k`") is proved:
  nondegenerate critical points are isolated (`finite_criticalPoints_of_isSurfaceMorse`, via
  `inner_fderiv_surfaceGradient`: the derivative of the tangential gradient is the surface
  Hessian).
* `lem:morse-band` (ingredients, PARTIAL): the band field `X = ∇_Σ h / |∇_Σ h|²`
  (`bandField`) is smooth on an open neighbourhood of the regular part of the surface, tangent to
  the surface, satisfies `dh(X) = 1` (`eq:band-derivative`), and `h` increases with unit speed
  along its integral curves in the surface. The product diffeomorphism `Θ` itself is not yet
  assembled here; see `Surface/MorseBand.lean` (`morse_band`).
* `lem:one-manifold`, last clause (ingredient): `levelTangentField = n × ∇_Σ h`, the rotation of
  the tangential gradient by `π/2`, is tangent to the surface and to the level sets of `h`, with
  the same norm as `∇_Σ h`, hence nowhere zero on a regular level. The classification of
  one-manifolds itself is not formalized.
-/

noncomputable section
open Set Function InnerProductSpace MeasureTheory Filter
open scoped Topology
namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- At a regular value the fibre of the Gauss map of a compact surface is finite. -/
theorem finite_gaussMap_fiber {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n) {y : E₃}
    (hy : IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y) :
    {p ∈ S | n p = y}.Finite :=
  finite_fiber_of_isSurfaceRegularValue hS (isSmoothEmbeddedSurface_sphere one_pos) hc
    (fun p hp => by simpa using (hn.2 p hp).1)
    (fun p hp => (hn.contDiffAt hp).differentiableAt (by simp)) hy

/-- The critical set of a Morse height function on a compact surface is finite. -/
theorem finite_criticalPoints_height {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {v : E₃} (hv : ‖v‖ = 1)
    (hreg : IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n v)
    (hreg' : IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n (-v)) :
    {p | IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p}.Finite := by
  rw [setOf_isSurfaceCriticalPoint_height hS hn hv]
  exact (finite_gaussMap_fiber hS hc hn hreg).union (finite_gaussMap_fiber hS hc hn hreg')

/-- lem:morse-height, pointwise clause: if `v` and `-v` are regular values of the Gauss map of a
compact surface, then `h_v` is Morse with finitely many critical points, all in `n⁻¹{±v}`. -/
theorem morse_height_of_regular {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {v : E₃} (hv : ‖v‖ = 1)
    (hreg : IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n v)
    (hreg' : IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n (-v)) :
    IsSurfaceMorse S n (fun x => inner ℝ x v) ∧
      {p | IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p}.Finite ∧
      {p | IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p} ⊆ n ⁻¹' {v} ∪ n ⁻¹' {-v} := by
  refine ⟨(isSurfaceMorse_height_iff hS hn hv).mpr ⟨hreg, hreg'⟩,
    finite_criticalPoints_height hS hc hn hv hreg hreg', ?_⟩
  rw [setOf_isSurfaceCriticalPoint_height hS hn hv]
  exact union_subset_union inter_subset_right inter_subset_right

/-- The antipodal map preserves `H²` restricted to the unit sphere. -/
theorem measurePreserving_neg_sphere :
    MeasurePreserving (fun y : E₃ => -y)
      ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1))
      ((hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1)) := by
  let e : E₃ ≃ᵢ E₃ := (LinearIsometryEquiv.neg ℝ : E₃ ≃ₗᵢ[ℝ] E₃).toIsometryEquiv
  have hsph : MeasurableSet (Metric.sphere (0 : E₃) 1) := Metric.isClosed_sphere.measurableSet
  have hpre : e ⁻¹' Metric.sphere (0 : E₃) 1 = Metric.sphere (0 : E₃) 1 := by
    ext y
    change -y ∈ Metric.sphere (0 : E₃) 1 ↔ y ∈ Metric.sphere (0 : E₃) 1
    simp
  have h1 := (e.measurePreserving_euclideanHausdorffMeasure 2).restrict_preimage hsph
  rw [hpre] at h1
  exact h1

/-- lem:morse-height, PARTIAL: given almost-everywhere regularity of the Gauss map
(`cor:sard-charts`, named hypothesis `h_sard_charts`), for almost every `v ∈ S²` both `v` and `-v`
are regular values and `h_v` is Morse with finitely many critical points, all in `n⁻¹{±v}`. -/
theorem ae_morse_height_of_sard_charts {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    (h_sard_charts : ∀ᵐ y ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n y) :
    ∀ᵐ v ∂(hausdorffMeasure2 3).restrict (Metric.sphere (0 : E₃) 1),
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n v ∧
      IsSurfaceRegularValue S (Metric.sphere (0 : E₃) 1) n (-v) ∧
      IsSurfaceMorse S n (fun x => inner ℝ x v) ∧
      {p | IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p}.Finite ∧
      {p | IsSurfaceCriticalPoint S (fun x => inner ℝ x v) p} ⊆ n ⁻¹' {v} ∪ n ⁻¹' {-v} := by
  have hsph : MeasurableSet (Metric.sphere (0 : E₃) 1) := Metric.isClosed_sphere.measurableSet
  have hneg := measurePreserving_neg_sphere.quasiMeasurePreserving.ae h_sard_charts
  filter_upwards [h_sard_charts, hneg, ae_restrict_mem hsph] with v hv hv' hvm
  have hv1 : ‖v‖ = 1 := by simpa using hvm
  exact ⟨hv, hv', morse_height_of_regular hS hc hn hv1 hv hv'⟩

/-- Tangential projection `g ↦ g - ⟪ν, g⟫ ν`. -/
def tangentialProj (ν g : E₃) : E₃ := g - inner ℝ ν g • ν

/-- The tangential gradient `∇_Σ f = ∇f - ⟪n, ∇f⟫ n`. -/
def surfaceGradient (n : E₃ → E₃) (f : E₃ → ℝ) (x : E₃) : E₃ :=
  tangentialProj (n x) (gradient f x)

lemma tangentialProj_add (ν g w : E₃) :
    tangentialProj ν (g + w) = tangentialProj ν g + tangentialProj ν w := by
  simp only [tangentialProj, inner_add_right, add_smul]
  abel

lemma norm_tangentialProj_le {ν : E₃} (hν : ‖ν‖ = 1) (g : E₃) :
    ‖tangentialProj ν g‖ ≤ 2 * ‖g‖ := by
  unfold tangentialProj
  calc ‖g - inner ℝ ν g • ν‖ ≤ ‖g‖ + ‖inner ℝ ν g • ν‖ := norm_sub_le _ _
    _ ≤ ‖g‖ + ‖g‖ := by
        rw [norm_smul, hν, mul_one, Real.norm_eq_abs]
        gcongr
        simpa [hν] using abs_real_inner_le_norm ν g
    _ = 2 * ‖g‖ := by ring

/-- On the surface, `p` is critical for `f|_S` iff the tangential gradient vanishes. -/
theorem isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {f : E₃ → ℝ} {x : E₃}
    (hx : x ∈ S) : IsSurfaceCriticalPoint S f x ↔ surfaceGradient n f x = 0 := by
  have hν : ‖n x‖ = 1 := (hn.2 x hx).1
  have hT : ∀ X, X ∈ tangentPlane S x ↔ inner ℝ (n x) X = 0 := fun X => by
    rw [hn.tangentPlane_eq hS hx, Submodule.mem_orthogonal_singleton_iff_inner_right]
  have hd : ∀ X, fderiv ℝ f x X = inner ℝ (gradient f x) X := fun X => by
    rw [gradient, toDual_symm_apply]
  set g := gradient f x
  set X := surfaceGradient n f x with hXdef
  have hXT : inner ℝ (n x) X = 0 := by
    simp only [hXdef, surfaceGradient, tangentialProj, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hν]
    ring
  constructor
  · intro hc
    have h0 : inner ℝ g X = 0 := by rw [← hd]; exact hc.2 X ((hT X).mpr hXT)
    have hXX : inner ℝ X X = 0 := by
      have : X = g - inner ℝ (n x) g • n x := rfl
      calc inner ℝ X X = inner ℝ (g - inner ℝ (n x) g • n x) X := by rw [← this]
        _ = 0 := by rw [inner_sub_left, real_inner_smul_left, h0, hXT]; ring
    exact inner_self_eq_zero.mp hXX
  · intro h0
    refine ⟨hx, fun Y hY => ?_⟩
    have hY' : inner ℝ (n x) Y = 0 := (hT Y).mp hY
    have hg : g = X + inner ℝ (n x) g • n x := by
      simp only [hXdef, surfaceGradient, tangentialProj]
      abel
    rw [hd, hg, h0, zero_add, real_inner_smul_left, hY', mul_zero]

/-- The derivative of the tangential gradient, paired with a tangent vector, is the surface
Hessian. -/
theorem inner_fderiv_surfaceGradient {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ}
    (hh : ContDiff ℝ 2 h) {p : E₃} (hp : p ∈ S) (u Y : E₃) (hY : Y ∈ tangentPlane S p) :
    inner ℝ (fderiv ℝ (surfaceGradient n h) p u) Y = surfaceHessian n h p u Y := by
  have hY' : inner ℝ (n p) Y = 0 := by
    rw [hn.tangentPlane_eq hS hp, Submodule.mem_orthogonal_singleton_iff_inner_right] at hY
    exact hY
  have hfd : DifferentiableAt ℝ (fderiv ℝ h) p :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by simp) p
  let G : E₃ →L[ℝ] E₃ :=
    (toDual ℝ E₃).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (fderiv ℝ (fderiv ℝ h) p)
  have hgrad : HasFDerivAt (gradient h) G p := by
    have : gradient h = fun x => (toDual ℝ E₃).symm (fderiv ℝ h x) := rfl
    rw [this]
    exact (toDual ℝ E₃).symm.toContinuousLinearEquiv.hasFDerivAt.comp p hfd.hasFDerivAt
  have hnd : HasFDerivAt n (fderiv ℝ n p) p :=
    ((hn.contDiffAt hp).differentiableAt (by simp)).hasFDerivAt
  have hsgd : DifferentiableAt ℝ (surfaceGradient n h) p := by
    have h1 := hgrad.differentiableAt
    have h2 := hnd.differentiableAt
    exact h1.sub ((h2.inner ℝ h1).smul h2)
  let ℓ : ℝ → E₃ := fun t => p + t • u
  have hℓ : HasDerivAt ℓ u 0 := by
    change HasDerivAt (fun t : ℝ => p + t • u) u 0
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
  have hℓ0 : ℓ 0 = p := by simp [ℓ]
  have hA : HasDerivAt (fun t => gradient h (ℓ t)) (G u) 0 :=
    hgrad.comp_hasDerivAt_of_eq 0 hℓ hℓ0.symm
  have hB : HasDerivAt (fun t => n (ℓ t)) (fderiv ℝ n p u) 0 :=
    hnd.comp_hasDerivAt_of_eq 0 hℓ hℓ0.symm
  have hcomb := hA.sub ((hB.inner ℝ hA).smul hB)
  have hsg : HasDerivAt (fun t => surfaceGradient n h (ℓ t))
      (fderiv ℝ (surfaceGradient n h) p u) 0 :=
    hsgd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hℓ hℓ0.symm
  have huniq := hsg.unique hcomb
  rw [huniq]
  simp only [hℓ0]
  rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hY', mul_zero,
    add_zero]
  have hG : inner ℝ (G u) Y = fderiv ℝ (fderiv ℝ h) p u Y := by
    change inner ℝ ((toDual ℝ E₃).symm (fderiv ℝ (fderiv ℝ h) p u)) Y = _
    rw [toDual_symm_apply]
  have hdn : fderiv ℝ h p (n p) = inner ℝ (n p) (gradient h p) := by
    rw [real_inner_comm, gradient, toDual_symm_apply]
  rw [hG, surfaceHessian, hdn, secondFundamentalForm, shapeOperator]

/-- Nondegenerate critical points are isolated: a Morse function on a compact surface has
finitely many critical points. -/
theorem finite_criticalPoints_of_isSurfaceMorse {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ 2 h) (hM : IsSurfaceMorse S n h) :
    {p | IsSurfaceCriticalPoint S h p}.Finite := by
  by_contra hinf
  obtain ⟨p, hp, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hc
    (show {p | IsSurfaceCriticalPoint S h p} ⊆ S from fun _ h => h.1)
  have hcl : p ∈ closure ({p | IsSurfaceCriticalPoint S h p} \ {p}) :=
    (accPt_principal_iff_clusterPt.mp hacc).mem_closure
  obtain ⟨q, hqmem, hq⟩ := mem_closure_iff_seq_limit.mp hcl
  have hqS (k : ℕ) : q k ∈ S := (hqmem k).1.1
  have hqz (k : ℕ) : surfaceGradient n h (q k) = 0 :=
    (isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn (hqS k)).mp (hqmem k).1
  have hqne (k : ℕ) : q k ≠ p := (hqmem k).2
  have hgradc : Continuous (gradient h) := by
    have : gradient h = fun x => (toDual ℝ E₃).symm (fderiv ℝ h x) := rfl
    rw [this]
    exact (toDual ℝ E₃).symm.continuous.comp (hh.continuous_fderiv (by norm_num))
  have hnc : ContinuousAt n p := (hn.contDiffAt hp).continuousAt
  have hsgc : ContinuousAt (surfaceGradient n h) p := by
    have h1 := hgradc.continuousAt (x := p)
    exact h1.sub ((hnc.inner h1).fun_smul hnc)
  have hp0 : surfaceGradient n h p = 0 := by
    have := (hsgc.tendsto.comp hq)
    simp only [Function.comp_def, hqz] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hpc : IsSurfaceCriticalPoint S h p :=
    (isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn hp).mpr hp0
  have hunit (k : ℕ) : ‖q k - p‖⁻¹ • (q k - p) ∈ Metric.sphere (0 : E₃) 1 := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hqne k))]
  obtain ⟨u, huunit, r, hr, hu⟩ := (isCompact_sphere (0 : E₃) 1).tendsto_subseq hunit
  have hqr : Tendsto (q ∘ r) atTop (𝓝 p) := hq.comp hr.tendsto_atTop
  have huT : u ∈ tangentPlane S p :=
    mem_tangentPlane_of_tendsto_normalized_secant hp (fun k => hqS (r k)) hqr hu
  have hsgd : DifferentiableAt ℝ (surfaceGradient n h) p := by
    have hfd : DifferentiableAt ℝ (fderiv ℝ h) p :=
      (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by simp) p
    have h1 : DifferentiableAt ℝ (gradient h) p := by
      have : gradient h = fun x => (toDual ℝ E₃).symm (fderiv ℝ h x) := rfl
      rw [this]
      exact (toDual ℝ E₃).symm.toContinuousLinearEquiv.differentiableAt.comp p hfd
    have h2 : DifferentiableAt ℝ n p := (hn.contDiffAt hp).differentiableAt (by simp)
    exact h1.sub ((h2.inner ℝ h1).smul h2)
  have hdu : fderiv ℝ (surfaceGradient n h) p u = 0 :=
    fderiv_eq_zero_of_tendsto_normalized_secant hsgd hqr
      (Eventually.of_forall fun k => (hqz (r k)).trans hp0.symm) hu
  have hzero := hM p hpc ⟨u, huT⟩ (fun Y => by
    change surfaceHessian n h p u Y = 0
    rw [← inner_fderiv_surfaceGradient hS hn hh hp u Y Y.property, hdu, inner_zero_left])
  have hu0 : u = 0 := congrArg Subtype.val hzero
  simp [hu0] at huunit

/-- lem:morse-distinct: a smooth Morse function on a compact surface can be perturbed to a
smooth Morse function with the same critical points, the same Hessians
there (hence the same indices), and pairwise distinct critical values. -/
theorem exists_morse_distinct_critical_values {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S) (hn : IsUnitNormalField S n)
    {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hM : IsSurfaceMorse S n h) :
    ∃ h' : E₃ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h' ∧
      (∀ x, IsSurfaceCriticalPoint S h' x ↔ IsSurfaceCriticalPoint S h x) ∧
      (∀ p, IsSurfaceCriticalPoint S h p →
        tangentHessian S n h' p = tangentHessian S n h p ∧
          surfaceIndex S n h' p = surfaceIndex S n h p) ∧
      IsSurfaceMorse S n h' ∧ InjOn h' {p | IsSurfaceCriticalPoint S h p} := by
  classical
  have hfin : {p | IsSurfaceCriticalPoint S h p}.Finite :=
    finite_criticalPoints_of_isSurfaceMorse hS hc hn (hh.of_le (by norm_cast)) hM
  set F := hfin.toFinset with hF
  have hmemF : ∀ p, p ∈ F ↔ IsSurfaceCriticalPoint S h p := fun p => by simp [hF]
  -- separation radius
  have hr_ev : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ p ∈ F, ∀ q ∈ F, p ≠ q → 3 * r < dist p q := by
    rw [eventually_all_finset]
    intro p _
    rw [eventually_all_finset]
    intro q _
    by_cases hpq : p = q
    · exact Eventually.of_forall fun _ h => absurd hpq h
    · have hd : 0 < dist p q := dist_pos.mpr hpq
      have hopen : IsOpen {r : ℝ | 3 * r < dist p q} :=
        isOpen_lt (continuous_const.mul continuous_id) continuous_const
      have h0 : (0 : ℝ) ∈ {r : ℝ | 3 * r < dist p q} := by simpa using hd
      filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds h0)] with r hr _
      exact hr
  obtain ⟨r, hsep, hr⟩ := (hr_ev.and self_mem_nhdsWithin).exists
  have hr : 0 < r := hr
  -- bumps
  let b : E₃ → ContDiffBump (0 : E₃) := fun _ => ⟨r, 2 * r, hr, by linarith⟩
  let β : E₃ → E₃ → ℝ := fun p x => b p (x - p)
  have hβ_smooth : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (β p) := fun p =>
    (b p).contDiff.comp (contDiff_id.sub contDiff_const)
  have hβ_one : ∀ p x, dist x p < r → β p x = 1 := by
    intro p x hx
    apply (b p).one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm]
    exact hx.le
  have hβ_zero : ∀ p x, 2 * r ≤ dist x p → β p x = 0 := by
    intro p x hx
    apply (b p).zero_of_le_dist
    rw [dist_zero_right, ← dist_eq_norm]
    exact hx
  have hβ_bound : ∀ p, ∃ C, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (β p) x‖ ≤ C := by
    intro p
    have hcs : HasCompactSupport (β p) :=
      (b p).hasCompactSupport.comp_homeomorph (Homeomorph.subRight p)
    obtain ⟨C, hC⟩ := (hcs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
      ((hβ_smooth p).continuous_fderiv (by simp))
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  choose C hC0 hC using hβ_bound
  -- tangential-gradient lower bound away from the critical points
  set K := S \ ⋃ p ∈ F, Metric.ball p r with hK
  have hKc : IsCompact K := hc.diff (isOpen_biUnion fun p _ => Metric.isOpen_ball)
  have hKS : K ⊆ S := sdiff_subset
  obtain ⟨U, hU, hSU, hnU⟩ := hn.1
  have hncont : ContinuousOn n S := (hnU.continuousOn).mono hSU
  have hgcont : Continuous (gradient h) := by
    have : gradient h = fun x => (toDual ℝ E₃).symm (fderiv ℝ h x) := rfl
    rw [this]
    exact (toDual ℝ E₃).symm.continuous.comp (hh.continuous_fderiv (by simp))
  have hGcont : ContinuousOn (fun x => ‖surfaceGradient n h x‖) K := by
    have h1 : ContinuousOn (fun x => inner ℝ (n x) (gradient h x)) S :=
      hncont.inner hgcont.continuousOn
    have h2 : ContinuousOn (fun x => inner ℝ (n x) (gradient h x) • n x) S := h1.smul hncont
    have h3 : ContinuousOn (fun x => gradient h x - inner ℝ (n x) (gradient h x) • n x) S :=
      hgcont.continuousOn.sub h2
    exact (h3.mono hKS).norm
  have hKpos : ∀ x ∈ K, 0 < ‖surfaceGradient n h x‖ := by
    intro x hx
    rw [norm_pos_iff]
    intro h0
    have hcrit := (isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn (hKS hx)).mpr h0
    apply hx.2
    exact mem_biUnion ((hmemF x).mpr hcrit) (Metric.mem_ball_self hr)
  obtain ⟨m, hm, hmK⟩ : ∃ m > 0, ∀ x ∈ K, m ≤ ‖surfaceGradient n h x‖ := by
    rcases K.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hne hGcont
      exact ⟨_, hKpos x₀ hx₀, fun x hx => hmin hx⟩
  -- indices and the size of the perturbation
  let idx : E₃ → ℕ := fun p => if hp : p ∈ F then (F.equivFin ⟨p, hp⟩ : ℕ) else 0
  have hidx : ∀ p ∈ F, ∀ q ∈ F, p ≠ q → (idx p : ℝ) ≠ idx q := by
    intro p hp q hq hpq he
    have he' : idx p = idx q := by exact_mod_cast he
    simp only [idx, hp, hq, ↓reduceDIte] at he'
    exact hpq (congrArg Subtype.val (F.equivFin.injective (Fin.ext he')))
  set Q : ℝ := ∑ q ∈ F, (idx q : ℝ) * C q with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun q _ => mul_nonneg (Nat.cast_nonneg _) (hC0 q)
  have hη_ev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 2 * (η * Q) < m ∧
      ∀ p ∈ F, ∀ q ∈ F, p ≠ q → h p + η * idx p ≠ h q + η * idx q := by
    refine Eventually.and ?_ ?_
    · have hopen : IsOpen {η : ℝ | 2 * (η * Q) < m} :=
        isOpen_lt (continuous_const.mul (continuous_id.mul continuous_const)) continuous_const
      exact nhdsWithin_le_nhds (hopen.mem_nhds (by simpa using hm))
    · rw [eventually_all_finset]
      intro p hp
      rw [eventually_all_finset]
      intro q hq
      by_cases hpq : p = q
      · exact Eventually.of_forall fun _ h => absurd hpq h
      · have hne : (idx p : ℝ) - idx q ≠ 0 := sub_ne_zero.mpr (hidx p hp q hq hpq)
        set η₀ := (h q - h p) / ((idx p : ℝ) - idx q)
        have hkey : ∀ η : ℝ, η ≠ η₀ → h p + η * idx p ≠ h q + η * idx q := by
          intro η hη heq
          apply hη
          rw [eq_div_iff hne]
          linarith
        rcases le_or_gt η₀ 0 with hle | hgt
        · filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η) _
          exact hkey η (hle.trans_lt hη).ne'
        · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hgt)] with η (hη : η < η₀) _
          exact hkey η hη.ne
  obtain ⟨η, ⟨hηQ, hηinj⟩, hη⟩ := (hη_ev.and self_mem_nhdsWithin).exists
  have hη : 0 < η := hη
  -- the perturbation
  let c : E₃ → ℝ := fun q => η * idx q
  let h' : E₃ → ℝ := fun x => h x + ∑ q ∈ F, c q * β q x
  have hh' : ContDiff ℝ (⊤ : ℕ∞) h' :=
    hh.add (ContDiff.sum fun q _ => contDiff_const.mul (hβ_smooth q))
  -- near a critical point `h'` is `h` plus a constant
  have hlocal : ∀ p ∈ F, ∀ x, dist x p < r → h' x = h x + c p := by
    intro p hp x hx
    simp only [h']
    congr 1
    rw [Finset.sum_eq_single p]
    · rw [hβ_one p x hx, mul_one]
    · intro q hq hqp
      have hpq := hsep p hp q hq (Ne.symm hqp)
      have : 2 * r ≤ dist x q := by
        have := dist_triangle p x q
        rw [dist_comm p x] at this
        linarith
      rw [hβ_zero q x this, mul_zero]
    · intro hp'
      exact absurd hp hp'
  have hlocal_ev : ∀ p ∈ F, ∀ x, dist x p < r →
      h' =ᶠ[𝓝 x] fun y => h y + c p := by
    intro p hp x hx
    filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball p r from hx)] with y hy
    exact hlocal p hp y hy
  have hfd_ev : ∀ p ∈ F, ∀ x, dist x p < r → fderiv ℝ h' =ᶠ[𝓝 x] fderiv ℝ h := by
    intro p hp x hx
    filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball p r from hx)] with y hy
    rw [(hlocal_ev p hp y hy).fderiv_eq]
    exact fderiv_add_const (c p)
  -- critical points agree
  have hcrit_iff : ∀ x, IsSurfaceCriticalPoint S h' x ↔ IsSurfaceCriticalPoint S h x := by
    intro x
    by_cases hxS : x ∈ S
    swap
    · exact ⟨fun hx => absurd hx.1 hxS, fun hx => absurd hx.1 hxS⟩
    by_cases hxB : ∃ p ∈ F, dist x p < r
    · obtain ⟨p, hp, hxp⟩ := hxB
      have he : fderiv ℝ h' x = fderiv ℝ h x := (hfd_ev p hp x hxp).self_of_nhds
      simp only [IsSurfaceCriticalPoint, he]
    · have hxK : x ∈ K := ⟨hxS, by
        simp only [mem_iUnion, Metric.mem_ball, not_exists]
        intro p hp hxp
        exact hxB ⟨p, hp, hxp⟩⟩
      constructor
      · intro hcrit'
        exfalso
        have hsg := (isSurfaceCriticalPoint_iff_surfaceGradient_eq_zero hS hn hxS).mp hcrit'
        have hν : ‖n x‖ = 1 := (hn.2 x hxS).1
        have hdh : HasFDerivAt h (fderiv ℝ h x) x :=
          (hh.differentiable (by simp) x).hasFDerivAt
        have hdsum : HasFDerivAt (fun y => ∑ q ∈ F, c q * β q y)
            (∑ q ∈ F, c q • fderiv ℝ (β q) x) x :=
          HasFDerivAt.fun_sum fun q _ =>
            (((hβ_smooth q).differentiable (by simp) x).hasFDerivAt).const_mul (c q)
        have hd' := (hdh.add hdsum).fderiv
        set w := (toDual ℝ E₃).symm (∑ q ∈ F, c q • fderiv ℝ (β q) x)
        have hgrad : gradient h' x = gradient h x + w := by
          change (toDual ℝ E₃).symm (fderiv ℝ h' x) = (toDual ℝ E₃).symm (fderiv ℝ h x) + w
          rw [show fderiv ℝ h' x = fderiv ℝ h x + ∑ q ∈ F, c q • fderiv ℝ (β q) x from hd',
            map_add]
        have hw : ‖w‖ ≤ η * Q := by
          rw [LinearIsometryEquiv.norm_map]
          refine (norm_sum_le _ _).trans ?_
          rw [hQ, Finset.mul_sum]
          refine Finset.sum_le_sum fun q _ => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hC q x) (Nat.cast_nonneg _)) hη.le
        have hsplit : surfaceGradient n h' x =
            surfaceGradient n h x + tangentialProj (n x) w := by
          simp only [surfaceGradient, hgrad, tangentialProj_add]
        rw [hsplit, add_eq_zero_iff_eq_neg] at hsg
        have h1 : ‖surfaceGradient n h x‖ ≤ 2 * (η * Q) := by
          rw [hsg, norm_neg]
          exact (norm_tangentialProj_le hν w).trans (by linarith)
        linarith [hmK x hxK]
      · intro hcrit
        exfalso
        exact hxB ⟨x, (hmemF x).mpr hcrit, by simpa using hr⟩
  -- Hessians agree at the critical points
  have hhess : ∀ p, IsSurfaceCriticalPoint S h p →
      tangentHessian S n h' p = tangentHessian S n h p := by
    intro p hp
    have hpF := (hmemF p).mpr hp
    have hdist : dist p p < r := by simpa using hr
    have hev := hfd_ev p hpF p hdist
    have h1 : fderiv ℝ h' p = fderiv ℝ h p := hev.self_of_nhds
    have h2 : fderiv ℝ (fderiv ℝ h') p = fderiv ℝ (fderiv ℝ h) p := hev.fderiv_eq
    funext X Y
    simp only [tangentHessian, surfaceHessian, h1, h2]
  refine ⟨h', hh', hcrit_iff, fun p hp => ⟨hhess p hp, ?_⟩, ?_, ?_⟩
  · simp only [surfaceIndex, hhess p hp]
  · intro p hp'
    have hp := (hcrit_iff p).mp hp'
    rw [hhess p hp]
    exact hM p hp
  · intro p hp q hq hpq
    have hpF := (hmemF p).mpr hp
    have hqF := (hmemF q).mpr hq
    by_contra hne
    have hp1 := hlocal p hpF p (by simpa using hr)
    have hq1 := hlocal q hqF q (by simpa using hr)
    exact hηinj p hpF q hqF hne (by rw [← hp1, ← hq1]; exact hpq)

/-- The band field `X = ∇_Σ h / |∇_Σ h|²` of `eq:band-field`. -/
def bandField (n : E₃ → E₃) (h : E₃ → ℝ) (x : E₃) : E₃ :=
  (inner ℝ (surfaceGradient n h x) (surfaceGradient n h x))⁻¹ • surfaceGradient n h x

private lemma inner_normal_surfaceGradient {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} {x : E₃} (hx : x ∈ S) :
    inner ℝ (n x) (surfaceGradient n h x) = 0 := by
  have hν : ‖n x‖ = 1 := (hn.2 x hx).1
  simp only [surfaceGradient, tangentialProj, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hν]
  ring

/-- lem:morse-band: the band field is tangent to the surface. -/
theorem bandField_mem_tangentPlane {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ} {x : E₃}
    (hx : x ∈ S) : bandField n h x ∈ tangentPlane S x := by
  rw [hn.tangentPlane_eq hS hx, Submodule.mem_orthogonal_singleton_iff_inner_right,
    bandField, real_inner_smul_right, inner_normal_surfaceGradient hn hx, mul_zero]

/-- lem:morse-band, `eq:band-derivative`: `dh(X) = 1` at regular points of the surface. -/
theorem fderiv_bandField_eq_one {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} {x : E₃} (hx : x ∈ S)
    (hreg : surfaceGradient n h x ≠ 0) :
    fderiv ℝ h x (bandField n h x) = 1 := by
  have hd : ∀ Y, fderiv ℝ h x Y = inner ℝ (gradient h x) Y := fun Y => by
    rw [gradient, toDual_symm_apply]
  set g := surfaceGradient n h x with hg
  have hsplit : gradient h x = g + inner ℝ (n x) (gradient h x) • n x := by
    simp only [hg, surfaceGradient, tangentialProj]
    abel
  have hgg : inner ℝ g g ≠ 0 := inner_self_ne_zero.mpr hreg
  have hng : inner ℝ (n x) g = 0 := inner_normal_surfaceGradient hn hx
  rw [hd, bandField, ← hg, real_inner_smul_right, hsplit, inner_add_left, real_inner_smul_left,
    hng, mul_zero, add_zero]
  exact inv_mul_cancel₀ hgg

/-- lem:morse-band: the band field is smooth on the open set of points of the normal field's
domain where the tangential gradient does not vanish. -/
theorem contDiffOn_bandField {n : E₃ → E₃} {U : Set E₃} (hU : IsOpen U)
    (hnU : ContDiffOn ℝ (⊤ : ℕ∞) n U) {h : E₃ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    IsOpen (U ∩ {x | surfaceGradient n h x ≠ 0}) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (bandField n h) (U ∩ {x | surfaceGradient n h x ≠ 0}) := by
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (gradient h) := by
    have : gradient h = fun x => (toDual ℝ E₃).symm (fderiv ℝ h x) := rfl
    rw [this]
    exact (toDual ℝ E₃).symm.toContinuousLinearEquiv.contDiff.comp
      (hh.fderiv_right (m := (⊤ : ℕ∞)) le_rfl)
  have hsg : ContDiffOn ℝ (⊤ : ℕ∞) (surfaceGradient n h) U := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => inner ℝ (n x) (gradient h x)) U :=
      hnU.inner ℝ hgrad.contDiffOn
    exact hgrad.contDiffOn.sub (h1.smul hnU)
  refine ⟨hsg.continuousOn.isOpen_inter_preimage hU isOpen_ne, ?_⟩
  have hsg' := hsg.mono (inter_subset_left (t := {x | surfaceGradient n h x ≠ 0}))
  have hin : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => (inner ℝ (surfaceGradient n h x) (surfaceGradient n h x))⁻¹)
      (U ∩ {x | surfaceGradient n h x ≠ 0}) :=
    (hsg'.inner ℝ hsg').inv fun x hx => inner_self_ne_zero.mpr hx.2
  exact hin.smul hsg'

/-- lem:morse-band: along an integral curve of the band field that stays in the regular part of
the surface, `h` increases with unit speed. -/
theorem hasDerivAt_comp_bandField_curve {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h) {γ : ℝ → E₃} {t : ℝ}
    (hγ : HasDerivAt γ (bandField n h (γ t)) t) (hγS : γ t ∈ S)
    (hreg : surfaceGradient n h (γ t) ≠ 0) :
    HasDerivAt (fun s => h (γ s)) 1 t := by
  have hd := ((hh.differentiable one_ne_zero (γ t)).hasFDerivAt).comp_hasDerivAt t hγ
  rw [fderiv_bandField_eq_one hn hγS hreg] at hd
  exact hd

/-- lem:morse-band: on an interval of such times, `h (γ t) = h (γ t₀) + (t - t₀)`. -/
theorem height_bandField_curve {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} (hh : ContDiff ℝ 1 h) {γ : ℝ → E₃}
    {a b : ℝ}
    (hγ : ∀ t ∈ Icc a b, HasDerivAt γ (bandField n h (γ t)) t ∧ γ t ∈ S ∧
      surfaceGradient n h (γ t) ≠ 0) :
    ∀ t ∈ Icc a b, h (γ t) = h (γ a) + (t - a) := by
  intro t ht
  have hderiv : ∀ s ∈ Icc a b, HasDerivAt (fun u => h (γ u) - u) 0 s := by
    intro s hs
    obtain ⟨h1, h2, h3⟩ := hγ s hs
    have h4 := (hasDerivAt_comp_bandField_curve hn hh h1 h2 h3).fun_sub (hasDerivAt_id' s)
    rw [sub_self] at h4
    exact h4
  have hcont : ContinuousOn (fun u => h (γ u) - u) (Icc a b) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun s hs => (hderiv s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht
  linarith

/-- lem:one-manifold, last clause: the rotation `n × ∇_Σ h` of the tangential gradient by `π/2`. -/
def levelTangentField (n : E₃ → E₃) (h : E₃ → ℝ) (x : E₃) : E₃ :=
  cross3 (n x) (surfaceGradient n h x)

/-- The rotated tangential gradient is tangent to the surface. -/
theorem levelTangentField_mem_tangentPlane {S : Set E₃} {n : E₃ → E₃}
    (hS : IsSmoothEmbeddedSurface S) (hn : IsUnitNormalField S n) {h : E₃ → ℝ} {x : E₃}
    (hx : x ∈ S) : levelTangentField n h x ∈ tangentPlane S x := by
  rw [hn.tangentPlane_eq hS hx, Submodule.mem_orthogonal_singleton_iff_inner_right]
  exact inner_left_cross3 _ _

/-- The rotated tangential gradient is tangent to the level sets of `h`. -/
theorem fderiv_levelTangentField_eq_zero (n : E₃ → E₃) (h : E₃ → ℝ) (x : E₃) :
    fderiv ℝ h x (levelTangentField n h x) = 0 := by
  have hd : ∀ Y, fderiv ℝ h x Y = inner ℝ (gradient h x) Y := fun Y => by
    rw [gradient, toDual_symm_apply]
  have hsplit : gradient h x = surfaceGradient n h x + inner ℝ (n x) (gradient h x) • n x := by
    simp only [surfaceGradient, tangentialProj]
    abel
  rw [hd, hsplit, inner_add_left, real_inner_smul_left, levelTangentField,
    inner_right_cross3, inner_left_cross3, mul_zero, add_zero]

/-- The rotated tangential gradient has the norm of the tangential gradient. -/
theorem norm_levelTangentField {S : Set E₃} {n : E₃ → E₃}
    (hn : IsUnitNormalField S n) {h : E₃ → ℝ} {x : E₃} (hx : x ∈ S) :
    ‖levelTangentField n h x‖ = ‖surfaceGradient n h x‖ := by
  have hν : ‖n x‖ = 1 := (hn.2 x hx).1
  have hsq := norm_cross3_sq (n x) (surfaceGradient n h x)
  rw [hν, inner_normal_surfaceGradient hn hx] at hsq
  have h2 : ‖levelTangentField n h x‖ ^ 2 = ‖surfaceGradient n h x‖ ^ 2 := by
    rw [levelTangentField, hsq]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end LiquidDrop
