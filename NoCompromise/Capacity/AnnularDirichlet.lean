import NoCompromise.Capacity.FluxIdentity
import NoCompromise.Capacity.ExistenceLimit
import NoCompromise.Elliptic.WeakDirichlet
import NoCompromise.Elliptic.WeakMaximum
import NoCompromise.BV.StrictApprox

/-!
# The annular weak Dirichlet problem

Blueprint `thm:capacitary-potential`, annular minimisation and comparison.
The boundary datum is a fixed smooth cutoff, equal to one near the compact
obstacle and supported in its enclosing ball. All boundary values below use
the actual Hausdorff trace on the genuine Sobolev space.

`exists_annular_weak_dirichlet` proves existence, uniqueness, distributional
harmonicity, the trace values, the interval bounds, and the reciprocal-radius
barrier. `annular_weak_dirichlet_mono` proves comparison for increasing radii.
The final existence theorem feeds these results to
`capacitary_potential_of_annular_family`, with boundary regularity kept
explicit as the sole additional hypothesis `AnnularBoundaryContinuity`.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop

/-- The bounded exterior truncation used in the capacitary construction. -/
def annularDomain (K : Set AmbientSpace) (R : ℝ) : Set AmbientSpace :=
  ball 0 R ∩ Kᶜ

lemma annularDomain_isOpen {K : Set AmbientSpace} (hK : IsCompact K) (R : ℝ) :
    IsOpen (annularDomain K R) := isOpen_ball.inter hK.isClosed.isOpen_compl

lemma annularDomain_isBounded (K : Set AmbientSpace) (R : ℝ) :
    Bornology.IsBounded (annularDomain K R) := isBounded_ball.subset inter_subset_left

/-- A single cutoff supplies the Dirichlet datum on every exterior truncation. -/
structure IsAnnularDatum (K : Set AmbientSpace) (R₀ : ℝ) (ψ : AmbientSpace → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) ψ
  compactSupport : HasCompactSupport ψ
  support_subset : tsupport ψ ⊆ ball 0 R₀
  one_near : ∀ᶠ x in 𝓝ˢ K, ψ x = 1
  bounds : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1

lemma exists_annularDatum {K : Set AmbientSpace} (hK : IsCompact K) {R₀ : ℝ}
    (hKR : K ⊆ ball 0 R₀) : ∃ ψ, IsAnnularDatum K R₀ ψ := by
  obtain ⟨ψ, hs, hc, ht, h1, hb⟩ :=
    exists_smooth_cutoff_one_near_compact hK isOpen_ball hKR
  exact ⟨ψ, hs, hc, ht, h1, hb⟩

lemma IsAnnularDatum.one_on_frontier {K : Set AmbientSpace} {R₀ : ℝ}
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ) (hK : IsCompact K) :
    ∀ x ∈ frontier K, ψ x = 1 :=
  fun x hx => hψ.one_near.self_of_nhdsSet x (hK.isClosed.frontier_subset hx)

lemma IsAnnularDatum.zero_on_sphere {K : Set AmbientSpace} {R₀ R : ℝ}
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ) (hR : R₀ < R) :
    ∀ x ∈ sphere (0 : AmbientSpace) R, ψ x = 0 := by
  intro x hx
  apply image_eq_zero_of_notMem_tsupport
  intro ht
  have hlt := mem_ball.mp (hψ.support_subset ht)
  rw [mem_sphere.mp hx] at hlt
  exact (not_lt_of_ge hR.le) hlt

lemma IsAnnularDatum.hasH1GradientOn {K : Set AmbientSpace} {R₀ : ℝ}
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ)
    {D : Set AmbientSpace} (hD : IsOpen D) : HasH1GradientOn ψ (gradient ψ) D := by
  exact h1ZeroTestFunctions.hasH1GradientOn
    (⟨ψ, hψ.smooth, hψ.compactSupport, subset_univ _⟩ : h1ZeroTestFunctions univ) hD

/-- The H¹ realization of the fixed smooth boundary datum. -/
def IsAnnularDatum.toH1 {K : Set AmbientSpace} {R₀ : ℝ} {ψ : AmbientSpace → ℝ}
    (hψ : IsAnnularDatum K R₀ ψ) (hK : IsCompact K) (R : ℝ) :
    H1Space (annularDomain K R) :=
  H1Space.ofFunction ψ (gradient ψ) (hψ.hasH1GradientOn (annularDomain_isOpen hK R))

/-- Homogeneous variational Dirichlet solutions are distributionally harmonic. -/
lemma IsWeakDirichletSolution.harmonic {D : Set AmbientSpace} {hD : IsOpen D}
    {g z : H1Space D} (hz : IsWeakDirichletSolution hD 0 g z) :
    HasDistributionalLaplacianOn (⇑z) (fun _ => 0) D := by
  refine ⟨z.hasH1GradientOn.locallyIntegrable_function, locallyIntegrableOn_const 0, ?_⟩
  intro φ hφ hcφ hsφ
  let t : h1ZeroTestFunctions D := ⟨φ, hφ, hcφ, hsφ⟩
  let v := h1ZeroTestFunctions.toH1Space hD t
  have hv : v ∈ h1ZeroSubmodule hD :=
    (h1ZeroTestFunctions.toH1Space hD).range.le_topologicalClosure ⟨t, rfl⟩
  have he := hz.test_eq ⟨v, hv⟩
  have hgrad : ⇑v.gradientLp =ᵐ[volume.restrict D] gradient φ :=
    H1Space.gradientLp_ofFunction _ _ (h1ZeroTestFunctions.hasH1GradientOn t hD)
  have hzero : (∫ x in D, (0 : Lp ℝ 2 (volume.restrict D)) x * v x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict D)] with x hx
    change (0 : Lp ℝ 2 (volume.restrict D)) x = 0 at hx
    rw [hx, zero_mul]
    rfl
  rw [hzero, neg_zero] at he
  rw [z.hasH1GradientOn.toHasWeakGradientOn.integral_mul_laplacianN
    (hφ.of_le (by simp)) hcφ hsφ]
  simp only [zero_mul, integral_zero, neg_eq_zero]
  exact (integral_congr_ae (hgrad.mono fun x hx => by rw [hx])).symm.trans he

/-- Any actual trace of a weak Dirichlet solution agrees with its continuous datum. -/
lemma IsWeakDirichletSolution.trace_eq_annular {D : Set AmbientSpace} {hD : IsOpen D}
    {ψ : AmbientSpace → ℝ} {G : AmbientSpace → AmbientSpace}
    (hψ : HasH1GradientOn ψ G D) (hcψ : Continuous ψ) {z : H1Space D}
    (hz : IsWeakDirichletSolution hD 0 (H1Space.ofFunction ψ G hψ) z)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure 2).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf))
        =ᵐ[(Measure.euclideanHausdorffMeasure 2).restrict (frontier D)] f) :
    ⇑(T z) =ᵐ[(Measure.euclideanHausdorffMeasure 2).restrict (frontier D)] ψ := by
  have he := h1ZeroSubmodule_le_trace_ker hD T hT hz.1
  change T (z - H1Space.ofFunction ψ G hψ) = 0 at he
  rw [map_sub, sub_eq_zero] at he
  rw [he]
  exact hT _ _ hψ hcψ

/-- Harmonic H¹ functions obey comparison whenever their actual traces do. -/
lemma annular_h1_harmonic_comparison {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (T : H1Space D →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure 2).restrict (frontier D)))
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf))
        =ᵐ[(Measure.euclideanHausdorffMeasure 2).restrict (frontier D)] f)
    (u v : H1Space D)
    (hu : HasDistributionalLaplacianOn (⇑u) (fun _ => 0) D)
    (hv : HasDistributionalLaplacianOn (⇑v) (fun _ => 0) D)
    (ht : ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure 2).restrict (frontier D),
      T u x ≤ T v x) : ∀ᵐ x ∂volume.restrict D, u x ≤ v x := by
  have hh : HasDistributionalLaplacianOn (⇑(u - v)) (fun _ => 0) D := by
    have hh := hu.sub hv
    simp only [sub_self] at hh
    exact hh.congr_ae (H1Space.coeFn_sub u v).symm EventuallyEq.rfl
  have hb : ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure 2).restrict (frontier D),
      T (u - v) x ≤ 0 := by
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (T u) (T v), ht] with x he hx
    simpa only [he, Pi.sub_apply, sub_nonpos] using hx
  have hw := weak_maximum_distributional hD hbD hL T hT (u - v)
    (fun φ hφ hcφ hsφ _ => by
      have he := hh.test_eq φ hφ hcφ hsφ
      simpa only [zero_mul, integral_zero, he] using (le_refl (0 : ℝ))) hb
  filter_upwards [hw, H1Space.coeFn_sub u v] with x hx he
  rw [he] at hx
  exact sub_nonpos.mp hx

/-- The variational solution on each annular domain exists and is unique. -/
theorem exists_unique_annular_weak_dirichlet {K : Set AmbientSpace} (hK : IsCompact K)
    {R₀ : ℝ} {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ) (R : ℝ) :
    ∃! z : H1Space (annularDomain K R),
      IsWeakDirichletSolution (annularDomain_isOpen hK R) 0 (hψ.toH1 hK R) z := by
  obtain ⟨z, hz, -, -, hu, -⟩ := exists_weak_dirichlet (annularDomain_isOpen hK R)
    (annularDomain_isBounded K R).measure_lt_top 0 (hψ.toH1 hK R)
  exact ⟨z, hz, hu⟩

/-- Constants are harmonic as elements of the genuine H¹ space. -/
lemma annular_h1_const_harmonic {D : Set AmbientSpace} (hD : IsOpen D)
    (hvol : volume D < ∞) (c : ℝ) :
    HasDistributionalLaplacianOn (⇑(H1Space.const hD hvol c)) (fun _ => 0) D :=
  (hasDistributionalLaplacianOn_const D c).congr_ae
    (H1Space.coeFn_const hD hvol c).symm EventuallyEq.rfl

/-- Weak maximum gives the interval bounds for the annular solution. -/
theorem annular_weak_dirichlet_bounds {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hzero : (0 : AmbientSpace) ∈ interior K) {R₀ : ℝ} (hKR : K ⊆ ball 0 R₀)
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ) {R : ℝ} (hR : R₀ < R)
    {z : H1Space (annularDomain K R)}
    (hz : IsWeakDirichletSolution (annularDomain_isOpen hK R) 0 (hψ.toH1 hK R) z) :
    ∀ᵐ x ∂volume.restrict (annularDomain K R), 0 ≤ z x ∧ z x ≤ 1 := by
  have hR₀ : 0 < R₀ := by simpa using hKR (interior_subset hzero)
  have hD := annularDomain_isOpen hK R
  have hb := annularDomain_isBounded K R
  have hL : HasLipschitzBoundary (annularDomain K R) :=
    (annulus_hasC1Boundary hK hreg hC1 (hR₀.trans hR)
      (hKR.trans (ball_subset_ball hR.le))).hasLipschitzBoundary
  obtain ⟨T, -, -, -, hT⟩ := exists_h1_trace_operator hD hb hL
  have ht := hz.trace_eq_annular (hψ.hasH1GradientOn hD) hψ.smooth.continuous T hT
  let c (a : ℝ) := H1Space.const hD hb.measure_lt_top a
  have htc (a : ℝ) : ⇑(T (c a)) =ᵐ[
      (Measure.euclideanHausdorffMeasure 2).restrict (frontier (annularDomain K R))]
      fun _ => a := hT _ _ _ continuous_const
  have hlo := annular_h1_harmonic_comparison hD hb hL T hT (c 0) z
    (annular_h1_const_harmonic hD hb.measure_lt_top 0) hz.harmonic (by
      filter_upwards [htc 0, ht] with x hc hx
      rw [hc, hx]
      exact (hψ.bounds x).1)
  have hhi := annular_h1_harmonic_comparison hD hb hL T hT z (c 1)
    hz.harmonic (annular_h1_const_harmonic hD hb.measure_lt_top 1) (by
      filter_upwards [ht, htc 1] with x hx hc
      rw [hx, hc]
      exact (hψ.bounds x).2)
  filter_upwards [hlo, hhi, H1Space.coeFn_const hD hb.measure_lt_top 0,
    H1Space.coeFn_const hD hb.measure_lt_top 1] with x hl hh h0 h1
  exact ⟨by simpa only [c, h0] using hl, by simpa only [c, h1] using hh⟩

/-- Smooth functions define H¹ classes on bounded open sets. -/
lemma annular_hasH1GradientOn_of_smooth {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) {f : AmbientSpace → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : HasH1GradientOn f (gradient f) D := by
  let : IsFiniteMeasure (volume.restrict D) := ⟨by simpa using hbD.measure_lt_top⟩
  have h1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  obtain ⟨C, hC⟩ := hbD.isCompact_closure.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨B, hB⟩ := hbD.isCompact_closure.exists_bound_of_continuousOn
    (continuous_gradient_of_contDiff h1).continuousOn
  refine ⟨hasWeakGradientOn_of_contDiffOn hD h1.contDiffOn,
    MemLp.of_bound hf.continuous.aestronglyMeasurable C ?_,
    MemLp.of_bound (continuous_gradient_of_contDiff h1).aestronglyMeasurable B ?_⟩
  · filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    exact hC x (subset_closure hx)
  · filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    exact hB x (subset_closure hx)

/-- A smooth global representative of the reciprocal-radius barrier near the
closed annulus. Its values in the obstacle are immaterial. -/
lemma exists_annular_smooth_barrier {K : Set AmbientSpace}
    (hzero : (0 : AmbientSpace) ∈ interior K) (R₀ R : ℝ) :
    ∃ β : AmbientSpace → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧
      ∀ x ∈ closure (annularDomain K R), β x = R₀ / ‖x‖ := by
  have hs : closure (annularDomain K R) ⊆ ({0} : Set AmbientSpace)ᶜ := by
    intro x hx hxe
    have hxK := closure_mono (show annularDomain K R ⊆ Kᶜ from inter_subset_right) hx
    rw [closure_compl] at hxK
    exact hxK (by simpa only [mem_singleton_iff.mp hxe] using hzero)
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : AmbientSpace => R₀ / ‖x‖)
      ({0} : Set AmbientSpace)ᶜ := by
    intro x hx
    exact (contDiffAt_const.div (contDiffAt_id.norm ℝ hx)
      (norm_ne_zero_iff.mpr hx)).contDiffWithinAt
  obtain ⟨β, hβ, he⟩ := exists_global_contDiff_eq_near_compact isOpen_compl_singleton
    (annularDomain_isBounded K R).isCompact_closure hs hsm
  exact ⟨β, hβ, fun x hx => (he x hx).self_of_nhds⟩

/-- The reciprocal-radius barrier bounds each weak annular solution. -/
theorem annular_weak_dirichlet_barrier {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hzero : (0 : AmbientSpace) ∈ interior K) {R₀ : ℝ} (hKR : K ⊆ ball 0 R₀)
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ) {R : ℝ} (hR : R₀ < R)
    {z : H1Space (annularDomain K R)}
    (hz : IsWeakDirichletSolution (annularDomain_isOpen hK R) 0 (hψ.toH1 hK R) z) :
    ∀ᵐ x ∂volume.restrict (annularDomain K R), z x ≤ R₀ / ‖x‖ := by
  have hR₀ : 0 < R₀ := by simpa using hKR (interior_subset hzero)
  have hD := annularDomain_isOpen hK R
  have hb := annularDomain_isBounded K R
  have hL : HasLipschitzBoundary (annularDomain K R) :=
    (annulus_hasC1Boundary hK hreg hC1 (hR₀.trans hR)
      (hKR.trans (ball_subset_ball hR.le))).hasLipschitzBoundary
  obtain ⟨β, hβ, heβ⟩ := exists_annular_smooth_barrier hzero R₀ R
  have hβH := annular_hasH1GradientOn_of_smooth hD hb hβ
  let b := H1Space.ofFunction β (gradient β) hβH
  have he : ⇑b =ᵐ[volume.restrict (annularDomain K R)] fun x => R₀ / ‖x‖ := by
    filter_upwards [H1Space.coeFn_ofFunction β (gradient β) hβH,
      ae_restrict_mem hD.measurableSet] with x hx hxd
    exact hx.trans (heβ x (subset_closure hxd))
  have hbh : HasDistributionalLaplacianOn (⇑b) (fun _ => 0) (annularDomain K R) := by
    have hh := (hasDistributionalLaplacianOn_newtonKernel_away 0
      (show (0 : AmbientSpace) ∉ annularDomain K R from
        fun hx => hx.2 (interior_subset hzero))).const_mul R₀
    simp only [sub_zero, mul_zero, ← div_eq_mul_inv] at hh
    exact hh.congr_ae he.symm EventuallyEq.rfl
  obtain ⟨T, -, -, -, hT⟩ := exists_h1_trace_operator hD hb hL
  have ht := hz.trace_eq_annular (hψ.hasH1GradientOn hD) hψ.smooth.continuous T hT
  have htb : ⇑(T b) =ᵐ[
      (Measure.euclideanHausdorffMeasure 2).restrict (frontier (annularDomain K R))] β :=
    hT _ _ hβH hβ.continuous
  have hcomp := annular_h1_harmonic_comparison hD hb hL T hT z b hz.harmonic hbh (by
    filter_upwards [ht, htb, ae_restrict_mem isClosed_frontier.measurableSet] with x hx hb hxF
    rw [hx, hb, heβ x (frontier_subset_closure hxF)]
    change x ∈ frontier (ball (0 : AmbientSpace) R ∩ Kᶜ) at hxF
    rw [annulus_frontier hK (hR₀.trans hR) (hKR.trans (ball_subset_ball hR.le))] at hxF
    rcases hxF with hxF | hxF
    · rw [hψ.zero_on_sphere hR x hxF]
      exact div_nonneg hR₀.le (norm_nonneg x)
    · rw [hψ.one_on_frontier hK x hxF]
      have hxn : 0 < ‖x‖ := norm_pos_iff.mpr (by
        intro hx0
        subst x
        exact (disjoint_interior_frontier (s := K)).le_bot ⟨hzero, hxF⟩)
      apply (le_div_iff₀ hxn).mpr
      simpa only [one_mul, dist_zero_right] using
        (mem_ball.mp (hKR (hK.isClosed.frontier_subset hxF))).le)
  filter_upwards [hcomp, he] with x hx hxβ
  exact hx.trans_eq hxβ

/-- Milestone 1: the unique annular weak solution, with harmonicity, the
prescribed actual trace, interval bounds, and the reciprocal-radius barrier. -/
theorem exists_annular_weak_dirichlet {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hzero : (0 : AmbientSpace) ∈ interior K) {R₀ : ℝ} (hKR : K ⊆ ball 0 R₀)
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ) {R : ℝ} (hR : R₀ < R) :
    ∃ z : H1Space (annularDomain K R),
      IsWeakDirichletSolution (annularDomain_isOpen hK R) 0 (hψ.toH1 hK R) z ∧
      (∀ w, IsWeakDirichletSolution (annularDomain_isOpen hK R) 0 (hψ.toH1 hK R) w →
        w = z) ∧
      HasDistributionalLaplacianOn (⇑z) (fun _ => 0) (annularDomain K R) ∧
      (∀ (T : H1Space (annularDomain K R) →L[ℝ]
          Lp ℝ 2 ((Measure.euclideanHausdorffMeasure 2).restrict
            (frontier (annularDomain K R)))),
        (∀ f G (hf : HasH1GradientOn f G (annularDomain K R)), Continuous f →
          ⇑(T (H1Space.ofFunction f G hf)) =ᵐ[
            (Measure.euclideanHausdorffMeasure 2).restrict (frontier (annularDomain K R))] f) →
        ⇑(T z) =ᵐ[(Measure.euclideanHausdorffMeasure 2).restrict
          (frontier (annularDomain K R))] ψ) ∧
      (∀ᵐ x ∂volume.restrict (annularDomain K R), 0 ≤ z x ∧ z x ≤ 1) ∧
      (∀ᵐ x ∂volume.restrict (annularDomain K R), z x ≤ R₀ / ‖x‖) := by
  obtain ⟨z, hz, hu⟩ := exists_unique_annular_weak_dirichlet hK hψ R
  exact ⟨z, hz, hu, hz.harmonic,
    fun T hT => hz.trace_eq_annular (hψ.hasH1GradientOn (annularDomain_isOpen hK R))
      hψ.smooth.continuous T hT,
    annular_weak_dirichlet_bounds hK hreg hC1 hzero hKR hψ hR hz,
    annular_weak_dirichlet_barrier hK hreg hC1 hzero hKR hψ hR hz⟩

/-- Restriction agrees almost everywhere with the original H¹ representative. -/
lemma annular_restriction_coeFn {U V : Set AmbientSpace}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) (u : H1Space U) :
    ⇑(H1Space.restrictionCLM hU hV hVU u) =ᵐ[volume.restrict V] u := by
  conv_lhs => rw [← H1Space.ofFunction_coeFn hU u, H1Space.restrictionCLM_ofFunction]
  exact H1Space.coeFn_ofFunction _ _ _

/-- Nonnegative H¹ functions have nonnegative actual traces. -/
lemma annular_trace_nonneg {D : Set AmbientSpace} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    {μ : Measure AmbientSpace} (T : H1Space D →L[ℝ] Lp ℝ 2 μ)
    (hT : ∀ f G (hf : HasH1GradientOn f G D), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf)) =ᵐ[μ] f)
    (u : H1Space D) (hu : ∀ᵐ x ∂volume.restrict D, 0 ≤ u x) :
    ∀ᵐ x ∂μ, 0 ≤ T u x := by
  obtain ⟨v, hv, ht, -⟩ := H1Space.exists_positivePart_of_trace hD hbD hL T hT u
  have he : v = u := H1Space.ext_ae hD (by
    filter_upwards [hv, hu] with x hx hu
    exact hx.trans (max_eq_left hu))
  rw [he] at ht
  exact ht.mono fun x hx => hx.symm ▸ le_max_right (T u x) 0

/-- Restricting an H¹₀ function preserves zero trace on any closed boundary
piece lying outside the larger open domain. -/
lemma annular_restriction_zero_trace {U V A : Set AmbientSpace}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (hA : IsClosed A) (hAU : Disjoint A U)
    (T : H1Space V →L[ℝ]
      Lp ℝ 2 ((Measure.euclideanHausdorffMeasure 2).restrict (frontier V)))
    (hT : ∀ f G (hf : HasH1GradientOn f G V), Continuous f →
      ⇑(T (H1Space.ofFunction f G hf))
        =ᵐ[(Measure.euclideanHausdorffMeasure 2).restrict (frontier V)] f)
    {u : H1Space U} (hu : u ∈ h1ZeroSubmodule hU) :
    ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure 2).restrict (frontier V),
      x ∈ A → T (H1Space.restrictionCLM hU hV hVU u) x = 0 := by
  let μ := (Measure.euclideanHausdorffMeasure 2).restrict (frontier V)
  let S := LpToLpRestrictCLM AmbientSpace ℝ ℝ μ 2 A
  let F := S.comp (T.comp (H1Space.restrictionCLM hU hV hVU))
  have hker : h1ZeroSubmodule hU ≤ F.ker := by
    apply Submodule.topologicalClosure_minimal _ ?_ F.isClosed_ker
    rintro v ⟨f, rfl⟩
    change S (T (H1Space.restrictionCLM hU hV hVU
      (H1Space.ofFunction f.val (gradient f.val) (h1ZeroTestFunctions.hasH1GradientOn f hU)))) = 0
    rw [H1Space.restrictionCLM_ofFunction]
    apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℝ A
        (T (H1Space.ofFunction f.val (gradient f.val)
          ((h1ZeroTestFunctions.hasH1GradientOn f hU).mono hVU))),
      ae_restrict_of_ae (hT _ _ ((h1ZeroTestFunctions.hasH1GradientOn f hU).mono hVU)
        f.property.1.continuous),
      ae_restrict_mem hA.measurableSet,
      Lp.coeFn_zero ℝ 2 (μ.restrict A)] with x hs ht hx hz
    have hf : f.val x = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
      (Set.disjoint_left.mp hAU hx) (f.property.2.2 h))
    exact hs.trans (ht.trans (hf.trans hz.symm))
  have he : S (T (H1Space.restrictionCLM hU hV hVU u)) = 0 := hker hu
  apply (ae_restrict_iff' hA.measurableSet).mp
  have hs := LpToLpRestrictCLM_coeFn ℝ A (T (H1Space.restrictionCLM hU hV hVU u))
  change ⇑(S _) =ᵐ[μ.restrict A] _ at hs
  rw [he] at hs
  filter_upwards [hs, Lp.coeFn_zero ℝ 2 (μ.restrict A)] with x hx hz
  exact hx.symm.trans hz

/-- Milestone 2: annular weak solutions increase as the outer radius increases. -/
theorem annular_weak_dirichlet_mono {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hzero : (0 : AmbientSpace) ∈ interior K) {R₀ : ℝ} (hKR : K ⊆ ball 0 R₀)
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ)
    {R R' : ℝ} (hR : R₀ < R) (hRR : R ≤ R')
    {z : H1Space (annularDomain K R)} {z' : H1Space (annularDomain K R')}
    (hz : IsWeakDirichletSolution (annularDomain_isOpen hK R) 0 (hψ.toH1 hK R) z)
    (hz' : IsWeakDirichletSolution (annularDomain_isOpen hK R') 0 (hψ.toH1 hK R') z') :
    ∀ᵐ x ∂volume.restrict (annularDomain K R), z x ≤ z' x := by
  have hR₀ : 0 < R₀ := by simpa using hKR (interior_subset hzero)
  have hD := annularDomain_isOpen hK R
  have hD' := annularDomain_isOpen hK R'
  have hb := annularDomain_isBounded K R
  have hL : HasLipschitzBoundary (annularDomain K R) :=
    (annulus_hasC1Boundary hK hreg hC1 (hR₀.trans hR)
      (hKR.trans (ball_subset_ball hR.le))).hasLipschitzBoundary
  have hsub : annularDomain K R ⊆ annularDomain K R' :=
    inter_subset_inter_left _ (ball_subset_ball hRR)
  let Q := H1Space.restrictionCLM hD' hD hsub
  have he := annular_restriction_coeFn hD' hD hsub z'
  have hq : HasDistributionalLaplacianOn (⇑(Q z')) (fun _ => 0) (annularDomain K R) :=
    (hz'.harmonic.mono hsub).congr_ae he.symm EventuallyEq.rfl
  obtain ⟨T, -, -, -, hT⟩ := exists_h1_trace_operator hD hb hL
  have ht := hz.trace_eq_annular (hψ.hasH1GradientOn hD) hψ.smooth.continuous T hT
  have hq0 : ∀ᵐ x ∂volume.restrict (annularDomain K R), 0 ≤ Q z' x := by
    have hn := ae_restrict_of_ae_restrict_of_subset hsub
      (annular_weak_dirichlet_bounds hK hreg hC1 hzero hKR hψ (hR.trans_le hRR) hz')
    filter_upwards [he, hn] with x hx hn
    exact hx.symm ▸ hn.1
  have htq0 := annular_trace_nonneg hD hb hL T hT (Q z') hq0
  have hdis : Disjoint (frontier K) (annularDomain K R') := by
    apply Set.disjoint_left.mpr
    intro x hx hxD
    exact hxD.2 (hK.isClosed.frontier_subset hx)
  have htzero := annular_restriction_zero_trace hD' hD hsub isClosed_frontier hdis T hT hz'.1
  have hQψ : Q (hψ.toH1 hK R') = hψ.toH1 hK R := by
    change H1Space.restrictionCLM hD' hD hsub (H1Space.ofFunction _ _ _) = _
    rw [H1Space.restrictionCLM_ofFunction]
    rfl
  change ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure 2).restrict (frontier (annularDomain K R)),
    x ∈ frontier K → T (Q (z' - hψ.toH1 hK R')) x = 0 at htzero
  rw [map_sub, hQψ, map_sub] at htzero
  have htψ : ⇑(T (hψ.toH1 hK R)) =ᵐ[
      (Measure.euclideanHausdorffMeasure 2).restrict (frontier (annularDomain K R))] ψ :=
    hT _ _ (hψ.hasH1GradientOn hD) hψ.smooth.continuous
  have htcomp : ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure 2).restrict
      (frontier (annularDomain K R)), T z x ≤ T (Q z') x := by
    filter_upwards [ht, htq0, htzero, htψ, Lp.coeFn_sub (T (Q z')) (T (hψ.toH1 hK R)),
      ae_restrict_mem isClosed_frontier.measurableSet] with x hx h0 hi hψx hsubx hxF
    rw [hx]
    change x ∈ frontier (ball (0 : AmbientSpace) R ∩ Kᶜ) at hxF
    rw [annulus_frontier hK (hR₀.trans hR) (hKR.trans (ball_subset_ball hR.le))] at hxF
    rcases hxF with hxF | hxF
    · rw [hψ.zero_on_sphere hR x hxF]
      exact h0
    · have h := hi hxF
      rw [hsubx, Pi.sub_apply, hψx] at h
      exact (sub_eq_zero.mp h).symm.le
  have hcomp := annular_h1_harmonic_comparison hD hb hL T hT z (Q z') hz.harmonic hq htcomp
  filter_upwards [hcomp, he] with x hx he
  exact hx.trans_eq he

/-- The remaining boundary regularity input: each weak annular solution has
a representative continuous across the obstacle and equal to one there. -/
def AnnularBoundaryContinuity {K : Set AmbientSpace} (hK : IsCompact K)
    {R₀ : ℝ} {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ) : Prop :=
  ∀ R, R₀ < R → ∀ z : H1Space (annularDomain K R),
    IsWeakDirichletSolution (annularDomain_isOpen hK R) 0 (hψ.toH1 hK R) z →
    ∃ v : AmbientSpace → ℝ, ContinuousOn v (ball 0 R) ∧
      v =ᵐ[volume.restrict (annularDomain K R)] z ∧ ∀ x ∈ K, v x = 1

/-- Almost-everywhere order between continuous functions holds everywhere on
an open Euclidean set. -/
lemma annular_le_on_of_ae {D : Set AmbientSpace} (hD : IsOpen D)
    {f g : AmbientSpace → ℝ} (hf : ContinuousOn f D) (hg : ContinuousOn g D)
    (he : ∀ᵐ x ∂volume.restrict D, f x ≤ g x) : ∀ x ∈ D, f x ≤ g x := by
  have hmax : (fun x => max (f x) (g x)) =ᵐ[volume.restrict D] g :=
    he.mono fun _ hx => max_eq_right hx
  have heq := Measure.eqOn_open_of_ae_eq hmax hD (hf.sup hg) hg
  exact fun x hx => max_eq_right_iff.mp (heq hx)

/-- Milestone 3: the capacitary potential exists under the explicitly named
boundary-continuity input. Radius monotonicity is proved above, not assumed. -/
theorem exists_capacitary_potential_of_annular_boundary_continuity
    {K : Set AmbientSpace} (hK : IsCompact K)
    (hreg : K = closure (interior K)) (hC1 : HasC1Boundary (interior K))
    (hzero : (0 : AmbientSpace) ∈ interior K) {R₀ : ℝ} (hKR : K ⊆ ball 0 R₀)
    {ψ : AmbientSpace → ℝ} (hψ : IsAnnularDatum K R₀ ψ)
    (hboundary : AnnularBoundaryContinuity hK hψ) :
    ∃ u : AmbientSpace → ℝ, Continuous u ∧
      HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ ∧
      ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ ∧
      (∀ x ∈ K, u x = 1) ∧ Tendsto u (cocompact AmbientSpace) (𝓝 0) ∧
      (∀ x, 0 ≤ u x ∧ u x ≤ 1) ∧ (∀ x ∉ K, u x ≤ R₀ / ‖x‖) := by
  classical
  have hR₀ : 0 < R₀ := by simpa using hKR (interior_subset hzero)
  have hex (R : ℝ) : ∃ z : H1Space (annularDomain K R),
      IsWeakDirichletSolution (annularDomain_isOpen hK R) 0 (hψ.toH1 hK R) z :=
    (exists_unique_annular_weak_dirichlet hK hψ R).exists
  choose z hz using hex
  have hrep (R : ℝ) : ∃ v : AmbientSpace → ℝ, R₀ < R →
      ContinuousOn v (ball 0 R) ∧
      v =ᵐ[volume.restrict (annularDomain K R)] z R ∧ ∀ x ∈ K, v x = 1 := by
    by_cases hR : R₀ < R
    · obtain ⟨v, hv⟩ := hboundary R hR (z R) (hz R)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨fun _ => 1, fun h => (hR h).elim⟩
  choose v hv using hrep
  have hv01 (R : ℝ) (hR : R₀ < R) : ∀ x ∈ ball (0 : AmbientSpace) R,
      0 ≤ v R x ∧ v R x ≤ 1 := by
    have hb := annular_weak_dirichlet_bounds hK hreg hC1 hzero hKR hψ hR (hz R)
    have hvc := (hv R hR).1.mono (show annularDomain K R ⊆ ball 0 R from inter_subset_left)
    have hl := annular_le_on_of_ae (annularDomain_isOpen hK R) continuousOn_const hvc (by
      filter_upwards [(hv R hR).2.1, hb] with x he hb
      exact he.symm ▸ hb.1)
    have hu := annular_le_on_of_ae (annularDomain_isOpen hK R) hvc continuousOn_const (by
      filter_upwards [(hv R hR).2.1, hb] with x he hb
      exact he.symm ▸ hb.2)
    intro x hx
    by_cases hxK : x ∈ K
    · rw [(hv R hR).2.2 x hxK]
      exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨hl x ⟨hx, hxK⟩, hu x ⟨hx, hxK⟩⟩
  have hvbar (R : ℝ) (hR : R₀ < R) :
      ∀ x ∈ annularDomain K R, v R x ≤ R₀ / ‖x‖ := by
    apply annular_le_on_of_ae (annularDomain_isOpen hK R)
      ((hv R hR).1.mono inter_subset_left)
      (continuousOn_const.div continuous_norm.continuousOn ?_)
    · filter_upwards [(hv R hR).2.1,
        annular_weak_dirichlet_barrier hK hreg hC1 hzero hKR hψ hR (hz R)] with x he hb
      exact he.symm ▸ hb
    · intro x hx
      exact norm_ne_zero_iff.mpr (fun hx0 => hx.2 (hx0 ▸ interior_subset hzero))
  have hvmono (R R' : ℝ) (hR : R₀ < R) (hRR : R ≤ R') :
      ∀ x ∈ ball (0 : AmbientSpace) R, v R x ≤ v R' x := by
    have hR' := hR.trans_le hRR
    have hsub : annularDomain K R ⊆ annularDomain K R' :=
      inter_subset_inter_left _ (ball_subset_ball hRR)
    have hm := annular_le_on_of_ae (annularDomain_isOpen hK R)
      ((hv R hR).1.mono inter_subset_left)
      ((hv R' hR').1.mono (inter_subset_left.trans (ball_subset_ball hRR))) (by
        filter_upwards [(hv R hR).2.1,
          ae_restrict_of_ae_restrict_of_subset hsub (hv R' hR').2.1,
          annular_weak_dirichlet_mono hK hreg hC1 hzero hKR hψ hR hRR (hz R) (hz R')]
          with x he he' hm
        simpa only [he, he'] using hm)
    intro x hx
    by_cases hxK : x ∈ K
    · rw [(hv R hR).2.2 x hxK, (hv R' hR').2.2 x hxK]
    · exact hm x ⟨hx, hxK⟩
  let w : ℝ → AmbientSpace → ℝ := fun R x => if x ∈ ball 0 R then v R x else 0
  have hwc : ∀ R, R₀ + 1 ≤ R → ContinuousOn (w R) (ball 0 R) := by
    intro R hR
    have hR' : R₀ < R := by linarith
    exact (hv R hR').1.congr (fun x hx => by simp only [w, ite_eq_left hx])
  have hwh : ∀ R, R₀ + 1 ≤ R →
      HasDistributionalLaplacianOn (w R) (fun _ => 0) (ball 0 R \ K) := by
    intro R hR
    have hR' : R₀ < R := by linarith
    change HasDistributionalLaplacianOn (w R) (fun _ => 0) (annularDomain K R)
    apply (hz R).harmonic.congr_ae _ EventuallyEq.rfl
    filter_upwards [(hv R hR').2.1, ae_restrict_mem (annularDomain_isOpen hK R).measurableSet]
      with x he hx
    simpa only [w, ite_eq_left hx.1] using he.symm
  have hw1 : ∀ R, R₀ + 1 ≤ R → ∀ x ∈ K, w R x = 1 := by
    intro R hR x hx
    have hR' : R₀ < R := by linarith
    rw [show w R x = v R x from ite_eq_left ((ball_subset_ball hR'.le) (hKR hx))]
    exact (hv R hR').2.2 x hx
  have hw01 : ∀ R, R₀ + 1 ≤ R → ∀ x, 0 ≤ w R x ∧ w R x ≤ 1 := by
    intro R hR x
    dsimp only [w]
    split_ifs with hx
    · exact hv01 R (by linarith) x hx
    · exact ⟨le_rfl, zero_le_one⟩
  have hwmono : ∀ R R', R₀ + 1 ≤ R → R ≤ R' → ∀ x, w R x ≤ w R' x := by
    intro R R' hR hRR x
    by_cases hx : x ∈ ball (0 : AmbientSpace) R
    · have hx' := ball_subset_ball hRR hx
      simpa only [w, ite_eq_left hx, ite_eq_left hx'] using hvmono R R' (by linarith) hRR x hx
    · simpa only [w, ite_eq_right hx] using (hw01 R' (hR.trans hRR) x).1
  have hwbar : ∀ R, R₀ + 1 ≤ R → ∀ x ∉ K, w R x ≤ R₀ / ‖x‖ := by
    intro R hR x hxK
    dsimp only [w]
    split_ifs with hx
    · exact hvbar R (by linarith) x ⟨hx, hxK⟩
    · exact div_nonneg hR₀.le (norm_nonneg x)
  obtain ⟨u, hc, hh, hs, h1, hd, hb, hbar, -⟩ :=
    capacitary_potential_of_annular_family hK
      (hKR.trans (ball_subset_ball (show R₀ ≤ R₀ + 1 by linarith)))
      w hwc hwh hw1 hw01 hwmono hwbar
  exact ⟨u, hc, hh, hs, h1, hd, hb, hbar⟩

end LiquidDrop
