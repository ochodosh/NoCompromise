import NoCompromise.Stationary.CapEstimateAssembly
import NoCompromise.Capacity.LocalExtension
import NoCompromise.Capacity.HullPotential
import NoCompromise.Capacity.HullPotentialCaccioppoliBound
import NoCompromise.Elliptic.BoundaryC2aLocalAssembly
import NoCompromise.Elliptic.BoundaryC2aShear
import NoCompromise.Elliptic.BoundaryC2aPullback
import NoCompromise.Elliptic.BoundaryC2aReflection
import NoCompromise.Elliptic.BoundaryC2aFlatTraceZero

/-!
# `thm:boundary-C2a` for the capacitary potential of the filled hull

The named predicate `HullPotentialBoundaryC2` (Stationary/CapEstimateAssembly.lean) is proved.
At a point `p ∈ ∂K`, `K = filledHull Ω`, a `C³` chart of `Kᶜ` gives the shear flattening `Θ`
(`boundaryShearMap`, a global `C³` diffeomorphism). The flattened potential `w = u ∘ Θ` solves
`div (A ∇w) = 0` weakly on the unit half ball with `A` the `C²` Dirichlet pullback coefficient
(`isWeakDivergenceEquationOn_dirichletPullback`), is `H¹` there by the boundary Caccioppoli
estimate (`exterior_gradient_sq_integrableOn`) and the `L²` pullback, and `w - 1` has zero flat
trace (`hasZeroFlatTraceOn_of_continuousOn`). `boundary_c2a_local_of_h1` with `φ ≡ 1` gives a
`C²` representative with Hölder second derivatives on a slab above the face; the three-term
reflection (`boundary_c2_reflection`) extends it to a `C²` function across the face, which is
transported back by `Θ⁻¹`, cut off, and glued over `∂K` by
`filledHull_capacitary_c2_extension_of_local`.
-/

noncomputable section
open MeasureTheory Set Filter Metric Topology InnerProductSpace
open scoped Gradient

namespace LiquidDrop

/-- A function `C²` on an open set agrees near a compact subset with a global `C²` function. -/
theorem hullPotential_exists_global_c2_near_compact {U K : Set AmbientSpace} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {f : AmbientSpace → ℝ} (hf : ContDiffOn ℝ 2 f U) :
    ∃ w : AmbientSpace → ℝ, ContDiff ℝ 2 w ∧ ∀ x ∈ K, w =ᶠ[𝓝 x] f := by
  obtain ⟨χ, hcχ, _, hsχ, hχ, _⟩ := exists_smooth_cutoff_one_near_compact hK hU hKU
  have hcχ2 : ContDiff ℝ 2 χ := hcχ.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨fun x => χ x * f x, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ U
    · exact hcχ2.contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
    · have hxt : x ∉ tsupport χ := fun ht => hx (hsχ ht)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hxt] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · intro x hx
    filter_upwards [hχ.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp only [hy, one_mul]

/-- The fixed reflection slab lies in the `C²` slab of `boundary_c2a_local_of_h1` at the origin. -/
lemma hullPotential_reflectUpper_subset :
    boundaryReflectUpper (1 / 8388608) (1 / 8796093022208) ⊆
      (fun y => (0 : AmbientSpace) + (1 / 2097152 : ℝ) • y) '' boundaryNondivC2Slab := by
  rintro y ⟨hy1, hy2, hy3⟩
  refine ⟨(2097152 : ℝ) • y, ?_, ?_⟩
  · change (4 / 3 : ℝ) • ((2097152 : ℝ) • y) ∈ boundaryC1UpperSlab
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change graphProjectionN 2 ((4 / 3 : ℝ) • ((2097152 : ℝ) • y)) ∈ ball 0 (5 / 8)
      rw [mem_ball_zero_iff, map_smul, map_smul, norm_smul, norm_smul, Real.norm_of_nonneg
        (by norm_num), Real.norm_of_nonneg (by norm_num)]
      nlinarith
    · change |((4 / 3 : ℝ) • ((2097152 : ℝ) • y)) (Fin.last 2)| < 1 / 1048576
      simp only [PiLp.smul_apply, smul_eq_mul]
      rw [abs_of_pos (by positivity)]
      nlinarith
    · change 0 < ((4 / 3 : ℝ) • ((2097152 : ℝ) • y)) (Fin.last 2)
      simp only [PiLp.smul_apply, smul_eq_mul]
      positivity
  · simp only [zero_add, smul_smul]
    norm_num

lemma hullPotential_reflectSlab_subset_c1Slab :
    boundaryReflectSlab (1 / 8388608) (1 / 8796093022208) ⊆ boundaryC1Slab := by
  rintro y ⟨hy1, hy2⟩
  refine ⟨?_, ?_⟩
  · change graphProjectionN 2 y ∈ ball 0 (5 / 8)
    rw [mem_ball_zero_iff]
    linarith
  · change |y (Fin.last 2)| < 1 / 1048576
    linarith

lemma hullPotential_reflectSlab_subset_ball :
    boundaryReflectSlab (1 / 8388608) (1 / 8796093022208) ⊆ ball (0 : AmbientSpace) 1 := by
  rintro y ⟨hy1, hy2⟩
  rw [mem_ball_zero_iff]
  have hsq := norm_sq_graphProjectionN y
  have h1 : ‖graphProjectionN 2 y‖ ^ 2 < 1 / 4 := by
    have h0 := norm_nonneg (graphProjectionN 2 y)
    nlinarith
  have h2 : y (Fin.last 2) ^ 2 < 1 / 4 := by
    have := sq_abs (y (Fin.last 2))
    nlinarith [abs_nonneg (y (Fin.last 2))]
  have h3 : ‖y‖ ^ 2 < 1 := by linarith
  nlinarith [norm_nonneg y]

/-- Local form of `thm:boundary-C2a` for the capacitary potential of the filled hull: near every
point of `∂K`, `u` agrees on `closure Kᶜ` with a global `C²` function. -/
theorem hullPotential_local_c2_extension {Ω : Set AmbientSpace} (ho : IsOpen Ω)
    (hbd : Bornology.IsBounded Ω) (h3 : HasCkBoundary 3 Ω) (h0 : (0 : AmbientSpace) ∈ Ω)
    {u : AmbientSpace → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) (filledHull Ω)ᶜ)
    (h1 : ∀ x ∈ filledHull Ω, u x = 1) (hinf : Tendsto u (cocompact AmbientSpace) (𝓝 0)) :
    ∀ p ∈ frontier (filledHull Ω), ∃ U : Set AmbientSpace, IsOpen U ∧ p ∈ U ∧
      ∃ g : AmbientSpace → ℝ, ContDiff ℝ 2 g ∧ EqOn u g (U ∩ closure (filledHull Ω)ᶜ) := by
  intro p hp
  set K := filledHull Ω with hKdef
  have hKc : IsClosed K := filledHull_isClosed Ω
  have hKo : IsOpen Kᶜ := hKc.isOpen_compl
  have hsigns := (filledHull_capacitary_properties ho hbd h0 hu hh h1 hinf).1
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ :=
    hh.contDiffOn_of_continuous (by norm_num) hKo hu.continuousOn
  have hu1 : ContDiffOn ℝ 1 u Kᶜ := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu2 : ContDiffOn ℝ 2 u Kᶜ := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  -- a `C³` chart of `Kᶜ` at `p`
  have hpi : p ∈ frontier (interior K) := by rwa [filledHull_frontier_interior ho]
  obtain ⟨c, hc, hpc, hh3⟩ := filledHull_hasCkBoundary_interior h3 ho p hpi
  have hcl : closure (interior (filledHull Ω)) = filledHull Ω :=
    (filledHull_eq_closure_interior ho).symm
  have hc' : c.exteriorChart.IsChartFor Kᶜ := by
    have h := hc.exterior
    rw [hcl] at h
    exact h
  have hpf : p ∈ frontier Kᶜ := by rwa [frontier_compl]
  have hpc' : p ∈ c.exteriorChart.region := hpc
  have hh3' : ContDiff ℝ (3 : ℕ) c.exteriorChart.height := by
    have : ContDiff ℝ 3 (fun x => -c.height x) := hh3.neg
    exact_mod_cast this
  set c' := c.exteriorChart with hc'def
  set a := graphProjectionN 2 (c'.placement.symm p) with hadef
  obtain ⟨ρ, hρ, hreg⟩ := exists_boundaryShearMap_region hc' hpf hpc'
  set Θ := boundaryShearMap c' a ρ with hΘdef
  set Θi := boundaryShearInv c' a ρ with hΘidef
  have hl : Function.LeftInverse Θi Θ := boundaryShearMap_leftInverse c' a hρ.ne'
  have hr : Function.RightInverse Θi Θ := boundaryShearMap_rightInverse c' a hρ.ne'
  have hΘ3 : ContDiff ℝ (3 : ℕ) Θ := contDiff_boundaryShearMap c' a ρ hh3'
  have hΘi3 : ContDiff ℝ (3 : ℕ) Θi := contDiff_boundaryShearInv c' a ρ hh3'
  have hΘ1 : ContDiff ℝ 1 Θ := hΘ3.of_le (by norm_num)
  have hΘi1 : ContDiff ℝ 1 Θi := hΘi3.of_le (by norm_num)
  have hΘ0 : Θ 0 = p := boundaryShearMap_zero hc' hpf hpc' ρ
  have hmem : ∀ y ∈ closedBall (0 : AmbientSpace) 2, (Θ y ∈ Kᶜ ↔ 0 < y (Fin.last 2)) :=
    fun y hy => boundaryShearMap_mem_iff hc' a hρ (hreg y hy)
  have hmemcl : ∀ y ∈ closedBall (0 : AmbientSpace) 2,
      (Θ y ∈ closure Kᶜ ↔ 0 ≤ y (Fin.last 2)) :=
    fun y hy => boundaryShearMap_mem_closure_iff hc' a hρ (hreg y hy)
  have hball12 : ball (0 : AmbientSpace) 1 ⊆ closedBall 0 2 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  -- the flattened potential
  set w : AmbientSpace → ℝ := u ∘ Θ with hwdef
  have hwc : Continuous w := hu.comp hΘ1.continuous
  have hw1 : ∀ y ∈ closedBall (0 : AmbientSpace) 2, y (Fin.last 2) ≤ 0 → w y = 1 := by
    intro y hy ht
    apply h1
    by_contra hK
    exact absurd ((hmem y hy).mp hK) (not_lt.mpr ht)
  have hwb : ∀ y, |w y| ≤ 1 := by
    intro y
    by_cases hy : Θ y ∈ K
    · simp [w, h1 _ hy]
    · obtain ⟨h0', h1'⟩ := hsigns _ hy
      rw [abs_le]
      constructor <;> simp only [w, Function.comp] <;> linarith
  have hhalf : MapsTo Θ (boundaryHalfBall 1) Kᶜ := fun y hy =>
    (hmem y (hball12 hy.1)).mpr hy.2
  have hwC2 : ContDiffOn ℝ 2 w (boundaryHalfBall 1) :=
    hu2.comp (hΘ3.of_le (by norm_num)).contDiffOn hhalf
  have hU1 : IsOpen (boundaryHalfBall 1) := isOpen_boundaryHalfBall 1
  -- weak equation
  have hweak := isWeakDivergenceEquationOn_dirichletPullback hΘ1 hΘi1 hl hr hKo hhalf hu1
    (isWeakDivergenceEquationOn_id_of_harmonic hKo hu.continuousOn hh)
  -- H¹ on the half ball
  have hbdU : Bornology.IsBounded (boundaryHalfBall 1) :=
    isBounded_ball.subset inter_subset_left
  obtain ⟨R, hR⟩ := c'.bounded_region.subset_ball p
  have hL2 : IntegrableOn (fun x => ‖gradient u x‖ ^ 2) (Θ '' boundaryHalfBall 1) := by
    refine (exterior_gradient_sq_integrableOn hKc hu hh h1 hsigns p R).mono_set ?_
    rintro z ⟨y, hy, rfl⟩
    exact ⟨hhalf hy, hR (hreg y (hball12 hy.1))⟩
  have hgradL2 : MemLp (gradient w) 2 (volume.restrict (boundaryHalfBall 1)) :=
    memLp_gradient_comp_dirichletPullback hΘ1 hΘi1 hl hr hKo hU1 hhalf hbdU hu1 hL2
  have : IsFiniteMeasure (volume.restrict (boundaryHalfBall 1)) :=
    isFiniteMeasure_restrict.mpr hbdU.measure_lt_top.ne
  have hwL2 : MemLp w 2 (volume.restrict (boundaryHalfBall 1)) :=
    MemLp.of_bound hwc.aestronglyMeasurable 1
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hwb y)
  have hH1 : HasH1GradientOn w (gradient w) (boundaryHalfBall 1) :=
    ⟨hasWeakGradientOn_of_contDiffOn hU1 (hwC2.of_le (by norm_num)), hwL2, hgradL2⟩
  -- zero trace of `w - 1`
  have hgc : gradient (fun _ : AmbientSpace => (1 : ℝ)) = fun _ => 0 := by
    funext x
    simp [gradient]
  have htr : HasZeroFlatTraceOn (fun x => w x - (fun _ : AmbientSpace => (1 : ℝ)) x)
      (fun x => gradient w x - gradient (fun _ : AmbientSpace => (1 : ℝ)) x) (ball 0 1) := by
    apply hasZeroFlatTraceOn_of_continuousOn
    · exact (hwc.sub continuous_const).continuousOn
    · exact (hwC2.of_le (by norm_num)).sub contDiffOn_const
    · intro x _
      simp only [hgc, sub_zero]
      simp [gradient, fderiv_sub_const]
    · simp only [hgc, sub_zero]
      exact (hgradL2.integrable one_le_two).norm
    · intro x hx ht
      simp [hw1 x (hball12 hx) ht.le]
  -- boundary C²,α from H¹
  set α : ℝ := 1 / 2 with hαdef
  set S := closure (boundaryHalfBall 1) with hSdef
  have hScpt : IsCompact S :=
    (isCompact_closedBall (0 : AmbientSpace) 1).of_isClosed_subset isClosed_closure
      (closure_minimal (fun x hx => ball_subset_closedBall hx.1) isClosed_closedBall)
  set A := dirichletPullbackCoefficient Θ with hAdef
  have hA2 : ContDiff ℝ 2 A := contDiff_dirichletPullbackCoefficient hΘ3 hΘi1 hl hr
  obtain ⟨lam, cap, hlam, hlamcap, hbnd⟩ := dirichletPullbackCoefficient_bounds hΘ1 hΘi1 hl hr hScpt
  have hα0 : (0 : ℝ) < α := by norm_num [hαdef]
  have hα1 : α ≤ 1 := by norm_num [hαdef]
  have hAh : HasC1HolderOn α A S := hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα0 hα1 hA2
  have hφh : HasC1HolderOn α (fun _ : AmbientSpace => (1 : ℝ)) S :=
    hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα0 hα1 contDiff_const
  have hgφh : HasC1HolderOn α (gradient fun _ : AmbientSpace => (1 : ℝ)) S := by
    rw [hgc]
    exact hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα0 hα1 contDiff_const
  have hGh : HasC1HolderOn α (fun _ : AmbientSpace => (0 : AmbientSpace)) S :=
    hasC1HolderOn_closure_boundaryHalfBall_of_contDiff hα0 hα1 contDiff_const
  obtain ⟨C, _, hmain⟩ := boundary_c2a_local_of_h1 (α := α) (lam := lam) (cap := cap)
    (M := nondivC1HolderNorm α A S)
    (N := nondivC1HolderNorm α (fun _ : AmbientSpace => (1 : ℝ)) S +
      nondivC1HolderNorm α (gradient fun _ : AmbientSpace => (1 : ℝ)) S +
      nondivC1HolderNorm α (fun _ : AmbientSpace => (0 : AmbientSpace)) S)
    (P₁ := 0) (P₂ := 0)
    (E := ∫ x in boundaryHalfBall 1,
      ‖gradient w x - gradient (fun _ : AmbientSpace => (1 : ℝ)) x‖ ^ 2)
    hα0 (by norm_num [hαdef]) hlam hlamcap hAh.norm_nonneg
    (add_nonneg (add_nonneg hφh.norm_nonneg hgφh.norm_nonneg) hGh.norm_nonneg) le_rfl le_rfl
    (integral_nonneg fun _ => by positivity)
  obtain ⟨W, v, hWo, hWslab, hv1, hvae, hvface, hv2⟩ :=
    hmain w (fun _ => 1) (gradient w) (fun _ => 0) A contDiff_const hAh hGh hφh hgφh le_rfl le_rfl
      (fun x hx => (hbnd x hx).1) (fun x hx => (hbnd x hx).2)
      (fun x _ => by simp [hgc]) (fun x _ y _ => by simp [hgc]) hH1 hweak htr le_rfl
  obtain ⟨hv2c, hent⟩ := hv2 0 (by simp) (by simp)
  -- reflection across the face
  obtain ⟨V, hV2, hVv⟩ := boundary_c2_reflection (a := 1 / 8388608) (b := 1 / 8796093022208)
    (α := α) (C := C) (by norm_num) (by norm_num) hα0 hWo
    (fun y hy ht => hWslab (hullPotential_reflectSlab_subset_c1Slab
      ⟨hy, by rw [ht, abs_zero]; norm_num⟩))
    hv1 (hv2c.mono hullPotential_reflectUpper_subset)
    (fun i j x hx y hy => (hent i j).2 x (hullPotential_reflectUpper_subset hx) y
      (hullPotential_reflectUpper_subset hy))
  set O := boundaryReflectSlab (1 / 8388608) (1 / 8796093022208) with hOdef
  have hupper : IsOpen (W ∩ {x : AmbientSpace | 0 < x (Fin.last 2)}) :=
    hWo.inter (isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous)
  have hvw : EqOn v w (W ∩ {x | 0 < x (Fin.last 2)}) :=
    Measure.eqOn_open_of_ae_eq hvae hupper (hv1.continuousOn.mono inter_subset_left)
      hwc.continuousOn
  have hVw : ∀ y ∈ O, 0 ≤ y (Fin.last 2) → V y = w y := by
    intro y hy ht
    have hyW : y ∈ W := hWslab (hullPotential_reflectSlab_subset_c1Slab hy)
    rw [hVv y hy ht]
    rcases ht.lt_or_eq with ht | ht
    · exact hvw ⟨hyW, ht⟩
    · rw [hvface y hyW ht.symm,
        hw1 y (hball12 (hullPotential_reflectSlab_subset_ball hy)) ht.symm.le]
  -- back to ambient coordinates
  have hOo : IsOpen O := isOpen_boundaryReflectSlab _ _
  have h0O : (0 : AmbientSpace) ∈ O := by
    refine ⟨?_, ?_⟩ <;> simp
  set O' := Θi ⁻¹' O with hO'def
  have hO'o : IsOpen O' := hOo.preimage hΘi1.continuous
  have hpO' : p ∈ O' := by
    change Θi p ∈ O
    rw [← hΘ0, hl 0]
    exact h0O
  have hg0 : ContDiffOn ℝ 2 (V ∘ Θi) O' :=
    hV2.comp (hΘi3.of_le (by norm_num)).contDiffOn (fun z hz => hz)
  obtain ⟨g, hg2, hge⟩ := hullPotential_exists_global_c2_near_compact hO'o isCompact_singleton
    (singleton_subset_iff.mpr hpO') hg0
  obtain ⟨U, hUeq, hUo, hpU⟩ := _root_.eventually_nhds_iff.mp (hge p rfl)
  refine ⟨U ∩ O', hUo.inter hO'o, ⟨hpU, hpO'⟩, g, hg2, ?_⟩
  rintro z ⟨⟨hzU, hzO⟩, hzcl⟩
  rw [hUeq z hzU]
  have hzy : Θ (Θi z) = z := hr z
  have hyB : Θi z ∈ closedBall (0 : AmbientSpace) 2 :=
    hball12 (hullPotential_reflectSlab_subset_ball hzO)
  have ht : 0 ≤ (Θi z) (Fin.last 2) := (hmemcl _ hyB).mp (by rw [hzy]; exact hzcl)
  change u z = V (Θi z)
  rw [hVw _ hzO ht]
  simp only [w, Function.comp, hzy]

/-- `thm:boundary-C2a` applied to the capacitary potential of the filled hull
(`thm:capacitary-potential`, regularity up to `∂K`): the named predicate
`HullPotentialBoundaryC2` holds. -/
theorem hullPotentialBoundaryC2 : HullPotentialBoundaryC2 := by
  intro Ω ho hbd h3 h0 u hu hh h1 hinf
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) u (filledHull Ω)ᶜ :=
    hh.contDiffOn_of_continuous (by norm_num) (filledHull_isClosed Ω).isOpen_compl
      hu.continuousOn
  exact filledHull_capacitary_c2_extension_of_local hbd hsm
    (hullPotential_local_c2_extension ho hbd h3 h0 hu hh h1 hinf)

end LiquidDrop
