import NoCompromise.Topology.ParityCrossing
import NoCompromise.Topology.ParityEndpoint

/-!
# Path independence of intersection parity

The intersection parity of a transverse path depends only on its endpoints:
`prop:orientation-parity (i)`. Reversal and endpoint normalization allow two paths
to form the boundary of a smooth Cartesian disk interpolation. Boundary parity
then proves path independence. The resulting parity predicate is locally
constant off the surface and changes across a transverse segment.
-/

namespace LiquidDrop

noncomputable section
open Set

/-- prop:orientation-parity (i): reversal preserves transversality pointwise. -/
theorem transverseAt_reverse_iff {S : Set E₃}
    {α : EuclideanSpace ℝ (Fin 1) → E₃} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    (p : EuclideanSpace ℝ (Fin 1)) :
    TransverseAt S (α ∘ fun q => -q) p ↔ TransverseAt S α (-p) := by
  have hd := ((hα.differentiable (by simp) (-p)).hasFDerivAt.comp p
    (hasFDerivAt_id p).neg).fderiv
  have hr : LinearMap.range
      (fderiv ℝ (α ∘ fun q => -q) p : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] E₃) =
      LinearMap.range (fderiv ℝ α (-p) : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] E₃) := by
    rw [hd]
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨-u, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨-u, by simp⟩
  simp only [TransverseAt, Function.comp_apply, hr]

/-- prop:orientation-parity (i): reversal preserves transversality on the path interval. -/
theorem transverse_reverse_iff {S : Set E₃}
    {α : EuclideanSpace ℝ (Fin 1) → E₃} (hα : ContDiff ℝ (⊤ : ℕ∞) α) :
    (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1,
      TransverseAt S (α ∘ fun q => -q) p) ↔
    (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α p) := by
  constructor
  · intro ht p hp
    simpa using (transverseAt_reverse_iff hα (-p)).mp (ht (-p) (by simpa using hp))
  · intro ht p hp
    exact (transverseAt_reverse_iff hα p).mpr (ht (-p) (by simpa using hp))

/-- prop:orientation-parity (i): reversal preserves the intersection count, even without
smoothness or finiteness assumptions. -/
theorem ncard_intersections_reverse (S : Set E₃) (α : EuclideanSpace ℝ (Fin 1) → E₃) :
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ (α ∘ fun q => -q) ⁻¹' S).ncard =
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S).ncard := by
  apply Set.ncard_congr (fun p _ => -p)
  · rintro p ⟨hp, hS⟩
    exact ⟨by simpa using hp, hS⟩
  · intro p q hp hq he
    exact neg_injective he
  · rintro p ⟨hp, hS⟩
    exact ⟨-p, ⟨by simpa using hp, by simpa using hS⟩, neg_neg p⟩

/-- prop:orientation-parity (i): freeze both endpoints of a transverse path without changing
its endpoints or intersection count. The common collar includes its inner boundary. -/
theorem exists_transverse_path_normalization {S : Set E₃} (hc : IsCompact S)
    {α : EuclideanSpace ℝ (Fin 1) → E₃} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    (htα : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α p)
    (hz : α (EuclideanSpace.single 0 (-1)) ∉ S)
    (hx : α (EuclideanSpace.single 0 1) ∉ S) :
    ∃ β : EuclideanSpace ℝ (Fin 1) → E₃, ContDiff ℝ (⊤ : ℕ∞) β ∧
      β (EuclideanSpace.single 0 (-1)) = α (EuclideanSpace.single 0 (-1)) ∧
      β (EuclideanSpace.single 0 1) = α (EuclideanSpace.single 0 1) ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S β p) ∧
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ β ⁻¹' S).ncard =
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S).ncard ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧
        (∀ p : EuclideanSpace ℝ (Fin 1), p 0 ≤ -1 + η →
          β p = α (EuclideanSpace.single 0 (-1))) ∧
        (∀ p : EuclideanSpace ℝ (Fin 1), 1 - η ≤ p 0 →
          β p = α (EuclideanSpace.single 0 1)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hc.isClosed.isOpen_compl _ hx
  have hdisj : Disjoint (Metric.ball (α (EuclideanSpace.single 0 1)) r) S :=
    Set.disjoint_left.mpr fun _ ha hS => hball ha hS
  obtain ⟨α₁, hα₁, hα₁left, hα₁end, ⟨η₁, hη₁, hα₁right⟩, htα₁, hα₁S⟩ :=
    exists_transverse_path_endpoint_shift hα htα hdisj rfl (Metric.mem_ball_self hr)
  have hα₁start : α₁ (EuclideanSpace.single 0 (-1)) = α (EuclideanSpace.single 0 (-1)) :=
    hα₁left _ (by simp)
  have hrev : ContDiff ℝ (⊤ : ℕ∞) (α₁ ∘ fun p => -p) := hα₁.comp contDiff_id.neg
  have hn (s : ℝ) : -(EuclideanSpace.single 0 s : EuclideanSpace ℝ (Fin 1)) =
      EuclideanSpace.single 0 (-s) := by ext i; fin_cases i; simp
  obtain ⟨r', hr', hball'⟩ := Metric.isOpen_iff.mp hc.isClosed.isOpen_compl _ hz
  have hdisj' : Disjoint (Metric.ball (α (EuclideanSpace.single 0 (-1))) r') S :=
    Set.disjoint_left.mpr fun _ ha hS => hball' ha hS
  have hrevEnd : (α₁ ∘ fun p => -p) (EuclideanSpace.single 0 1) =
      α (EuclideanSpace.single 0 (-1)) := by simpa [hn] using hα₁start
  obtain ⟨α₂, hα₂, hα₂left, hα₂end, ⟨η₂, hη₂, hα₂right⟩, htα₂, hα₂S⟩ :=
    exists_transverse_path_endpoint_shift hrev ((transverse_reverse_iff hα₁).mpr htα₁)
      hdisj' hrevEnd (Metric.mem_ball_self hr')
  refine ⟨α₂ ∘ fun p => -p, hα₂.comp contDiff_id.neg, ?_, ?_,
    (transverse_reverse_iff hα₂).mpr htα₂, ?_, ?_⟩
  · simpa [hn] using hα₂end
  · simpa [hn] using (hα₂left (EuclideanSpace.single 0 (-1)) (by simp)).trans
      (show (α₁ ∘ fun p => -p) (EuclideanSpace.single 0 (-1)) =
        α (EuclideanSpace.single 0 1) by simpa [hn] using hα₁end)
  · rw [ncard_intersections_reverse, hα₂S, ncard_intersections_reverse, hα₁S]
  · refine ⟨min (min η₁ η₂) 1 / 2, by positivity, ?_, ?_, ?_⟩
    · have := min_le_right (min η₁ η₂) (1 : ℝ)
      linarith
    · intro p hp
      apply hα₂right
      change 1 - η₂ < -(p 0)
      have := (min_le_left (min η₁ η₂) (1 : ℝ)).trans (min_le_right η₁ η₂)
      linarith [lt_min (lt_min hη₁ hη₂) zero_lt_one]
    · intro p hp
      change α₂ (-p) = _
      rw [hα₂left (-p) (by
        change -(p 0) ≤ 0
        have := min_le_right (min η₁ η₂) (1 : ℝ)
        linarith)]
      simp only [Function.comp_apply, neg_neg]
      apply hα₁right
      have := (min_le_left (min η₁ η₂) (1 : ℝ)).trans (min_le_left η₁ η₂)
      linarith [lt_min (lt_min hη₁ hη₂) zero_lt_one]

/-- prop:orientation-parity (i): Cartesian equation of the parameter circle. -/
theorem mem_unit_circle_iff (q : EuclideanSpace ℝ (Fin 2)) :
    q ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔ q 0 ^ 2 + q 1 ^ 2 = 1 := by
  have hn : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [Metric.mem_sphere, dist_zero_right]
  constructor
  · intro h; rw [h] at hn; linarith
  · intro h; nlinarith [norm_nonneg q]

/-- prop:orientation-parity (i): projection identifies either open semicircle's intersections
with the path intersections, provided the path endpoints are off the surface. -/
theorem bijOn_semicircle_intersections {S : Set E₃}
    (α : EuclideanSpace ℝ (Fin 1) → E₃)
    (hz : α (EuclideanSpace.single 0 (-1)) ∉ S)
    (hx : α (EuclideanSpace.single 0 1) ∉ S)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    Set.BijOn (fun q : EuclideanSpace ℝ (Fin 2) => EuclideanSpace.single 0 (q 0))
      {q | q ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
        0 < σ * q 1 ∧ α (EuclideanSpace.single 0 (q 0)) ∈ S}
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S) := by
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · rintro q ⟨hq, -, hqS⟩
    refine ⟨?_, hqS⟩
    rw [mem_closedBall_zero_iff, euclideanSpace_fin_one_norm_eq]
    simp only [EuclideanSpace.single, PiLp.single_apply, ite_true]
    rw [abs_le]
    have := (mem_unit_circle_iff q).mp hq
    constructor <;> nlinarith [sq_nonneg (q 1)]
  · rintro q ⟨hq, hqsgn, -⟩ r ⟨hr, hrsgn, -⟩ he
    have he0 : q 0 = r 0 := by
      simpa using congrArg (fun p : EuclideanSpace ℝ (Fin 1) => p 0) he
    have hqeq := (mem_unit_circle_iff q).mp hq
    have hreq := (mem_unit_circle_iff r).mp hr
    rw [he0] at hqeq
    have he1 : q 1 = r 1 := by
      rcases hσ with rfl | rfl <;> norm_num at hqsgn hrsgn <;> nlinarith
    ext i
    fin_cases i
    · exact he0
    · exact he1
  · rintro p ⟨hp, hpS⟩
    have hpbd : |p 0| ≤ 1 := by
      rw [← euclideanSpace_fin_one_norm_eq]; simpa using hp
    have hp0 : -1 < p 0 ∧ p 0 < 1 := by
      have hne0 : p 0 ≠ -1 := fun he => hz (by
        rw [euclideanSpace_fin_one_eq_single p, he] at hpS; exact hpS)
      have hne1 : p 0 ≠ 1 := fun he => hx (by
        rw [euclideanSpace_fin_one_eq_single p, he] at hpS; exact hpS)
      exact ⟨lt_of_le_of_ne (abs_le.mp hpbd).1 (Ne.symm hne0),
        lt_of_le_of_ne (abs_le.mp hpbd).2 hne1⟩
    have hpos : 0 < 1 - p 0 ^ 2 := by nlinarith [hp0.1, hp0.2]
    let q : EuclideanSpace ℝ (Fin 2) :=
      EuclideanSpace.single 0 (p 0) + EuclideanSpace.single 1 (σ * Real.sqrt (1 - p 0 ^ 2))
    have hq0 : q 0 = p 0 := by simp [q]
    have hq1 : q 1 = σ * Real.sqrt (1 - p 0 ^ 2) := by simp [q]
    refine ⟨q, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [mem_unit_circle_iff, hq0, hq1, mul_pow, hσsq, one_mul,
        Real.sq_sqrt hpos.le]
      ring
    · rw [hq1, ← mul_assoc, ← pow_two, hσsq, one_mul]
      exact Real.sqrt_pos.mpr hpos
    · rwa [hq0, ← euclideanSpace_fin_one_eq_single p]
    · change EuclideanSpace.single 0 (q 0) = p
      rw [hq0, ← euclideanSpace_fin_one_eq_single p]

/-- prop:orientation-parity (i): a transverse path, pulled back by the first coordinate,
is transverse along the circle wherever the second coordinate is nonzero. -/
theorem boundaryTransverseAt_of_path_projection {S : Set E₃}
    {α : EuclideanSpace ℝ (Fin 1) → E₃} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    {F : EuclideanSpace ℝ (Fin 2) → E₃} {q : EuclideanSpace ℝ (Fin 2)}
    (heq : F =ᶠ[nhds q] fun r => α (EuclideanSpace.single 0 (r 0)))
    (hq1 : q 1 ≠ 0) (ht : TransverseAt S α (EuclideanSpace.single 0 (q 0))) :
    BoundaryTransverseAt S F q := by
  let P : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight (EuclideanSpace.single 0 1)
  have hP (r : EuclideanSpace ℝ (Fin 2)) : P r = EuclideanSpace.single 0 (r 0) := by
    ext i; fin_cases i; simp [P]
  have hd : fderiv ℝ F q = (fderiv ℝ α (P q)).comp P := by
    rw [heq.fderiv_eq]
    have he : (fun r => α (EuclideanSpace.single 0 (r 0))) = α ∘ P := by
      funext r; rw [Function.comp_apply, hP]
    rw [he]
    exact ((hα.differentiable (by simp) (P q)).hasFDerivAt.comp q P.hasFDerivAt).fderiv
  have hrange : LinearMap.range
      (fderiv ℝ α (P q) : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] E₃) ≤
      Submodule.map (fderiv ℝ F q : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E₃) (ℝ ∙ q)ᗮ := by
    rintro _ ⟨u, rfl⟩
    let w : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (u 0) +
      EuclideanSpace.single 1 (-(q 0 * u 0) / q 1)
    refine ⟨w, ?_, ?_⟩
    · change w ∈ (ℝ ∙ q)ᗮ
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      simp [w, PiLp.inner_apply, Fin.sum_univ_two]
      field_simp [hq1]
      ring
    · change fderiv ℝ F q w = fderiv ℝ α (P q) u
      have hw : P w = u := by
        rw [hP]
        simpa [w] using (euclideanSpace_fin_one_eq_single u).symm
      rw [hd, ContinuousLinearMap.comp_apply, hw]
  intro hmem
  have hval := heq.eq_of_nhds
  have ht' := ht (hval ▸ hmem)
  rw [← hP] at ht'
  apply top_unique
  rw [← ht']
  exact sup_le_sup hrange (by rw [hval, hP])

/-- prop:orientation-parity (i): path independence for paths already constant on common
endpoint collars. A Cartesian interpolation fills the loop formed by the two paths. -/
theorem even_add_ncard_transverse_paths_of_constant_ends {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {α β : EuclideanSpace ℝ (Fin 1) → E₃}
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (htα : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α p)
    (htβ : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S β p)
    {z x : E₃} (hz : z ∉ S) (hx : x ∉ S) {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hαz : ∀ p : EuclideanSpace ℝ (Fin 1), p 0 ≤ -1 + η → α p = z)
    (hαx : ∀ p : EuclideanSpace ℝ (Fin 1), 1 - η ≤ p 0 → α p = x)
    (hβz : ∀ p : EuclideanSpace ℝ (Fin 1), p 0 ≤ -1 + η → β p = z)
    (hβx : ∀ p : EuclideanSpace ℝ (Fin 1), 1 - η ≤ p 0 → β p = x) :
    Even ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S).ncard +
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ β ⁻¹' S).ncard) := by
  let P : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight (EuclideanSpace.single 0 1)
  have hP (q : EuclideanSpace ℝ (Fin 2)) : P q = EuclideanSpace.single 0 (q 0) := by
    ext i; fin_cases i; simp [P]
  have hP0 (q : EuclideanSpace ℝ (Fin 2)) : (P q) 0 = q 0 := by simp [hP]
  let ψ : ℝ → ℝ := fun s => Real.smoothTransition ((s + η / 2) / η)
  have hψ0 (s : ℝ) (hs : s ≤ -η / 2) : ψ s = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le)
  have hψ1 (s : ℝ) (hs : η / 2 ≤ s) : ψ s = 1 :=
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hη]; linarith)
  let F : EuclideanSpace ℝ (Fin 2) → E₃ :=
    fun q => ψ (q 1) • α (P q) + (1 - ψ (q 1)) • β (P q)
  have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun q : EuclideanSpace ℝ (Fin 2) => q 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun q : EuclideanSpace ℝ (Fin 2) => ψ (q 1)) :=
    Real.smoothTransition.contDiff.comp ((hcoord.add contDiff_const).div_const η)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (hψ.smul (hα.comp P.contDiff)).add ((contDiff_const.sub hψ).smul (hβ.comp P.contDiff))
  have hband : ∀ q ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      -η < q 1 → q 1 < η → α (P q) ∉ S ∧ β (P q) ∉ S ∧ F q ∉ S := by
    intro q hq hlo hhi
    have hcircle := (mem_unit_circle_iff q).mp hq
    have hsq : q 1 ^ 2 < η ^ 2 := by
      nlinarith [mul_pos (show 0 < q 1 + η by linarith) (show 0 < η - q 1 by linarith)]
    have hends : q 0 ≤ -1 + η ∨ 1 - η ≤ q 0 := by
      by_contra hn
      push Not at hn
      nlinarith [mul_nonneg (show 0 ≤ q 0 + (1 - η) by linarith)
        (show 0 ≤ (1 - η) - q 0 by linarith)]
    rcases hends with hleft | hright
    · have ha := hαz (P q) (by rwa [hP0])
      have hb := hβz (P q) (by rwa [hP0])
      have hf : F q = z := by dsimp only [F]; rw [ha, hb]; module
      exact ⟨ha ▸ hz, hb ▸ hz, hf ▸ hz⟩
    · have ha := hαx (P q) (by rwa [hP0])
      have hb := hβx (P q) (by rwa [hP0])
      have hf : F q = x := by dsimp only [F]; rw [ha, hb]; module
      exact ⟨ha ▸ hx, hb ▸ hx, hf ▸ hx⟩
  have hupper : ∀ q : EuclideanSpace ℝ (Fin 2), η / 2 < q 1 →
      F =ᶠ[nhds q] fun r => α (EuclideanSpace.single 0 (r 0)) := by
    intro q hq
    have hopen : IsOpen {r : EuclideanSpace ℝ (Fin 2) | η / 2 < r 1} :=
      isOpen_lt continuous_const hcoord.continuous
    filter_upwards [hopen.mem_nhds hq] with r hr
    simp [F, hψ1 _ hr.le, hP]
  have hlower : ∀ q : EuclideanSpace ℝ (Fin 2), q 1 < -η / 2 →
      F =ᶠ[nhds q] fun r => β (EuclideanSpace.single 0 (r 0)) := by
    intro q hq
    have hopen : IsOpen {r : EuclideanSpace ℝ (Fin 2) | r 1 < -η / 2} :=
      isOpen_lt hcoord.continuous continuous_const
    filter_upwards [hopen.mem_nhds hq] with r hr
    simp [F, hψ0 _ hr.le, hP]
  have hPball : ∀ q ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      EuclideanSpace.single 0 (q 0) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    intro q hq
    rw [mem_closedBall_zero_iff, euclideanSpace_fin_one_norm_eq]
    simp only [EuclideanSpace.single, PiLp.single_apply, ite_true]
    rw [abs_le]
    have := (mem_unit_circle_iff q).mp hq
    constructor <;> nlinarith [sq_nonneg (q 1)]
  have hbd : ∀ q ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      BoundaryTransverseAt S F q := by
    intro q hq hqS
    by_cases hu : η ≤ q 1
    · exact boundaryTransverseAt_of_path_projection hα (hupper q (by linarith))
        (by linarith) (htα _ (hPball q hq)) hqS
    · have hl : q 1 ≤ -η := by
        by_contra hn
        exact (hband q hq (by linarith) (by linarith)).2.2 hqS
      exact boundaryTransverseAt_of_path_projection hβ (hlower q (by linarith))
        (by linarith) (htβ _ (hPball q hq)) hqS
  let A : Set (EuclideanSpace ℝ (Fin 2)) :=
    {q | q ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      0 < (1 : ℝ) * q 1 ∧ α (EuclideanSpace.single 0 (q 0)) ∈ S}
  let B : Set (EuclideanSpace ℝ (Fin 2)) :=
    {q | q ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∧
      0 < (-1 : ℝ) * q 1 ∧ β (EuclideanSpace.single 0 (q 0)) ∈ S}
  have hαend0 : α (EuclideanSpace.single 0 (-1)) ∉ S := by
    rw [hαz _ (by simp; linarith)]; exact hz
  have hαend1 : α (EuclideanSpace.single 0 1) ∉ S := by
    rw [hαx _ (by simp; linarith)]; exact hx
  have hβend0 : β (EuclideanSpace.single 0 (-1)) ∉ S := by
    rw [hβz _ (by simp; linarith)]; exact hz
  have hβend1 : β (EuclideanSpace.single 0 1) ∉ S := by
    rw [hβx _ (by simp; linarith)]; exact hx
  have hA := bijOn_semicircle_intersections α hαend0 hαend1 (σ := 1) (Or.inl rfl)
  have hB := bijOn_semicircle_intersections β hβend0 hβend1 (σ := -1) (Or.inr rfl)
  have hAfin : A.Finite :=
    (finite_transverse_preimage_path hS hc hα htα).of_injOn hA.mapsTo hA.injOn
  have hBfin : B.Finite :=
    (finite_transverse_preimage_path hS hc hβ htβ).of_injOn hB.mapsTo hB.injOn
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    rintro q ⟨-, ha, -⟩ ⟨-, hb, -⟩
    norm_num at ha hb
    linarith
  have hset : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ∩ F ⁻¹' S = A ∪ B := by
    ext q
    constructor
    · rintro ⟨hq, hqS⟩
      by_cases hu : η ≤ q 1
      · left
        refine ⟨hq, by dsimp; linarith, ?_⟩
        rwa [← (hupper q (by linarith)).eq_of_nhds]
      · have hl : q 1 ≤ -η := by
          by_contra hn
          exact (hband q hq (by linarith) (by linarith)).2.2 hqS
        right
        refine ⟨hq, by dsimp; linarith, ?_⟩
        rwa [← (hlower q (by linarith)).eq_of_nhds]
    · rintro (⟨hq, hsign, hhit⟩ | ⟨hq, hsign, hhit⟩)
      · have hu : η ≤ q 1 := by
          by_contra hn
          apply (hband q hq (by dsimp at hsign; linarith) (by linarith)).1
          rwa [hP]
        exact ⟨hq, by rw [mem_preimage, (hupper q (by linarith)).eq_of_nhds]; exact hhit⟩
      · have hl : q 1 ≤ -η := by
          by_contra hn
          apply (hband q hq (by linarith) (by dsimp at hsign; linarith)).2.1
          rwa [hP]
        exact ⟨hq, by rw [mem_preimage, (hlower q (by linarith)).eq_of_nhds]; exact hhit⟩
  have heven := even_ncard_boundary_intersections_of_boundary_loop_transverse hS hc hF hbd
  rw [hset, Set.ncard_union_eq hdisj hAfin hBfin, hA.ncard_eq, hB.ncard_eq] at heven
  exact heven

/-- prop:orientation-parity (i): two transverse smooth paths with the same endpoints off
a compact smooth embedded surface have intersection counts whose sum is even. -/
theorem even_add_ncard_transverse_paths {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {α β : EuclideanSpace ℝ (Fin 1) → E₃} (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (htα : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α p)
    (htβ : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S β p)
    (h0 : α (EuclideanSpace.single 0 (-1)) = β (EuclideanSpace.single 0 (-1)))
    (h1 : α (EuclideanSpace.single 0 1) = β (EuclideanSpace.single 0 1))
    (hz : α (EuclideanSpace.single 0 (-1)) ∉ S) (hx : α (EuclideanSpace.single 0 1) ∉ S) :
    Even ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S).ncard +
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ β ⁻¹' S).ncard) := by
  obtain ⟨α', hα', -, -, htα', hcountα, ηα, hηα, hηαhalf, hαz, hαx⟩ :=
    exists_transverse_path_normalization hc hα htα hz hx
  obtain ⟨β', hβ', -, -, htβ', hcountβ, ηβ, hηβ, -, hβz, hβx⟩ :=
    exists_transverse_path_normalization hc hβ htβ (h0 ▸ hz) (h1 ▸ hx)
  rw [← hcountα, ← hcountβ]
  apply even_add_ncard_transverse_paths_of_constant_ends hS hc hα' hβ' htα' htβ' hz hx
    (η := min ηα ηβ) (lt_min hηα hηβ) ((min_le_left _ _).trans hηαhalf)
  · intro p hp
    exact hαz p (by linarith [min_le_left ηα ηβ])
  · intro p hp
    exact hαx p (by linarith [min_le_left ηα ηβ])
  · intro p hp
    exact (hβz p (by linarith [min_le_right ηα ηβ])).trans h0.symm
  · intro p hp
    exact (hβx p (by linarith [min_le_right ηα ηβ])).trans h1.symm

/-- prop:orientation-parity (i): any two points off a compact smooth embedded surface can be
joined by a smooth transverse path; its intersection set is finite. -/
theorem exists_transverse_path {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {z x : E₃} (hz : z ∉ S) (hx : x ∉ S) :
    ∃ α : EuclideanSpace ℝ (Fin 1) → E₃, ContDiff ℝ (⊤ : ℕ∞) α ∧
      α (EuclideanSpace.single 0 (-1)) = z ∧ α (EuclideanSpace.single 0 1) = x ∧
      (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α p) ∧
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S).Finite := by
  let f : EuclideanSpace ℝ (Fin 1) → E₃ := fun p => z + ((p 0 + 1) / 2) • (x - z)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_const.add ((((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff.add
      contDiff_const).div_const 2).smul contDiff_const)
  have hf0 : f (EuclideanSpace.single 0 (-1)) = z := by simp [f]
  have hf1 : f (EuclideanSpace.single 0 1) = x := by simp [f]
  have hend : ∀ p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1, f p ∉ S := by
    intro p hp
    have habs : |p 0| = 1 := by
      rw [← euclideanSpace_fin_one_norm_eq]; simpa using hp
    rcases le_total 0 (p 0) with hpos | hneg
    · rw [abs_of_nonneg hpos] at habs
      rw [euclideanSpace_fin_one_eq_single p, habs, hf1]
      exact hx
    · rw [abs_of_nonpos hneg] at habs
      have hp0 : p 0 = -1 := by linarith
      rw [euclideanSpace_fin_one_eq_single p, hp0, hf0]
      exact hz
  obtain ⟨α, hα, -, ⟨V, -, hV, heq⟩, htα, hfin⟩ :=
    exists_transverse_path_perturbation_finite hS hc hf hend zero_lt_one
  refine ⟨α, hα, (heq _ (hV ?_)).trans hf0, (heq _ (hV ?_)).trans hf1, htα, hfin⟩ <;>
    simp

/-- prop:orientation-parity (i): odd intersection parity from a base point, defined by the
existence of a transverse smooth path with odd intersection count. -/
def SurfaceOddParity (S : Set E₃) (z x : E₃) : Prop :=
  ∃ α : EuclideanSpace ℝ (Fin 1) → E₃, ContDiff ℝ (⊤ : ℕ∞) α ∧
    α (EuclideanSpace.single 0 (-1)) = z ∧ α (EuclideanSpace.single 0 1) = x ∧
    (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α p) ∧
    Odd (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S).ncard

/-- prop:orientation-parity (i): every transverse smooth path between the given endpoints
computes the same odd-parity predicate. -/
theorem surfaceOddParity_iff {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {z x : E₃} (hz : z ∉ S) (hx : x ∉ S)
    {α : EuclideanSpace ℝ (Fin 1) → E₃} (hα : ContDiff ℝ (⊤ : ℕ∞) α)
    (htα : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α p)
    (hα0 : α (EuclideanSpace.single 0 (-1)) = z) (hα1 : α (EuclideanSpace.single 0 1) = x) :
    SurfaceOddParity S z x ↔
      Odd (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S).ncard := by
  constructor
  · rintro ⟨β, hβ, hβ0, hβ1, htβ, hodd⟩
    have heven := even_add_ncard_transverse_paths hS hc hβ hα htβ htα
      (hβ0.trans hα0.symm) (hβ1.trans hα1.symm) (hβ0 ▸ hz) (hβ1 ▸ hx)
    exact (Nat.even_add'.mp heven).mp hodd
  · intro hodd
    exact ⟨α, hα, hα0, hα1, htα, hodd⟩

/-- prop:orientation-parity (i), consequence for (ii): odd parity is locally constant on
the complement of a compact smooth embedded surface. -/
theorem surfaceOddParity_locally_constant {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {z : E₃} (hz : z ∉ S) :
    ∀ x ∉ S, ∀ᶠ y in nhds x, SurfaceOddParity S z y ↔ SurfaceOddParity S z x := by
  intro x hx
  obtain ⟨α, hα, hα0, hα1, htα, -⟩ := exists_transverse_path hS hc hz hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hc.isClosed.isOpen_compl x hx
  have hdisj : Disjoint (Metric.ball x r) S :=
    Set.disjoint_left.mpr fun _ ha hS => hball ha hS
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  obtain ⟨β, hβ, hβleft, hβ1, -, htβ, hβS⟩ :=
    exists_transverse_path_endpoint_shift hα htα hdisj hα1 hy
  have hβ0 : β (EuclideanSpace.single 0 (-1)) = z := (hβleft _ (by simp)).trans hα0
  rw [surfaceOddParity_iff hS hc hz (hball hy) hβ htβ hβ0 hβ1,
    surfaceOddParity_iff hS hc hz hx hα htα hα0 hα1, hβS]

/-- prop:orientation-parity (i), consequence for (ii): crossing the surface in a non-tangent
direction flips the odd-parity predicate. -/
theorem surfaceOddParity_crossing {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {z : E₃} (hz : z ∉ S) :
    ∀ p ∈ S, ∀ ν ∉ tangentPlane S p, ∃ t₀ > 0, ∀ t ∈ Ioo (0 : ℝ) t₀,
      ¬ (SurfaceOddParity S z (p - t • ν) ↔ SurfaceOddParity S z (p + t • ν)) := by
  intro p hp ν hν
  obtain ⟨t₀, ht₀, hcross⟩ := exists_transverse_path_crossing hS hc hp hν
  refine ⟨t₀, ht₀, fun t ht => ?_⟩
  obtain ⟨hminus, hplus, hextend⟩ := hcross t ht
  obtain ⟨α, hα, hα0, hα1, htα, -⟩ := exists_transverse_path hS hc hz hminus
  obtain ⟨β, hβ, hβ0, hβ1, htβ, hcount⟩ := hextend α hα htα hα1
  rw [surfaceOddParity_iff hS hc hz hminus hα htα hα0 hα1,
    surfaceOddParity_iff hS hc hz hplus hβ htβ (hβ0.trans hα0) hβ1,
    hcount, Nat.odd_add_one]
  tauto

end
end LiquidDrop
