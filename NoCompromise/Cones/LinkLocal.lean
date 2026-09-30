module

public import NoCompromise.Cones.LinkComponents

@[expose] public section

/-!
# A closed subset of `S²` which is locally a great-circle arc is one great circle

Local form of the last paragraph of blueprint `lem:cone-link-great-circle` (chapter 25):
"two distinct great circles intersect, whereas distinct components of the embedded link are
disjoint".  Instead of a global unit-speed parametrisation of each component, the hypothesis is
that near each of its points the link coincides with an arc of some great circle (the local
content of the Euler equation `γ'' = -γ`).

* `plane_eq_of_arc_subset` : two great circles sharing an open arc span the same plane;
* `isPreconnected_greatCircle` : great circles are connected;
* `eq_greatCircle_of_locally_greatCircle` : a closed nonempty set which is locally a great-circle
  arc is a single great circle;
* `cone3d_halfspace_of_locally_greatCircle_link` : `thm:cone-3d` under this local hypothesis on the
  link (nonemptiness and closedness of the link are proved);
* `cone3d_halfspace_of_locally_flat` : `thm:cone-3d` if the punctured boundary is locally an affine
  plane (such planes pass through the vertex by dilation invariance).

The local hypothesis itself (from `lem:cone-smooth` and the first variation of the cone) is not
proved here.
-/

noncomputable section
open Set Metric

namespace LiquidDrop

/-- Two nonzero vectors orthogonal to the same orthonormal pair define the same plane. -/
lemma plane_eq_of_orthonormal_pair {ν₁ ν₂ w u : AmbientSpace} (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0)
    (hw : ‖w‖ = 1) (hu : ‖u‖ = 1) (hwu : inner ℝ w u = 0)
    (h1w : inner ℝ ν₁ w = 0) (h1u : inner ℝ ν₁ u = 0)
    (h2w : inner ℝ ν₂ w = 0) (h2u : inner ℝ ν₂ u = 0) :
    {y : AmbientSpace | inner ℝ ν₁ y = 0} = {y | inner ℝ ν₂ y = 0} := by
  let f : AmbientSpace →ₗ[ℝ] ℝ × ℝ := (innerₛₗ ℝ w).prod (innerₛₗ ℝ u)
  have hsurj : Function.Surjective f := by
    rintro ⟨a, b⟩
    refine ⟨a • w + b • u, ?_⟩
    have hww : inner ℝ w w = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hw, one_pow]
    have huu : inner ℝ u u = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
    have huw : inner ℝ u w = (0 : ℝ) := by rw [real_inner_comm]; exact hwu
    ext
    · simp [f, LinearMap.prod_apply, inner_add_right, real_inner_smul_right, hw, hwu]
    · simp [f, LinearMap.prod_apply, inner_add_right, real_inner_smul_right, hu, huw]
  have hrank : Module.finrank ℝ (LinearMap.ker f) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod, Module.finrank_self,
      finrank_euclideanSpace, Fintype.card_fin] at h
    omega
  have hm (ν : AmbientSpace) (hνw : inner ℝ ν w = 0) (hνu : inner ℝ ν u = 0) :
      ν ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    ext
    · simpa [f, LinearMap.prod_apply, innerₛₗ_apply_apply, real_inner_comm] using hνw
    · simpa [f, LinearMap.prod_apply, innerₛₗ_apply_apply, real_inner_comm] using hνu
  have hne : (⟨ν₁, hm ν₁ h1w h1u⟩ : LinearMap.ker f) ≠ 0 := by
    intro h
    exact hν₁ (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hrank ⟨ν₂, hm ν₂ h2w h2u⟩
  have hc' : c • ν₁ = ν₂ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc'
    exact hν₂ hc'.symm
  ext y
  simp only [mem_ofPred_eq, ← hc', real_inner_smul_left]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hc0

/-- Two great circles sharing an open arc (around a point `w` of the first) span the same plane. -/
lemma plane_eq_of_arc_subset {ν₁ ν₂ w : AmbientSpace} (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0)
    (hw1 : ‖w‖ = 1) (hwν : inner ℝ ν₁ w = 0) {δ : ℝ} (hδ : 0 < δ)
    (hsub : ∀ y : AmbientSpace, inner ℝ ν₁ y = 0 → ‖y‖ = 1 → dist y w < δ →
      inner ℝ ν₂ y = 0) :
    {y : AmbientSpace | inner ℝ ν₁ y = 0} = {y | inner ℝ ν₂ y = 0} := by
  obtain ⟨u, hu1, huν, huw⟩ := greatCircles_meet ν₁ w
  set t : ℝ := min (δ / 4) 1 with ht
  have ht0 : 0 < t := lt_min (by positivity) one_pos
  have ht1 : t ≤ 1 := min_le_right _ _
  have htδ : t ≤ δ / 4 := min_le_left _ _
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.two_le_pi])
  have hww : inner ℝ w w = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hw1, one_pow]
  have huu : inner ℝ u u = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu1, one_pow]
  have huw' : inner ℝ u w = (0 : ℝ) := by rw [real_inner_comm]; exact huw
  set w' : AmbientSpace := Real.cos t • w + Real.sin t • u with hw'
  have hw'ν : inner ℝ ν₁ w' = 0 := by
    simp only [w', inner_add_right, real_inner_smul_right, hwν, huν, mul_zero, add_zero]
  have hw'n : ‖w'‖ = 1 := by
    have hsq : ‖w'‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [w', inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hww, huu, huw, huw', mul_one, mul_zero, add_zero, zero_add]
      nlinarith [Real.sin_sq_add_cos_sq t]
    have h0 : 0 ≤ ‖w'‖ := norm_nonneg _
    nlinarith
  have hdist : dist w' w < δ := by
    rw [dist_eq_norm]
    have hsplit : w' - w = (Real.cos t - 1) • w + Real.sin t • u := by
      rw [hw', sub_smul, one_smul]
      abel
    have hcos1 : Real.cos t ≤ 1 := Real.cos_le_one t
    have hcos2 : 1 - t ^ 2 / 2 ≤ Real.cos t := Real.one_sub_sq_div_two_le_cos
    have hsinle : Real.sin t ≤ t := Real.sin_le ht0.le
    calc ‖w' - w‖ ≤ ‖(Real.cos t - 1) • w‖ + ‖Real.sin t • u‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ = (1 - Real.cos t) + Real.sin t := by
          rw [norm_smul, norm_smul, hw1, hu1, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonpos (by linarith), abs_of_pos hsin]
          ring
      _ ≤ t ^ 2 / 2 + t := by linarith
      _ < δ := by nlinarith
  have h2w : inner ℝ ν₂ w = 0 := hsub w hwν hw1 (by rw [dist_self]; exact hδ)
  have h2w' : inner ℝ ν₂ w' = 0 := hsub w' hw'ν hw'n hdist
  have h2u : inner ℝ ν₂ u = 0 := by
    have h := h2w'
    simp only [w', inner_add_right, real_inner_smul_right, h2w, mul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left hsin.ne'
  exact plane_eq_of_orthonormal_pair hν₁ hν₂ hw1 hu1 huw hwν huν h2w h2u

/-- Great circles are connected. -/
lemma isPreconnected_greatCircle {ν : AmbientSpace} (hν : ν ≠ 0) :
    IsPreconnected ({y : AmbientSpace | inner ℝ ν y = 0} ∩ sphere 0 1) := by
  obtain ⟨a, ha1, haν, -⟩ := greatCircles_meet ν ν
  obtain ⟨b, hb1, hbν, hab⟩ := greatCircles_meet ν a
  obtain ⟨ν', hν', hR⟩ := range_cos_sin_eq_greatCircle ha1 hb1 hab
  have ha' : a ∈ {y : AmbientSpace | inner ℝ ν' y = 0} ∩ sphere 0 1 := by
    rw [← hR]
    exact ⟨0, by simp⟩
  have hpl := plane_eq_of_arc_subset hν' hν ha1 ha'.1 one_pos (by
    intro y hy hy1 _
    have hy' : y ∈ {y : AmbientSpace | inner ℝ ν' y = 0} ∩ sphere 0 1 :=
      ⟨hy, by simpa using hy1⟩
    rw [← hR] at hy'
    obtain ⟨s, rfl⟩ := hy'
    simp only [inner_add_right, real_inner_smul_right, haν, hbν, mul_zero, add_zero])
  rw [← hpl, ← hR]
  exact isPreconnected_range (by fun_prop)

/-- **Local form of the last paragraph of `lem:cone-link-great-circle`.**  A closed nonempty set
which near each of its points coincides with an arc of some great circle is one great circle. -/
theorem eq_greatCircle_of_locally_greatCircle {Γ : Set AmbientSpace} (hΓ : IsClosed Γ)
    (hne : Γ.Nonempty)
    (hloc : ∀ x ∈ Γ, ∃ ε > 0, ∃ ν : AmbientSpace, ν ≠ 0 ∧
      Γ ∩ ball x ε = {y | inner ℝ ν y = 0} ∩ sphere 0 1 ∩ ball x ε) :
    ∃ ν : AmbientSpace, ν ≠ 0 ∧ Γ = {y | inner ℝ ν y = 0} ∩ sphere 0 1 := by
  -- a great circle meeting `Γ` in a relatively open arc lies in `Γ`
  have hkey : ∀ ν : AmbientSpace, ν ≠ 0 → ∀ x ∈ Γ, ∀ ε > 0,
      Γ ∩ ball x ε = {y | inner ℝ ν y = 0} ∩ sphere 0 1 ∩ ball x ε →
      {y : AmbientSpace | inner ℝ ν y = 0} ∩ sphere 0 1 ⊆ Γ := by
    intro ν hν x hx ε hε hxeq
    set G : Set AmbientSpace := {y | inner ℝ ν y = 0} ∩ sphere 0 1 with hG
    set T : Set AmbientSpace := {y | y ∈ G ∧ ∃ δ > 0, G ∩ ball y δ ⊆ Γ} with hT
    set U : Set AmbientSpace := ⋃ (y : AmbientSpace) (δ : ℝ) (_ : 0 < δ ∧ G ∩ ball y δ ⊆ Γ),
      ball y (δ / 2) with hU
    have hUo : IsOpen U := isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
      isOpen_iUnion fun _ => isOpen_ball
    have hGU : ∀ z ∈ G, z ∈ U → z ∈ T := by
      intro z hz hzU
      simp only [U, mem_iUnion] at hzU
      obtain ⟨y, δ, ⟨hδ, hsub⟩, hzy⟩ := hzU
      refine ⟨hz, δ / 2, by positivity, fun q hq => hsub ⟨hq.1, ?_⟩⟩
      have h1 := hq.2
      rw [mem_ball] at h1 hzy ⊢
      linarith [dist_triangle q z y]
    have hTU : T ⊆ U := by
      rintro y ⟨_, δ, hδ, hsub⟩
      simp only [U, mem_iUnion]
      exact ⟨y, δ, ⟨hδ, hsub⟩, mem_ball_self (by positivity)⟩
    have hTΓ : T ⊆ Γ := by
      rintro y ⟨hy, δ, hδ, hsub⟩
      exact hsub ⟨hy, mem_ball_self hδ⟩
    have hxT : x ∈ T := by
      have hxG : x ∈ G := by
        have : x ∈ Γ ∩ ball x ε := ⟨hx, mem_ball_self hε⟩
        rw [hxeq] at this
        exact this.1
      refine ⟨hxG, ε, hε, fun q hq => ?_⟩
      have : q ∈ G ∩ ball x ε := hq
      rw [← hxeq] at this
      exact this.1
    have hcl : ∀ y ∈ G, y ∈ closure T → y ∈ T := by
      intro y hyG hyc
      have hyΓ : y ∈ Γ := closure_minimal hTΓ hΓ hyc
      obtain ⟨ε₀, hε₀, ν₀, hν₀, heq⟩ := hloc y hyΓ
      obtain ⟨t, htT, hty⟩ := Metric.mem_closure_iff.mp hyc (ε₀ / 2) (by positivity)
      obtain ⟨htG, δ, hδ, hsub⟩ := htT
      have hpl := plane_eq_of_arc_subset hν hν₀ (by simpa using htG.2) htG.1
        (lt_min hδ (by positivity : 0 < ε₀ / 2)) (by
          intro q hq hq1 hqt
          have hqΓ : q ∈ Γ := hsub ⟨⟨hq, by simpa using hq1⟩,
            mem_ball.mpr (hqt.trans_le (min_le_left _ _))⟩
          have hqb : q ∈ ball y ε₀ := by
            rw [mem_ball]
            have := hqt.trans_le (min_le_right _ _)
            rw [dist_comm] at hty
            linarith [dist_triangle q t y]
          have : q ∈ Γ ∩ ball y ε₀ := ⟨hqΓ, hqb⟩
          rw [heq] at this
          exact this.1.1)
      refine ⟨hyG, ε₀, hε₀, fun q hq => ?_⟩
      have hq' : q ∈ {y | inner ℝ ν₀ y = 0} ∩ sphere 0 1 ∩ ball y ε₀ := by
        refine ⟨⟨?_, hq.1.2⟩, hq.2⟩
        have h := hq.1.1
        rw [← hpl]
        exact h
      rw [← heq] at hq'
      exact hq'.1
    rcases (isPreconnected_iff_subset_of_disjoint.mp (isPreconnected_greatCircle hν))
      U (closure T)ᶜ hUo isClosed_closure.isOpen_compl
      (fun y hy => by
        by_cases hyc : y ∈ closure T
        · exact Or.inl (hTU (hcl y hy hyc))
        · exact Or.inr hyc)
      (by
        apply eq_empty_iff_forall_notMem.mpr
        rintro y ⟨hyG, hyU, hyc⟩
        exact hyc (subset_closure (hGU y hyG hyU))) with hsub | hsub
    · exact fun y hy => hTΓ (hGU y hy (hsub hy))
    · exact absurd (subset_closure hxT) (hsub hxT.1)
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨ε₀, hε₀, ν₀, hν₀, heq₀⟩ := hloc x₀ hx₀
  have hG₀ := hkey ν₀ hν₀ x₀ hx₀ ε₀ hε₀ heq₀
  refine ⟨ν₀, hν₀, Subset.antisymm ?_ hG₀⟩
  intro z hz
  obtain ⟨εz, hεz, νz, hνz, heqz⟩ := hloc z hz
  have hGz := hkey νz hνz z hz εz hεz heqz
  have hzG : z ∈ {y : AmbientSpace | inner ℝ νz y = 0} ∩ sphere 0 1 := by
    have : z ∈ Γ ∩ ball z εz := ⟨hz, mem_ball_self hεz⟩
    rw [heqz] at this
    exact this.1
  obtain ⟨w, hw1, hw₀, hwz⟩ := greatCircles_meet ν₀ νz
  have hwΓ : w ∈ Γ := hG₀ ⟨hw₀, by simpa using hw1⟩
  obtain ⟨εw, hεw, νw, hνw, heqw⟩ := hloc w hwΓ
  have harc : ∀ ν : AmbientSpace, ν ≠ 0 → inner ℝ ν w = 0 →
      {y : AmbientSpace | inner ℝ ν y = 0} ∩ sphere 0 1 ⊆ Γ →
      {y : AmbientSpace | inner ℝ ν y = 0} = {y | inner ℝ νw y = 0} := by
    intro ν hν hνw' hsubΓ
    refine plane_eq_of_arc_subset hν hνw hw1 hνw' hεw fun q hq hq1 hqw => ?_
    have : q ∈ Γ ∩ ball w εw := ⟨hsubΓ ⟨hq, by simpa using hq1⟩, hqw⟩
    rw [heqw] at this
    exact this.1.1
  have h₀ := harc ν₀ hν₀ hw₀ hG₀
  have hz' := harc νz hνz hwz hGz
  refine ⟨?_, hzG.2⟩
  have h := hzG.1
  change inner ℝ ν₀ z = 0
  have : z ∈ {y : AmbientSpace | inner ℝ νz y = 0} := h
  rw [hz', ← h₀] at this
  exact this

/-- **`thm:cone-3d` from the local great-circle structure of the link.**  If near each of its
points the link `∂C ∩ S²` of a nontrivial locally perimeter-minimising cone in `ℝ³` coincides with
an arc of a great circle, then `densityOne C` is an open halfspace. -/
theorem cone3d_halfspace_of_locally_greatCircle_link {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C)
    (hloc : ∀ x ∈ frontier (densityOne C) ∩ sphere 0 1, ∃ ε > 0, ∃ ν : AmbientSpace, ν ≠ 0 ∧
      frontier (densityOne C) ∩ sphere 0 1 ∩ ball x ε =
        {y | inner ℝ ν y = 0} ∩ sphere 0 1 ∩ ball x ε) :
    ∃ μ : AmbientSpace, ‖μ‖ = 1 ∧ densityOne C = {x | 0 < inner ℝ μ x} := by
  obtain ⟨ν, hν, hlink⟩ := eq_greatCircle_of_locally_greatCircle
    (isClosed_frontier.inter isClosed_sphere) hC.link_nonempty hloc
  exact cone3d_halfspace_of_link_eq hC hν hlink

/-- **`thm:cone-3d` from local flatness of the punctured boundary.**  If near each nonzero boundary
point `p` the boundary of `densityOne C` coincides with an affine plane through `p`, then
`densityOne C` is an open halfspace.  (Dilation invariance forces each such plane through `0`, so
the link is locally a great-circle arc.) -/
theorem cone3d_halfspace_of_locally_flat {C : Set AmbientSpace}
    (hC : IsNontrivialMinimizingCone C)
    (hflat : ∀ p ∈ frontier (densityOne C), p ≠ 0 → ∃ ε > 0, ∃ ν : AmbientSpace, ν ≠ 0 ∧
      frontier (densityOne C) ∩ ball p ε = {y | inner ℝ ν (y - p) = 0} ∩ ball p ε) :
    ∃ μ : AmbientSpace, ‖μ‖ = 1 ∧ densityOne C = {x | 0 < inner ℝ μ x} := by
  apply cone3d_halfspace_of_locally_greatCircle_link hC
  rintro x ⟨hxf, hxs⟩
  have hx1 : ‖x‖ = 1 := by simpa using hxs
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx1
    exact zero_ne_one hx1
  obtain ⟨ε, hε, ν, hν, heq⟩ := hflat x hxf hx0
  -- the plane passes through the origin
  have hνx : inner ℝ ν x = 0 := by
    set s : ℝ := ε / 2 with hs
    have hs0 : 0 < s := by positivity
    have hmem : (1 + s) • x ∈ frontier (densityOne C) ∩ ball x ε := by
      refine ⟨hC.smul_mem_frontier hxf (by linarith), ?_⟩
      rw [mem_ball, dist_eq_norm, add_smul, one_smul, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hs0, hx1, mul_one]
      linarith
    rw [heq] at hmem
    have h := hmem.1
    simp only [mem_ofPred_eq, add_smul, one_smul, add_sub_cancel_left,
      real_inner_smul_right] at h
    exact (mul_eq_zero.mp h).resolve_left hs0.ne'
  refine ⟨ε, hε, ν, hν, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hyf, hys⟩, hyb⟩
    have : y ∈ frontier (densityOne C) ∩ ball x ε := ⟨hyf, hyb⟩
    rw [heq] at this
    refine ⟨⟨?_, hys⟩, hyb⟩
    have h := this.1
    simp only [mem_ofPred_eq, inner_sub_right, hνx, sub_zero] at h
    exact h
  · rintro ⟨⟨hyν, hys⟩, hyb⟩
    have : y ∈ {y | inner ℝ ν (y - x) = 0} ∩ ball x ε := by
      refine ⟨?_, hyb⟩
      simp only [mem_ofPred_eq, inner_sub_right, hνx, sub_zero]
      exact hyν
    rw [← heq] at this
    exact ⟨⟨this.1, hys⟩, hyb⟩

end LiquidDrop
