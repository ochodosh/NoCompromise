module

public import NoCompromise.Topology.ParityEndpoint

@[expose] public section

/-!
# Crossing the surface once (towards `prop:orientation-parity` (ii))

Near a point `p₀` of a smooth embedded surface and a direction `ν` not tangent at `p₀`, a
transverse path ending at `p₀ - t • ν` extends, after its endpoint is frozen by
`exists_transverse_path_endpoint_shift`, to a transverse path ending at `p₀ + t • ν` with
exactly one more intersection. Hence the two local sides have opposite intersection parity.
-/

noncomputable section
open Set Filter Topology

namespace LiquidDrop

/-- Points of `EuclideanSpace ℝ (Fin 1)` are determined by their coordinate. -/
theorem euclideanSpace_fin_one_eq_single (p : EuclideanSpace ℝ (Fin 1)) :
    p = EuclideanSpace.single 0 (p 0) := by
  ext i
  fin_cases i
  simp

/-- A direction outside the tangent plane in the range of the differential gives
transversality. -/
theorem transverseAt_of_mem_range {S : Set E₃} (hS : IsSmoothEmbeddedSurface S) {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → E₃} {q : EuclideanSpace ℝ (Fin k)} {ν : E₃}
    (hν : ν ∉ tangentPlane S (f q)) (hr : ∃ u, fderiv ℝ f q u = ν) : TransverseAt S f q := by
  intro hq
  set M := LinearMap.range (fderiv ℝ f q : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E₃) ⊔
    tangentPlane S (f q)
  have hTM : tangentPlane S (f q) < M := by
    refine lt_of_le_of_ne le_sup_right fun h => hν ?_
    obtain ⟨u, hu⟩ := hr
    rw [h]
    exact Submodule.mem_sup_left ⟨u, hu⟩
  have h2 := hS.finrank_tangentPlane hq
  have hlt := Submodule.finrank_lt_finrank_of_lt hTM
  apply Submodule.eq_top_of_finrank_eq
  have hle := Submodule.finrank_le M
  simp only [E₃, finrank_euclideanSpace_fin] at hle h2 hlt ⊢
  omega

/-- A non-tangent segment through a surface point meets the surface only at that point,
for small parameters. -/
theorem exists_segment_meets_surface_only_at {S : Set E₃} (hS : IsSmoothEmbeddedSurface S)
    {p₀ ν : E₃} (hp₀ : p₀ ∈ S) (hν : ν ∉ tangentPlane S p₀) :
    ∃ t₁ > 0, ∀ l : ℝ, |l| < t₁ → (p₀ + l • ν ∈ S ↔ l = 0) := by
  obtain ⟨U, φ, hU, hp₀U, hφ, hzero, hreg⟩ := hS p₀ hp₀
  have hT : tangentPlane S p₀ = (ℝ ∙ gradient φ p₀)ᗮ :=
    tangentPlane_eq hU hp₀U (hφ.contDiffAt.of_le (by exact_mod_cast le_top)) hzero hp₀
      (hreg _ ⟨hp₀, hp₀U⟩)
  have hd : fderiv ℝ φ p₀ ν ≠ 0 := by
    intro h0
    apply hν
    rw [hT, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_gradient_left]
    exact h0
  have hl : HasDerivAt (fun l : ℝ => p₀ + l • ν) ν 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_add p₀
  have hφd : HasFDerivAt φ (fderiv ℝ φ p₀) (p₀ + (0 : ℝ) • ν) := by
    simpa using (hφ.differentiable (by simp) p₀).hasFDerivAt
  have hh : HasDerivAt (fun l : ℝ => φ (p₀ + l • ν)) (fderiv ℝ φ p₀ ν) 0 :=
    hφd.comp_hasDerivAt 0 hl
  have hne : ∀ᶠ l in 𝓝[≠] (0 : ℝ), φ (p₀ + l • ν) ≠ 0 := hh.eventually_ne hd
  have hin : ∀ᶠ l in 𝓝 (0 : ℝ), p₀ + l • ν ∈ U :=
    hl.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hp₀U)
  have hboth : ∀ᶠ l in 𝓝[≠] (0 : ℝ), p₀ + l • ν ∉ S := by
    filter_upwards [hne, nhdsWithin_le_nhds hin] with l hl1 hl2 hlS
    have : p₀ + l • ν ∈ S ∩ U := ⟨hlS, hl2⟩
    rw [hzero] at this
    exact hl1 this.2
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hboth
  obtain ⟨t₁, ht₁, h⟩ := hboth
  refine ⟨t₁, ht₁, fun l hl => ⟨fun hlS => ?_, fun hl0 => by simpa [hl0] using hp₀⟩⟩
  by_contra hl0
  exact h (by rwa [Real.dist_eq, sub_zero]) hl0 hlS

/-- The crossing step: near a surface point and a non-tangent direction, a transverse path
ending on one side extends to a transverse path ending on the other side with exactly one
more intersection point. -/
theorem exists_transverse_path_crossing {S : Set E₃}
    (hS : IsSmoothEmbeddedSurface S) (hc : IsCompact S)
    {p₀ ν : E₃} (hp₀ : p₀ ∈ S) (hν : ν ∉ tangentPlane S p₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t ∈ Ioo (0 : ℝ) t₀, p₀ - t • ν ∉ S ∧ p₀ + t • ν ∉ S ∧
      ∀ α : EuclideanSpace ℝ (Fin 1) → E₃, ContDiff ℝ (⊤ : ℕ∞) α →
        (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S α p) →
        α (EuclideanSpace.single 0 1) = p₀ - t • ν →
        ∃ β : EuclideanSpace ℝ (Fin 1) → E₃, ContDiff ℝ (⊤ : ℕ∞) β ∧
          β (EuclideanSpace.single 0 (-1)) = α (EuclideanSpace.single 0 (-1)) ∧
          β (EuclideanSpace.single 0 1) = p₀ + t • ν ∧
          (∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, TransverseAt S β p) ∧
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ β ⁻¹' S).ncard =
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α ⁻¹' S).ncard + 1 := by
  obtain ⟨t₁, ht₁, hseg⟩ := exists_segment_meets_surface_only_at hS hp₀ hν
  refine ⟨t₁, ht₁, fun t ht => ?_⟩
  obtain ⟨ht0, htt₁⟩ := ht
  have hy : p₀ - t • ν ∉ S := by
    have h := hseg (-t) (by rw [abs_neg, abs_of_pos ht0]; exact htt₁)
    rw [neg_smul, ← sub_eq_add_neg] at h
    exact fun hS' => (neg_ne_zero.mpr ht0.ne') (h.mp hS')
  refine ⟨hy, ?_, ?_⟩
  · intro hS'
    have h := (hseg t (by rw [abs_of_pos ht0]; exact htt₁)).mp hS'
    exact ht0.ne' h
  intro α hα htα hαe
  set y := p₀ - t • ν with hydef
  -- freeze the path near its terminal end
  obtain ⟨r, hr, hry⟩ := Metric.isOpen_iff.mp hc.isClosed.isOpen_compl y hy
  have hdisj : Disjoint (Metric.ball y r) S :=
    Set.disjoint_left.mpr fun a ha haS => hry ha haS
  obtain ⟨α₁, hα₁, hα₁0, -, ⟨η, hη, hα₁c⟩, htα₁, hα₁S⟩ :=
    exists_transverse_path_endpoint_shift hα htα hdisj hαe (Metric.mem_ball_self hr)
  set η' := min η 1 with hη'def
  have hη'0 : 0 < η' := lt_min hη one_pos
  have hη'1 : η' ≤ 1 := min_le_right _ _
  have hη'η : η' ≤ η := min_le_left _ _
  set s₀ : ℝ := 1 - η' / 4 with hs₀
  set L : ℝ := 4 * t / η' with hL
  have hL0 : 0 < L := by positivity
  have hLη : L * (η' / 4) = t := by rw [hL]; field_simp
  let ψ : ℝ → ℝ := fun s => Real.smoothTransition ((s - (1 - η' / 2)) / (η' / 8))
  have hψ0 : ∀ s, s ≤ 1 - η' / 2 → ψ s = 0 := fun s hs =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity))
  have hψ1 : ∀ s, 1 - 3 * η' / 8 ≤ s → ψ s = 1 := fun s hs =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by positivity)]; linarith)
  let g : ℝ → ℝ := fun s => ψ s * (t + L * (s - s₀))
  have hg0 : ∀ s, s ≤ 1 - η' / 2 → g s = 0 := fun s hs => by simp [g, hψ0 s hs]
  have hg1 : ∀ s, 1 - 3 * η' / 8 ≤ s → g s = t + L * (s - s₀) := fun s hs => by
    simp [g, hψ1 s hs]
  have hgbd : ∀ s, 1 - η' < s → s ≤ 1 → |g s - t| < t₁ ∧ (g s = t ↔ s = s₀) := by
    intro s hs1 hs2
    by_cases hsa : s ≤ 1 - η' / 2
    · rw [hg0 s hsa]
      refine ⟨by rw [zero_sub, abs_neg, abs_of_pos ht0]; exact htt₁, ?_⟩
      constructor
      · intro h; exact absurd h.symm ht0.ne'
      · intro h; rw [h, hs₀] at hsa; linarith
    · push Not at hsa
      have hlow : -t < L * (s - s₀) := by
        rw [← hLη, ← mul_neg]; exact mul_lt_mul_of_pos_left (by linarith) hL0
      have hhigh : L * (s - s₀) ≤ t := by
        rw [← hLη]; exact mul_le_mul_of_nonneg_left (by linarith) hL0.le
      have hψnn := Real.smoothTransition.nonneg ((s - (1 - η' / 2)) / (η' / 8))
      have hψle := Real.smoothTransition.le_one ((s - (1 - η' / 2)) / (η' / 8))
      have hℓ : 0 < t + L * (s - s₀) := by linarith
      have hgle : g s ≤ t + L * (s - s₀) := by
        show ψ s * _ ≤ _
        exact mul_le_of_le_one_left hℓ.le hψle
      have hgnn : 0 ≤ g s := mul_nonneg hψnn hℓ.le
      refine ⟨by rw [abs_lt]; constructor <;> linarith, ?_⟩
      by_cases hsb : 1 - 3 * η' / 8 ≤ s
      · rw [hg1 s hsb]
        constructor
        · intro h
          have : L * (s - s₀) = 0 := by linarith
          rcases mul_eq_zero.mp this with h' | h'
          · exact absurd h' hL0.ne'
          · linarith
        · intro h; rw [h, sub_self, mul_zero, add_zero]
      · push Not at hsb
        have hneg : L * (s - s₀) < 0 := mul_neg_of_pos_of_neg hL0 (by linarith)
        constructor
        · intro h; linarith
        · intro h; rw [h] at hsb; linarith
  let β : EuclideanSpace ℝ (Fin 1) → E₃ := fun p => α₁ p + g (p 0) • ν
  have hcoord : ContDiff ℝ (⊤ : ℕ∞) fun p : EuclideanSpace ℝ (Fin 1) => p 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).contDiff
  have hgc : ContDiff ℝ (⊤ : ℕ∞) fun p : EuclideanSpace ℝ (Fin 1) => g (p 0) := by
    have hψc : ContDiff ℝ (⊤ : ℕ∞) fun p : EuclideanSpace ℝ (Fin 1) => ψ (p 0) :=
      Real.smoothTransition.contDiff.comp ((hcoord.sub contDiff_const).div_const _)
    exact hψc.mul (contDiff_const.add (contDiff_const.mul (hcoord.sub contDiff_const)))
  have hβc : ContDiff ℝ (⊤ : ℕ∞) β := hα₁.add (hgc.smul contDiff_const)
  -- the two regions
  have hR1 : ∀ p : EuclideanSpace ℝ (Fin 1), p 0 < 1 - η' / 2 → β =ᶠ[𝓝 p] α₁ := by
    intro p hp
    have hopen : IsOpen {q : EuclideanSpace ℝ (Fin 1) | q 0 < 1 - η' / 2} :=
      isOpen_lt hcoord.continuous continuous_const
    filter_upwards [hopen.mem_nhds hp] with q hq
    simp [β, hg0 _ hq.le]
  have hR2 : ∀ p : EuclideanSpace ℝ (Fin 1), 1 - η' < p 0 → β p = p₀ + (g (p 0) - t) • ν := by
    intro p hp
    simp only [β, hα₁c p (by linarith), hydef]
    module
  have hβS : ∀ p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, 1 - η' < p 0 →
      (β p ∈ S ↔ p 0 = s₀) := by
    intro p hp hp1
    have hpn : |p 0| ≤ 1 := by rw [← euclideanSpace_fin_one_norm_eq]; simpa using hp
    obtain ⟨hlt, hiff⟩ := hgbd (p 0) hp1 (abs_le.mp hpn).2
    rw [hR2 p hp1, hseg _ hlt, sub_eq_zero, hiff]
  have hs₀mem : EuclideanSpace.single (0 : Fin 1) s₀ ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    rw [mem_closedBall_zero_iff, euclideanSpace_fin_one_norm_eq]
    rw [show (EuclideanSpace.single (0 : Fin 1) s₀ : EuclideanSpace ℝ (Fin 1)) 0 = s₀ by simp,
      abs_le]
    constructor <;> linarith
  have hs₀c : (EuclideanSpace.single (0 : Fin 1) s₀ : EuclideanSpace ℝ (Fin 1)) 0 = s₀ := by
    simp
  refine ⟨β, hβc, ?_, ?_, ?_, ?_⟩
  · have h0 : (EuclideanSpace.single (0 : Fin 1) (-1 : ℝ) : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
      simp
    simp only [β, h0, hg0 (-1) (by linarith), zero_smul, add_zero]
    exact hα₁0 _ (by rw [h0]; norm_num)
  · have h1 : (EuclideanSpace.single (0 : Fin 1) (1 : ℝ) : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
      simp
    rw [hR2 _ (by rw [h1]; linarith), h1, hg1 1 (by linarith)]
    have : t + L * (1 - s₀) - t = t := by rw [hs₀]; linarith [hLη]
    rw [this]
  · intro p hp
    by_cases hp0 : p 0 < 1 - η' / 2
    · have hev := hR1 p hp0
      intro hmem
      rw [hev.eq_of_nhds] at hmem ⊢
      rw [hev.fderiv_eq]
      exact htα₁ p hp hmem
    · push Not at hp0
      intro hmem
      have hps : p 0 = s₀ := (hβS p hp (by linarith)).mp hmem
      have hβp : β p = p₀ := by
        rw [hR2 p (by linarith), hps, hg1 s₀ (by rw [hs₀]; linarith)]
        simp
      -- near `p` the path is affine
      set Λ : EuclideanSpace ℝ (Fin 1) →L[ℝ] E₃ :=
        L • (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).smulRight ν
      have hopen : IsOpen {q : EuclideanSpace ℝ (Fin 1) | 1 - 3 * η' / 8 < q 0} :=
        isOpen_lt continuous_const hcoord.continuous
      have hev : β =ᶠ[𝓝 p] fun q => (y + (t - L * s₀) • ν) + Λ q := by
        filter_upwards [hopen.mem_nhds (show 1 - 3 * η' / 8 < p 0 by rw [hps, hs₀]; linarith)]
          with q hq
        simp only [β, hα₁c q (by linarith), hg1 _ hq.le, Λ, FunLike.coe_smul,
          Pi.smul_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, hydef]
        module
      have hfd : fderiv ℝ β p = Λ := by
        rw [hev.fderiv_eq]
        exact (Λ.hasFDerivAt.const_add _).fderiv
      refine transverseAt_of_mem_range hS (ν := ν) (by rw [hβp]; exact hν)
        ⟨EuclideanSpace.single 0 L⁻¹, ?_⟩ hmem
      rw [hfd]
      simp [Λ, smul_smul, hL0.ne']
  · have hset : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ β ⁻¹' S =
        insert (EuclideanSpace.single 0 s₀)
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α₁ ⁻¹' S) := by
      ext p
      simp only [mem_insert_iff, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hp, hmem⟩
        by_cases hp1 : 1 - η' < p 0
        · left
          rw [euclideanSpace_fin_one_eq_single p, (hβS p hp hp1).mp hmem]
        · right
          push Not at hp1
          refine ⟨hp, ?_⟩
          have : β p = α₁ p := by simp [β, hg0 (p 0) (by linarith)]
          rwa [← this]
      · rintro (rfl | ⟨hp, hmem⟩)
        · exact ⟨hs₀mem, (hβS _ hs₀mem (by rw [hs₀c, hs₀]; linarith)).mpr hs₀c⟩
        · refine ⟨hp, ?_⟩
          by_cases hp1 : 1 - η < p 0
          · rw [hα₁c p hp1] at hmem; exact absurd hmem hy
          · push Not at hp1
            have : β p = α₁ p := by simp [β, hg0 (p 0) (by linarith)]
            rwa [this]
    have hnot : EuclideanSpace.single (0 : Fin 1) s₀ ∉
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 ∩ α₁ ⁻¹' S := by
      rintro ⟨-, hmem⟩
      rw [mem_preimage, hα₁c _ (by rw [hs₀c, hs₀]; linarith)] at hmem
      exact hy hmem
    have hfin := finite_transverse_preimage_path hS hc hα₁ htα₁
    rw [hset, Set.ncard_insert_of_notMem hnot hfin, hα₁S]

end LiquidDrop
