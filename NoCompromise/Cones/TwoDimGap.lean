module

public import NoCompromise.Cones.TwoDimParity

@[expose] public section

/-!
# Short gaps in the planar link

A finite link not contained in an antipodal pair has a gap shorter than pi.
For a minimizing cone, the phase on a gap determines the phases just outside it.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace LiquidDrop

/-- A half-turn sends a circle point to its antipode. -/
theorem cone2dCircle_add_pi (θ : ℝ) :
    cone2dCircle (θ + Real.pi) = -cone2dCircle θ := by
  ext i
  fin_cases i <;> simp [Real.cos_add, Real.sin_add]

/-- A finite subset of the unit circle not contained in an antipodal pair has two angularly
consecutive points at angular distance less than pi. -/
theorem cone2d_exists_short_gap {Γ : Set (EuclideanSpace ℝ (Fin 2))}
    (hfin : Γ.Finite) (hsub : Γ ⊆ Metric.sphere 0 1)
    (hnot : ¬ ∃ u : EuclideanSpace ℝ (Fin 2), Γ ⊆ {u, -u}) :
    ∃ θ₁ θ₂ : ℝ, θ₁ < θ₂ ∧ θ₂ < θ₁ + Real.pi ∧
      cone2dCircle θ₁ ∈ Γ ∧ cone2dCircle θ₂ ∈ Γ ∧
      ∀ θ ∈ Ioo θ₁ θ₂, cone2dCircle θ ∉ Γ := by
  classical
  have hne : Γ.Nonempty := by
    by_contra h
    exact hnot ⟨0, by simp [Set.not_nonempty_iff_eq_empty.mp h]⟩
  obtain ⟨u, hu⟩ := hne
  obtain ⟨a, -, ha⟩ := cone2dCircle_surjOn (hsub hu)
  have hw : ∃ w ∈ Γ, w ≠ u ∧ w ≠ -u := by
    by_contra h
    apply hnot
    refine ⟨u, ?_⟩
    intro w hw
    simpa only [mem_insert_iff, mem_singleton_iff, not_and_or, not_not] using
      (show ¬ (w ≠ u ∧ w ≠ -u) from fun hn => h ⟨w, hw, hn⟩)
  obtain ⟨w, hw, hwu, hwn⟩ := hw
  have hrot : (cone2dRotation a).symm w ∈ Metric.sphere 0 1 := by
    simpa only [mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map] using hsub hw
  obtain ⟨t, ht, htw⟩ := cone2dCircle_surjOn hrot
  have hat : cone2dCircle (a + t) = w := by
    apply (cone2dRotation a).symm.injective
    simpa only [cone2dRotation_symm_circle, add_sub_cancel_left] using htw
  have ht0 : t ≠ 0 := by
    intro h
    apply hwu
    simpa [h, ha] using hat.symm
  have htp : t < Real.pi := lt_of_le_of_ne ht.2 (by
    intro h
    apply hwn
    rw [← hat, h, cone2dCircle_add_pi, ha])
  have htm : -Real.pi < t := lt_of_le_of_ne ht.1 (by
    intro h
    apply hwn
    rw [← hat, ← h]
    have he : cone2dCircle (a + -Real.pi) = cone2dCircle (a + Real.pi) := by
      calc
        cone2dCircle (a + -Real.pi) =
            cone2dCircle ((a + -Real.pi) + 2 * Real.pi) :=
          (cone2dCircle_add_two_pi _).symm
        _ = cone2dCircle (a + Real.pi) := by congr 1; ring
    rw [he, cone2dCircle_add_pi, ha])
  have hpair : ∃ a b : ℝ, a < b ∧ b < a + Real.pi ∧
      cone2dCircle a ∈ Γ ∧ cone2dCircle b ∈ Γ := by
    rcases lt_or_gt_of_ne ht0 with htneg | htpos
    · exact ⟨a + t, a, by linarith, by linarith, hat ▸ hw, ha ▸ hu⟩
    · exact ⟨a, a + t, by linarith, by linarith, ha ▸ hu, hat ▸ hw⟩
  obtain ⟨a, b, hab, hbp, ha, hb⟩ := hpair
  let S := cone2dCircle ⁻¹' Γ ∩ Ioc a b
  have hS : S.Finite := by
    apply (finite_image_iff ((cone2dCircle_injOn a).mono ?_)).mp
    · exact hfin.subset (by rintro _ ⟨θ, hθ, rfl⟩; exact hθ.1)
    · intro θ hθ
      exact ⟨hθ.2.1.le, by linarith [hθ.2.2, Real.pi_pos]⟩
  obtain ⟨c, hc, hmin⟩ := Set.exists_min_image S id hS ⟨b, hb, hab, le_rfl⟩
  refine ⟨a, c, hc.2.1, lt_of_le_of_lt hc.2.2 hbp, ha, hc.1, ?_⟩
  intro θ hθ hΓ
  have hle := hmin θ ⟨hΓ, hθ.1, le_trans hθ.2.le hc.2.2⟩
  exact (not_le_of_gt hθ.2) hle

/-- The phase on an angular gap is constant, and the phases immediately outside
both endpoints are the opposite phase. -/
theorem cone2d_gap_phases {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    (h₁ : cone2dCircle θ₁ ∈ frontier (densityOne C))
    (h₂ : cone2dCircle θ₂ ∈ frontier (densityOne C))
    (havoid : ∀ θ ∈ Ioo θ₁ θ₂, cone2dCircle θ ∉ frontier (densityOne C)) :
    ∃ η > 0,
      ((∀ θ ∈ Ioo θ₁ θ₂, cone2dCircle θ ∈ interior (densityOne C)) ∧
        (∀ θ ∈ Ioo (θ₁ - η) θ₁, cone2dCircle θ ∈ interior (densityOne C)ᶜ) ∧
        (∀ θ ∈ Ioo θ₂ (θ₂ + η), cone2dCircle θ ∈ interior (densityOne C)ᶜ)) ∨
      ((∀ θ ∈ Ioo θ₁ θ₂, cone2dCircle θ ∈ interior (densityOne C)ᶜ) ∧
        (∀ θ ∈ Ioo (θ₁ - η) θ₁, cone2dCircle θ ∈ interior (densityOne C)) ∧
        (∀ θ ∈ Ioo θ₂ (θ₂ + η), cone2dCircle θ ∈ interior (densityOne C))) := by
  let D := densityOne C
  have hcover : Ioo θ₁ θ₂ ⊆
      (cone2dCircle ⁻¹' interior D) ∪ (cone2dCircle ⁻¹' interior Dᶜ) := by
    intro θ hθ
    have h := havoid θ hθ
    rw [← mem_compl_iff, compl_frontier_eq_union_interior] at h
    exact h
  have hdisj : Disjoint (interior D) (interior Dᶜ) := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact interior_subset hx' (interior_subset hx)
  have hdisj' : Disjoint (cone2dCircle ⁻¹' interior D)
      (cone2dCircle ⁻¹' interior Dᶜ) := hdisj.preimage _
  have hphase :
      (∀ θ ∈ Ioo θ₁ θ₂, cone2dCircle θ ∈ interior D) ∨
      (∀ θ ∈ Ioo θ₁ θ₂, cone2dCircle θ ∈ interior Dᶜ) := by
    obtain ⟨θ, hθ⟩ := nonempty_Ioo.mpr hθ
    rcases hcover hθ with hi | he
    · exact Or.inl (isPreconnected_Ioo.subset_left_of_subset_union
        (isOpen_interior.preimage cone2dCircle_continuous)
        (isOpen_interior.preimage cone2dCircle_continuous)
        hdisj' hcover ⟨θ, hθ, hi⟩)
    · exact Or.inr (isPreconnected_Ioo.subset_left_of_subset_union
        (isOpen_interior.preimage cone2dCircle_continuous)
        (isOpen_interior.preimage cone2dCircle_continuous)
        hdisj'.symm (fun _ ht => (hcover ht).symm) ⟨θ, hθ, he⟩)
  have hleft_bad {A B : Set (EuclideanSpace ℝ (Fin 2))}
      (hd : Disjoint A B) (hA : ∀ θ ∈ Ioo θ₁ θ₂, cone2dCircle θ ∈ A)
      (hB : ∀ᶠ θ in 𝓝[>] θ₁, cone2dCircle θ ∈ B) : False := by
    obtain ⟨θ, ⟨hB, hlt⟩, hgt⟩ :=
      ((hB.and ((eventually_lt_nhds hθ).filter_mono nhdsWithin_le_nhds)).and
        self_mem_nhdsWithin).exists
    exact disjoint_left.mp hd (hA θ ⟨hgt, hlt⟩) hB
  have hright_bad {A B : Set (EuclideanSpace ℝ (Fin 2))}
      (hd : Disjoint A B) (hA : ∀ θ ∈ Ioo θ₁ θ₂, cone2dCircle θ ∈ A)
      (hB : ∀ᶠ θ in 𝓝[<] θ₂, cone2dCircle θ ∈ B) : False := by
    obtain ⟨θ, ⟨hB, hgt⟩, hlt⟩ :=
      ((hB.and ((eventually_gt_nhds hθ).filter_mono nhdsWithin_le_nhds)).and
        self_mem_nhdsWithin).exists
    exact disjoint_left.mp hd (hA θ ⟨hgt, hlt⟩) hB
  have hwidth {P : ℝ → Prop} (hl : ∀ᶠ θ in 𝓝[<] θ₁, P θ)
      (hr : ∀ᶠ θ in 𝓝[>] θ₂, P θ) :
      ∃ η > 0, (∀ θ ∈ Ioo (θ₁ - η) θ₁, P θ) ∧
        (∀ θ ∈ Ioo θ₂ (θ₂ + η), P θ) := by
    obtain ⟨l, hl, hlP⟩ := mem_nhdsLT_iff_exists_Ico_subset.mp hl
    obtain ⟨r, hr, hrP⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hr
    refine ⟨min (θ₁ - l) (r - θ₂), lt_min (sub_pos.mpr hl) (sub_pos.mpr hr), ?_, ?_⟩
    · intro θ hθ
      exact hlP ⟨by linarith [min_le_left (θ₁ - l) (r - θ₂), hθ.1], hθ.2⟩
    · intro θ hθ
      exact hrP ⟨hθ.1, by linarith [min_le_right (θ₁ - l) (r - θ₂), hθ.2]⟩
  have hf₁ := cone2dCircle_frontier_flip hmin hcone h₁
  have hf₂ := cone2dCircle_frontier_flip hmin hcone h₂
  rcases hphase with hi | he
  · have hl : ∀ᶠ θ in 𝓝[<] θ₁, cone2dCircle θ ∈ interior Dᶜ := by
      rcases hf₁ with ⟨_, hr⟩ | ⟨hl, _⟩
      · exact (hleft_bad hdisj hi hr).elim
      · exact hl
    have hr : ∀ᶠ θ in 𝓝[>] θ₂, cone2dCircle θ ∈ interior Dᶜ := by
      rcases hf₂ with ⟨_, hr⟩ | ⟨hl, _⟩
      · exact hr
      · exact (hright_bad hdisj hi hl).elim
    obtain ⟨η, hη, hl, hr⟩ := hwidth hl hr
    exact ⟨η, hη, Or.inl ⟨hi, hl, hr⟩⟩
  · have hl : ∀ᶠ θ in 𝓝[<] θ₁, cone2dCircle θ ∈ interior D := by
      rcases hf₁ with ⟨hl, _⟩ | ⟨_, hr⟩
      · exact hl
      · exact (hleft_bad hdisj.symm he hr).elim
    have hr : ∀ᶠ θ in 𝓝[>] θ₂, cone2dCircle θ ∈ interior D := by
      rcases hf₂ with ⟨hl, _⟩ | ⟨_, hr⟩
      · exact (hright_bad hdisj.symm he hl).elim
      · exact hr
    obtain ⟨η, hη, hl, hr⟩ := hwidth hl hr
    exact ⟨η, hη, Or.inr ⟨he, hl, hr⟩⟩

/-- The phases on a gap and just outside it persist under every positive
dilation, with one common angular width and one common phase choice. -/
theorem cone2d_gap_phases_smul {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hmin : IsLocallyPerimeterMinimizing C)
    (hcone : ∀ r : ℝ, 0 < r → (fun y => r • y) '' densityOne C = densityOne C)
    {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    (h₁ : cone2dCircle θ₁ ∈ frontier (densityOne C))
    (h₂ : cone2dCircle θ₂ ∈ frontier (densityOne C))
    (havoid : ∀ θ ∈ Ioo θ₁ θ₂, cone2dCircle θ ∉ frontier (densityOne C)) :
    ∃ η > 0,
      ((∀ θ ∈ Ioo θ₁ θ₂, ∀ r : ℝ, 0 < r →
          r • cone2dCircle θ ∈ interior (densityOne C)) ∧
        (∀ θ ∈ Ioo (θ₁ - η) θ₁, ∀ r : ℝ, 0 < r →
          r • cone2dCircle θ ∈ interior (densityOne C)ᶜ) ∧
        (∀ θ ∈ Ioo θ₂ (θ₂ + η), ∀ r : ℝ, 0 < r →
          r • cone2dCircle θ ∈ interior (densityOne C)ᶜ)) ∨
      ((∀ θ ∈ Ioo θ₁ θ₂, ∀ r : ℝ, 0 < r →
          r • cone2dCircle θ ∈ interior (densityOne C)ᶜ) ∧
        (∀ θ ∈ Ioo (θ₁ - η) θ₁, ∀ r : ℝ, 0 < r →
          r • cone2dCircle θ ∈ interior (densityOne C)) ∧
        (∀ θ ∈ Ioo θ₂ (θ₂ + η), ∀ r : ℝ, 0 < r →
          r • cone2dCircle θ ∈ interior (densityOne C))) := by
  have hD : IsDilationInvariant (densityOne C) := hcone
  have hi {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ interior (densityOne C))
      (r : ℝ) (hr : 0 < r) : r • x ∈ interior (densityOne C) :=
    hD.interior.smul_mem hr hx
  have he {x : EuclideanSpace ℝ (Fin 2)} (hx : x ∈ interior (densityOne C)ᶜ)
      (r : ℝ) (hr : 0 < r) : r • x ∈ interior (densityOne C)ᶜ := by
    rw [interior_compl] at hx ⊢
    exact fun h => hx (hD.closure.mem_of_smul_mem hr h)
  obtain ⟨η, hη, hphases⟩ := cone2d_gap_phases hmin hcone hθ h₁ h₂ havoid
  refine ⟨η, hη, ?_⟩
  rcases hphases with ⟨ha, hl, hr⟩ | ⟨ha, hl, hr⟩
  · exact Or.inl ⟨fun θ hθ => hi (ha θ hθ),
      fun θ hθ => he (hl θ hθ), fun θ hθ => he (hr θ hθ)⟩
  · exact Or.inr ⟨fun θ hθ => he (ha θ hθ),
      fun θ hθ => hi (hl θ hθ), fun θ hθ => hi (hr θ hθ)⟩

end LiquidDrop
