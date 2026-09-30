module

public import NoCompromise.Regularity.TiltImprovement
public import NoCompromise.Regularity.GeometricNormals

@[expose] public section

/-!
# Excess iteration and convergence of the selected normals

The iteration is constructed from the actual quasiminimal set. Its smallness,
excess recurrence, and normal increments follow from the proved one-step decay;
they are not additional hypotheses. The full epsilon-regularity graph theorem
is not asserted in this module yet.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
namespace LiquidDrop

/-- The actual excess-decay iteration exists at every admissible center and
initial unit axis. The original smallness threshold is preserved at all scales. -/
theorem excess_decay_iteration :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ ε > 0,
      let θ := excessDecayScale C
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
        (x : AmbientSpace) (r : ℝ) (ν₀ : AmbientSpace),
      0 < r → r ≤ 1 → ‖ν₀‖ = 1 → x ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν₀ + ω * r ≤ ε →
      ∃ ν : ℕ → AmbientSpace, ν 0 = ν₀ ∧ (∀ j, ‖ν j‖ = 1) ∧
        let e := fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable
          x (θ ^ j * r) (ν j)
        (∀ j, e j + ω * (θ ^ j * r) ≤ ε) ∧
        (∀ j, e (j + 1) ≤ θ / 2 * e j + C * θ * ω * (θ ^ j * r)) ∧
        (∀ j, ‖ν (j + 1) - ν j‖ ≤ C * Real.sqrt (e j + ω * (θ ^ j * r))) := by
  classical
  obtain ⟨C, hC, ε, hε, hstep⟩ := excess_decay
  refine ⟨C, hC, ε, hε, ?_⟩
  let θ := excessDecayScale C
  obtain ⟨hθ, hθ32, _, _⟩ := excessDecayScale_bounds hC
  have hθ1 : θ ≤ 1 := by dsimp only [θ]; linarith only [hθ32]
  dsimp only
  intro E ω hE x r ν₀ hr hr1 hν₀ hx hsmall
  let e (j : ℕ) (ν : AmbientSpace) :=
    cylindricalExcess E hE.locallyFinite hE.nullMeasurable x (θ ^ j * r) ν
  have he (j : ℕ) (ν : AmbientSpace) : 0 ≤ e j ν :=
    div_nonneg (normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable _ _)
      (sq_nonneg _)
  let S (j : ℕ) := {ν : AmbientSpace // ‖ν‖ = 1 ∧ e j ν + ω * (θ ^ j * r) ≤ ε}
  have hnext (j : ℕ) (v : S j) : ∃ w : S (j + 1),
      ‖w.val - v.val‖ ≤ C * Real.sqrt (e j v.val + ω * (θ ^ j * r)) ∧
      e (j + 1) w.val ≤ θ / 2 * e j v.val + C * θ * ω * (θ ^ j * r) := by
    have hrj : 0 < θ ^ j * r := mul_pos (pow_pos hθ j) hr
    have hrj1 : θ ^ j * r ≤ 1 :=
      (mul_le_of_le_one_left hr.le (pow_le_one₀ hθ.le hθ1)).trans hr1
    obtain ⟨w, hw, hclose, hdecay⟩ :=
      hstep E ω hE x (θ ^ j * r) v.val hrj hrj1 v.property.1 hx v.property.2
    have hrnext : θ ^ (j + 1) * r = θ * (θ ^ j * r) := by rw [pow_succ']; ring
    have hd : e (j + 1) w ≤ θ / 2 * e j v.val + C * θ * ω * (θ ^ j * r) := by
      simpa only [e, hrnext] using hdecay
    have hpres := excessDecayScale_preserves_smallness hC (he j v.val)
      hE.nonneg hrj.le v.property.2
    have hs : e (j + 1) w + ω * (θ ^ (j + 1) * r) ≤ ε := by
      rw [hrnext]
      calc
        _ ≤ (θ / 2 * e j v.val + C * θ * ω * (θ ^ j * r)) +
            ω * (θ * (θ ^ j * r)) := add_le_add hd le_rfl
        _ ≤ ε / 2 := hpres
        _ ≤ ε := by linarith only [hε]
    exact ⟨⟨w, hw, hs⟩, hclose, hd⟩
  choose next hnext_spec using hnext
  let v : (j : ℕ) → S j := Nat.rec
    ⟨ν₀, hν₀, by simpa only [e, pow_zero, one_mul] using hsmall⟩
    (fun j v => next j v)
  refine ⟨fun j => (v j).val, rfl, fun j => (v j).property.1,
    fun j => (v j).property.2, ?_, ?_⟩
  · intro j
    exact (hnext_spec j (v j)).2
  · intro j
    exact (hnext_spec j (v j)).1


/-- Full blueprint `lem:normals-cauchy` for normals selected by the actual
excess-decay iteration. The sequence, its unit limit, the squared increment
bound, and the geometric convergence rate are all constructed from the original
quasiminimality and small-excess hypotheses. Constants precede all geometric data. -/
theorem normals_cauchy :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 32 ∧ ∃ ε > 0, ∃ C > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
        (x : AmbientSpace) (r : ℝ) (ν₀ : AmbientSpace),
      0 < r → r ≤ 1 → ‖ν₀‖ = 1 → x ∈ frontier (densityOne E) →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν₀ + ω * r ≤ ε →
      ∃ (ν : ℕ → AmbientSpace) (νlim : AmbientSpace),
        ν 0 = ν₀ ∧ (∀ j, ‖ν j‖ = 1) ∧ ‖νlim‖ = 1 ∧ Tendsto ν atTop (𝓝 νlim) ∧
        let e := fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable
          x (θ ^ j * r) (ν j)
        ∀ j, e j + ω * (θ ^ j * r) ≤ ε ∧
          e j + ω * (θ ^ j * r) ≤ C * θ ^ j * (e 0 + ω * r) ∧
          ‖ν (j + 1) - ν j‖ ^ 2 ≤ C * (e j + ω * (θ ^ j * r)) ∧
          ‖ν j - νlim‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt (e 0 + ω * r) := by
  obtain ⟨C₀, hC₀, ε, hε, hiter⟩ := excess_decay_iteration
  let θ := excessDecayScale C₀
  obtain ⟨hθ, hθ32, _, _⟩ := excessDecayScale_bounds hC₀
  have hθ1 : θ < 1 := by dsimp only [θ]; linarith only [hθ32]
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  obtain ⟨B, hB, henergy⟩ := geometric_recurrence_with_error C₀
  obtain ⟨A, hA, hlimit⟩ := geometric_limit_of_recurrence (X := AmbientSpace)
    C₀ (C₀ ^ 2) (sq_nonneg C₀)
  have hden : 0 < 1 - Real.sqrt θ := sub_pos.mpr
    ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hθ1))
  have hquot : 0 < A / (1 - Real.sqrt θ) := div_pos hA hden
  let C := B + C₀ ^ 2 + A / (1 - Real.sqrt θ) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hBC : B ≤ C := by dsimp only [C]; linarith only [sq_nonneg C₀, hquot]
  have hsqC : C₀ ^ 2 ≤ C := by dsimp only [C]; linarith only [hB, hquot]
  have htailC : A / (1 - Real.sqrt θ) ≤ C := by
    dsimp only [C]
    linarith only [hB, sq_nonneg C₀]
  refine ⟨θ, hθ, hθ32, ε, hε, C, hC, ?_⟩
  intro E ω hE x r ν₀ hr hr1 hν₀ hx hsmall
  obtain ⟨ν, hinit, hunit, hsmall_all, hrec, hinc⟩ :=
    hiter E ω hE x r ν₀ hr hr1 hν₀ hx hsmall
  let e := fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable
    x (θ ^ j * r) (ν j)
  have he (j : ℕ) : 0 ≤ e j :=
    div_nonneg (normalExcessIntegral_nonneg E hE.locallyFinite hE.nullMeasurable _ _)
      (sq_nonneg _)
  have hs (j : ℕ) : 0 ≤ e j + ω * (θ ^ j * r) :=
    add_nonneg (he j) (mul_nonneg hE.nonneg (mul_nonneg (pow_nonneg hθ.le j) hr.le))
  have hT : 0 ≤ e 0 + ω * r := add_nonneg (he 0) (mul_nonneg hE.nonneg hr.le)
  have hincsq (j : ℕ) :
      dist (ν j) (ν (j + 1)) ^ 2 ≤ C₀ ^ 2 * (e j + ω * (θ ^ j * r)) := by
    have hb := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC₀pos.le (Real.sqrt_nonneg _))).mpr (hinc j)
    rw [mul_pow, Real.sq_sqrt (hs j)] at hb
    simpa only [dist_eq_norm, norm_sub_rev (ν j) (ν (j + 1))] using hb
  obtain ⟨νlim, hνlim, hrate⟩ :=
    hlimit θ ω r e ν hθ hθ1 hE.nonneg hr.le he hrec hincsq
  refine ⟨ν, νlim, hinit, hunit, geometricNormals_norm_limit hνlim hunit, hνlim, ?_⟩
  dsimp only
  intro j
  refine ⟨hsmall_all j, ?_, ?_, ?_⟩
  · apply (henergy θ ω r e hθ hθ1 hE.nonneg hr.le he hrec j).trans
    have hb := mul_le_mul_of_nonneg_right hBC (mul_nonneg (pow_nonneg hθ.le j) hT)
    simpa only [mul_assoc] using hb
  · have hi := hincsq j
    rw [dist_eq_norm, norm_sub_rev] at hi
    exact hi.trans (mul_le_mul_of_nonneg_right hsqC (hs j))
  · have ht := hrate j
    rw [dist_eq_norm] at ht
    apply ht.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right htailC (Real.rpow_nonneg hθ.le _))
      (Real.sqrt_nonneg _)

end LiquidDrop
