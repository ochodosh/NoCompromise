module

public import NoCompromise.Capacity.Potential
public import NoCompromise.Elliptic.HarmonicMeanValue

@[expose] public section

/-!
# The monotone limit of annular capacitary solutions

Blueprint `thm:capacitary-potential`, Steps 2-3. A monotone bounded family of
continuous annular solutions converges pointwise. The limit is weakly harmonic
off `K` by dominated convergence against test functions, equals its smooth
representative off `K` by the mean-value identity, and is continuous at points
of `K` by squeezing between the first annular solution and `1`.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace LiquidDrop

private lemma annular_le_add_nat (R₁ : ℝ) (n : ℕ) : R₁ ≤ R₁ + n :=
  le_add_of_nonneg_right n.cast_nonneg

/-- A bounded set lies in all annular balls of large index. -/
private lemma annular_exists_nat_ball {S : Set AmbientSpace} (hS : Bornology.IsBounded S)
    (R₁ : ℝ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → S ⊆ ball 0 (R₁ + n) := by
  obtain ⟨r, hr⟩ := hS.subset_ball 0
  obtain ⟨N, hN⟩ := exists_nat_ge (r - R₁)
  refine ⟨N, fun n hn => hr.trans (ball_subset_ball ?_)⟩
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The pointwise limit of the annular family is almost everywhere strongly measurable. -/
private lemma annular_limit_aestronglyMeasurable {v : ℝ → AmbientSpace → ℝ} {R₁ : ℝ}
    (hvc : ∀ R, R₁ ≤ R → ContinuousOn (v R) (ball 0 R)) {u : AmbientSpace → ℝ}
    (hlim : ∀ x, Tendsto (fun n : ℕ => v (R₁ + n) x) atTop (𝓝 (u x))) :
    AEStronglyMeasurable u volume := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n : ℕ => (ball (0 : AmbientSpace) (R₁ + n)).indicator (v (R₁ + n)))
    (fun n => ?_) (ae_of_all _ fun x => ?_)
  · exact (aestronglyMeasurable_indicator_iff measurableSet_ball).mpr
      ((hvc _ (annular_le_add_nat R₁ n)).aestronglyMeasurable measurableSet_ball)
  · obtain ⟨N, hN⟩ := annular_exists_nat_ball (Bornology.isBounded_singleton (x := x)) R₁
    refine (hlim x).congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [indicator_of_mem (hN n hn (mem_singleton x))]


/-- Boundedness by `1` makes the limit globally locally integrable. -/
private lemma annular_limit_locallyIntegrable {u : AmbientSpace → ℝ}
    (hmeas : AEStronglyMeasurable u volume) (hu01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1) :
    LocallyIntegrable u volume := by
  have : MemLp u ⊤ volume := memLp_top_of_bound hmeas 1 (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hu01 x])
  exact this.locallyIntegrable le_top

/-- Step 2: dominated convergence against test functions supported off `K`. -/
private lemma annular_limit_harmonic {K : Set AmbientSpace} {R₁ : ℝ}
    {v : ℝ → AmbientSpace → ℝ}
    (hvc : ∀ R, R₁ ≤ R → ContinuousOn (v R) (ball 0 R))
    (hvh : ∀ R, R₁ ≤ R → HasDistributionalLaplacianOn (v R) (fun _ => 0) (ball 0 R \ K))
    (hv01 : ∀ R, R₁ ≤ R → ∀ x, 0 ≤ v R x ∧ v R x ≤ 1)
    {u : AmbientSpace → ℝ} (hmeas : AEStronglyMeasurable u volume)
    (hu01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1)
    (hlim : ∀ x, Tendsto (fun n : ℕ => v (R₁ + n) x) atTop (𝓝 (u x))) :
    HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ := by
  refine ⟨(annular_limit_locallyIntegrable hmeas hu01).locallyIntegrableOn _,
    locallyIntegrableOn_zero, ?_⟩
  intro φ hφ hcφ hsφ
  simp only [zero_mul, integral_zero]
  set Δφ := laplacianN φ with hΔdef
  have hΔc : Continuous Δφ := (sobolevChain_contDiff_laplacianN hφ).continuous
  have hΔs : tsupport Δφ ⊆ tsupport φ := tsupport_laplacianN_subset φ
  have hset (f : AmbientSpace → ℝ) (s : Set AmbientSpace) (hs : tsupport φ ⊆ s) :
      (∫ x in s, f x * Δφ x) = ∫ x in tsupport φ, f x * Δφ x := by
    have hw (t : Set AmbientSpace) (ht : tsupport φ ⊆ t) :
        (∫ x in t, f x * Δφ x) = ∫ x, f x * Δφ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (ht (hΔs h))), mul_zero]
    rw [hw s hs, hw _ subset_rfl]
  obtain ⟨N, hN⟩ := annular_exists_nat_ball hcφ.isCompact.isBounded R₁
  have hzero : ∀ n : ℕ, N ≤ n → (∫ x in tsupport φ, v (R₁ + n) x * Δφ x) = 0 := by
    intro n hn
    have h := (hvh _ (annular_le_add_nat R₁ n)).test_eq φ hφ hcφ
      (fun y hy => ⟨hN n hn hy, hsφ hy⟩)
    simp only [zero_mul, integral_zero] at h
    rw [← hset _ (ball 0 (R₁ + n) \ K) (fun y hy => ⟨hN n hn hy, hsφ hy⟩), h]
  have hmeasS : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hlimit : Tendsto (fun n : ℕ => ∫ x in tsupport φ, v (R₁ + n) x * Δφ x) atTop
      (𝓝 (∫ x in tsupport φ, u x * Δφ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖Δφ x‖) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop N] with n hn
      exact (((hvc _ (annular_le_add_nat R₁ n)).mono (hN n hn)).mul
        hΔc.continuousOn).aestronglyMeasurable hmeasS
    · refine Eventually.of_forall fun n => ae_of_all _ fun x => ?_
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      have := hv01 _ (annular_le_add_nat R₁ n) x
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    · exact (hΔc.continuousOn.integrableOn_compact hcφ.isCompact).norm
    · exact ae_of_all _ fun x => (hlim x).mul_const _
  rw [hset u Kᶜ hsφ]
  exact tendsto_nhds_unique hlimit (tendsto_const_nhds.congr' <|
    (eventually_ge_atTop N).mono fun n hn => (hzero n hn).symm)

/-- Step 3 input: the limit satisfies the mean-value identity on balls off `K`. -/
private lemma annular_limit_eq_average {K : Set AmbientSpace} (hK : IsCompact K) {R₁ : ℝ}
    {v : ℝ → AmbientSpace → ℝ}
    (hvc : ∀ R, R₁ ≤ R → ContinuousOn (v R) (ball 0 R))
    (hvh : ∀ R, R₁ ≤ R → HasDistributionalLaplacianOn (v R) (fun _ => 0) (ball 0 R \ K))
    (hv01 : ∀ R, R₁ ≤ R → ∀ x, 0 ≤ v R x ∧ v R x ≤ 1)
    {u : AmbientSpace → ℝ}
    (hlim : ∀ x, Tendsto (fun n : ℕ => v (R₁ + n) x) atTop (𝓝 (u x)))
    (c : AmbientSpace) {r : ℝ} (hr : 0 < r) (hs : closedBall c r ⊆ Kᶜ) :
    u c = ⨍ x in ball c r, u x := by
  obtain ⟨N, hN⟩ := annular_exists_nat_ball (isBounded_closedBall (x := c) (r := r)) R₁
  have hmean : ∀ n : ℕ, N ≤ n → v (R₁ + n) c = ⨍ x in ball c r, v (R₁ + n) x := by
    intro n hn
    exact ((hvh _ (annular_le_add_nat R₁ n)).average_ball_eq (by norm_num)
      (isOpen_ball.sdiff hK.isClosed) ((hvc _ (annular_le_add_nat R₁ n)).mono sdiff_subset)
      c hr (fun y hy => ⟨hN n hn hy, hs hy⟩)).symm
  have hint : Tendsto (fun n : ℕ => ∫ x in ball c r, v (R₁ + n) x) atTop
      (𝓝 (∫ x in ball c r, u x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop N] with n hn
      exact ((hvc _ (annular_le_add_nat R₁ n)).mono
        (ball_subset_closedBall.trans (hN n hn))).aestronglyMeasurable measurableSet_ball
    · refine Eventually.of_forall fun n => ae_of_all _ fun x => ?_
      have := hv01 _ (annular_le_add_nat R₁ n) x
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    · exact (continuousOn_const.integrableOn_compact (isCompact_closedBall c r)).mono_set
        ball_subset_closedBall
    · exact ae_of_all _ fun x => hlim x
  have havg : Tendsto (fun n : ℕ => ⨍ x in ball c r, v (R₁ + n) x) atTop
      (𝓝 (⨍ x in ball c r, u x)) := by
    simp only [setAverage_eq]
    exact hint.const_smul _
  exact tendsto_nhds_unique (hlim c) (havg.congr' <|
    (eventually_ge_atTop N).mono fun n hn => (hmean n hn).symm)

/-- Blueprint `thm:capacitary-potential`, Steps 2-3: the monotone limit of annular solutions. -/
theorem capacitary_potential_of_annular_family {K : Set AmbientSpace} (hK : IsCompact K)
    {R₁ : ℝ} (hKR : K ⊆ ball 0 R₁) (v : ℝ → AmbientSpace → ℝ)
    (hvc : ∀ R, R₁ ≤ R → ContinuousOn (v R) (ball 0 R))
    (hvh : ∀ R, R₁ ≤ R → HasDistributionalLaplacianOn (v R) (fun _ => 0) (ball 0 R \ K))
    (hv1 : ∀ R, R₁ ≤ R → ∀ x ∈ K, v R x = 1)
    (hv01 : ∀ R, R₁ ≤ R → ∀ x, 0 ≤ v R x ∧ v R x ≤ 1)
    (hmono : ∀ R R', R₁ ≤ R → R ≤ R' → ∀ x, v R x ≤ v R' x)
    {C : ℝ} (hbar : ∀ R, R₁ ≤ R → ∀ x ∉ K, v R x ≤ C / ‖x‖) :
    ∃ u : AmbientSpace → ℝ, Continuous u ∧
      HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ ∧ ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ ∧
      (∀ x ∈ K, u x = 1) ∧ Tendsto u (cocompact AmbientSpace) (𝓝 0) ∧
      (∀ x, 0 ≤ u x ∧ u x ≤ 1) ∧ (∀ x ∉ K, u x ≤ C / ‖x‖) ∧
      ∀ R, R₁ ≤ R → ∀ x, v R x ≤ u x := by
  set u : AmbientSpace → ℝ := fun x => ⨆ n : ℕ, v (R₁ + n) x with hudef
  have hbdd : ∀ x, BddAbove (range fun n : ℕ => v (R₁ + n) x) := fun x =>
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hv01 _ (annular_le_add_nat R₁ n) x).2⟩
  have hmon : ∀ x, Monotone fun n : ℕ => v (R₁ + n) x := fun x m n hmn =>
    hmono _ _ (annular_le_add_nat R₁ m) (by gcongr) x
  have hlim : ∀ x, Tendsto (fun n : ℕ => v (R₁ + n) x) atTop (𝓝 (u x)) := fun x =>
    tendsto_atTop_ciSup (hmon x) (hbdd x)
  have hle : ∀ x (n : ℕ), v (R₁ + n) x ≤ u x := fun x n => le_ciSup (hbdd x) n
  have hu01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1 := fun x =>
    ⟨(hv01 _ (annular_le_add_nat R₁ 0) x).1.trans (hle x 0),
      ciSup_le fun n => (hv01 _ (annular_le_add_nat R₁ n) x).2⟩
  have hvu : ∀ R, R₁ ≤ R → ∀ x, v R x ≤ u x := by
    intro R hR x
    refine (hmono R (R₁ + ⌈R - R₁⌉₊) hR ?_ x).trans (hle x _)
    have := Nat.le_ceil (R - R₁)
    linarith
  have hu1 : ∀ x ∈ K, u x = 1 := fun x hx =>
    le_antisymm (hu01 x).2 ((hv1 R₁ le_rfl x hx).symm.le.trans (hvu R₁ le_rfl x))
  have hubar : ∀ x ∉ K, u x ≤ C / ‖x‖ := fun x hx =>
    ciSup_le fun n => hbar _ (annular_le_add_nat R₁ n) x hx
  have hmeas := annular_limit_aestronglyMeasurable hvc hlim
  have hharm := annular_limit_harmonic hvc hvh hv01 hmeas hu01 hlim
  have hopen : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hL2 : ∀ x ∈ Kᶜ, ∃ R > 0, ball x R ⊆ Kᶜ ∧ MemLp u 2 (volume.restrict (ball x R)) := by
    intro x hx
    obtain ⟨R, hR, hRK⟩ := Metric.isOpen_iff.mp hopen x hx
    let : IsFiniteMeasure (volume.restrict (ball x R)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_ball.measure_lt_top⟩
    refine ⟨R, hR, hRK, MemLp.of_bound hmeas.restrict 1 (ae_of_all _ fun y => ?_)⟩
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hu01 y]
  obtain ⟨w, hw, he, -, hwm⟩ := hharm.exists_smooth_mean_value (by norm_num) hopen hL2
  have huw : ∀ x ∈ Kᶜ, u x = w x := by
    intro c hc
    obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.mp hopen c hc
    have hs : closedBall c (ε / 2) ⊆ Kᶜ :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεK
    have hae : w =ᵐ[volume.restrict (ball c (ε / 2))] u :=
      ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hs) he
    rw [annular_limit_eq_average hK hvc hvh hv01 hlim c (half_pos hε) hs, ← average_congr hae,
      hwm c _ (half_pos hε) hs]
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ := hw.congr huw
  have hcont : Continuous u := by
    refine continuous_iff_continuousAt.mpr fun p => ?_
    by_cases hp : p ∈ K
    · have hc0 : ContinuousAt (v R₁) p :=
        (hvc R₁ le_rfl).continuousAt (isOpen_ball.mem_nhds (hKR hp))
      have hlow : Tendsto (v R₁) (𝓝 p) (𝓝 1) := by
        have := hc0.tendsto
        rwa [hv1 R₁ le_rfl p hp] at this
      rw [ContinuousAt, hu1 p hp]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
        (fun x => hvu R₁ le_rfl x) (fun x => (hu01 x).2)
    · exact hsmooth.continuousOn.continuousAt (hopen.mem_nhds hp)
  have hdecay : Tendsto u (cocompact AmbientSpace) (𝓝 0) := by
    have hC : Tendsto (fun x : AmbientSpace => C / ‖x‖) (cocompact AmbientSpace) (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_norm_cocompact_atTop
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
      (Eventually.of_forall fun x => (hu01 x).1)
      (Filter.mem_of_superset hK.compl_mem_cocompact fun x hx => hubar x hx)
  exact ⟨u, hcont, hharm, hsmooth, hu1, hdecay, hu01, hubar, hvu⟩

end LiquidDrop
