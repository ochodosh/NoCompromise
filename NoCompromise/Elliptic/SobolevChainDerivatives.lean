import NoCompromise.Elliptic.InteriorH2

/-!
# Weak derivatives and the interior Sobolev bootstrap

The weak Sobolev hierarchy below is recursive in actual distributional gradients.
Differentiating the Poisson equation is proved against compact smooth tests, so
iteration of the interior H² estimate does not assume unproved weak derivatives.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient

namespace LiquidDrop

lemma sobolevChain_contDiff_laplacianN {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) : ContDiff ℝ (⊤ : ℕ∞) (laplacianN u) := by
  classical
  apply ContDiff.sum
  intro i _
  exact poissonCoordinateDerivative_smooth (poissonCoordinateDerivative_smooth hu i) i

/-- A coordinate derivative commutes with the classical Laplacian on smooth functions. -/
lemma sobolevChain_poissonCoordinateDerivative_laplacianN {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (i : Fin n) :
    poissonCoordinateDerivative i (laplacianN u) =
      laplacianN (poissonCoordinateDerivative i u) := by
  classical
  funext x
  change fderiv ℝ (fun y => ∑ j, poissonCoordinateDerivative j
    (poissonCoordinateDerivative j u) y) x (EuclideanSpace.single i 1) = ∑ j, _
  rw [fderiv_fun_sum (fun j _ =>
    (poissonCoordinateDerivative_smooth (poissonCoordinateDerivative_smooth hu j) j).differentiable
      (by simp) x), sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  change poissonCoordinateDerivative i (poissonCoordinateDerivative j
    (poissonCoordinateDerivative j u)) x = _
  rw [poissonCoordinateDerivative_comm
    ((poissonCoordinateDerivative_smooth hu j).of_le (by simp)) i j]
  have heq : poissonCoordinateDerivative i (poissonCoordinateDerivative j u) =
      poissonCoordinateDerivative j (poissonCoordinateDerivative i u) :=
    funext (poissonCoordinateDerivative_comm (hu.of_le (by simp)) i j)
  rw [heq]

/-- Differentiating the distributional Poisson equation differentiates its source. -/
theorem HasDistributionalLaplacianOn.gradient_component {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h : HasDistributionalLaplacianOn u f U)
    (hu : HasWeakGradientOn u G U) (hf : HasWeakGradientOn f F U) (i : Fin n) :
    HasDistributionalLaplacianOn (fun x => G x i) (fun x => F x i) U := by
  refine ⟨locallyIntegrableOn_component hu.locallyIntegrable_gradient i,
    locallyIntegrableOn_component hf.locallyIntegrable_gradient i, ?_⟩
  intro φ hφ hcφ hsφ
  have hΔ := sobolevChain_contDiff_laplacianN hφ
  have hcΔ : HasCompactSupport (laplacianN φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset _)
  have hsΔ : tsupport (laplacianN φ) ⊆ U := (tsupport_laplacianN_subset _).trans hsφ
  have hD := poissonCoordinateDerivative_smooth hφ i
  have hcD := HasCompactSupport.poissonCoordinateDerivative hcφ i
  have hsD := (tsupport_poissonCoordinateDerivative_subset i φ).trans hsφ
  have h₁ := hu.test_eq i (laplacianN φ) (hΔ.of_le (by simp)) hcΔ hsΔ
  have h₂ := h.test_eq (poissonCoordinateDerivative i φ) hD hcD hsD
  have h₃ := hf.test_eq i φ (hφ.of_le (by simp)) hcφ hsφ
  change -(∫ x in U, u x * poissonCoordinateDerivative i (laplacianN φ) x) =
    ∫ x in U, laplacianN φ x * G x i at h₁
  change -(∫ x in U, f x * poissonCoordinateDerivative i φ x) =
    ∫ x in U, φ x * F x i at h₃
  rw [← sobolevChain_poissonCoordinateDerivative_laplacianN hφ i] at h₂
  calc
    (∫ x in U, G x i * laplacianN φ x) =
        -(∫ x in U, u x * poissonCoordinateDerivative i (laplacianN φ) x) := by
      simpa only [mul_comm] using h₁.symm
    _ = -(∫ x in U, f x * poissonCoordinateDerivative i φ x) := congrArg Neg.neg h₂
    _ = ∫ x in U, F x i * φ x := by simpa only [mul_comm] using h₃

/-- Integer Sobolev regularity, expressed by recursively constructed weak gradients.
Order zero is L²; each successor requires H¹ and the preceding order for every
coordinate of its genuine weak gradient. -/
def HasSobolevOrderOn {n : ℕ} : ℕ → (EuclideanSpace ℝ (Fin n) → ℝ) →
    Set (EuclideanSpace ℝ (Fin n)) → Prop
  | 0, u, U => MemLp u 2 (volume.restrict U)
  | m + 1, u, U => ∃ G, HasH1GradientOn u G U ∧
      ∀ i, HasSobolevOrderOn m (fun x => G x i) U

lemma HasSobolevOrderOn.memLp {n m : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasSobolevOrderOn m u U) :
    MemLp u 2 (volume.restrict U) := by
  cases m with
  | zero => exact hu
  | succ m => exact hu.choose_spec.1.memLp_function

lemma HasSobolevOrderOn.mono {n m : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hu : HasSobolevOrderOn m u U) (hVU : V ⊆ U) :
    HasSobolevOrderOn m u V := by
  induction m generalizing u with
  | zero => exact hu.mono_measure (Measure.restrict_mono hVU le_rfl)
  | succ m ih =>
      obtain ⟨G, hG, hGi⟩ := hu
      exact ⟨G, hG.mono hVU, fun i => ih (hGi i)⟩

lemma HasH1GradientOn.hasSobolevOrderOn_one {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasH1GradientOn u G U) :
    HasSobolevOrderOn 1 u U := by
  refine ⟨G, hu, fun i => ?_⟩
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hu.memLp_gradient

lemma HasH2DerivativesOn.hasSobolevOrderOn_two {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {H : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasH2DerivativesOn u G H U) :
    HasSobolevOrderOn 2 u U :=
  ⟨G, hu.hasH1GradientOn, fun i => (hu.coordinate_hasH1GradientOn i).hasSobolevOrderOn_one⟩

lemma hasSobolevOrderOn_one_iff {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} : HasSobolevOrderOn 1 u U ↔ IsH1On u U := by
  constructor
  · rintro ⟨G, hG, _⟩
    exact ⟨G, hG⟩
  · rintro ⟨G, hG⟩
    exact hG.hasSobolevOrderOn_one

lemma HasSobolevOrderOn.of_le {n m k : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasSobolevOrderOn k u U) (hmk : m ≤ k) :
    HasSobolevOrderOn m u U := by
  induction k generalizing m u with
  | zero => simpa only [show m = 0 by omega] using hu
  | succ k ih =>
      cases m with
      | zero => exact hu.memLp
      | succ m =>
          obtain ⟨G, hG, hGi⟩ := hu
          exact ⟨G, hG, fun i => ih (hGi i) (by omega)⟩

lemma HasSobolevOrderOn.zero {n : ℕ} (m : ℕ) (U : Set (EuclideanSpace ℝ (Fin n))) :
    HasSobolevOrderOn m (fun _ => 0) U := by
  induction m with
  | zero => exact (HasH1GradientOn.zero U).memLp_function
  | succ m ih => exact ⟨fun _ => 0, HasH1GradientOn.zero U, fun _ => ih⟩

/-- Full finite-order interior bootstrap from actual distributional Poisson data.
No first weak derivative of the original solution is assumed. -/
theorem interior_poisson_sobolev_order {n k : ℕ} (z : EuclideanSpace ℝ (Fin n))
    {r R : ℝ} (hrR : r < R) {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u f (ball z R))
    (hu : MemLp u 2 (volume.restrict (ball z R)))
    (hf : HasSobolevOrderOn k f (ball z R)) :
    HasSobolevOrderOn (k + 2) u (ball z r) := by
  induction k generalizing r R u f with
  | zero =>
      obtain ⟨_, _, hH2⟩ := interior_h2 z hrR
      obtain ⟨G, H, hH, _⟩ := hH2 u f h hu hf
      exact hH.hasSobolevOrderOn_two
  | succ k ih =>
      obtain ⟨F, hF, hFi⟩ := hf
      let s := (r + R) / 2
      have hrs : r < s := by dsimp [s]; linarith
      have hsR : s < R := by dsimp [s]; linarith
      have hsmall : ball z s ⊆ ball z R := ball_subset_ball hsR.le
      obtain ⟨_, _, hH2⟩ := interior_h2 z hsR
      obtain ⟨G, H, hH, _⟩ := hH2 u f h hu hF.memLp_function
      refine ⟨G, hH.hasH1GradientOn.mono (ball_subset_ball hrs.le), fun i => ?_⟩
      apply ih hrs ((h.mono hsmall).gradient_component hH.hasH1GradientOn.toHasWeakGradientOn
        (hF.mono hsmall).toHasWeakGradientOn i)
      · exact (hH.coordinate_hasH1GradientOn i).memLp_function
      · exact (hFi i).mono hsmall

/-- Weakly harmonic L² functions have all finite weak Sobolev orders in smaller balls. -/
theorem interior_harmonic_sobolev_order {n : ℕ} (k : ℕ) (z : EuclideanSpace ℝ (Fin n))
    {r R : ℝ} (hrR : r < R) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasDistributionalLaplacianOn u (fun _ => 0) (ball z R))
    (hu : MemLp u 2 (volume.restrict (ball z R))) :
    HasSobolevOrderOn k u (ball z r) :=
  (interior_poisson_sobolev_order z hrR h hu (HasSobolevOrderOn.zero k (ball z R))).of_le
    (by omega)

lemma hasSobolevOrderOn_two_iff {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} : HasSobolevOrderOn 2 u U ↔
      ∃ G H, HasH2DerivativesOn u G H U := by
  constructor
  · rintro ⟨G, hG, hGi⟩
    choose H hHi using fun i => hasSobolevOrderOn_one_iff.mp (hGi i)
    exact ⟨G, H, ⟨hG, hHi⟩⟩
  · rintro ⟨G, H, hH⟩
    exact hH.hasSobolevOrderOn_two

/-- The trace of the genuine weak Hessian is the distributional Laplacian. -/
theorem HasH2DerivativesOn.hasDistributionalLaplacianOn {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {H : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasH2DerivativesOn u G H U) :
    HasDistributionalLaplacianOn u (fun x => ∑ i, H i x i) U ∧
      MemLp (fun x => ∑ i, H i x i) 2 (volume.restrict U) := by
  classical
  have hmi (i) : MemLp (fun x => H i x i) 2 (volume.restrict U) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp'
      (hu.coordinate_hasH1GradientOn i).memLp_gradient
  have hm : MemLp (fun x => ∑ i, H i x i) 2 (volume.restrict U) :=
    memLp_finsetSum Finset.univ (fun i _ => hmi i)
  refine ⟨⟨hu.hasH1GradientOn.locallyIntegrable_function,
    locallyIntegrableOn_of_locallyIntegrable_restrict
      (hm.locallyIntegrable (by norm_num)), ?_⟩, hm⟩
  intro φ hφ hcφ hsφ
  have hD i := poissonCoordinateDerivative_smooth hφ i
  have hDD i := poissonCoordinateDerivative_smooth (hD i) i
  have hcD i := HasCompactSupport.poissonCoordinateDerivative hcφ i
  have hcDD i := HasCompactSupport.poissonCoordinateDerivative (hcD i) i
  have hsD i := (tsupport_poissonCoordinateDerivative_subset i φ).trans hsφ
  have hsDD i := (tsupport_poissonCoordinateDerivative_subset i
    (poissonCoordinateDerivative i φ)).trans (hsD i)
  have hleft i : IntegrableOn (fun x => u x *
      poissonCoordinateDerivative i (poissonCoordinateDerivative i φ) x) U := by
    simpa only [mul_comm] using
      (integrable_mul_compact_factor hu.hasH1GradientOn.locallyIntegrable_function
        (hDD i).continuous (hcDD i) (hsDD i)).integrableOn
  have hright i : IntegrableOn (fun x => H i x i * φ x) U := by
    simpa only [mul_comm] using
      (integrable_mul_compact_factor (locallyIntegrableOn_component
        (hu.coordinate_hasH1GradientOn i).locallyIntegrable_gradient i)
          hφ.continuous hcφ hsφ).integrableOn
  simp only [laplacianN, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hleft i), integral_finsetSum _ (fun i _ => hright i)]
  apply Finset.sum_congr rfl
  intro i _
  have h₁ := hu.hasH1GradientOn.test_eq i (poissonCoordinateDerivative i φ)
    ((hD i).of_le (by simp)) (hcD i) (hsD i)
  have h₂ := (hu.coordinate_hasH1GradientOn i).test_eq i φ
    (hφ.of_le (by simp)) hcφ hsφ
  change -(∫ x in U, u x * poissonCoordinateDerivative i (poissonCoordinateDerivative i φ) x) =
    ∫ x in U, poissonCoordinateDerivative i φ x * G x i at h₁
  change -(∫ x in U, G x i * poissonCoordinateDerivative i φ x) =
    ∫ x in U, φ x * H i x i at h₂
  calc
    _ = -(∫ x in U, poissonCoordinateDerivative i φ x * G x i) := neg_eq_iff_eq_neg.mp h₁
    _ = _ := by simpa only [mul_comm] using h₂

/-- The L² norm of the weak Hessian trace is bounded by the sum of its row norms. -/
lemma HasH2DerivativesOn.lpNorm_trace_le {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {H : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasH2DerivativesOn u G H U) :
    lpNorm (fun x => ∑ i, H i x i) 2 (volume.restrict U) ≤
      ∑ i, lpNorm (H i) 2 (volume.restrict U) := by
  classical
  have hi (i) := (hu.coordinate_hasH1GradientOn i).memLp_gradient
  have hmi (i) : MemLp (fun x => H i x i) 2 (volume.restrict U) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (hi i)
  have hb := lpNorm_sum_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hmi i)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have heq : (∑ i, fun x => H i x i) = (fun x => ∑ i, H i x i) := by
    ext x
    simp only [Finset.sum_apply]
  rw [heq] at hb
  apply hb.trans
  apply Finset.sum_le_sum
  intro i _
  have hc := poisson_lpNorm_le_mul_of_norm_le (hi i) zero_le_one
    (fun x => (show ‖H i x i‖ ≤ 1 * ‖H i x‖ by simpa using PiLp.norm_apply_le (H i x) i))
  simpa only [one_mul] using hc

end LiquidDrop
