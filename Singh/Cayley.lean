module

public import Singh.Loop

@[expose] public section

/-!
The Cayley transform `u = cot(θ/2)` from the circle weight `|1-e^{iθ}|^4` to the Hua ensemble.
-/

open MeasureTheory Finset Real

namespace Singh

variable {n : ℕ}

/-- `θ_k = π - 2 arctan u_k`, the inverse of `u_k = cot(θ_k/2)`. -/
noncomputable def cmap (u : Fin n → ℝ) : Fin n → ℝ := fun k => π - 2 * arctan (u k)

/-- The open box `(0, 2π)^n`. -/
noncomputable def boxC (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ fun _ => Set.Ioo 0 (2 * π)

/-- Derivative of `cmap`: the diagonal map with entries `-2/(1+u_k^2)`. -/
noncomputable def cmapD (u : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    (Matrix.toLin' (Matrix.diagonal fun k => -2 / (1 + u k ^ 2)))

lemma cmapD_apply (u v : Fin n → ℝ) (k : Fin n) :
    cmapD u v k = -2 / (1 + u k ^ 2) * v k := by
  show (Matrix.toLin' (Matrix.diagonal fun k => -2 / (1 + u k ^ 2))) v k = _
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma hasFDerivAt_cmap (u : Fin n → ℝ) : HasFDerivAt cmap (cmapD u) u := by
  rw [hasFDerivAt_pi']
  intro i
  have h := (((hasDerivAt_arctan (u i)).comp_hasFDerivAt u
    (hasFDerivAt_apply (𝕜 := ℝ) i u)).const_mul 2).const_sub π
  convert h using 1
  · funext v; simp [cmap]
  · ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, cmapD_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp; ring

lemma det_cmapD (u : Fin n → ℝ) : |(cmapD u).det| = 2 ^ n / bigG u := by
  have : (cmapD u).det = ∏ k, (-2 / (1 + u k ^ 2)) := by
    simp [cmapD, ContinuousLinearMap.det, LinearMap.det_toLin', Matrix.det_diagonal]
  rw [this, abs_prod, bigG, div_eq_mul_inv, ← prod_inv_distrib,
    show (2 : ℝ) ^ n = ∏ _k : Fin n, (2 : ℝ) by simp, ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  rw [abs_div, abs_neg, abs_two, abs_of_pos (by positivity : (0 : ℝ) < 1 + u k ^ 2)]; ring

lemma cmap_injective : Function.Injective (cmap (n := n)) := by
  intro u v h
  funext k
  have := congrFun h k
  simp only [cmap] at this
  exact arctan_injective (by linarith)

lemma cmap_image : cmap '' Set.univ = boxC n := by
  ext θ
  simp only [Set.image_univ, Set.mem_range, boxC, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioo]
  constructor
  · rintro ⟨u, rfl⟩ k
    have := arctan_lt_pi_div_two (u k)
    have := neg_pi_div_two_lt_arctan (u k)
    simp only [cmap]; constructor <;> linarith
  · intro h
    refine ⟨fun k => tan ((π - θ k) / 2), funext fun k => ?_⟩
    obtain ⟨h1, h2⟩ := h k
    simp only [cmap]
    rw [arctan_tan (by linarith) (by linarith)]; ring

lemma half_cmap (u : Fin n → ℝ) (k : Fin n) : cmap u k / 2 = π / 2 - arctan (u k) := by
  simp only [cmap]; ring

lemma sin_half_cmap (u : Fin n → ℝ) (k : Fin n) :
    sin (cmap u k / 2) = 1 / √(1 + u k ^ 2) := by
  rw [half_cmap, sin_pi_div_two_sub, cos_arctan]

lemma cos_half_cmap (u : Fin n → ℝ) (k : Fin n) :
    cos (cmap u k / 2) = u k / √(1 + u k ^ 2) := by
  rw [half_cmap, cos_pi_div_two_sub, sin_arctan]

lemma cot_half_cmap (u : Fin n → ℝ) (k : Fin n) :
    cos (cmap u k / 2) / sin (cmap u k / 2) = u k := by
  rw [sin_half_cmap, cos_half_cmap]
  have : 0 < √(1 + u k ^ 2) := Real.sqrt_pos.mpr (by positivity)
  field_simp

lemma sin_sq_diff_cmap (u : Fin n → ℝ) (a b : Fin n) :
    sin ((cmap u a - cmap u b) / 2) ^ 2 = (u a - u b) ^ 2 / ((1 + u a ^ 2) * (1 + u b ^ 2)) := by
  have e : (cmap u a - cmap u b) / 2 = arctan (u b) - arctan (u a) := by simp only [cmap]; ring
  have ha : 0 < √(1 + u a ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hb : 0 < √(1 + u b ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have sa := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + u a ^ 2)
  have sb := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + u b ^ 2)
  rw [e, sin_sub, sin_arctan, sin_arctan, cos_arctan, cos_arctan]
  field_simp
  rw [sa, sb]; ring

/-- Circle weight `∏_{a<b} sin^2((θ_a-θ_b)/2) ∏_k sin^4(θ_k/2)`, proportional to
`∏_{a<b} |e^{iθ_a}-e^{iθ_b}|^2 ∏_k |1-e^{iθ_k}|^4`. -/
noncomputable def wC (θ : Fin n → ℝ) : ℝ :=
  (∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2) * ∏ k, sin (θ k / 2) ^ 4

/-- `S = (1/2) ∑_k cot(θ_k/2)`. -/
noncomputable def Ssum (θ : Fin n → ℝ) : ℝ := (1 / 2) * ∑ k, cos (θ k / 2) / sin (θ k / 2)

/-- `E_{w₀}[S^2]` for the circle weight on `n` angles. -/
noncomputable def circleE (n : ℕ) : ℝ :=
  (∫ θ in boxC n, Ssum θ ^ 2 * wC θ) / ∫ θ in boxC n, wC θ

lemma Ssum_cmap (u : Fin n → ℝ) : Ssum (cmap u) = (∑ k, u k) / 2 := by
  simp only [Ssum, cot_half_cmap]; ring

lemma jac_wC_cmap (u : Fin n → ℝ) :
    |(cmapD u).det| * wC (cmap u) = 2 ^ n * huaWeight u := by
  have hG := bigG_pos u
  have e1 : ∏ p ∈ pairs n, sin ((cmap u p.1 - cmap u p.2) / 2) ^ 2
      = Wp u / (bigG u ^ n / bigG u) := by
    simp only [sin_sq_diff_cmap]
    rw [prod_div_distrib, pairs_prod_g, Wp]
  have e2 : ∏ k, sin (cmap u k / 2) ^ 4 = (bigG u ^ 2)⁻¹ := by
    rw [bigG, ← prod_pow, ← prod_inv_distrib]
    refine prod_congr rfl fun k _ => ?_
    rw [sin_half_cmap]
    have s := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + u k ^ 2)
    rw [div_pow, show √(1 + u k ^ 2) ^ 4 = (√(1 + u k ^ 2) ^ 2) ^ 2 by ring, s]; simp
  rw [det_cmapD, wC, e1, e2, huaWeight, vdm_eq_Wp]
  field_simp
  ring

/-- Change of variables `θ = cmap u` on the box. -/
lemma integral_boxC (g : (Fin n → ℝ) → ℝ) :
    ∫ θ in boxC n, g θ = ∫ u, 2 ^ n / bigG u * g (cmap u) := by
  rw [← cmap_image, integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
    MeasurableSet.univ (fun u _ => (hasFDerivAt_cmap u).hasFDerivWithinAt)
    cmap_injective.injOn g, Measure.restrict_univ]
  simp only [det_cmapD, smul_eq_mul]

lemma jac_wC_cmap' (u : Fin n → ℝ) : 2 ^ n / bigG u * wC (cmap u) = 2 ^ n * huaWeight u := by
  rw [← det_cmapD]; exact jac_wC_cmap u

/-- **Cayley transform.** `E_{w₀}[S^2] = E_{n,2}[((∑ u)/2)^2]`. -/
theorem circleE_eq_hua (n : ℕ) :
    circleE n = ∫ u, ((∑ k, u k) / 2) ^ 2 ∂(huaMeasure n) := by
  have h1 : ∫ θ in boxC n, Ssum θ ^ 2 * wC θ
      = 2 ^ n * ∫ u : Fin n → ℝ, huaWeight u * ((∑ k, u k) / 2) ^ 2 := by
    rw [integral_boxC, ← integral_const_mul]
    congr 1; funext u
    rw [Ssum_cmap]
    calc 2 ^ n / bigG u * (((∑ k, u k) / 2) ^ 2 * wC (cmap u))
        = ((∑ k, u k) / 2) ^ 2 * (2 ^ n / bigG u * wC (cmap u)) := by ring
      _ = _ := by rw [jac_wC_cmap']; ring
  have h2 : ∫ θ in boxC n, wC θ = 2 ^ n * huaZ n := by
    rw [integral_boxC, huaZ, ← integral_const_mul]
    congr 1; funext u; exact jac_wC_cmap' u
  have hZ := (huaZ_pos (n := n)).ne'
  rw [circleE, h1, h2, integral_hua_eq]
  field_simp

lemma integral_wC_pos (n : ℕ) : 0 < ∫ θ in boxC n, wC θ := by
  rw [integral_boxC, show (fun u : Fin n → ℝ => 2 ^ n / bigG u * wC (cmap u))
    = fun u => 2 ^ n * huaWeight u from funext jac_wC_cmap', integral_const_mul]
  exact mul_pos (by positivity) huaZ_pos

end Singh
