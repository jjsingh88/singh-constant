module

public import Singh.Cayley

@[expose] public section

/-!
Linearization: the conditional variance of `log|Λ'(θ₁)| - log|Λ'(θ₂)|` given an adjacent
pair of eigenangles at gap `δ`, under the Weyl density, satisfies `Var/δ^2 → E_{w₀}[S^2]`.
-/

open MeasureTheory Finset Real Filter Topology

namespace Singh

variable {n : ℕ}

/-- `fL x = log|sin(x/2)|`; `log|e^{iφ}-e^{iψ}| = log 2 + fL(φ-ψ)`. -/
noncomputable def fL (x : ℝ) : ℝ := Real.log (sin (x / 2))

/-- `log|Λ'(θ₁)| - log|Λ'(θ₂)|` for eigenangles `θ₁ = -δ/2`, `θ₂ = δ/2` and the remaining
angles `θ`: the common factor `|e^{iθ₁}-e^{iθ₂}|` cancels. -/
noncomputable def Xd (δ : ℝ) (θ : Fin n → ℝ) : ℝ := ∑ k, (fL (θ k + δ / 2) - fL (θ k - δ / 2))

/-- Adjacency: no remaining angle lies in the arc `(-δ/2, δ/2)`. -/
noncomputable def boxD (n : ℕ) (δ : ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun _ => Set.Ioo (δ / 2) (2 * π - δ / 2)

/-- Weyl density of the remaining angles given eigenangles at `±δ/2`, before restriction:
`∏_{a<b} |e^{iθ_a}-e^{iθ_b}|^2 ∏_k |e^{iθ_k}-e^{-iδ/2}|^2 |e^{iθ_k}-e^{iδ/2}|^2`
up to a constant factor. -/
noncomputable def pwRaw (δ : ℝ) (θ : Fin n → ℝ) : ℝ :=
  (∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2)
    * ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2)

/-- Conditional (Palm) weight of the remaining angles for an adjacent pair at gap `δ`. -/
noncomputable def pw (δ : ℝ) (θ : Fin n → ℝ) : ℝ := (boxD n δ).indicator (pwRaw δ) θ

/-- Conditional variance of `Xd δ` under the Palm weight. -/
noncomputable def palmVar (n : ℕ) (δ : ℝ) : ℝ :=
  (∫ θ : Fin n → ℝ, Xd δ θ ^ 2 * pw δ θ) / (∫ θ : Fin n → ℝ, pw δ θ)
    - ((∫ θ : Fin n → ℝ, Xd δ θ * pw δ θ) / (∫ θ : Fin n → ℝ, pw δ θ)) ^ 2

/-! ### Chord identities -/

lemma norm_exp_sub_exp (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ = 2 * |sin ((a - b) / 2)| := by
  have e : Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)
      = Complex.exp (Complex.I * b) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [e, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one,
    norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]

/-! ### Reflection `θ ↦ 2π - θ` -/

/-- The reflection `θ_k ↦ 2π - θ_k`. -/
noncomputable def refl (θ : Fin n → ℝ) : Fin n → ℝ := fun k => 2 * π - θ k

noncomputable def reflD : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Matrix.diagonal fun _ => (-1 : ℝ)))

lemma hasFDerivAt_refl (θ : Fin n → ℝ) : HasFDerivAt refl (reflD (n := n)) θ := by
  rw [hasFDerivAt_pi']
  intro i
  have h := (hasFDerivAt_apply (𝕜 := ℝ) i θ).const_sub (2 * π)
  refine h.congr_fderiv ?_
  ext v
  show _ = (Matrix.toLin' (Matrix.diagonal fun _ => (-1 : ℝ))) v i
  rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal]; simp

lemma integral_refl (g : (Fin n → ℝ) → ℝ) : ∫ θ, g (refl θ) = ∫ θ, g θ := by
  have himg : refl '' Set.univ = (Set.univ : Set (Fin n → ℝ)) := by
    refine Set.eq_univ_of_forall fun θ => ⟨refl θ, trivial, funext fun k => ?_⟩
    simp [refl]
  have hinj : Set.InjOn (refl (n := n)) Set.univ := fun x _ y _ h => by
    funext k; have := congrFun h k; simp only [refl] at this; linarith
  have hdet : |(reflD (n := n)).det| = 1 := by
    have : (reflD (n := n)).det = ∏ _k : Fin n, (-1 : ℝ) := by
      simp [reflD, ContinuousLinearMap.det, LinearMap.det_toLin', Matrix.det_diagonal]
    rw [this, abs_prod]; simp
  have := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume) MeasurableSet.univ
    (fun θ _ => (hasFDerivAt_refl θ).hasFDerivWithinAt) hinj g
  rw [himg] at this
  simp only [Measure.restrict_univ] at this
  simp only [hdet, one_smul] at this
  exact this.symm

lemma fL_two_pi_sub (y : ℝ) : fL (2 * π - y) = fL y := by
  unfold fL
  rw [show (2 * π - y) / 2 = π - y / 2 by ring, sin_pi_sub]

lemma Xd_refl (δ : ℝ) (θ : Fin n → ℝ) : Xd δ (refl θ) = -Xd δ θ := by
  unfold Xd refl
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [show 2 * π - θ k + δ / 2 = 2 * π - (θ k - δ / 2) by ring,
    show 2 * π - θ k - δ / 2 = 2 * π - (θ k + δ / 2) by ring, fL_two_pi_sub, fL_two_pi_sub]
  ring

lemma pwRaw_refl (δ : ℝ) (θ : Fin n → ℝ) : pwRaw δ (refl θ) = pwRaw δ θ := by
  unfold pwRaw refl
  have h1 : (∏ p ∈ pairs n, sin ((2 * π - θ p.1 - (2 * π - θ p.2)) / 2) ^ 2)
      = ∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2 := by
    refine prod_congr rfl fun p _ => ?_
    rw [show (2 * π - θ p.1 - (2 * π - θ p.2)) / 2 = -((θ p.1 - θ p.2) / 2) by ring, sin_neg,
      neg_sq]
  have h2 : (∏ k, (sin ((2 * π - θ k - δ / 2) / 2) ^ 2 * sin ((2 * π - θ k + δ / 2) / 2) ^ 2))
      = ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2) := by
    refine prod_congr rfl fun k _ => ?_
    rw [show (2 * π - θ k - δ / 2) / 2 = π - (θ k + δ / 2) / 2 by ring,
      show (2 * π - θ k + δ / 2) / 2 = π - (θ k - δ / 2) / 2 by ring, sin_pi_sub, sin_pi_sub]
    ring
  rw [h1, h2]

lemma refl_mem_boxD (δ : ℝ) (θ : Fin n → ℝ) : refl θ ∈ boxD n δ ↔ θ ∈ boxD n δ := by
  simp only [boxD, refl, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
  refine forall_congr' fun k => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma pw_refl (δ : ℝ) (θ : Fin n → ℝ) : pw δ (refl θ) = pw δ θ := by
  unfold pw
  by_cases h : θ ∈ boxD n δ
  · rw [Set.indicator_of_mem ((refl_mem_boxD δ θ).mpr h), Set.indicator_of_mem h, pwRaw_refl]
  · rw [Set.indicator_of_notMem (fun h' => h ((refl_mem_boxD δ θ).mp h')),
      Set.indicator_of_notMem h]

/-- The conditional mean of `Xd` vanishes. -/
lemma integral_Xd_pw (δ : ℝ) : ∫ θ : Fin n → ℝ, Xd δ θ * pw δ θ = 0 := by
  have h := integral_refl (n := n) (fun θ => Xd δ θ * pw δ θ)
  simp only [Xd_refl, pw_refl, neg_mul, integral_neg] at h
  linarith

/-! ### The domination bound -/

lemma log_sub_mul_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 1) :
    (Real.log y - Real.log x) * x * y ≤ y - x := by
  have h := Real.log_le_sub_one_of_pos (div_pos (hx.trans_le hxy) hx)
  rw [Real.log_div (hx.trans_le hxy).ne' hx.ne'] at h
  have hl : 0 ≤ Real.log y - Real.log x :=
    sub_nonneg.mpr (Real.log_le_log hx hxy)
  have h2 : (Real.log y - Real.log x) * x ≤ y - x := by
    have := mul_le_mul_of_nonneg_right h hx.le
    rwa [sub_one_mul, div_mul_cancel₀ _ hx.ne'] at this
  calc (Real.log y - Real.log x) * x * y ≤ (Real.log y - Real.log x) * x * 1 :=
        mul_le_mul_of_nonneg_left hy (mul_nonneg hl hx.le)
    _ ≤ y - x := by rw [mul_one]; exact h2

lemma abs_log_sub_mul_le {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hy : 0 < y) (hy1 : y ≤ 1) :
    |Real.log y - Real.log x| * x * y ≤ |y - x| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hx h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact log_sub_mul_le hx h hy1
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy h)), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr h), mul_right_comm]
    exact log_sub_mul_le hy h hx1

lemma sin_half_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 2 * π) : 0 < sin (x / 2) :=
  sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- Per-angle bound: `|t_k| sin a sin b ≤ δ/2`. -/
lemma term_bound {δ x : ℝ} (hδ : 0 ≤ δ) (h1 : δ / 2 < x) (h2 : x < 2 * π - δ / 2) :
    |fL (x + δ / 2) - fL (x - δ / 2)| * (sin ((x - δ / 2) / 2) * sin ((x + δ / 2) / 2))
      ≤ δ / 2 := by
  have ha := sin_half_pos (x := x - δ / 2) (by linarith) (by linarith)
  have hb := sin_half_pos (x := x + δ / 2) (by linarith) (by linarith)
  have := abs_log_sub_mul_le ha (sin_le_one _) hb (sin_le_one _)
  rw [← mul_assoc]
  refine this.trans ((Real.abs_sin_sub_sin_le _ _).trans (le_of_eq ?_))
  rw [show (x + δ / 2) / 2 - (x - δ / 2) / 2 = δ / 2 by ring, abs_of_nonneg (by linarith)]

lemma pairs_prod_nonneg_le_one (θ : Fin n → ℝ) :
    0 ≤ (∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2) ∧
      (∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2) ≤ 1 :=
  ⟨prod_nonneg fun _ _ => sq_nonneg _,
    prod_le_one₀ (fun _ _ => sq_nonneg _) fun _ _ => by
      rw [sq_le_one_iff_abs_le_one]; exact abs_sin_le_one _⟩

lemma pwRaw_nonneg_le_one (δ : ℝ) (θ : Fin n → ℝ) : 0 ≤ pwRaw δ θ ∧ pwRaw δ θ ≤ 1 := by
  have hs : ∀ y : ℝ, 0 ≤ sin y ^ 2 ∧ sin y ^ 2 ≤ 1 := fun y =>
    ⟨sq_nonneg _, by rw [sq_le_one_iff_abs_le_one]; exact abs_sin_le_one _⟩
  have hq : 0 ≤ ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2) ∧
      ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2) ≤ 1 :=
    ⟨prod_nonneg fun k _ => mul_nonneg (hs _).1 (hs _).1,
      prod_le_one₀ (fun k _ => mul_nonneg (hs _).1 (hs _).1) fun k _ =>
        mul_le_one₀ (hs _).2 (hs _).1 (hs _).2⟩
  obtain ⟨p0, p1⟩ := pairs_prod_nonneg_le_one θ
  exact ⟨mul_nonneg p0 hq.1, mul_le_one₀ p1 hq.1 hq.2⟩

lemma boxD_subset {δ : ℝ} (hδ : 0 ≤ δ) : boxD n δ ⊆ boxC n := by
  intro θ h
  simp only [boxD, boxC, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo] at h ⊢
  exact fun k => ⟨by linarith [(h k).1], by linarith [(h k).2]⟩

/-- Domination: `(Xd/δ)^2 · pw ≤ n^2/4` on `boxC`, and `0` off it. -/
lemma F_bound {δ : ℝ} (hδ : 0 < δ) (θ : Fin n → ℝ) :
    ‖(Xd δ θ / δ) ^ 2 * pw δ θ‖ ≤ (boxC n).indicator (fun _ => (n : ℝ) ^ 2 / 4) θ := by
  unfold pw
  by_cases h : θ ∈ boxD n δ
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (boxD_subset hδ.le h)]
    have hm : ∀ k, δ / 2 < θ k ∧ θ k < 2 * π - δ / 2 := by
      intro k; simpa [boxD] using h k
    set t : Fin n → ℝ := fun k => fL (θ k + δ / 2) - fL (θ k - δ / 2)
    set s : Fin n → ℝ := fun k => sin ((θ k - δ / 2) / 2) * sin ((θ k + δ / 2) / 2)
    have hs0 : ∀ k, 0 ≤ s k := fun k =>
      mul_nonneg (sin_half_pos (by linarith [(hm k).1]) (by linarith [(hm k).2])).le
        (sin_half_pos (by linarith [(hm k).1]) (by linarith [(hm k).2])).le
    have hs1 : ∀ k, s k ≤ 1 := fun k =>
      mul_le_one₀ (sin_le_one _)
        (sin_half_pos (x := θ k + δ / 2) (by linarith [(hm k).1]) (by linarith [(hm k).2])).le
        (sin_le_one _)
    have hts : ∀ k, |t k| * s k ≤ δ / 2 := fun k => term_bound hδ.le (hm k).1 (hm k).2
    have hQ : ∏ k, (sin ((θ k - δ / 2) / 2) ^ 2 * sin ((θ k + δ / 2) / 2) ^ 2)
        = ∏ k, s k ^ 2 := prod_congr rfl fun k _ => by simp only [s]; ring
    have hP : ∀ j, ∏ k, s k ^ 2 ≤ s j ^ 2 := by
      intro j
      rw [← mul_prod_erase _ _ (mem_univ j)]
      refine mul_le_of_le_one_right (sq_nonneg _) (prod_le_one₀ (fun _ _ => sq_nonneg _)
        fun k _ => ?_)
      exact pow_le_one₀ (hs0 k) (hs1 k)
    have hQ0 : 0 ≤ ∏ k, s k ^ 2 := prod_nonneg fun _ _ => sq_nonneg _
    obtain ⟨p0, p1⟩ := pairs_prod_nonneg_le_one θ
    have hX : Xd δ θ = ∑ k, t k := rfl
    have hCS : (∑ k, t k) ^ 2 ≤ n * ∑ k, t k ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := t)
    have hterm : ∀ j, t j ^ 2 * ∏ k, s k ^ 2 ≤ (δ / 2) ^ 2 := by
      intro j
      calc t j ^ 2 * ∏ k, s k ^ 2 ≤ t j ^ 2 * s j ^ 2 :=
            mul_le_mul_of_nonneg_left (hP j) (sq_nonneg _)
        _ = (|t j| * s j) ^ 2 := by rw [mul_pow (|t j|), sq_abs]
        _ ≤ (δ / 2) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (hs0 j)) (hts j) 2
    have hmain : (∑ k, t k) ^ 2 * ∏ k, s k ^ 2 ≤ (n : ℝ) ^ 2 * (δ / 2) ^ 2 := by
      calc (∑ k, t k) ^ 2 * ∏ k, s k ^ 2 ≤ (n * ∑ k, t k ^ 2) * ∏ k, s k ^ 2 :=
            mul_le_mul_of_nonneg_right hCS hQ0
        _ = n * ∑ j, t j ^ 2 * ∏ k, s k ^ 2 := by rw [mul_assoc, sum_mul]
        _ ≤ n * ∑ _j : Fin n, (δ / 2) ^ 2 :=
            mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => hterm j) (Nat.cast_nonneg _)
        _ = (n : ℝ) ^ 2 * (δ / 2) ^ 2 := by simp; ring
    have hpw0 := (pwRaw_nonneg_le_one δ θ).1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hpw0), pwRaw, hQ, hX,
      div_pow]
    have hδ2 : 0 < δ ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ2]
    calc (∑ k, t k) ^ 2 * ((∏ p ∈ pairs n, sin ((θ p.1 - θ p.2) / 2) ^ 2) * ∏ k, s k ^ 2)
        ≤ (∑ k, t k) ^ 2 * (1 * ∏ k, s k ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right p1 hQ0) (sq_nonneg _)
      _ ≤ (n : ℝ) ^ 2 * (δ / 2) ^ 2 := by rw [one_mul]; exact hmain
      _ = (n : ℝ) ^ 2 / 4 * δ ^ 2 := by ring
  · rw [Set.indicator_of_notMem h, mul_zero, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _

/-! ### Pointwise limits -/

lemma hasDerivAt_fL {x : ℝ} (h0 : 0 < x) (h1 : x < 2 * π) :
    HasDerivAt fL (cos (x / 2) * (1 / 2) / sin (x / 2)) x := by
  have h := ((hasDerivAt_id x).div_const 2).sin
  simp only [id] at h
  exact h.log (sin_half_pos h0 h1).ne'

lemma tendsto_half_ne (c : ℝ) (hc : c ≠ 0) :
    Tendsto (fun δ : ℝ => c * δ) (𝓝[>] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun δ : ℝ => c * δ) (𝓝 0) (𝓝 (c * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact mul_ne_zero hc (ne_of_gt hδ)

/-- The symmetric difference quotient converges to the derivative. -/
lemma tendsto_sym_quot {f : ℝ → ℝ} {d x : ℝ} (hf : HasDerivAt f d x) :
    Tendsto (fun δ => (f (x + δ / 2) - f (x - δ / 2)) / δ) (𝓝[>] 0) (𝓝 d) := by
  have hs := hasDerivAt_iff_tendsto_slope_zero.mp hf
  have h1 := hs.comp (tendsto_half_ne (1 / 2) (by norm_num))
  have h2 := hs.comp (tendsto_half_ne (-1 / 2) (by norm_num))
  have h3 := (h1.add h2).div_const 2
  rw [show (d + d) / 2 = d by ring] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  simp only [Function.comp, smul_eq_mul]
  rw [show x + -1 / 2 * δ = x - δ / 2 by ring, show x + 1 / 2 * δ = x + δ / 2 by ring]
  field_simp
  ring

lemma eventually_mem_boxD {θ : Fin n → ℝ} (h : θ ∈ boxC n) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), θ ∈ boxD n δ := by
  have hm : ∀ k, 0 < θ k ∧ θ k < 2 * π := by intro k; simpa [boxC] using h k
  have : ∀ k, ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ / 2 < θ k ∧ θ k < 2 * π - δ / 2 := by
    intro k
    have ha : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < 2 * θ k := eventually_lt_nhds (by linarith [(hm k).1])
    have hb : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < 2 * (2 * π - θ k) :=
      eventually_lt_nhds (by linarith [(hm k).2])
    filter_upwards [nhdsWithin_le_nhds ha, nhdsWithin_le_nhds hb] with δ h1 h2
    exact ⟨by linarith, by linarith⟩
  filter_upwards [Filter.eventually_all.mpr this] with δ hδ
  simpa [boxD] using hδ

lemma continuous_pwRaw (θ : Fin n → ℝ) : Continuous fun δ => pwRaw δ θ := by
  unfold pwRaw; fun_prop

lemma pwRaw_zero (θ : Fin n → ℝ) : pwRaw 0 θ = wC θ := by
  unfold pwRaw wC
  rw [prod_congr rfl (fun k _ => show sin ((θ k - 0 / 2) / 2) ^ 2 * sin ((θ k + 0 / 2) / 2) ^ 2
    = sin (θ k / 2) ^ 4 by simp only [zero_div, sub_zero, add_zero]; ring)]

lemma Xd_div_tendsto {θ : Fin n → ℝ} (h : θ ∈ boxC n) :
    Tendsto (fun δ => Xd δ θ / δ) (𝓝[>] 0) (𝓝 (Ssum θ)) := by
  have hm : ∀ k, 0 < θ k ∧ θ k < 2 * π := by intro k; simpa [boxC] using h k
  have hS : Ssum θ = ∑ k, cos (θ k / 2) * (1 / 2) / sin (θ k / 2) := by
    rw [Ssum, mul_sum]; refine sum_congr rfl fun k _ => ?_; ring
  rw [hS]
  have : (fun δ => Xd δ θ / δ)
      = fun δ => ∑ k, (fL (θ k + δ / 2) - fL (θ k - δ / 2)) / δ := by
    funext δ; rw [Xd, sum_div]
  rw [this]
  exact tendsto_finsetSum _ fun k _ => tendsto_sym_quot (hasDerivAt_fL (hm k).1 (hm k).2)

lemma pw_tendsto (θ : Fin n → ℝ) :
    Tendsto (fun δ => pw δ θ) (𝓝[>] 0) (𝓝 ((boxC n).indicator wC θ)) := by
  by_cases h : θ ∈ boxC n
  · rw [Set.indicator_of_mem h, ← pwRaw_zero]
    have hc := ((continuous_pwRaw θ).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    refine hc.congr' ?_
    filter_upwards [eventually_mem_boxD h] with δ hδ
    rw [pw, Set.indicator_of_mem hδ]
  · rw [Set.indicator_of_notMem h]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [pw, Set.indicator_of_notMem (fun h' => h (boxD_subset (le_of_lt hδ) h'))]

lemma F_tendsto (θ : Fin n → ℝ) :
    Tendsto (fun δ => (Xd δ θ / δ) ^ 2 * pw δ θ) (𝓝[>] 0)
      (𝓝 ((boxC n).indicator (fun θ => Ssum θ ^ 2 * wC θ) θ)) := by
  by_cases h : θ ∈ boxC n
  · have hp := pw_tendsto θ
    rw [Set.indicator_of_mem h] at hp ⊢
    exact ((Xd_div_tendsto h).pow 2).mul hp
  · rw [Set.indicator_of_notMem h]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [pw, Set.indicator_of_notMem (fun h' => h (boxD_subset (le_of_lt hδ) h')), mul_zero]

/-! ### Dominated convergence -/

lemma measurableSet_boxD (δ : ℝ) : MeasurableSet (boxD n δ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

lemma measurableSet_boxC : MeasurableSet (boxC n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

lemma measurable_pw (δ : ℝ) : Measurable (pw (n := n) δ) := by
  unfold pw
  refine Measurable.indicator ?_ (measurableSet_boxD δ)
  unfold pwRaw; fun_prop

lemma measurable_Xd (δ : ℝ) : Measurable (Xd (n := n) δ) := by
  unfold Xd fL; fun_prop

lemma volume_boxC_ne_top : volume (boxC n) ≠ ⊤ := by
  rw [boxC, volume_pi_pi]; simp [Real.volume_Ioo, ENNReal.mul_eq_top]

lemma integrable_indicator_const (c : ℝ) :
    Integrable ((boxC n).indicator fun _ => c) := by
  rw [integrable_indicator_iff measurableSet_boxC]
  exact integrableOn_const volume_boxC_ne_top

lemma integral_F_tendsto :
    Tendsto (fun δ => ∫ θ : Fin n → ℝ, (Xd δ θ / δ) ^ 2 * pw δ θ) (𝓝[>] 0)
      (𝓝 (∫ θ in boxC n, Ssum θ ^ 2 * wC θ)) := by
  rw [← integral_indicator measurableSet_boxC]
  refine tendsto_integral_filter_of_dominated_convergence
    ((boxC n).indicator fun _ => (n : ℝ) ^ 2 / 4) ?_ ?_ (integrable_indicator_const _)
    (Eventually.of_forall F_tendsto)
  · exact Eventually.of_forall fun δ =>
      (((measurable_Xd δ).div_const δ).pow_const 2 |>.mul (measurable_pw δ)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact Eventually.of_forall (F_bound hδ)

lemma integral_pw_tendsto :
    Tendsto (fun δ => ∫ θ : Fin n → ℝ, pw δ θ) (𝓝[>] 0) (𝓝 (∫ θ in boxC n, wC θ)) := by
  rw [← integral_indicator measurableSet_boxC]
  refine tendsto_integral_filter_of_dominated_convergence
    ((boxC n).indicator fun _ => (1 : ℝ)) ?_ ?_ (integrable_indicator_const _)
    (Eventually.of_forall pw_tendsto)
  · exact Eventually.of_forall fun δ => (measurable_pw δ).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    refine Eventually.of_forall fun θ => ?_
    unfold pw
    by_cases h : θ ∈ boxD n δ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (boxD_subset (le_of_lt hδ) h),
        Real.norm_eq_abs, abs_of_nonneg (pwRaw_nonneg_le_one δ θ).1]
      exact (pwRaw_nonneg_le_one δ θ).2
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

/-- **Linearization.** `Var(X_δ | adjacent pair at gap δ) / δ^2 → E_{w₀}[S^2]`. -/
theorem palmVar_tendsto (n : ℕ) :
    Tendsto (fun δ => palmVar n δ / δ ^ 2) (𝓝[>] 0) (𝓝 (circleE n)) := by
  have h := (integral_F_tendsto (n := n)).div (integral_pw_tendsto (n := n))
    (integral_wC_pos n).ne'
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ2 : δ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hδ)
  rw [palmVar, integral_Xd_pw, zero_div, sq (0 : ℝ), mul_zero, sub_zero]
  have : (fun θ : Fin n → ℝ => (Xd δ θ / δ) ^ 2 * pw δ θ)
      = fun θ => (δ ^ 2)⁻¹ * (Xd δ θ ^ 2 * pw δ θ) := by
    funext θ; rw [div_pow]; field_simp
  simp only [Pi.div_apply]
  rw [this, integral_const_mul]
  field_simp

end Singh
