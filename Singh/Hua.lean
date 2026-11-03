module

public import Singh.Algebra

@[expose] public section

/-!
# The Hua ensemble `P_{n,2}`

`P_{n,2}(u) = Z⁻¹ ∏_{j<k} (u_j-u_k)^2 ∏_k (1+u_k^2)^{-(n+2)}` on `ℝ^n`, written with
`∏_{j<k}(u_j-u_k)^2 = ∏_k ∏_{j≠k} |u_k-u_j|`.
We prove that it is a probability measure, that it is absolutely continuous
(so `u` has distinct coordinates almost surely), and that `(∑u)^2` and `∑u^2`
are integrable.
-/

open MeasureTheory Finset
open scoped ENNReal NNReal

namespace Singh

variable {n : ℕ}

/-- `∏_k ∏_{j≠k} |u_k - u_j| = ∏_{j<k} (u_j-u_k)^2`. -/
noncomputable def vdm (u : Fin n → ℝ) : ℝ := ∏ k, ∏ j ∈ univ.erase k, |u k - u j|

/-- `G(u) = ∏_k (1+u_k^2)`. -/
noncomputable def bigG (u : Fin n → ℝ) : ℝ := ∏ k, (1 + u k ^ 2)

/-- Unnormalized Hua weight with `h = 2`. -/
noncomputable def huaWeight (u : Fin n → ℝ) : ℝ := vdm u / bigG u ^ (n + 2)

lemma one_le_g (x : ℝ) : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]

lemma one_le_bigG (u : Fin n → ℝ) : 1 ≤ bigG u := by
  unfold bigG
  calc (1 : ℝ) = ∏ _k : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) (fun k _ => one_le_g (u k))

lemma bigG_pos (u : Fin n → ℝ) : 0 < bigG u := lt_of_lt_of_le one_pos (one_le_bigG u)

lemma vdm_nonneg (u : Fin n → ℝ) : 0 ≤ vdm u :=
  prod_nonneg fun _ _ => prod_nonneg fun _ _ => abs_nonneg _

lemma huaWeight_nonneg (u : Fin n → ℝ) : 0 ≤ huaWeight u :=
  div_nonneg (vdm_nonneg u) (pow_nonneg (bigG_pos u).le _)

lemma pair_bound (a b : ℝ) : (a - b) ^ 2 ≤ 2 * ((1 + a ^ 2) * (1 + b ^ 2)) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a * b)]

lemma prod_erase_prod (g : Fin n → ℝ) (hg : ∀ k, 0 < g k) :
    ∏ k, ∏ j ∈ univ.erase k, g j = (∏ k, g k) ^ n / ∏ k, g k := by
  have e : ∀ k, ∏ j ∈ univ.erase k, g j = (∏ j, g j) / g k := fun k => by
    rw [eq_div_iff (hg k).ne', mul_comm, mul_prod_erase _ _ (mem_univ k)]
  simp only [e, prod_div_distrib, prod_const, card_univ, Fintype.card_fin]

lemma vdm_sq_le (u : Fin n → ℝ) :
    vdm u ^ 2 ≤ ((2 : ℝ) ^ n) ^ n * bigG u ^ (2 * n) := by
  have hg : ∀ k, 0 < 1 + u k ^ 2 := fun k => by positivity
  have hG := bigG_pos u
  have e1 : vdm u ^ 2 = ∏ k, ∏ j ∈ univ.erase k, (u k - u j) ^ 2 := by
    unfold vdm; rw [← prod_pow]; simp only [← prod_pow, sq_abs]
  have e2 : ∏ k, ∏ j ∈ univ.erase k, (u k - u j) ^ 2
      ≤ ∏ k, ∏ j ∈ univ.erase k, (2 * ((1 + u k ^ 2) * (1 + u j ^ 2))) :=
    prod_le_prod₀ (fun _ _ => prod_nonneg fun _ _ => sq_nonneg _)
      (fun k _ => prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun j _ => pair_bound _ _))
  have e3 : ∏ k, ∏ j ∈ univ.erase k, (2 * ((1 + u k ^ 2) * (1 + u j ^ 2)))
      = ((2 : ℝ) ^ (n - 1)) ^ n * (bigG u ^ (n - 1) * (bigG u ^ n / bigG u)) := by
    simp only [prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin, prod_pow]
    rw [prod_erase_prod (fun k => 1 + u k ^ 2) hg]
    unfold bigG; ring
  have h1 : (1 : ℝ) ≤ bigG u := one_le_bigG u
  have e4 : bigG u ^ (n - 1) * (bigG u ^ n / bigG u) ≤ bigG u ^ (2 * n) := by
    have a : bigG u ^ (n - 1) ≤ bigG u ^ n := pow_le_pow_right₀ h1 (Nat.sub_le n 1)
    have b : bigG u ^ n / bigG u ≤ bigG u ^ n := div_le_self (by positivity) h1
    calc _ ≤ bigG u ^ n * bigG u ^ n :=
          mul_le_mul a b (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]; ring_nf
  have e5 : ((2 : ℝ) ^ (n - 1)) ^ n ≤ ((2 : ℝ) ^ n) ^ n :=
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)) n
  rw [e1]
  calc _ ≤ _ := e2
    _ = _ := e3
    _ ≤ _ := mul_le_mul e5 e4 (by positivity) (by positivity)

/-- `w(u) ≤ C / G(u)^2` with `C = 2^{n^2/2}`. -/
lemma huaWeight_le (u : Fin n → ℝ) :
    huaWeight u ≤ Real.sqrt (((2 : ℝ) ^ n) ^ n) / bigG u ^ 2 := by
  have hG := bigG_pos u
  have hw := huaWeight_nonneg u
  have hsq : huaWeight u ^ 2 ≤ (Real.sqrt (((2 : ℝ) ^ n) ^ n) / bigG u ^ 2) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    unfold huaWeight
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    calc vdm u ^ 2 * (bigG u ^ 2) ^ 2 ≤ ((2 : ℝ) ^ n) ^ n * bigG u ^ (2 * n) * (bigG u ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right (vdm_sq_le u) (by positivity)
      _ = ((2 : ℝ) ^ n) ^ n * (bigG u ^ (n + 2)) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ hw (by positivity) two_ne_zero).mp hsq

lemma g_le_bigG (u : Fin n → ℝ) (k : Fin n) : 1 + u k ^ 2 ≤ bigG u := by
  unfold bigG
  rw [← mul_prod_erase _ _ (mem_univ k)]
  have : (1 : ℝ) ≤ ∏ x ∈ univ.erase k, (1 + u x ^ 2) :=
    calc (1 : ℝ) = ∏ _x ∈ univ.erase k, (1 : ℝ) := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => zero_le_one) (fun k _ => one_le_g (u k))
  have := one_le_g (u k)
  nlinarith

lemma sum_sq_le (u : Fin n → ℝ) : ∑ k, u k ^ 2 ≤ n * bigG u := by
  calc ∑ k, u k ^ 2 ≤ ∑ _k : Fin n, bigG u :=
        sum_le_sum fun k _ => by have := g_le_bigG u k; nlinarith
    _ = n * bigG u := by simp

lemma sq_sum_le (u : Fin n → ℝ) : (∑ k, u k) ^ 2 ≤ n * (n * bigG u) := by
  calc (∑ k, u k) ^ 2 ≤ (univ : Finset (Fin n)).card * ∑ k, u k ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ n * (n * bigG u) := by
        simp only [card_univ, Fintype.card_fin]
        exact mul_le_mul_of_nonneg_left (sum_sq_le u) (Nat.cast_nonneg n)

lemma continuous_bigG : Continuous (fun u : Fin n → ℝ => bigG u) := by
  unfold bigG; fun_prop

lemma continuous_huaWeight : Continuous (fun u : Fin n → ℝ => huaWeight u) := by
  have hv : Continuous (fun u : Fin n → ℝ => vdm u) := by unfold vdm; fun_prop
  exact hv.div (continuous_bigG.pow _) fun u => (pow_pos (bigG_pos u) _).ne'

lemma integrable_inv_bigG : Integrable (fun u : Fin n → ℝ => (bigG u)⁻¹) := by
  have e : (fun u : Fin n → ℝ => (bigG u)⁻¹) = fun u => ∏ k, (1 + u k ^ 2)⁻¹ := by
    funext u; unfold bigG; rw [prod_inv_distrib]
  rw [e, volume_pi]
  exact Integrable.fintype_prod (f := fun _ x => (1 + x ^ 2)⁻¹) (μ := fun _ => volume)
    (fun _ => integrable_inv_one_add_sq)

/-- Integrability from a bound `|f| ≤ C / G`. -/
lemma integrable_of_le_inv_bigG (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (C : ℝ)
    (hb : ∀ u, |f u| ≤ C * (bigG u)⁻¹) : Integrable f :=
  Integrable.mono' (integrable_inv_bigG.const_mul C) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hb u)

lemma weight_le_inv (u : Fin n → ℝ) :
    huaWeight u ≤ Real.sqrt (((2 : ℝ) ^ n) ^ n) * (bigG u)⁻¹ := by
  have hG := one_le_bigG u
  calc huaWeight u ≤ Real.sqrt (((2 : ℝ) ^ n) ^ n) / bigG u ^ 2 := huaWeight_le u
    _ ≤ Real.sqrt (((2 : ℝ) ^ n) ^ n) / bigG u :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (by positivity)
          (by nlinarith)
    _ = _ := by ring

lemma weight_mul_le (u : Fin n → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (D : ℝ) (hq : q ≤ D * bigG u) :
    huaWeight u * q ≤ Real.sqrt (((2 : ℝ) ^ n) ^ n) * D * (bigG u)⁻¹ := by
  have hG := bigG_pos u
  have hD : 0 ≤ D := by
    by_contra h; push Not at h; nlinarith
  calc huaWeight u * q ≤ (Real.sqrt (((2 : ℝ) ^ n) ^ n) / bigG u ^ 2) * (D * bigG u) :=
        mul_le_mul (huaWeight_le u) hq hq0 (by positivity)
    _ = Real.sqrt (((2 : ℝ) ^ n) ^ n) * D * (bigG u)⁻¹ := by field_simp

lemma integrable_huaWeight : Integrable (fun u : Fin n → ℝ => huaWeight u) :=
  integrable_of_le_inv_bigG _ continuous_huaWeight _ fun u => by
    rw [abs_of_nonneg (huaWeight_nonneg u)]; exact weight_le_inv u

/-- The coincidence set `{u_i = u_j}` for `i ≠ j` is Lebesgue-null. -/
lemma volume_diag_eq_zero {i j : Fin n} (hij : i ≠ j) :
    volume {u : Fin n → ℝ | u i = u j} = 0 := by
  let L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i
    - LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j
  have hs : {u : Fin n → ℝ | u i = u j} = (LinearMap.ker L : Set (Fin n → ℝ)) := by
    ext u; simp [L, sub_eq_zero]
  rw [hs]
  apply Measure.addHaar_submodule
  intro htop
  have : (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ LinearMap.ker L := by rw [htop]; trivial
  simp [L, Pi.single_apply, hij.symm] at this

lemma ae_injective_volume : ∀ᵐ u : Fin n → ℝ, Function.Injective u := by
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ i : Fin n, ⋃ j : Fin n, ⋃ (_ : i ≠ j), {u | u i = u j})
  · intro u hu
    simp only [Function.Injective, not_forall, Set.mem_ofPred_eq] at hu
    obtain ⟨i, j, h, hne⟩ := hu
    simp only [Set.mem_iUnion]
    exact ⟨i, j, hne, h⟩
  · simp only [measure_iUnion_null_iff]
    intro i j hij
    exact volume_diag_eq_zero hij

lemma vdm_pos {u : Fin n → ℝ} (hu : Function.Injective u) : 0 < vdm u :=
  prod_pos fun k _ => prod_pos fun j hj =>
    abs_pos.mpr (sub_ne_zero.mpr (hu.ne (ne_of_mem_erase hj).symm))

/-- Normalizing constant. -/
noncomputable def huaZ (n : ℕ) : ℝ := ∫ u : Fin n → ℝ, huaWeight u

lemma huaZ_pos : 0 < huaZ n := by
  unfold huaZ
  rw [integral_pos_iff_support_of_nonneg (fun u => huaWeight_nonneg u) integrable_huaWeight]
  have hsub : {u : Fin n → ℝ | ¬ Function.Injective u}ᶜ ⊆ Function.support huaWeight := by
    intro u hu
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hu
    exact (div_pos (vdm_pos hu) (pow_pos (bigG_pos u) _)).ne'
  have hnull : volume {u : Fin n → ℝ | ¬ Function.Injective u} = 0 := ae_iff.mp ae_injective_volume
  have huniv : volume (Set.univ : Set (Fin n → ℝ)) ≠ 0 :=
    isOpen_univ.measure_ne_zero volume Set.univ_nonempty
  refine pos_iff_ne_zero.mpr fun h0 => huniv ?_
  apply measure_mono_null (t := {u : Fin n → ℝ | ¬ Function.Injective u} ∪ Function.support huaWeight)
  · intro u _
    by_cases h : Function.Injective u
    · exact Or.inr (hsub (by simpa using h))
    · exact Or.inl h
  · exact measure_union_null hnull h0

/-- Normalized Hua density. -/
noncomputable def huaDensity (u : Fin n → ℝ) : ℝ≥0 :=
  (huaWeight u / huaZ n).toNNReal

lemma coe_huaDensity (u : Fin n → ℝ) : (huaDensity u : ℝ) = huaWeight u / huaZ n :=
  Real.coe_toNNReal _ (div_nonneg (huaWeight_nonneg u) huaZ_pos.le)

lemma measurable_huaDensity : Measurable (fun u : Fin n → ℝ => huaDensity u) :=
  ((continuous_huaWeight.div_const _).measurable).real_toNNReal

/-- The Hua ensemble `P_{n,2}` as a measure on `ℝ^n`. -/
noncomputable def huaMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  volume.withDensity fun u => (huaDensity u : ℝ≥0∞)

instance : IsProbabilityMeasure (huaMeasure n) := by
  constructor
  rw [huaMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_coe_eq_integral]
  · simp only [coe_huaDensity]
    rw [integral_div, ← huaZ, div_self huaZ_pos.ne', ENNReal.ofReal_one]
  · simpa [coe_huaDensity] using integrable_huaWeight.div_const (huaZ n)

theorem huaMeasure_ae_injective : ∀ᵐ u ∂(huaMeasure n), Function.Injective u :=
  (withDensity_absolutelyContinuous _ _).ae_le ae_injective_volume

lemma integrable_hua_iff (f : (Fin n → ℝ) → ℝ) :
    Integrable f (huaMeasure n) ↔ Integrable (fun u => huaWeight u / huaZ n * f u) := by
  rw [huaMeasure, integrable_withDensity_iff_integrable_smul measurable_huaDensity]
  simp [NNReal.smul_def, coe_huaDensity]

theorem huaMeasure_int_sq_sum :
    Integrable (fun u : Fin n → ℝ => (∑ k, u k) ^ 2) (huaMeasure n) := by
  rw [integrable_hua_iff]
  have : Integrable (fun u : Fin n → ℝ => huaWeight u * (∑ k, u k) ^ 2) :=
    integrable_of_le_inv_bigG _ (by have := continuous_huaWeight (n := n); fun_prop)
      (Real.sqrt (((2 : ℝ) ^ n) ^ n) * (n * n)) fun u => by
        rw [abs_of_nonneg (mul_nonneg (huaWeight_nonneg u) (sq_nonneg _))]
        exact weight_mul_le u _ (sq_nonneg _) _ (by have := sq_sum_le u; linarith)
  exact (this.div_const (huaZ n)).congr (Filter.Eventually.of_forall fun u => by ring)

theorem huaMeasure_int_sum_sq :
    Integrable (fun u : Fin n → ℝ => ∑ k, u k ^ 2) (huaMeasure n) := by
  rw [integrable_hua_iff]
  have : Integrable (fun u : Fin n → ℝ => huaWeight u * ∑ k, u k ^ 2) :=
    integrable_of_le_inv_bigG _ (by have := continuous_huaWeight (n := n); fun_prop)
      (Real.sqrt (((2 : ℝ) ^ n) ^ n) * n) fun u => by
        rw [abs_of_nonneg (mul_nonneg (huaWeight_nonneg u)
          (sum_nonneg fun _ _ => sq_nonneg _))]
        exact weight_mul_le u _ (sum_nonneg fun _ _ => sq_nonneg _) _ (sum_sq_le u)
  exact (this.div_const (huaZ n)).congr (Filter.Eventually.of_forall fun u => by ring)

end Singh
