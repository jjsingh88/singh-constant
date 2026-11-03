module

public import Singh.Hua
public import Singh.Algebra
public import Singh.Defs

@[expose] public section

/-!
Loop equations for the Hua ensemble via integration by parts.
-/

open MeasureTheory Finset Filter
open scoped ENNReal NNReal

namespace Singh

variable {n : ℕ}


lemma sum_offdiag_eq_two_pairs (g : Fin n → Fin n → ℝ) (hg : ∀ a b, g a b = g b a) :
    ∑ a, ∑ b ∈ univ.erase a, g a b = 2 * ∑ p ∈ pairs n, g p.1 p.2 := by
  have h1 : ∀ a, ∑ b ∈ univ.erase a, g a b = ∑ b, if a ≠ b then g a b else 0 := by
    intro a; rw [← sum_filter, filter_ne]
  simp only [h1]
  rw [← Fintype.sum_prod_type' (fun a b => if a ≠ b then g a b else 0)]
  have h2 : ∀ p : Fin n × Fin n, (if p.1 ≠ p.2 then g p.1 p.2 else 0)
      = (if p.1 < p.2 then g p.1 p.2 else 0) + (if p.2 < p.1 then g p.1 p.2 else 0) := by
    intro p
    by_cases a : p.1 < p.2
    · simp [a, ne_of_lt a, not_lt_of_gt a]
    · by_cases b : p.2 < p.1
      · simp [a, b, ne_of_gt b]
      · have : p.1 = p.2 := le_antisymm (not_lt.mp b) (not_lt.mp a)
        simp [this]
  simp only [h2, sum_add_distrib]
  have h3 : ∑ p : Fin n × Fin n, (if p.2 < p.1 then g p.1 p.2 else 0)
      = ∑ p : Fin n × Fin n, (if p.1 < p.2 then g p.1 p.2 else 0) :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun p => by
      rcases p with ⟨a, b⟩; by_cases h : b < a <;> simp [h, hg a b]
  rw [h3, pairs, sum_filter]; ring

lemma prod_offdiag_eq_sq_pairs (g : Fin n → Fin n → ℝ) (hg : ∀ a b, g a b = g b a) :
    ∏ a, ∏ b ∈ univ.erase a, g a b = (∏ p ∈ pairs n, g p.1 p.2) ^ 2 := by
  have h1 : ∀ a, ∏ b ∈ univ.erase a, g a b = ∏ b, if a ≠ b then g a b else 1 := by
    intro a; rw [← prod_filter, filter_ne]
  simp only [h1]
  rw [← Fintype.prod_prod_type' (fun a b => if a ≠ b then g a b else 1)]
  have h2 : ∀ p : Fin n × Fin n, (if p.1 ≠ p.2 then g p.1 p.2 else 1)
      = (if p.1 < p.2 then g p.1 p.2 else 1) * (if p.2 < p.1 then g p.1 p.2 else 1) := by
    intro p
    by_cases a : p.1 < p.2
    · simp [a, ne_of_lt a, not_lt_of_gt a]
    · by_cases b : p.2 < p.1
      · simp [a, b, ne_of_gt b]
      · have : p.1 = p.2 := le_antisymm (not_lt.mp b) (not_lt.mp a)
        simp [this]
  simp only [h2, prod_mul_distrib]
  have h3 : ∏ p : Fin n × Fin n, (if p.2 < p.1 then g p.1 p.2 else 1)
      = ∏ p : Fin n × Fin n, (if p.1 < p.2 then g p.1 p.2 else 1) :=
    Fintype.prod_equiv (Equiv.prodComm _ _) _ _ fun p => by
      rcases p with ⟨a, b⟩; by_cases h : b < a <;> simp [h, hg a b]
  rw [h3, pairs, prod_filter]; ring

/-- Squared Vandermonde as a polynomial. -/
noncomputable def Wp (u : Fin n → ℝ) : ℝ := ∏ p ∈ pairs n, (u p.1 - u p.2) ^ 2

lemma vdm_eq_Wp (u : Fin n → ℝ) : vdm u = Wp u := by
  unfold vdm Wp
  rw [prod_offdiag_eq_sq_pairs (fun a b => |u a - u b|) (fun a b => abs_sub_comm _ _),
    ← prod_pow]
  exact prod_congr rfl fun p _ => sq_abs _


/-- Coordinate of the direction `e_k`. -/
def dlt (k a : Fin n) : ℝ := if a = k then 1 else 0

lemma line_apply (u : Fin n → ℝ) (k a : Fin n) (t : ℝ) :
    (u + t • (Pi.single k (1 : ℝ) : Fin n → ℝ)) a = u a + t * dlt k a := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, dlt]

/-- One-variable factor `(1+x^2)^{-(n+2)}`. -/
noncomputable def qf (n : ℕ) (x : ℝ) : ℝ := ((1 + x ^ 2) ^ (n + 2))⁻¹

/-- `G^{-(n+2)}` as a product. -/
noncomputable def Hn (u : Fin n → ℝ) : ℝ := ∏ a, qf n (u a)

lemma Hn_eq (u : Fin n → ℝ) : Hn u = (bigG u ^ (n + 2))⁻¹ := by
  unfold Hn qf bigG; rw [prod_inv_distrib, prod_pow]

lemma Hn_pos (u : Fin n → ℝ) : 0 < Hn u := by
  rw [Hn_eq]; have := bigG_pos u; positivity

lemma huaWeight_eq (u : Fin n → ℝ) : huaWeight u = Wp u * Hn u := by
  rw [huaWeight, vdm_eq_Wp, Hn_eq, div_eq_mul_inv]

/-- Derivative of `Wp` along `e_k`. -/
noncomputable def dWp (k : Fin n) (u : Fin n → ℝ) : ℝ :=
  ∑ p ∈ pairs n, (∏ p' ∈ (pairs n).erase p, (u p'.1 - u p'.2) ^ 2)
    * (2 * (u p.1 - u p.2) * (dlt k p.1 - dlt k p.2))

/-- Derivative of `Hn` along `e_k`. -/
noncomputable def dHn (k : Fin n) (u : Fin n → ℝ) : ℝ :=
  -(2 * ((n : ℝ) + 2) * u k) / (1 + u k ^ 2) * Hn u

lemma hasLineDerivAt_Wp (k : Fin n) (u : Fin n → ℝ) :
    HasLineDerivAt ℝ Wp (dWp k u) u (Pi.single k 1) := by
  unfold HasLineDerivAt
  have e : (fun t : ℝ => Wp (u + t • Pi.single k (1 : ℝ))) = fun t =>
      ∏ p ∈ pairs n, ((u p.1 - u p.2) + t * (dlt k p.1 - dlt k p.2)) ^ 2 := by
    funext t; unfold Wp; refine prod_congr rfl fun p _ => ?_
    rw [line_apply, line_apply]; ring
  rw [e]
  have h : ∀ p ∈ pairs n, HasDerivAt (fun t : ℝ => ((u p.1 - u p.2) + t * (dlt k p.1 - dlt k p.2)) ^ 2)
      (2 * (u p.1 - u p.2) * (dlt k p.1 - dlt k p.2)) 0 := by
    intro p _
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (dlt k p.1 - dlt k p.2)).const_add
      (u p.1 - u p.2)).pow 2
    convert this using 1
    · funext t; simp only [Pi.pow_apply, id]
    · simp
  convert HasDerivAt.fun_finsetProd h using 1
  unfold dWp; refine sum_congr rfl fun p _ => ?_
  simp [smul_eq_mul]

lemma hasDerivAt_qf (x : ℝ) :
    HasDerivAt (qf n) (-(2 * ((n : ℝ) + 2) * x) / (1 + x ^ 2) * qf n x) x := by
  have hc : HasDerivAt (fun y : ℝ => (1 + y ^ 2) ^ (n + 2))
      (((n + 2 : ℕ) : ℝ) * (1 + x ^ 2) ^ (n + 2 - 1) * (2 * x)) x := by
    have := ((hasDerivAt_pow 2 x).const_add 1).pow (n + 2)
    convert this using 1; norm_num
  have hx : (1 + x ^ 2) ^ (n + 2) ≠ 0 := by positivity
  convert hc.inv hx using 1
  have h1 : (0 : ℝ) < 1 + x ^ 2 := by positivity
  · rfl
  unfold qf
  rw [show n + 2 - 1 = n + 1 from rfl]
  field_simp
  push_cast
  ring

lemma hasLineDerivAt_Hn (k : Fin n) (u : Fin n → ℝ) :
    HasLineDerivAt ℝ Hn (dHn k u) u (Pi.single k 1) := by
  unfold HasLineDerivAt
  have e : (fun t : ℝ => Hn (u + t • Pi.single k (1 : ℝ))) = fun t =>
      qf n (u k + t) * ∏ a ∈ univ.erase k, qf n (u a) := by
    funext t; unfold Hn
    rw [← mul_prod_erase univ (fun a => qf n ((u + t • (Pi.single k (1 : ℝ) : Fin n → ℝ)) a))
      (mem_univ k)]
    simp only [line_apply, dlt, ite_true, mul_one]
    congr 1
    refine prod_congr rfl fun a ha => ?_
    simp [ne_of_mem_erase ha]
  rw [e]
  have h0 : HasDerivAt (fun t : ℝ => u k + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (u k)
  have hq : HasDerivAt (qf n) (-(2 * ((n : ℝ) + 2) * u k) / (1 + u k ^ 2) * qf n (u k))
      (u k + 0) := by rw [add_zero]; exact hasDerivAt_qf (u k)
  have := (hq.comp (0 : ℝ) h0).mul_const (∏ a ∈ univ.erase k, qf n (u a))
  convert this using 1
  · funext t; simp
  · unfold dHn Hn; rw [← mul_prod_erase _ _ (mem_univ k)]; simp; ring


lemma dWp_eq (k : Fin n) (u : Fin n → ℝ) (hu : Function.Injective u) :
    dWp k u = Wp u * ∑ j ∈ univ.erase k, 2 / (u k - u j) := by
  have hne : ∀ p ∈ pairs n, u p.1 - u p.2 ≠ 0 := fun p hp =>
    sub_ne_zero.mpr fun h => (ne_of_lt (mem_filter.mp hp).2) (hu h)
  have e1 : ∀ p ∈ pairs n, ∏ p' ∈ (pairs n).erase p, (u p'.1 - u p'.2) ^ 2
      = Wp u / (u p.1 - u p.2) ^ 2 := fun p hp => by
    rw [eq_div_iff (pow_ne_zero 2 (hne p hp)), Wp, ← mul_prod_erase _ _ hp, mul_comm]
  have e2 : dWp k u
      = Wp u * ∑ p ∈ pairs n, (2 * dlt k p.1 - 2 * dlt k p.2) / (u p.1 - u p.2) := by
    unfold dWp; rw [mul_sum]; refine sum_congr rfl fun p hp => ?_
    rw [e1 p hp]; have := hne p hp; field_simp
  rw [e2]; congr 1
  have h3 := sum_offdiag_eq_two_pairs (fun a b => (2 * dlt k a - 2 * dlt k b) / (u a - u b))
    (fun a b => by
      rw [show 2 * dlt k b - 2 * dlt k a = -(2 * dlt k a - 2 * dlt k b) by ring,
        show u b - u a = -(u a - u b) by ring, neg_div_neg_eq])
  have h4 := pair_sum_symm u (fun a => 2 * dlt k a)
  have h5 : ∑ a, ∑ b ∈ univ.erase a, 2 * dlt k a / (u a - u b)
      = ∑ j ∈ univ.erase k, 2 / (u k - u j) := by
    simp only [dlt, mul_ite, mul_one, mul_zero, ite_div, zero_div]
    rw [Fintype.sum_eq_single k]
    · simp
    · intro x hx; simp [hx]
  linarith

lemma pairs_prod_g (u : Fin n → ℝ) :
    ∏ p ∈ pairs n, ((1 + u p.1 ^ 2) * (1 + u p.2 ^ 2)) = bigG u ^ n / bigG u := by
  have hg : ∀ k, 0 < 1 + u k ^ 2 := fun k => by positivity
  have hG := bigG_pos u
  have hsq : (∏ p ∈ pairs n, ((1 + u p.1 ^ 2) * (1 + u p.2 ^ 2))) ^ 2
      = (bigG u ^ n / bigG u) ^ 2 := by
    rw [← prod_offdiag_eq_sq_pairs (fun a b => (1 + u a ^ 2) * (1 + u b ^ 2))
      (fun a b => mul_comm _ _)]
    simp only [prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ _), card_univ,
      Fintype.card_fin, prod_pow]
    rw [prod_erase_prod (fun k => 1 + u k ^ 2) hg]
    change bigG u ^ (n - 1) * (bigG u ^ n / bigG u) = _
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [bigG]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
  exact (pow_left_inj₀ (prod_nonneg fun p _ => by positivity) (by positivity)
    two_ne_zero).mp hsq

lemma factor_le (a b : ℝ) : (a - b) ^ 2 ≤ 6 * ((1 + a ^ 2) * (1 + b ^ 2)) := by
  have := pair_bound a b
  have : 0 ≤ (1 + a ^ 2) * (1 + b ^ 2) := by positivity
  linarith

lemma abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]

lemma dfactor_le (a b d : ℝ) (hd : |d| ≤ 1) :
    |2 * (a - b) * d| ≤ 6 * ((1 + a ^ 2) * (1 + b ^ 2)) := by
  have h1 : 2 * |a - b| ≤ 1 + (a - b) ^ 2 := by
    nlinarith [sq_nonneg (|a - b| - 1), sq_abs (a - b)]
  have hg : 1 ≤ (1 + a ^ 2) * (1 + b ^ 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_g a) (one_le_g b)
  rw [abs_mul, abs_mul, abs_two]
  nlinarith [abs_nonneg (a - b), abs_nonneg d, pair_bound a b,
    mul_le_mul_of_nonneg_left hd (abs_nonneg (a - b))]

lemma dlt_sub_le (k a b : Fin n) : |dlt k a - dlt k b| ≤ 1 := by
  unfold dlt; split_ifs <;> norm_num

/-- `∏_{a<b} 6 (1+u_a^2)(1+u_b^2) = 6^{#pairs} G^{n-1}`. -/
lemma Kp_eq (u : Fin n → ℝ) :
    ∏ p ∈ pairs n, (6 * ((1 + u p.1 ^ 2) * (1 + u p.2 ^ 2)))
      = 6 ^ (pairs n).card * (bigG u ^ n / bigG u) := by
  rw [prod_mul_distrib, prod_const, pairs_prod_g]

lemma Wp_nonneg (u : Fin n → ℝ) : 0 ≤ Wp u := prod_nonneg fun _ _ => sq_nonneg _

lemma Wp_le (u : Fin n → ℝ) :
    Wp u ≤ 6 ^ (pairs n).card * (bigG u ^ n / bigG u) := by
  rw [← Kp_eq]
  exact prod_le_prod₀ (fun _ _ => sq_nonneg _) fun p _ => factor_le _ _

lemma abs_dWp_le (k : Fin n) (u : Fin n → ℝ) :
    |dWp k u| ≤ (pairs n).card * (6 ^ (pairs n).card * (bigG u ^ n / bigG u)) := by
  rw [← Kp_eq]
  unfold dWp
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum fun p hp => ?_
  rw [abs_mul, abs_of_nonneg (prod_nonneg fun _ _ => sq_nonneg _), ← prod_erase_mul _ _ hp]
  exact mul_le_mul
    (prod_le_prod₀ (fun _ _ => sq_nonneg _) fun q _ => factor_le _ _)
    (dfactor_le _ _ _ (dlt_sub_le _ _ _)) (abs_nonneg _)
    (prod_nonneg fun _ _ => by positivity)

lemma abs_dHn_le (k : Fin n) (u : Fin n → ℝ) : |dHn k u| ≤ ((n : ℝ) + 2) * Hn u := by
  have hH := Hn_pos u
  have hg : 0 < 1 + u k ^ 2 := by positivity
  unfold dHn
  rw [abs_mul, abs_of_pos hH]
  refine mul_le_mul_of_nonneg_right ?_ hH.le
  rw [abs_div, abs_neg, abs_of_pos hg, div_le_iff₀ hg, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 2))]
  have h1 : 2 * |u k| ≤ 1 + u k ^ 2 := by
    nlinarith [sq_nonneg (|u k| - 1), sq_abs (u k)]
  have hn : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  nlinarith

lemma G_scale (u : Fin n → ℝ) : bigG u ^ 2 * (bigG u ^ n / bigG u) * Hn u = (bigG u)⁻¹ := by
  rw [Hn_eq]; have := bigG_pos u; field_simp; ring

lemma measurable_Wp : Measurable (fun u : Fin n → ℝ => Wp u) := by unfold Wp; fun_prop
lemma measurable_dWp (k : Fin n) : Measurable (fun u : Fin n → ℝ => dWp k u) := by
  unfold dWp; fun_prop
lemma measurable_Hn : Measurable (fun u : Fin n → ℝ => Hn u) := by unfold Hn qf; fun_prop
lemma measurable_dHn (k : Fin n) : Measurable (fun u : Fin n → ℝ => dHn k u) := by
  unfold dHn; have := measurable_Hn (n := n); fun_prop

lemma integrable_of_le_inv_bigG' (f : (Fin n → ℝ) → ℝ) (hf : Measurable f) (C : ℝ)
    (hb : ∀ u, |f u| ≤ C * (bigG u)⁻¹) : Integrable f :=
  Integrable.mono' (integrable_inv_bigG.const_mul C) hf.aestronglyMeasurable
    (Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hb u)

/-- A line derivative of an integrable function with integrable derivative integrates to zero. -/
lemma integral_lineDeriv_eq_zero {f f' : (Fin n → ℝ) → ℝ} (v : Fin n → ℝ)
    (hf : ∀ x, HasLineDerivAt ℝ f (f' x) x v) (hi : Integrable f) (hi' : Integrable f') :
    ∫ x, f' x = 0 := by
  have := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := volume) (B := ContinuousLinearMap.mul ℝ ℝ) (f := f) (f' := f')
    (g := fun _ => (1 : ℝ)) (g' := fun _ => (0 : ℝ)) (v := v)
    (by simpa using hi') (by simp) (by simpa using hi) (fun x _ => hf x)
    (fun x _ => hasDerivAt_const _ _)
  simp at this
  linarith

/-- The divergence term `∂_k (A · Wp · Hn)`. -/
noncomputable def loopD (k : Fin n) (A A' : (Fin n → ℝ) → ℝ) (u : Fin n → ℝ) : ℝ :=
  A' u * Wp u * Hn u + A u * dWp k u * Hn u + A u * Wp u * dHn k u

section generic

variable (k : Fin n) (A A' : (Fin n → ℝ) → ℝ) (a : ℝ)

lemma loopD_bound (ha : 0 ≤ a) (hAb : ∀ u, |A u| ≤ a * bigG u ^ 2)
    (hA'b : ∀ u, |A' u| ≤ a * bigG u ^ 2) (u : Fin n → ℝ) :
    |loopD k A A' u| ≤ a * 6 ^ (pairs n).card * (1 + (pairs n).card + ((n : ℝ) + 2))
      * (bigG u)⁻¹ := by
  have hW0 := Wp_nonneg u
  have hW := Wp_le u
  have hdW := abs_dWp_le k u
  have hdH := abs_dHn_le k u
  have hH := Hn_pos u
  have hG := bigG_pos u
  set K := 6 ^ (pairs n).card * (bigG u ^ n / bigG u) with hK
  have hK0 : 0 ≤ K := by positivity
  have hc : (0 : ℝ) ≤ (pairs n).card := by positivity
  have t1 : |A' u * Wp u * Hn u| ≤ a * bigG u ^ 2 * K * Hn u := by
    rw [abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_pos hH]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hA'b u) hW hW0 (by positivity)) hH.le
  have t2 : |A u * dWp k u * Hn u| ≤ a * bigG u ^ 2 * ((pairs n).card * K) * Hn u := by
    rw [abs_mul, abs_mul, abs_of_pos hH]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hAb u) hdW (abs_nonneg _) (by positivity)) hH.le
  have t3 : |A u * Wp u * dHn k u| ≤ a * bigG u ^ 2 * K * (((n : ℝ) + 2) * Hn u) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hW0]
    exact mul_le_mul (mul_le_mul (hAb u) hW hW0 (by positivity)) hdH (abs_nonneg _)
      (by positivity)
  have hs := G_scale u
  calc |loopD k A A' u|
      ≤ |A' u * Wp u * Hn u| + |A u * dWp k u * Hn u| + |A u * Wp u * dHn k u| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
    _ ≤ a * bigG u ^ 2 * K * Hn u + a * bigG u ^ 2 * ((pairs n).card * K) * Hn u
        + a * bigG u ^ 2 * K * (((n : ℝ) + 2) * Hn u) := by linarith
    _ = a * 6 ^ (pairs n).card * (1 + (pairs n).card + ((n : ℝ) + 2))
        * (bigG u ^ 2 * (bigG u ^ n / bigG u) * Hn u) := by rw [hK]; ring
    _ = _ := by rw [hs]

lemma loopF_bound (ha : 0 ≤ a) (hAb : ∀ u, |A u| ≤ a * bigG u ^ 2) (u : Fin n → ℝ) :
    |A u * Wp u * Hn u| ≤ a * 6 ^ (pairs n).card * (bigG u)⁻¹ := by
  have hW0 := Wp_nonneg u
  have hH := Hn_pos u
  have hG := bigG_pos u
  rw [abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_pos hH, ← G_scale u]
  calc |A u| * Wp u * Hn u ≤ a * bigG u ^ 2 * (6 ^ (pairs n).card * (bigG u ^ n / bigG u))
        * Hn u :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hAb u) (Wp_le u) hW0 (by positivity)) hH.le
    _ = _ := by ring

variable (hA : ∀ u, HasLineDerivAt ℝ A (A' u) u (Pi.single k 1))
  (hAm : Measurable A) (hA'm : Measurable A') (ha : 0 ≤ a)
  (hAb : ∀ u, |A u| ≤ a * bigG u ^ 2) (hA'b : ∀ u, |A' u| ≤ a * bigG u ^ 2)
include hA'm hAm ha hAb hA'b

lemma integrable_loopD : Integrable (fun u => loopD k A A' u) :=
  integrable_of_le_inv_bigG' _ (by
    unfold loopD
    have := measurable_Wp (n := n); have := measurable_Hn (n := n)
    have := measurable_dWp k; have := measurable_dHn k
    fun_prop) _ (loopD_bound k A A' a ha hAb hA'b)

include hA in
lemma integral_loopD : ∫ u, loopD k A A' u = 0 := by
  refine integral_lineDeriv_eq_zero (f := fun u => A u * Wp u * Hn u) (Pi.single k 1)
    (fun u => ?_) ?_ (integrable_loopD k A A' a hAm hA'm ha hAb hA'b)
  · have := ((hA u).mul (hasLineDerivAt_Wp k u)).mul (hasLineDerivAt_Hn k u)
    simp only [zero_smul, add_zero] at this
    unfold HasLineDerivAt
    convert this using 1
    unfold loopD; simp only [Pi.mul_apply, zero_smul, add_zero]; ring
  · exact integrable_of_le_inv_bigG' _ (by
      have := measurable_Wp (n := n); have := measurable_Hn (n := n); fun_prop) _
      (loopF_bound A a ha hAb)

end generic


lemma abs_sum_le_bigG (u : Fin n → ℝ) : |∑ j, u j| ≤ n * bigG u := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |u j| ≤ ∑ _j : Fin n, bigG u :=
        sum_le_sum fun j _ => (abs_le_one_add_sq _).trans (g_le_bigG u j)
    _ = n * bigG u := by simp

lemma bigG_le_sq (u : Fin n → ℝ) : bigG u ≤ bigG u ^ 2 := by
  have := one_le_bigG u; nlinarith

lemma sum_line (u : Fin n → ℝ) (k : Fin n) (t : ℝ) :
    ∑ j, (u + t • (Pi.single k (1 : ℝ) : Fin n → ℝ)) j = ∑ j, u j + t := by
  simp only [line_apply, sum_add_distrib, ← mul_sum]; simp [dlt]

/-- Field for loop equation (a). -/
noncomputable def fieldA (k : Fin n) (u : Fin n → ℝ) : ℝ := (1 + u k ^ 2) * ∑ j, u j
noncomputable def fieldA' (k : Fin n) (u : Fin n → ℝ) : ℝ :=
  2 * u k * ∑ j, u j + (1 + u k ^ 2)

/-- Field for loop equation (b). -/
noncomputable def fieldB (k : Fin n) (u : Fin n → ℝ) : ℝ := (1 + u k ^ 2) * u k
noncomputable def fieldB' (k : Fin n) (u : Fin n → ℝ) : ℝ := 1 + 3 * u k ^ 2

lemma hasLineDerivAt_fieldA (k : Fin n) (u : Fin n → ℝ) :
    HasLineDerivAt ℝ (fieldA k) (fieldA' k u) u (Pi.single k 1) := by
  unfold HasLineDerivAt
  have e : (fun t : ℝ => fieldA k (u + t • Pi.single k (1 : ℝ))) =
      fun t => (1 + (u k + t) * (u k + t)) * (∑ j, u j + t) := by
    funext t; unfold fieldA; rw [sum_line, line_apply, dlt, if_pos rfl]; ring
  rw [e]
  have h0 := (hasDerivAt_id (0 : ℝ)).const_add (u k)
  have h1 := (hasDerivAt_id (0 : ℝ)).const_add (∑ j, u j)
  have := ((h0.mul h0).const_add 1).mul h1
  convert this using 1
  · funext t; simp only [Pi.mul_apply, id]
  · unfold fieldA'; simp; ring

lemma hasLineDerivAt_fieldB (k : Fin n) (u : Fin n → ℝ) :
    HasLineDerivAt ℝ (fieldB k) (fieldB' k u) u (Pi.single k 1) := by
  unfold HasLineDerivAt
  have e : (fun t : ℝ => fieldB k (u + t • Pi.single k (1 : ℝ))) =
      fun t => (1 + (u k + t) * (u k + t)) * (u k + t) := by
    funext t; unfold fieldB; rw [line_apply, dlt, if_pos rfl]; ring
  rw [e]
  have h0 := (hasDerivAt_id (0 : ℝ)).const_add (u k)
  have := ((h0.mul h0).const_add 1).mul h0
  convert this using 1
  · funext t; simp only [Pi.mul_apply, id]
  · unfold fieldB'; simp; ring

lemma fieldA_bound (k : Fin n) (u : Fin n → ℝ) :
    |fieldA k u| ≤ (2 * n + 1) * bigG u ^ 2 := by
  have hg := g_le_bigG u k
  have hs := abs_sum_le_bigG u
  have hG := one_le_bigG u
  unfold fieldA
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + u k ^ 2)]
  calc (1 + u k ^ 2) * |∑ j, u j| ≤ bigG u * (n * bigG u) :=
        mul_le_mul hg hs (abs_nonneg _) (by positivity)
    _ ≤ (2 * n + 1) * bigG u ^ 2 := by nlinarith [sq_nonneg (bigG u)]

lemma fieldA'_bound (k : Fin n) (u : Fin n → ℝ) :
    |fieldA' k u| ≤ (2 * n + 1) * bigG u ^ 2 := by
  have hg := g_le_bigG u k
  have hs := abs_sum_le_bigG u
  have hG := one_le_bigG u
  have hu := (abs_le_one_add_sq (u k)).trans hg
  have hsq := bigG_le_sq u
  unfold fieldA'
  calc |2 * u k * ∑ j, u j + (1 + u k ^ 2)|
      ≤ 2 * |u k| * |∑ j, u j| + (1 + u k ^ 2) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_two, abs_of_pos (by positivity : (0 : ℝ) < 1 + u k ^ 2)]
    _ ≤ 2 * bigG u * (n * bigG u) + bigG u := by
        have := mul_le_mul hu hs (abs_nonneg _) (by positivity)
        linarith
    _ ≤ (2 * n + 1) * bigG u ^ 2 := by nlinarith

lemma fieldB_bound (k : Fin n) (u : Fin n → ℝ) : |fieldB k u| ≤ 3 * bigG u ^ 2 := by
  have hg := g_le_bigG u k
  have hu := (abs_le_one_add_sq (u k)).trans hg
  have hG := one_le_bigG u
  unfold fieldB
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + u k ^ 2)]
  have := mul_le_mul hg hu (abs_nonneg _) (by positivity)
  nlinarith

lemma fieldB'_bound (k : Fin n) (u : Fin n → ℝ) : |fieldB' k u| ≤ 3 * bigG u ^ 2 := by
  have hg := g_le_bigG u k
  have hsq := bigG_le_sq u
  unfold fieldB'
  rw [abs_of_pos (by positivity)]
  nlinarith [sq_nonneg (u k)]

lemma pointwise_A (k : Fin n) (u : Fin n → ℝ) (hu : Function.Injective u) :
    huaWeight u * (2 * u k * (∑ j, u j) + (1 + u k ^ 2)
        + (1 + u k ^ 2) * (∑ j, u j) * logDeriv 2 u k)
      = loopD k (fieldA k) (fieldA' k) u := by
  rw [huaWeight_eq, loopD, dWp_eq k u hu, dHn, logDeriv, fieldA, fieldA']; ring

lemma pointwise_B (k : Fin n) (u : Fin n → ℝ) (hu : Function.Injective u) :
    huaWeight u * ((1 + 3 * u k ^ 2) + (1 + u k ^ 2) * u k * logDeriv 2 u k)
      = loopD k (fieldB k) (fieldB' k) u := by
  rw [huaWeight_eq, loopD, dWp_eq k u hu, dHn, logDeriv, fieldB, fieldB']; ring

lemma integral_hua_eq (f : (Fin n → ℝ) → ℝ) :
    ∫ u, f u ∂(huaMeasure n) = (huaZ n)⁻¹ * ∫ u, huaWeight u * f u := by
  rw [huaMeasure, integral_withDensity_eq_integral_smul measurable_huaDensity,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [NNReal.smul_def, coe_huaDensity, smul_eq_mul]; ring

/-- Loop equation (a) for the Hua ensemble with `h = 2`. -/
theorem huaMeasure_loopA : ∫ u, divA 2 u ∂(huaMeasure n) = 0 := by
  rw [integral_hua_eq]
  have e : (fun u : Fin n → ℝ => huaWeight u * divA 2 u) =ᵐ[volume]
      fun u => ∑ k, loopD k (fieldA k) (fieldA' k) u := by
    filter_upwards [ae_injective_volume] with u hu
    rw [divA, mul_sum]; exact sum_congr rfl fun k _ => pointwise_A k u hu
  have hm : ∀ k : Fin n, Measurable (fieldA k) := fun k => by unfold fieldA; fun_prop
  have hm' : ∀ k : Fin n, Measurable (fieldA' k) := fun k => by unfold fieldA'; fun_prop
  have ha : (0 : ℝ) ≤ 2 * n + 1 := by positivity
  rw [integral_congr_ae e, integral_finsetSum _ fun k _ =>
    integrable_loopD k _ _ _ (hm k) (hm' k) ha (fieldA_bound k) (fieldA'_bound k)]
  rw [sum_eq_zero fun k _ => integral_loopD k _ _ _ (hasLineDerivAt_fieldA k) (hm k) (hm' k)
    ha (fieldA_bound k) (fieldA'_bound k), mul_zero]

/-- Loop equation (b) for the Hua ensemble with `h = 2`. -/
theorem huaMeasure_loopB : ∫ u, divB 2 u ∂(huaMeasure n) = 0 := by
  rw [integral_hua_eq]
  have e : (fun u : Fin n → ℝ => huaWeight u * divB 2 u) =ᵐ[volume]
      fun u => ∑ k, loopD k (fieldB k) (fieldB' k) u := by
    filter_upwards [ae_injective_volume] with u hu
    rw [divB, mul_sum]; exact sum_congr rfl fun k _ => pointwise_B k u hu
  have hm : ∀ k : Fin n, Measurable (fieldB k) := fun k => by unfold fieldB; fun_prop
  have hm' : ∀ k : Fin n, Measurable (fieldB' k) := fun k => by unfold fieldB'; fun_prop
  have ha : (0 : ℝ) ≤ 3 := by norm_num
  rw [integral_congr_ae e, integral_finsetSum _ fun k _ =>
    integrable_loopD k _ _ _ (hm k) (hm' k) ha (fieldB_bound k) (fieldB'_bound k)]
  rw [sum_eq_zero fun k _ => integral_loopD k _ _ _ (hasLineDerivAt_fieldB k) (hm k) (hm' k)
    ha (fieldB_bound k) (fieldB'_bound k), mul_zero]

end Singh
