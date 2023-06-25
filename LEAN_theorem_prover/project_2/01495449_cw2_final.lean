import tactic
import data.real.basic -- imports the real numbers
import analysis.inner_product_space.euclidean_dist
import analysis.inner_product_space.pi_L2
import algebra.module.linear_map


variables {m n : ℕ} (Ω : set (fin n → ℝ)) (f : (fin n → ℝ) → (fin m → ℝ)) 
variables {Ω} (p : fin n → ℝ) {K K': (fin n → ℝ) →ₗ[ℝ] (fin m → ℝ)}

/-Given Ω ⊂ R^n is open, f : Ω → R^m, p ∈ Ω, and Λ. Defines what it means for Λ to be the derivative of f.-/
def deriv_exists (D : (fin n → ℝ) →ₗ[ℝ] (fin m → ℝ)) : Prop :=
∀ (ε : ℝ), 0 < ε → ∃ (R : ℝ), 0 < R ∧ (∀ (h : fin n → ℝ) , (0 < ‖h‖) ∧ (‖h‖ ≤ R) → ‖f (p + h) - f p - D h‖ / ‖h‖ < ε)

/-Defines a sequence whose limit is 0 and where each term of the sequence is non-zero.-/
def non_zero_convergent_zero (a : ℕ → ℝ) : Prop :=
(∀ j, a j ≠ 0) ∧ (∀ (ε : ℝ), 0 < ε → ∃ B : ℕ, ∀ j, B ≤ j → |a j| < ε)

/-This proves that for a (D) is equal to (A) from the proof description.-/
lemma h_limit_is_diff_linear_maps_norm (a : ℕ → ℝ) (h_non_zero_convergent_zero : non_zero_convergent_zero a) : 
∀ (e : fin n → ℝ), ‖e‖ = 1 → (∀ (ε : ℝ), 0 < ε → ∃ (N : ℕ), ∀ z , N ≤ z → 
|(‖- f (p + ((a z) • e)) + (f (p)) + K ((a z) • e) + (f (p + ((a z) • e))) - (f p) - K' ((a z) • e)‖ / ‖ (a z) • e ‖) 
- ‖K e - K' e‖ | < ε) :=
begin
  cases h_non_zero_convergent_zero with h_nonzero h_converge,
  intros e he,

  intros ε hε,
  specialize h_converge ε,

  specialize h_converge _,
  exact hε,
  cases h_converge with B hx,

  use B,
  intro z,
  intro h_b_geq_z,
  
  rw norm_smul, --rewrite things similar to ‖a z • e‖ in goal to ‖a z‖ * ‖e‖
  rw he,
  norm_num,

  rw add_assoc,
  rw add_comm,
  rw add_assoc,
  rw add_neg_cancel_left, -- cancels out (f (p + a z • e) + (-f (p + a z • e)))
  rw add_sub_cancel, -- cancel outs f(p) - f(p)

  rw ← smul_sub, --rewrites a z • ⇑K e - a z • ⇑K' e in goal to a z • (⇑K e - ⇑K')
  rw norm_smul, --rewrites ‖a z • (⇑K e - ⇑K')‖ in goal to ‖a z‖ * ‖⇑K e - ⇑K' e‖
  norm_num,
  rw mul_comm,
  simp [h_nonzero], --|a z| / |a z| cancels to 1 because we know from h_nonzero: ∀ j, a j ≠ 0 
  exact hε,
end

/-This proves that (**) ≤ (E) + (F).-/
lemma h_norm_frac_traingle_ineq (a : ℕ → ℝ) (h_non_zero_convergent_zero : non_zero_convergent_zero a)  :∀ (e : fin n → ℝ), ‖e‖ = 1 → 
(∀ (z : ℕ), (‖- f (p + ((a z) • e)) + (f (p)) + K ((a z) • e) + (f (p + ((a z) • e))) - (f p) - K' ((a z) • e)‖ / ‖ (a z) • e ‖) 
≤ (‖f (p + ((a z) • e)) - f p - K ((a z) • e)‖ / ‖((a z) • e)‖) + (‖f (p + ((a z) • e)) - f p - K' ((a z) • e)‖ / ‖((a z) • e)‖)):=
begin
  cases h_non_zero_convergent_zero with h_nonzero h_converge,
  intros e he,
  intro z,
  have h_factoring_out_minus : ‖ - (f (p + ((a z) • e)) - f p - K ((a z) • e))‖ = ‖- f (p + ((a z) • e)) + f (p) + K ((a z) • e)‖,
    {
      ring_nf, -- simplifies by applying the distributive property, collecting like terms, and simplifying constants
      },

  have h_norm_neg : ‖f (p + ((a z) • e)) - f p - K ((a z) • e)‖ = ‖- f (p + ((a z) • e)) + (f (p)) + K ((a z) • e)‖,
    { 
      rw ← h_factoring_out_minus,
      rw norm_neg,
      },
  
  rw h_norm_neg,
  set r := (-f (p + a z • e) + f p + K (a z • e)), --labelling multiple terms into one making it easier to apply library items 

  /-Putting brackets in the right places so I can later set specific collective terms as g.-/
  have h_put_bracket_on : ‖r + f (p + a z • e) - f p - K' (a z • e)‖ = ‖r + (f (p + a z • e) - f p - K' (a z • e))‖,
    { 
      rw [add_sub, sub_eq_add_neg],
      rw add_sub,
      refl,
      },

  rw h_put_bracket_on,
  set g := (f (p + a z • e) - f p - K' (a z • e)),
  
  rw norm_smul, --rewrites ‖a z • e‖ to ‖a z‖ * ‖e‖
  rw he,
  norm_num,

  rw div_add_div_same, --rewrites ‖r‖ / |a z| + ‖g‖ / |a z| to (‖r‖ + ‖g‖) / |a z|
  rw div_le_div_right, --since both sides of the inequality have the same positive denominator we can cancel them
  apply norm_add_le, --this closes one of the goals by applying the traingle inequality for norms
  rw abs_pos, -- 0 < |a z| is equivalent to a z ≠ 0
  apply h_nonzero,

end

/-Proves part 3 from the document explaining the proof-/
lemma h_using_derivs_sequence (a : ℕ → ℝ) (h_non_zero_convergent_zero : non_zero_convergent_zero a) (h_deriv_K : deriv_exists f p K) 
(h_deriv_K_dash : deriv_exists f p K') : 
∀ (e : fin n → ℝ), ‖e‖ = 1 → (∀ (ε_one ε_two : ℝ), 0 < ε_one ∧ 0 < ε_two → ∃ (N_final : ℕ), ∀ z , N_final ≤ z → 
‖f (p + ((a z) • e)) - f p - K ((a z) • e)‖ / ‖((a z) • e)‖ + ‖f (p + ((a z) • e)) - f p - K' ((a z) • e)‖ / ‖((a z) • e)‖ < ε_one + ε_two):=
begin
  cases h_non_zero_convergent_zero with h_nonzero h_converge,
  intros e he,
  intros ε_one ε_two h_ε_one_two,
  cases h_ε_one_two with h_ε_one h_ε_two,
  specialize h_deriv_K ε_one h_ε_one,
  specialize h_deriv_K_dash ε_two h_ε_two,

  cases h_deriv_K with R_ε_one h_right1,
  cases h_deriv_K_dash with R_ε_two h_right2,

  cases h_right1 with h_R_1_greater_zero h_deriv_K_leftover,
  cases h_right2 with h_R_2_greater_zero h_deriv_K_dash_leftover,

  set δ := min R_ε_one R_ε_two,
  specialize h_converge δ,

  have min_pos_greater_zero : 0 < δ,
    { 
      simp only [lt_min_iff], --rewrites that for δ to be greater than 0, we must have R_1 > 0 and R_2 > 0
      exact ⟨h_R_1_greater_zero, h_R_2_greater_zero⟩,
      },

  specialize h_converge _,
  exact min_pos_greater_zero,

  cases h_converge with B hB,
  use B,

  /-Show that a j • e meets the criteria to be set as h in the deriv_exists definition-/
  have subs_denom : ∀ (j : ℕ), B ≤ j → ‖a j • e‖ < R_ε_one ∧ ‖a j • e‖ < R_ε_two,
    { 
      intro j,
      specialize hB j,
      intro h_B_leq_j,
      specialize hB h_B_leq_j,
      rw norm_smul,
      rw he,
      norm_num,
      simp only [lt_min_iff] at hB, --just rewrites hB in terms of R_1 and R_2
      exact hB,
      },

  intro j,
  specialize subs_denom j,

  --setting h in both derivatives definition as a j • e
  specialize h_deriv_K_leftover (a j • e),  
  specialize h_deriv_K_dash_leftover (a j • e),

  intro h_B_leq_j,
  specialize subs_denom h_B_leq_j,

  specialize h_nonzero j,
  rw norm_smul at h_deriv_K_leftover h_deriv_K_dash_leftover subs_denom,
  rw he at h_deriv_K_leftover h_deriv_K_dash_leftover subs_denom,
  rw real.norm_eq_abs at h_deriv_K_leftover h_deriv_K_dash_leftover subs_denom, -- a j is a real sequence, ‖ a j ‖ is the same as | a j |
  rw mul_one at h_deriv_K_leftover h_deriv_K_dash_leftover subs_denom,

  specialize h_deriv_K_leftover _,
  split,
  {rw abs_pos,
  exact h_nonzero,},
  {
    exact le_of_lt subs_denom.1, --since |a j| < R_ε_one then |a j| ≤ R_ε_one
  },

  {specialize h_deriv_K_dash_leftover _,
  split,
  rw abs_pos,
  exact h_nonzero,
  exact le_of_lt subs_denom.2,

  rw norm_smul,
  rw he,
  rw mul_one,
  rw real.norm_eq_abs,

  apply add_lt_add h_deriv_K_leftover h_deriv_K_dash_leftover, -- we have E < ε_1 and F < ε_2, then E + F < ε_1 + ε_2
  },

end


theorem deriv_unique
  {a : ℕ → ℝ} {h_non_zero_convergent_zero : non_zero_convergent_zero a} {m n : ℕ}
  {f : (fin n → ℝ) → (fin m → ℝ)} (p : fin n → ℝ)
  {K K': (fin n → ℝ) →ₗ[ℝ] (fin m → ℝ)}
  (h_deriv_K : deriv_exists f p K)
  (h_deriv_K_dash : deriv_exists f p K'):
  K = K' := 
begin
  have h_limit_is_diff_linear_maps_norm_main := h_limit_is_diff_linear_maps_norm,
  swap, --Prof. Kevin Buzzard introduced me to the swap tactic
  exact m,
  swap,
  exact n,
  specialize h_limit_is_diff_linear_maps_norm_main f,
  specialize h_limit_is_diff_linear_maps_norm_main p a h_non_zero_convergent_zero,
  exact K,
  exact K',

  have h_norm_frac_traingle_ineq_main := h_norm_frac_traingle_ineq,
  swap,
  exact m,
  swap,
  exact n,
  specialize h_norm_frac_traingle_ineq_main f,
  specialize h_norm_frac_traingle_ineq_main p a h_non_zero_convergent_zero,
  exact K,
  exact K',

  have h_using_derivs_sequence_main := h_using_derivs_sequence,
  swap,
  exact m,
  swap,
  exact n,
  specialize h_using_derivs_sequence_main f,
  specialize h_using_derivs_sequence_main p a h_non_zero_convergent_zero h_deriv_K h_deriv_K_dash,

  have h_upper_bound_lim_zero : ∀ (e : fin n → ℝ), ‖e‖ = 1 → (∀ (ε : ℝ), 0 < ε → 
  (∃ (H : ℕ), ∀ (z : ℕ), H ≤ z → | ‖-f (p + a z • e) + f p + K (a z • e) + f (p + a z • e) - f p - K' (a z • e)‖ / ‖a z • e‖ | < ε)),
    { 
      intros e he,
      intros ε hε,
      specialize h_using_derivs_sequence_main e he,
      specialize h_using_derivs_sequence_main (ε/2) (ε/2), --sets both ε_1 and ε_2 to ε/2
      specialize h_using_derivs_sequence_main _,
      norm_num,
      exact half_pos hε, --we can set ε_1 and ε_2 to be ε/2 because its greater than 0

      cases h_using_derivs_sequence_main with N h_using_derivs_sequence_main2,
      use N,

      intros z h_N_leq_z,
      specialize h_using_derivs_sequence_main2 z _,
      exact h_N_leq_z,

      specialize h_norm_frac_traingle_ineq_main e he z,
      
      /-This essentially shows that |a/b| = |a|/|b|, which then equals a/b if a and b are positive -/
      have h_pos_norm_eq_abs : |‖-f (p + a z • e) + f p + K (a z • e) + f (p + a z • e) - f p - K' (a z • e)‖ / ‖a z • e‖| = ‖-f (p + a z • e) + f p + K (a z • e) + f (p + a z • e) - f p - K' (a z • e)‖ / ‖a z • e‖,
        {
          rw abs_div,
          rw abs_norm_eq_norm,
          rw abs_norm_eq_norm,
        },
      linarith,
      },
  
  /-Suppose a convergent sequence has two limits, this shows that the limits are equal-/
  have h_fix_ε_for_contra : ∀ (e : fin n → ℝ), ‖e‖ = 1 → (‖K e - K' e‖ = 0),
    { 
      intros e he,
      by_contra,

      have helpful_thing : 0 < ‖K e - K' e‖/10,
        { 
          apply div_pos,
          norm_num,
          simpa using h,
          norm_num,
        },

      specialize h_limit_is_diff_linear_maps_norm_main e he, 
      specialize h_limit_is_diff_linear_maps_norm_main (‖K e - K' e‖/10) _,
      exact helpful_thing,

      specialize h_upper_bound_lim_zero e he, 
      specialize h_upper_bound_lim_zero (‖K e - K' e‖/10) _,
      exact helpful_thing,

      cases h_upper_bound_lim_zero with H h_upper_bound_lim_zero2,
      cases h_limit_is_diff_linear_maps_norm_main with N h_limit_is_diff_linear_maps_norm_main2,

      set N_max := max H N,
      
      specialize h_limit_is_diff_linear_maps_norm_main2 (N_max),
      specialize h_upper_bound_lim_zero2 (N_max),

      have h_using_max_defn : (N ≤ N_max) ∧ (H ≤ N_max),
        {
          split,
          apply le_max_right,
          apply le_max_left,
        },
      
      specialize h_limit_is_diff_linear_maps_norm_main2 _,
      exact h_using_max_defn.1,

      specialize h_upper_bound_lim_zero2 _,
      exact h_using_max_defn.2,

      have h'' := abs_add (‖-f (p + a N_max • e) + f p + K (a N_max • e) + f (p + a N_max • e) - f p - K' (a N_max • e)‖ / ‖a N_max • e‖ - ‖K e - K' e‖) (0 - ‖-f (p + a N_max • e) + f p + K (a N_max • e) + f (p + a N_max • e) - f p - K' (a N_max • e)‖ / ‖a N_max • e‖),
      set L := ‖K e - K' e‖,
      set a_n := ‖-f (p + a N_max • e) + f p + K (a N_max • e) + f (p + a N_max • e) - f p - K' (a N_max • e)‖ / ‖a N_max • e‖,

      simp only [zero_sub, abs_neg] at h'',

      have h_sub_in_upper_bound : |a_n - L| + |a_n| < 2*(L / 10),
        {linarith,},

      rw [sub_eq_neg_add, neg_add_eq_sub] at h'',
      
      have h_trans : |a_n - L + -a_n| < 2 * (L / 10),
        {
          apply lt_of_le_of_lt h'',
          exact h_sub_in_upper_bound,
        },
      
      rw [sub_eq_neg_add, add_assoc, add_neg_self, add_zero] at h_trans,

      rw abs_neg at h_trans,

      have h_L_more_zero : 0 < L,
        {simpa using h,},
      
      rw abs_of_pos at h_trans,
      linarith,
      exact h_L_more_zero,
      },
  
  --Adam Topaz gave me 'linear_map.ext' command. I was unable to find this in documentation.
  apply linear_map.ext,
  intro v,

  by_cases hv: v=0,
  {
    rw hv,
    simp [linear_map.map_zero], --this library tells us that all linear maps at 0 equal 0.
  },

  {
    set v_hat := λ i, v i / ‖ v ‖,

    have h_decompose : v = ‖ v ‖ • v_hat,
      {
        ext,  --Prof. Buzzard introduced me to the ext tactic
        --uses the fact that each componnet of v is equal to corresponding v_hat compononent times ‖ v‖ 
        --and also that scalar • v_hat is the same as scalar * v_hat
        simp only [pi.smul_apply, algebra.id.smul_eq_mul],
        rw mul_comm,
        field_simp [hv],
      },

    rw h_decompose,
    simp only [linear_map.map_smulₛₗ, ring_hom.id_apply],

    have h_v_hat_norm_1 : ‖ v_hat ‖ = 1,
      {
        have hsj : ‖v‖⁻¹ • v = v_hat,
          {
            ext i,
            simp only [pi.smul_apply, algebra.id.smul_eq_mul],
            field_simp [hv, mul_comm],
            },

        rw ← hsj,
        rw norm_smul,
        simp only [norm_inv, norm_norm],
        rw inv_mul_cancel,
        -- ne.def: a ≠ b = ¬a = b
        simp only [ne.def, norm_eq_zero],
        exact hv,
      },

    specialize h_fix_ε_for_contra v_hat h_v_hat_norm_1,
    rw [norm_eq_zero, sub_eq_zero] at h_fix_ε_for_contra,
    rw h_fix_ε_for_contra,
    },
  
end

--#lint