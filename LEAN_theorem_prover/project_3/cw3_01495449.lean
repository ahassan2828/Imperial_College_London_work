import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import analysis.calculus.cont_diff
import analysis.calculus.iterated_deriv
import analysis.calculus.taylor

open set

-- Declare a type E with some properties
variables (E : Type*) [normed_add_comm_group E] [normed_space ℝ E]

/--  Given a set `u` and a point `x_star` in `u`, and a set `hv_subset`,
which is a superset of `u`, if `u` is open, then `hv_subset` is in the neighborhood of `x_star`. -/
lemma hv_subset_nbhd_x_star {u hv_subset: set E} {x_star: E} (h_x_star: x_star ∈ u)
(hv_subset_is_superset_u: hv_subset ∈ filter.principal u) (h_open: is_open u) : hv_subset ∈ nhds x_star:=
begin
rw mem_nhds_iff,
use u,
split,
{
  rw filter.mem_principal at hv_subset_is_superset_u,
  exact hv_subset_is_superset_u,
},
{exact ⟨h_open, h_x_star⟩,},
end

/--Given a point `x_star`, a vector `d`, and two positive real numbers `α` and `r`,
  if 0 < α < r / ‖d‖, then x_star + α • d is in the open ball centered at x_star with radius r.-/
lemma x_star_αd_in_metric_ball {x_star d: E} {α r: ℝ} (hα: 0 < α ∧ α < r / ‖d‖) (h_d_not_zero: d ≠ 0)
: x_star + (α • d) ∈ metric.ball x_star r:=
begin
simp only [metric.mem_ball, dist_self_add_left],
cases hα with α_greater_zero α_less_r_over_norm_d,
simp only [norm_smul, real.norm_eq_abs],
rw abs_of_pos,
{
  have norm_d_greater_zero : 0 < ‖d‖,
  {
    rw norm_pos_iff,
    exact h_d_not_zero,
  },
  rw ← lt_div_iff,
  {exact α_less_r_over_norm_d,},
  {exact norm_d_greater_zero,},
},
{exact α_greater_zero,}
end

/--Given a point `x_star`, a vector `d`, two non-negative real numbers `a` and `b` such that
  a + b = 1, and a positive real number `α` with 0 < α < r / ‖d‖, then x_star + (b • α • d) is in the
  open ball centered at x_star with radius r.-/
lemma points_on_segment_in_metric (x_star d: E) {α a b r: ℝ} (ha: 0 ≤ a) (hb: 0 ≤ b) (hc: a + b = 1) 
(h_d_not_zero: d ≠ 0) (hα : 0 < α ∧ α < r / ‖d‖) : (x_star + (b • α • d)) ∈ metric.ball x_star r:=
begin
  simp only [metric.mem_ball, dist_self_add_left],
  rw [norm_smul, real.norm_of_nonneg hb, norm_smul, real.norm_of_nonneg],

  swap,
  {exact le_of_lt hα.1,},

  {
  rw ← mul_assoc,
  have bα_upper_bound_same_as_α : b * α < r / ‖d‖,
    {
      apply lt_of_le_of_lt _ hα.2,
      nlinarith [hα.1],
      },
  rw ← norm_pos_iff at h_d_not_zero,

  have useful_thing : (b * α) * ‖d‖ < r,
    {
      set pp := (b * α),
      rw [lt_div_iff h_d_not_zero] at bα_upper_bound_same_as_α,
      exact bα_upper_bound_same_as_α,
      },
  
  exact useful_thing,
  },
end

/--Given a point `x_star`, a vector `d`, and a real number `α`,
  the function f(c) = x_star + c • d is twice continuously differentiable
  on the closed interval [0, α].-/
lemma segment_cont_diff (x_star d: E) (α : ℝ) : cont_diff_on ℝ 2 (λ (c : ℝ), x_star + c • d) (Icc 0 α) :=
begin
  apply cont_diff_on.add,  --applies the rule that sum of two differentiable functions is differentiable
  {apply cont_diff_on_const,}, --applies the rule that a constant function, x_star is differentiable
  {
    apply cont_diff_on.smul, 
      {apply cont_diff_on_id,},
      {apply cont_diff_on_const,},
  }
end

/--Given a function `f` that is twice continuously differentiable on a set `u`,
  a point `x_star`, a vector `d`, and a real number `α` with 0 < α < r / ‖d‖, if the segment
  from x_star to x_star + α • d is a subset of `u`, then f is twice continuously differentiable
  on the segment.-/
lemma f_cont_diff_on_α_interval {u : set E} {x_star d: E} {α r : ℝ} {f: E → ℝ} 
(h_twice_continuous_diffable: cont_diff_on ℝ 2 f u) (hα: 0 < α ∧ α < r / ‖d‖)
(segment_subset_u_small_α: ∀ (α : ℝ), 0 < α ∧ α < r / ‖d‖ → segment ℝ x_star (x_star + α • d) ⊆ u)
: cont_diff_on ℝ 2 (f ∘ (λ (c : ℝ), x_star + c • d)) (Icc 0 α) :=
begin
  have segment_cont_diff := segment_cont_diff E x_star d α,
  apply cont_diff_on.comp h_twice_continuous_diffable segment_cont_diff, --Sebastien Gouezel introduced me to cont_diff_on.comp
  { intros x hx,
    simp only [mem_preimage],
    have point_in_segment : x_star + x • d ∈ segment ℝ x_star (x_star + α • d),
      {
        rw mem_segment_iff_div,
        use (α - x),
        use x,
        rw mem_Icc at hx, --kevin buzzard helped
        refine ⟨_, _, _, _⟩; try {linarith}, --kevin buzzard introduced me to '; try' that can do linarith multiple times
        
        simp only [sub_add_cancel, smul_add],
        rw [← add_assoc, ← add_smul],
        ring_nf,
        rw inv_mul_cancel,
        {
          simp only [one_smul, add_right_inj],
          rw [mul_smul, ← smul_assoc, ← smul_smul_smul_comm, smul_eq_mul, inv_mul_cancel, one_smul],
          exact ne_of_gt hα.1,
        },
        {exact ne_of_gt hα.1,},
      },
    specialize segment_subset_u_small_α α hα,
    exact segment_subset_u_small_α point_in_segment,
  },
end

/--Given a set `u` and a point `x_star`, if a metric ball with radius `r`
  centered at `x_star` is a subset of a set `j`, and `j` is a subset of the intersection of
  sets `v`, `hv_subset`, and `u`, then the metric ball is a subset of the intersection of
  sets `v`, `hv_subset`, and `u`.-/
lemma metric_r_ball_in_u {u v j hv_subset: set E} {x_star : E} {r : ℝ} 
(h_rest: metric.ball x_star r ⊆ j) (j_in_v_hv_u_set_inter: j ⊆ v ∩ hv_subset ∩ u)
: metric.ball x_star r ⊆ u :=
begin
  intros y hy,
  have metric_points_in_j : y ∈ j,
    {exact h_rest hy,},

  have metric_point_in_v_hv_u_inter : y ∈ (v ∩ hv_subset ∩ u),
    {exact j_in_v_hv_u_set_inter metric_points_in_j,},

  cases metric_point_in_v_hv_u_inter with y_in_v_hv y_in_u,
  exact y_in_u,
end

/--This proof demonstrates that there is a unique tangent space 
(a unique linear approximation) at a point x within the closed interval [0, α] -/
lemma unique_diff_within {d : E} {α x r : ℝ} (hα: 0 < α ∧ α < r / ‖d‖) 
(hx: x ∈ Icc 0 α): unique_diff_within_at ℝ (Icc 0 α) x:=
begin
  have h_interval : 0 < α ∧ x ≤ α,
    {
      split,
      { exact hα.1 },
      { 
      exact hx.2,},
    },

  apply unique_diff_on_convex,
  {apply convex_Icc,},
  {simp [hx],
  exact h_interval.1,},
  {exact hx,},
end

/--The proof shows that for each point x' in the interval [0, α], the function (λ (x : ℝ),
 x_star + x • d) maps x' to a point on the line segment between x_star and (x_star + α • d)-/
lemma maps_to_segment (x_star d : E) {α r: ℝ} (hα: 0 < α ∧ α < r / ‖d‖) :
 maps_to (λ (x : ℝ), x_star + x • d) (Icc 0 α) (segment ℝ x_star (x_star + α • d)) :=
begin
  intros x' hx',
  rw segment_eq_image',
  simp,
  use (x'/α),
  split,
  { 
    split,
    {exact div_nonneg hx'.1 hα.1.le,},
    {
      rwa [div_le_one hα.1],
      exact hx'.2,
    },
  },
  { 
    rw [←mul_smul, div_mul_cancel],
    exact ne_of_gt hα.1,},
end

/--this proof demonstrates that the function that maps x to x_star + x • d is 
differentiable within the closed interval [0, α] at any point x in that interval.-/
lemma differentiable_within_x_star (x_star d : E) (α x: ℝ) : 
differentiable_within_at ℝ (λ (x : ℝ), x_star + x • d) (Icc 0 α) x :=
begin
  simp only [differentiable_within_at_const_add_iff], --function is differentiable if and only if the function with its constant part removed is differentiable
  apply differentiable_within_at.smul_const differentiable_within_at_id,
  apply_instance, --automatically finds and applies an instance of a typeclass
end

/-- The necessary second-order optimality condition for a local minimum in a multivariable function:
Given a function `f` with continuous second-order derivatives in an open set `u`, if `x_star` is a
local minimum of `f` in `u`, then the Hessian of `f` at `x_star` is positive semi-definite. -/
theorem necess_2nd_order_optimality_condit
    (u : set E) (h_open : is_open u)  -- u is an open subset of E
    (h_d_nonzero : ∃ d ∈ u, d ≠ (0 : E) ) -- d is in u and d is a not zero vector
    (x_star : E) (h_x_star : x_star ∈ u) -- x_star is in u 
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (f'' : E → (E →L[ℝ] (E →L[ℝ] ℝ)))
    (h_deriv_exists : ∀ y ∈ u, has_fderiv_at f (f' y) y) -- f' is the first derivative of f
    (h_second_deriv_exists : ∀ y ∈ u, has_fderiv_at f' (f'' y) y) -- f'' is the second derivative of f
    (h_stationary : f' x_star = 0) -- x_star is a stationary point of f
    (h_twice_continuous_diffable : cont_diff_on ℝ 2 f u): --  f is twice continuously differentiable on u
    is_local_min_on f u x_star → ∀ y, 0 ≤ (f'' x_star) y y := -- if local min point then f'' at point is positive semi-definite
begin
  cases h_d_nonzero with d h_d,
  cases h_d with h_d_in_u h_d_not_zero,

  assume h_local_min,
  rcases h_local_min with ⟨v, hv_open, hv_subset, hx_min⟩,
  rcases hx_min with ⟨hv_subset_is_superset_u, x_star_min_space⟩,

  have hv_subset_nbhd_x_star := hv_subset_nbhd_x_star E h_x_star hv_subset_is_superset_u h_open,

  have u_in_nbhd_x_star : u ∈ nhds x_star,
    {
      rw mem_nhds_iff,
      use u,
      exact ⟨set.subset.refl _, h_open, h_x_star⟩,
    },

  have v_hv_and_u_in_nbhd_x_star : (v ∩ hv_subset ∩ u) ∈ nhds x_star,
    { 
      simp only [filter.inter_mem_iff],
      exact ⟨⟨hv_open, hv_subset_nbhd_x_star⟩, u_in_nbhd_x_star⟩,
    },

  rw mem_nhds_iff at v_hv_and_u_in_nbhd_x_star,
  rcases v_hv_and_u_in_nbhd_x_star with ⟨j, j_in_v_hv_u_set_inter, locally_ball, x_star_in_u⟩,
  rw metric.is_open_iff at locally_ball,
  cases locally_ball x_star x_star_in_u with r, --finally got the r

  have local_minimum_along_segment : ∀ α (h : (0 < α) ∧ (α < (r/‖ d ‖))), f (x_star) ≤ f (x_star + (α • d)),
  { 
    intros α hα,
    
    have x_star_αd_in_local_min_ball : (x_star + (α • d)) ∈ j,
      {
        cases h with h_r h_rest,
        have x_star_αd_in_metric_ball := x_star_αd_in_metric_ball E hα h_d_not_zero,        
        exact h_rest x_star_αd_in_metric_ball,
      },

    have x_star_plus_ad_in_v_hv_u_inter : (x_star + (α • d)) ∈ (v ∩ hv_subset ∩ u ),
      { exact j_in_v_hv_u_set_inter x_star_αd_in_local_min_ball,},

    have x_star_min_space_in_u : ∀ x ∈ (v ∩ hv_subset ∩ u), f(x_star) ≤  f(x),  
      { 
        intros x,
        rw ← x_star_min_space,
        simp only [set.mem_set_of_eq, imp_self],
        exact and.left, --efficient trick I learnt that does cases and then uses the left assumption. Tidy also works.
      },

    specialize x_star_min_space_in_u (x_star + (α • d)) x_star_plus_ad_in_v_hv_u_inter,
    exact x_star_min_space_in_u,
  },

  have segment_subset_u_small_α : ∀ α (h : (0 < α) ∧ (α < (r/‖ d ‖))), segment ℝ x_star (x_star + (α • d)) ⊆ u,
    {

      intros α hα,
      rw segment_subset_iff,
      intros a b ha hb hc,

      rw [smul_add, ← add_assoc, ← add_smul],
      simp only [hc, one_smul],
      
      cases h with h_r h_rest,
      
      have points_on_segment_in_metric := points_on_segment_in_metric E x_star d ha hb hc h_d_not_zero hα,
      
      have metric_r_ball_in_u := metric_r_ball_in_u E h_rest j_in_v_hv_u_set_inter,
      
      have all_segment_points_in_u : x_star + b • α • d ∈ u,
        {exact metric_r_ball_in_u points_on_segment_in_metric,},
      
      exact all_segment_points_in_u,
    },

  have second_order_MVT : ∀ α (h : (0 < α) ∧ (α < (r/‖ d ‖))), ∃ c ∈ segment ℝ x_star (x_star + (α • d)), f (x_star + (α • d)) - f x_star = ((α^2)/2) * (f'' c) d d , 
    {
      intros α hα,

      set g : ℝ → ℝ := λ c, f (x_star + (c • d)) with hg,
      
      set n : ℕ := 1 with hn,

      have g_cont_diffable_once_zero_α : cont_diff_on ℝ n (λ (c : ℝ), g c) (Icc 0 α),
        {  
          rw [hg, hn],
          simp only [enat.coe_one],
          
          have f_cont_diff_on_α_interval := f_cont_diff_on_α_interval E h_twice_continuous_diffable hα segment_subset_u_small_α,
          apply cont_diff_on.one_of_succ f_cont_diff_on_α_interval,
        },

      have first_deriv_diffable_on_open : differentiable_on ℝ (iterated_deriv_within n (λ (c : ℝ), g c) (Icc 0 α)) (Ioo 0 α),
        { 
          have h_diff_g : differentiable_on ℝ g (Icc 0 α),
          { 
            apply cont_diff_on.differentiable_on,
            rw hg,
            exact g_cont_diffable_once_zero_α,
            simp only [enat.coe_one, le_refl], --enat.coe_one converts the natural number 1 to its extended natural number representation.
          },

          have h_deriv_g : ∀ x ∈ Icc 0 α, deriv_within g (Icc 0 α) x = (fderiv_within ℝ (λ (x : E), f x) (segment ℝ x_star (x_star + α • d)) (x_star + x • d)) d,
            {
              intros x hx,
              rw [hg], 
              rw ← fderiv_within_deriv_within,
              --I need to use fderiv_within.comp here so below I am getting the hypothesis ready to so i can use it.
              
              have h_unique_diff_within := unique_diff_within E hα hx,

              have h_maps_to_segment := maps_to_segment E x_star d hα,

              have h_differentiable_within_x_star := differentiable_within_x_star E x_star d α x,

              --sorry didnt get the time to finish
              sorry,},

          sorry,
        }, 
      
      have taylor_theorem_with_lagrange_form_remainder : ∃ (x' : ℝ) (hx' : x' ∈ Ioo 0 α), g α - taylor_within_eval g n (Icc 0 α) 0 α =
          (iterated_deriv_within (n+1) g (Icc 0 α) x') * (α - 0)^(n+1) /(n+1).factorial,
        {
          apply taylor_mean_remainder_lagrange,
          exact hα.1,
          exact g_cont_diffable_once_zero_α,
          exact first_deriv_diffable_on_open,
        },
    sorry,
    },
  sorry,
end