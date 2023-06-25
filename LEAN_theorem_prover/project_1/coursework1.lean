import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
open finset -- finite subsets 

/-- a(n) is a convergent sequence iff the below is satisfied -/
def convergent (a : ℕ → ℝ) : Prop :=
∃t : ℝ, ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

/-- Definition of a cauchy sequence a(n) -/
def cauchy (a : ℕ → ℝ) : Prop :=
∀ ε > 0, ∃ B : ℕ, ∀ n, ∀ m, B ≤ n ∧ B ≤ m → |a n - a m| < ε

/--Definition for a sequence to be bounded-/
def bounded_seq (a : ℕ → ℝ) : Prop := ∃ M, ∀ m, |a m| ≤ M

/--Definition for a sequence to have a lower bound-/
def lower_bounded_seq (a : ℕ → ℝ) : Prop := 
∃ M, ∀ n, M ≤ a n

/--Definition for a sequence to be monotonically decreasing-/
def mono_dec_seq (a : ℕ → ℝ) : Prop :=
∀ ⦃m n⦄, m ≤ n → a n ≤ a m

/--Definition for a set to have a lower bound-/
def lower_bbd_set (S : set ℝ) (x : ℝ) : Prop :=
∀ i ∈ S, x ≤ i


/-Proof that a monotonically decreasing and lower bounded sequence is convergent.-/
theorem mono_dec_bdd_imp_convergent (a : ℕ → ℝ) (ha : mono_dec_seq a) 
(hb : lower_bounded_seq a) : convergent a :=
begin
  set S := {x | ∃ i, x = a i}, --defines a set that contains elements of sequence a. 

  have hS : S.nonempty, -- i prove S isnt empty as it has a 0 in it
  {
    use a 0, 
    simp only [S],
    simp, 
  },

  have h : ∃ x, lower_bbd_set S x, --there exists a lower bound of the set S
  {
  rw lower_bounded_seq at hb,
  cases hb with M hM,
  use M,  --lower bound of the sequence is also a lower bound of the set S
  intros i hi,
  have hc : ∃ (n : ℕ), i = a n, --i in S is of the form a n for some n
  {
    simp only [set.mem_set_of_eq] at hi,
    exact hi,
  },
  rcases hc with ⟨n, rfl⟩,
  apply hM,
  },

  --proof that there exists a infinum of set S
  have h_greatest_lower_bound1 : ∃ x, ∀ i ∈ S, x ≤ i ∧ ∀ y, ∀ j ∈ S, y ≤ j → y ≤ x,
    {
    sorry, -- difficult to prove due to involvement of completeness
    },


  rw convergent,
  rcases h_greatest_lower_bound1 with ⟨inf, hinf⟩, --the infinum of S is now inf
  use inf,
  intros ε hε,

  have h_s_ε : inf < inf + ε,
    {simp,
    exact hε,},

  have h_inf_ε_not_lb : ∃ (x : ℕ), a x < inf + ε,
    {
      obtain ⟨i, hi⟩ := hS, --since S is non empty i is in S
      specialize hinf i,
      
      have k : inf ≤ i ∧ ∀ (y j : ℝ), j ∈ S → y ≤ j → y ≤ inf,
        {exact hinf hi,},
      
      by_contra, --going to show ∃ (x : ℕ), a x < inf + ε by contradiction
      simp only [not_exists, not_lt] at h, --rewrites the contradiction hypothesis

      set y := inf + ε, --sets y so we can get a contradiction with inf + ε < inf later
      cases k with hP hQ,

      specialize hQ y,
      specialize hQ i,
      
      have h_one : y ≤ i → y ≤ inf,
        {apply hQ,
        exact hi,},
      
      have h_i_ax :∃ (x : ℕ),  i = a x, 
        {exact hi,},

      cases h_i_ax with x hj,
      specialize h_1 x,

      have h_two : y ≤ i,
        {rwa hj,},

      have h_three : y ≤ inf,
        {exact h_one h_two,},

      linarith,
    },
  
  obtain ⟨x, hx⟩ := h_inf_ε_not_lb,
  
  use x,  --sets B as x in definition of convergence
  intros n h_x_less_n, --x ≤ n

  have h_an_ax_ε : a n - inf ≤ a x - inf ∧ a x - inf < ε,
    {
    split,

    simp,
    rw mono_dec_seq at ha, --pulls the definition of monotonically decreasing seq
    -- a n - inf ≤ a x - inf → a n ≤ a x → n ≤ x (as decreasing)
    apply ha, 
    have h_first_goal : a x - inf < ε,
      {--below changes goal a x - inf < ε to a x < ε + inf, which is same as hx.
        apply sub_left_lt_of_lt_add hx,}, 
    exact h_x_less_n, -- left inequality proved

    exact sub_left_lt_of_lt_add hx, --a x < inf + ε → a x - inf < ε
    },

  have h_final : a n ∈ S,
    {use n,},
  
  have h_inf_an : inf ≤ a n,
    {-- Since a n is in S, we sub a n for i in hinf : ∀ (i : ℝ), i ∈ S → (inf ≤ i ∧ ...)
    --from that we can then retrieve the goal
      exact (hinf (a n) h_final).1,  --jazzon provided this command
      },
      
  have hzero_less_an_inf : 0 ≤ a n - inf,
    {nlinarith,},

  cases h_an_ax_ε with hleft hright,
  rw abs_lt,
  split,
  linarith,
  exact lt_of_le_of_lt hleft hright,
end

/--Proof if a sequence is cauchy then it is bounded-/
theorem cauchy_then_bounded {a : ℕ → ℝ} : cauchy a → bounded_seq a :=
begin
  intro ha,
  rw cauchy at ha,
  specialize ha 1, --gives the input that ε is 1 
  specialize ha _, --makes goal that ε = 1 is valid  
  norm_num,
  cases ha with B hB,
  rw bounded_seq at ⊢,
  specialize hB _,
  use B, -- taking n = B

  --So far i have hB: ∀ (m : ℕ), B ≤ m → |a B - a m| < 1, 
  -- As an intermediary step I need ∀ (m : ℕ), B ≤ m, |a m| < 1 + |a B|,


  have hB1 : ∀ (m : ℕ), B ≤ B ∧ B ≤ m → | |a B| - |a m| | ≤ |a B - a m|,
    {intros m hnm,
    exact abs_abs_sub_abs_le_abs_sub (a B) (a m),},

  have hB3 : ∀ (m : ℕ), B ≤ B ∧ B ≤ m → |a m| - |a B| ≤ | |a m| - |a B| |,
    {intros m hnm,
    exact le_abs_self (|a m| - |a B|),
    },
  
  have hB4 : ∀ (m : ℕ), B ≤ B ∧ B ≤ m → |a m| < 1 + |a B|,
    {intros m hnm, -- where hnm: B ≤ B ∧ B ≤ m
    specialize hB (m), -- gets rid of ∀ (m : ℕ)
    specialize hB1 (m),
    specialize hB3 (m),
    have h_zero := hB hnm,  
    have h_one := hB1 hnm, --ends up with just the RHS of hB1
    have h_three := hB3 hnm,

    have h_first := gt_of_gt_of_ge h_zero h_one, --does a > b → b ≥ c → a > c
    rw abs_sub_comm at h_first, 
    --below command changes ||a m| - |a B|| < 1 to |a m| - |a B| < 1
    have h_second := lt_of_abs_lt h_first, 
    apply lt_add_of_sub_right_lt, --|a m| < 1 + |a B| → |a m| - |a B| < 1
    exact h_second, 
    },

  have hL : 0 ≤ B,
    {apply zero_le,},

  ---credit to Prof. Buzzard for this proof (I have slighty adapted it and added comments)
  --This shows that set {|a 0|, |a 1|, ..., |a (B-1)|} has a maximal element
  have maximal : ∃ (x ≤ B), ∀ m ≤ B, |a m| ≤ |a x|, 
  {
  -- make the set {|a 0|, |a 1|, ..., |a (B-1)| }
  set S : finset ℝ := image (λ x, |a x|) (range (B + 1)) with hSdef,
  -- it's nonempty because 0 < B so |a 0| is in it
  have hSnonempty : S.nonempty,
    { 
      use |a 0|,
      rw hSdef,
      rw mem_image, -- since |a 0| is in set S then ∃ n s.t. |a n|=|a 0|
      refine ⟨0, _, rfl⟩, --leads to goal, 0 ∈ range (B + 1)
      rwa mem_range, -- changes goal to 0 < B + 1
      linarith,}, 
    
    -- let C be the max (which exists because S is nonempty)
    set C : ℝ := finset.max' S hSnonempty with hC,  
    -- we know C ∈ S
    have hC : C ∈ S,
    { exact max'_mem S hSnonempty, }, -- thanks `library_search`
    rw hSdef at hC,
    rw mem_image at hC,
    rcases hC with ⟨x, hxB, hxC⟩,
    use x,
    rw mem_range at hxB,

    have h_one : x ≤ B, --already have x < B + 1
    {linarith,},

    refine ⟨h_one, _⟩, --this tactic gets rid of h_one from goal
    intros m hmB,
    rw hxC,
    rw hC,
    apply le_max', -- Prof. Buzzard guessed the name of the lemma
    rw hSdef,
    rw mem_image,
    refine ⟨m, _, rfl⟩,
    rwa mem_range,
    linarith,
    },
  --Prof.Buzzard kind contribution ends here

  cases maximal with x,
  cases maximal_h with H,

  -- we have that |a m|<={|a1|, |a2|, . . . ,|aB−1|,|aB|}
  --aim is to show |a m|<={|a1| + 1, |a2| + 1, . . . ,|aB−1| + 1, 1 + |aB|}
  use max  (|a x| + 1) (1 + |a B|), 
  simp [abs_nonneg, lt_add_of_le_of_pos],
  intros m,
  by_cases B ≤ m,
    {--case |a m| ≤ 1 + |a B|
      right,
      specialize hB4 (m),
      have g : B ≤ B ∧ B ≤ m,
      split,
      linarith,
      linarith,
      specialize hB4 (g),
      exact le_of_lt hB4,
    },

    {--case |a m| ≤ |a x| + 1
    left,
    specialize hB4 (m),
    specialize maximal_h_h (m),
    
    have K : m < B,
      {exact not_le.mp h,}, --¬B ≤ m → m < B

    have P : |a m| ≤ |a x|,
      {
      have new : m ≤ B,
        {linarith, },

      apply maximal_h_h new,
      },
    
    linarith,
    },
end

/--Needed in the proof of cauchy implies convergence.-/
theorem expansion {a b : ℝ} (x : ℝ) : |a - b| = |(a - x) + (x - b)|:=
begin
  norm_num,
end

/--Proof that if a sequences is convergent then it is cauchy and if a
 sequence is cauchy it is convergent -/
theorem convergent_iff_cauchy {a : ℕ → ℝ} : convergent a ↔ cauchy a :=
begin
  split,
  {--Proving convergent sequences are cauchy
  intro ha, -- hypothesis that a is convergent
  rw convergent at ha,
  cases ha with t ht, 
  rw cauchy at ⊢, 
  intros ε hε, -- assumes everything before the first implies in the goal
  specialize ht (ε/2) (by linarith), --replaces ε with ε/2 in defintion of convergence 
  --...to replicate start and dagger in proof. 
  simp_rw expansion t, --replaces |a n - a m)| by |a n - t + (t - a m)| in goal
  cases ht with B hB,
  use B,
  intros n m hnm,
  cases hnm,
  have h := hB n hnm_left,  --uses hypothesis n and hn to argue forward in hB
  have h' := hB m hnm_right,
  rw abs_sub_comm at h', --replaces |a m - t| with |t - a m| as |.| is commutative
  --abs_add applies traingle hypothesis on |a n - t + (t - a m)|
  have h'' := abs_add (a n - t) (t - a m), 
  --brings in star and dagger like in the Prop 3.17 proof last step
  have h''' := add_lt_add h h', 
  linarith,  --proof my contradiction by simple arithmetic on not-goal and h''' 
  },
  {
  -- Proving cauchy sequences are convergent
  rintros h,
  rw convergent,
  have h_one : bounded_seq a,
  {apply cauchy_then_bounded,
  exact h,},
  rw bounded_seq at h_one,
  sorry,
  
    },
end

--All linter checks passed!
--#lint