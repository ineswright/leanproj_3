import tactic
import analysis.calculus.fderiv
import analysis.calculus.cont_diff
import analysis.inner_product_space.pi_L2
import measure_theory.integral.interval_integral
import geometry
import analysis.calculus.mean_value

-- missing 'noncomputable' modifier, definition 'tangent_line2' depends on 'real.densely_normed_field'
-- TODO: I probably can add these to the environment somehow, or prove them. Look in analysis.normed.field.basic

-- missing 'noncomputable' modifier, definition 'tangent_line' depends on 'pi_Lp.normed_add_comm_group'
noncomputable def tangent_line {n : ℕ} {f : ℝ → euclidean_space ℝ (fin n)} {a b : ℝ} (h : regular_curve n f a b) (t₀ : ℝ)
 : ℝ → euclidean_space ℝ (fin n) := λ t, f t₀ + ((fderiv ℝ f t₀) t)

noncomputable def tangent_line2 {f : ℝ → ℝ × ℝ} {a b : ℝ} (h : regular_curve2 f a b) (t₀ : ℝ) : ℝ → ℝ × ℝ := 
  λ t, f t₀ + ((fderiv ℝ f t₀) t)

noncomputable def tangent_line3 {f : ℝ → ℝ × ℝ × ℝ} {a b : ℝ} (h : regular_curve3 f a b) (t₀ : ℝ) : ℝ → ℝ × ℝ × ℝ := 
  λ t, f t₀ + ((fderiv ℝ f t₀) t)

-- TODO: the tangent map is smooth

-- TODO: if I define this without the a b c d and the regular curve assumptions,
-- then can prove φ regular → ψ regular
def is_parametrisation {n : ℕ} {a b c d : ℝ} {ψ : ℝ → euclidean_space ℝ (fin n)} {φ : ℝ → euclidean_space ℝ (fin n)}
  (h1 : regular_curve n ψ c d) (h2 : regular_curve n φ a b) 
  := ∃ f : ℝ → ℝ, cont_diff_on ℝ ⊤ f (set.Icc c d) ∧ f '' {c, d} = {a, b} ∧ 
    (∀ t : ℝ, t ∈ set.Icc c d → norm (fderiv ℝ f t) ≠ 0) ∧
    (∀ t, t ∈ set.Icc c d → φ ∘ f = ψ)

-- def parametrises {n : ℕ} {a b c d : ℝ} {ψ : ℝ → euclidean_space ℝ (fin n)} {φ : ℝ → euclidean_space ℝ (fin n)}
--   (h1 : regular_curve n ψ c d) (h2 : regular_curve n φ a b) {f : ℝ → ℝ} (hf1 : cont_diff_on ℝ ⊤ f (set.Icc c d)) 
--   (hf2 : f '' {c, d} = {a, b}) (hf3 : ∀ t : ℝ, t ∈ set.Icc c d → norm (fderiv ℝ f t) ≠ 0) 
--   := ∀ t, t ∈ set.Icc c d → φ ∘ f = ψ  

noncomputable def length {n : ℕ} {f : ℝ → euclidean_space ℝ (fin n)} {a b : ℝ} (h : regular_curve n f a b) : ℝ 
  := ∫ t in a..b, norm (fderiv ℝ f t)  

-- TODO: replace this with coercion to euclidean_space of length
noncomputable def length2 {f : ℝ → ℝ × ℝ} {a b : ℝ} (h : regular_curve2 f a b) : ℝ 
  := ∫ t in a..b, norm (fderiv ℝ f t) 

noncomputable def length3 {f : ℝ → ℝ × ℝ × ℝ} {a b : ℝ} (h : regular_curve3 f a b) : ℝ 
  := ∫ t in a..b, norm (fderiv ℝ f t) 

lemma continuous.all_lt_or_all_gt_of_ne {f : ℝ → ℝ } (h1 : continuous f) (h2 : ∀ t, f t ≠ 0) : (∀ t, f t < 0) ∨ (∀ t, f t > 0) :=
begin
  -- This _must_ be golfable !!! The proofs are virtually the same
  -- Using Kevin's wlog trick somehow ?
  rcases lt_or_gt_of_ne (h2 0) with (hlt | hgt),
  { apply or.intro_left,
    intro t,
    by_contra,
    push_neg at h,
    -- Application of IVT : ∃ y, f y = 0
    obtain ⟨y, hy⟩ := mem_range_of_exists_le_of_exists_ge h1 ⟨0, le_of_lt hlt⟩ ⟨t, h⟩,
    exact h2 y hy, },
  { apply or.intro_right,
    intro t,
    by_contra,
    push_neg at h,
    obtain ⟨y, hy⟩ := mem_range_of_exists_le_of_exists_ge h1 ⟨t, h⟩ ⟨0, le_of_lt hgt⟩,  
    exact h2 y hy, },
end

-- strict_anti_on_of_deriv_neg
-- strict_mono_of_deriv_neg,
-- strict_anti_of_deriv_neg

-- In order.mono.basic
-- strict_mono.is_min_of_apply
-- strict_mono.is_max_of_apply
-- strict_anti.is_min_of_apply
-- strict_anti.is_max_of_apply

-- This is an obvious statement to anyone who's studied first year analysis and calculus
-- And yet completely non trivial...!
-- hab and hcd shouldn't be necessary but its so hard without :cry:

lemma strict_mono_on_of_pos_deriv {c d : ℝ} {f : ℝ → ℝ} (hf :  cont_diff_on ℝ ⊤ f (set.Icc c d)) 
  (hs : (∀ s, s ∈ set.Ioo c d → (fderiv ℝ f s) 1 > 0 )) : strict_mono_on f (set.Icc c d) :=
begin
  apply @convex.strict_mono_on_of_deriv_pos (set.Icc c d) (convex_Icc c d) f 
    (cont_diff_on.continuous_on hf) _,
  intros x hx,
  specialize hs x ((set.ext_iff.mp interior_Icc x).mp hx),
  rw [←deriv_fderiv] at hs,
  dsimp at hs,
  simp only [one_mul] at hs,
  exact hs,
end

lemma strict_anti_on_of_neg_deriv {c d : ℝ} {f : ℝ → ℝ} (hf :  cont_diff_on ℝ ⊤ f (set.Icc c d)) 
  (hs : (∀ s, s ∈ set.Ioo c d → (fderiv ℝ f s) 1 < 0 )) : strict_anti_on f (set.Icc c d) :=
begin
  apply @convex.strict_anti_on_of_deriv_neg (set.Icc c d) (convex_Icc c d) f 
    (cont_diff_on.continuous_on hf) _,
  intros x hx,
  specialize hs x ((set.ext_iff.mp interior_Icc x).mp hx),
  rw [←deriv_fderiv] at hs,
  dsimp at hs,
  simp only [one_mul] at hs,
  exact hs,
end

lemma kevins_version (f : ℝ → ℝ) (hf : monotone f) (a b c d : ℝ) (hab : a ≤ b) (h : f '' set.Icc c d = set.Icc a b) :
  f c = a :=
begin
  have foo : a ∈ set.Icc a b := set.left_mem_Icc.mpr hab,
  rw ← h at foo,
  rcases foo with ⟨x, hx1, hx2⟩,
  rw set.mem_Icc at hx1,
  specialize hf hx1.1,
  rw hx2 at hf,
  have : f c ∈ set.Icc a b := (set.ext_iff.mp h (f c)).mp ⟨c, ⟨le_of_eq rfl, (le_trans hx1.1 hx1.2)⟩, rfl⟩,
  exact eq_of_le_of_not_lt hf (not_lt_of_ge this.1),
end

-- The number of times I was trying to prove something false here :sick:
lemma something {f : ℝ → ℝ} {a b c d : ℝ} (hfa : f c = a) (hf : f '' {c, d} = {a, b}) : f d = b :=
begin
  obtain ⟨x, hxcd, hfxb⟩ := (set.ext_iff.mp hf b).mpr (set.mem_insert_iff.mpr (or.intro_right _ (set.mem_singleton b))),
  obtain ⟨y, hycd, hfya⟩ := (set.ext_iff.mp hf a).mpr (set.mem_insert_iff.mpr (or.intro_left _ rfl)), 
  rcases hxcd with (hxc | hxd),
  { rw hxc at hfxb,
    cases em (a = b),
    { have := (set.ext_iff.mp hf (f d)).mp ⟨d, (or.intro_right _ (set.mem_singleton d)), rfl⟩,
      rw h at this,
      exact or.elim this id set.mem_singleton_iff.mp, 
    },
    { rcases hycd with (hyc | hyd),
      { rw [←hyc, hfya] at hfxb,
        exact false.elim (h hfxb), },
      { rw hfxb at hfa,
        exact false.elim (h hfa.symm),
      },
    },
  },
  { rw [← set.mem_singleton_iff.mp hxd, hfxb], },
end

-- What a ridiculous thing to need to prove...
lemma two_set_comm (a b : ℝ) : insert a ({b} : set ℝ) = {b, a} :=
begin
  ext, split; exact λ hx, or.comm.mp hx,
end

lemma two {a b c d : ℝ} (hab : a < b) (hcd : c < d) {f : ℝ → ℝ} (hf :  cont_diff_on ℝ ⊤ f (set.Icc c d)) 
  (hfim : f '' {c, d} = {a, b}) : ((∀ s, s ∈ set.Ioo c d → (fderiv ℝ f s) 1 > 0 ) → 
  f c = a ∧ f d = b) ∧ ((∀ s, s ∈ set.Ioo c d → (fderiv ℝ f s) 1 < 0) → f c = b ∧ f d = a) := 
begin
  refine ⟨_, _⟩, 
  { -- Goal: deriv is positive implies f c = a ∧ f d = b
    intro hs,
    have : f c = a, {
      by_contra,
      have : f c ∈ {a, b},
      { exact (set.ext_iff.mp hfim (f c)).mp ⟨c, (set.mem_insert c {d}), rfl⟩, },
      have thisb : f c = b,
      { exact set.mem_singleton_iff.mp (or.resolve_left (set.mem_insert_iff.mp this) h), },
      have thisa : f d = a, 
      { rw two_set_comm a b at hfim,
        exact something thisb hfim, },
      have : f c < f d := (strict_mono_on_of_pos_deriv hf hs) ⟨le_of_eq rfl, le_of_lt hcd⟩ ⟨le_of_lt hcd, le_of_eq rfl⟩ hcd,
      rw [thisb, thisa] at this,
      exact (not_lt_of_gt this) hab, },
    exact ⟨this, (something this hfim)⟩,
  },
  { -- Goal: deriv is neg implies f c = b ∧ f d = a
    intro hs,
    have : f c = b, {
      by_contra,
      apply (not_lt_of_gt _) hab,
      have : f c ∈ {a, b},
        { exact (set.ext_iff.mp hfim (f c)).mp ⟨c, (set.mem_insert c {d}), rfl⟩, },
      have thisa : f c = a := set.mem_singleton_iff.mp (or.resolve_right (set.mem_insert_iff.mp this) h),
      have thisb : f d = b := something thisa hfim,
      rw [←thisa, ←thisb],
      exact (strict_anti_on_of_neg_deriv hf hs) ⟨le_of_eq rfl, le_of_lt hcd⟩ ⟨le_of_lt hcd, le_of_eq rfl⟩ hcd,
    },
    rw two_set_comm a b at hfim,
    exact ⟨this, something this hfim⟩,
  },
end

lemma three {A B : set ℝ} (hab : A ⊆ B) {f : ℝ → ℝ} (hf : cont_diff_on ℝ ⊤ f B) : cont_diff_on ℝ ⊤ f A :=
begin
  intros t ht,
  specialize hf t (hab ht),
  -- Something.... idk
  -- Surely this is in mathlib somewhere what on earth
  sorry,
end

lemma integral_ext {f g : ℝ → ℝ} {c d : ℝ} (h : ∀ t, t ∈ set.Icc c d → f t = g t) : ∫ (t : ℝ) in c..d, f t = ∫ (t : ℝ) in c .. d, g t
:= 
begin
  rcases le_or_gt c d with (hc | hd),
  { -- The integrals have the same value where the set.Icc c d is nonempty
    apply interval_integral.integral_congr (_ : set.eq_on f g (set.uIcc c d)),
    rw set.uIcc_of_le hc,
    exact h,
  },
  { -- This isn't true!
    sorry,
  },
end


-- I would recommend first proving another lemma with the additional hypothesis a<=b and then in your 
-- main result invoking le_or_ge (or whatever it's called) to say that either a<=b or b<=a, and then invoking 
-- the sublemma in both branches, the first time with a and b, and the second time with b and a

-- Would I need to have is_parametrisation take everything in as parameters in order to 
-- have the hypothesis ∀ t, f t > 0

-- TODO: this and remove noncomputable once figured out how to define type
-- I think I need c ≤ d and a ≤ b 
lemma length_invariant_under_parameterisations {n : ℕ} {a b c d : ℝ} {ψ : ℝ → euclidean_space ℝ (fin n)} {φ : ℝ → euclidean_space ℝ (fin n)}
  {h1 : regular_curve n ψ c d} {h2 : regular_curve n φ a b} (h3 : is_parametrisation h1 h2) : length h1 = length h2 :=
begin
  obtain ⟨f, hf⟩ := h3,
  have : (∀ s, s ∈ set.Icc c d → norm (fderiv ℝ f s) < 0)
          ∨ (∀ s, s ∈ set.Icc c d → norm (fderiv ℝ f s) > 0),
    { have hfne0 := hf.2.2.1,
      have hdfcont_on := cont_diff_on.continuous_on_fderiv_of_open (three set.Ioo_subset_Icc_self hf.1) is_open_Ioo le_top,
      have hdnormfcont_on : continuous_on (λ (x : ℝ), ‖fderiv ℝ f x‖) (set.Ioo c d) := continuous_on.norm hdfcont_on,
      suffices : ((∀ (s : set.Icc c d), ‖fderiv ℝ f s‖ < 0) ∨ ∀ (s : set.Icc c d), ‖fderiv ℝ f s‖ > 0), sorry,
      sorry,
    },
  -- have him := two_a (three set.Ioo_subset_Icc_self hf.1) hf.2.1, 
  rcases this with (h | h),
  { unfold length,
    have : f c = a ∧ f d = b, sorry,
    rw [←this.1, ←this.2],
    have : ∫ (t : ℝ) in c..d, ‖fderiv ℝ ψ t‖ = ∫ (t : ℝ) in c..d, ‖fderiv ℝ (φ ∘ f) t‖, sorry,
    rw [this],
    -- ∘ f is too deep in the function to apply this ...
    -- apply @interval_integral.integral_comp_smul_deriv ℝ _ _ _ c d f,
    sorry, },
  { sorry, },
end

-- TODO: arc length parametrised regular curve
-- lemma, every regular curve can be parameterised by arc length

-- THIS IS THE END OF CHAPTER 1!