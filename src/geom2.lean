import tactic
import analysis.calculus.fderiv
import analysis.calculus.cont_diff
import analysis.inner_product_space.pi_L2
import measure_theory.integral.interval_integral
import geometry
import analysis.calculus.mean_value
import unordered_interval

-- missing 'noncomputable' modifier, definition 'tangent_line' depends on 'pi_Lp.normed_add_comm_group'
noncomputable def tangent_line {n : ℕ} {f : ℝ → euclidean_space ℝ (fin n)} {a b : ℝ} (h : regular_curve n f a b) (t₀ : ℝ)
 : ℝ → euclidean_space ℝ (fin n) := λ t, f t₀ + ((fderiv ℝ f t₀) t)

noncomputable def tangent_line2 {f : ℝ → ℝ × ℝ} {a b : ℝ} (h : regular_curve2 f a b) (t₀ : ℝ) : ℝ → ℝ × ℝ := 
  λ t, f t₀ + ((fderiv ℝ f t₀) t)

noncomputable def tangent_line3 {f : ℝ → ℝ × ℝ × ℝ} {a b : ℝ} (h : regular_curve3 f a b) (t₀ : ℝ) : ℝ → ℝ × ℝ × ℝ := 
  λ t, f t₀ + ((fderiv ℝ f t₀) t)

lemma is_smooth_tangent_map {n : ℕ} {f : ℝ → euclidean_space ℝ (fin n)} {a b : ℝ} (h : regular_curve n f a b) {t₀ : ℝ}
  : cont_diff_on ℝ ⊤ (tangent_line h t₀) (set.Ioo a b) := 
begin
  unfold tangent_line,
  cont_differentiability,
  -- Goal: fderiv is cont_diff_on set.Ioo
  -- I don't understand this fucking API why is this so impossible to use
  have hdcontdiff : cont_diff_on ℝ ⊤ (fderiv_within ℝ f (set.Icc a b) t₀) (set.Ioo a b),
  { 
    -- apply cont_diff_on.fderiv_within h.1 _ (le_top : ⊤ + 1 ≤ ⊤),
    sorry, -- Goal: unique_diff_on ℝ (set.Icc a b)
  },
  have hfderiv_eq_fderiv_within : ∀ (x : ℝ), x ∈ set.Ioo a b → (fderiv ℝ f t₀) x = (fderiv_within ℝ f (set.Icc a b) t₀) x,
  { sorry, },
  -- Goal: cont_diff_on ℝ ⊤ (λ (x : ℝ), ⇑(fderiv ℝ f t₀) x) (set.Ioo a b)
  exact @cont_diff_on.congr_mono ℝ _ _ _ _ _ _ _ (set.Ioo a b) (set.Ioo a b) _ (fderiv ℝ f t₀) 
    ⊤ hdcontdiff hfderiv_eq_fderiv_within (subset_of_eq rfl),
end

def is_parametrisation {n : ℕ} {a b c d : ℝ} {ψ : ℝ → euclidean_space ℝ (fin n)} {φ : ℝ → euclidean_space ℝ (fin n)}
  (h1 : regular_curve n ψ c d) (h2 : regular_curve n φ a b) 
  := ∃ f : ℝ → ℝ, cont_diff_on ℝ ⊤ f (set.uIcc c d) ∧ f '' {c, d} = {a, b} ∧ 
    (∀ t : ℝ, t ∈ set.uIcc c d → norm (fderiv ℝ f t) ≠ 0) ∧
    (∀ t, t ∈ set.uIcc c d → φ ∘ f = ψ)

def parametrises {n : ℕ} {a b c d : ℝ} {ψ : ℝ → euclidean_space ℝ (fin n)} {φ : ℝ → euclidean_space ℝ (fin n)}
  (h1 : regular_curve n ψ c d) (h2 : regular_curve n φ a b) (f : ℝ → ℝ) :=
  cont_diff_on ℝ ⊤ f (set.uIcc c d) ∧ f '' {c, d} = {a, b} ∧ 
    (∀ t : ℝ, t ∈ set.uIcc c d → norm (fderiv ℝ f t) ≠ 0) ∧
    (∀ t, t ∈ set.uIcc c d → φ ∘ f = ψ)

lemma is_parametrisation_of_parametrises {n : ℕ} {a b c d : ℝ} (hab : a < b) (hcd : c < d) {ψ : ℝ → euclidean_space ℝ (fin n)} {φ : ℝ → euclidean_space ℝ (fin n)}
  (h1 : regular_curve n ψ c d) (h2 : regular_curve n φ a b) (f : ℝ → ℝ) (hp : parametrises h1 h2 f) : is_parametrisation h1 h2
  := 
begin
  refine ⟨f, _⟩,
  unfold parametrises at hp,
  exact hp,
end 

noncomputable def length {n : ℕ} {f : ℝ → euclidean_space ℝ (fin n)} {a b : ℝ} (h : regular_curve n f a b) : ℝ 
  := ∫ t in a..b, norm (fderiv ℝ f t)  

-- TODO: replace this with coercion to euclidean_space of length
noncomputable def length2 {f : ℝ → ℝ × ℝ} {a b : ℝ} (h : regular_curve2 f a b) : ℝ 
  := ∫ t in a..b, norm (fderiv ℝ f t) 

noncomputable def length3 {f : ℝ → ℝ × ℝ × ℝ} {a b : ℝ} (h : regular_curve3 f a b) : ℝ 
  := ∫ t in a..b, norm (fderiv ℝ f t) 

-- Why is this not in Mathlib ??
lemma fderiv_deriv_general {f : ℝ → ℝ} {x t : ℝ} : (fderiv ℝ f x : ℝ →L[ℝ] ℝ) t = (deriv f x) * t :=
begin
  rw ←fderiv_deriv,
  -- rw linear_map.coe_mul 
  sorry,
end

-- Figuring out exactly how I want to apply the IVT and under what conditions was a little rough
lemma continuous_on.all_lt_or_all_gt_of_ne {c d : ℝ} (hcd : c ≤ d ){f : ℝ → ℝ } (h1 : continuous_on f (set.Icc c d)) 
  (h2 : ∀ t, t ∈ set.Icc c d → f t ≠ 0) : (∀ t, t ∈ set.Icc c d → f t < 0) ∨ (∀ t, t ∈ set.Icc c d → f t > 0) :=
begin
  -- The by { split; linarith, }s prove that (c + (d - c) / 2) ∈ set.Icc c d 
  rcases lt_or_gt_of_ne (h2 (c + (d - c) / 2) (by { split; linarith, })) with (hlt | hgt),
  { apply or.intro_left,
    intros t ht,
    by_contra,
    push_neg at h,
    haveI : preconnected_space ↥(set.Icc c d) := subtype.preconnected_space is_preconnected_Icc,
    -- Apply the mathlib version of the IVT on the function f, 
    -- restricted to the interval we're interesting in
    obtain ⟨⟨y, hy1⟩, hy2⟩ := mem_range_of_exists_le_of_exists_ge (continuous_on_iff_continuous_restrict.mp h1) 
      ⟨⟨ c + (d - c) / 2, by { split; linarith, }⟩, le_of_lt hlt⟩ ⟨⟨t, ht⟩, h⟩,
    exact h2 y hy1 hy2,
    },
  { apply or.intro_right,
    intros t ht,
    by_contra,
    push_neg at h,
    haveI : preconnected_space ↥(set.Icc c d) := subtype.preconnected_space is_preconnected_Icc,
    obtain ⟨⟨y, hy1⟩, hy2⟩ := mem_range_of_exists_le_of_exists_ge (continuous_on_iff_continuous_restrict.mp h1)
     ⟨⟨t, ht⟩, h⟩ ⟨⟨ c + (d - c) / 2, by { split; linarith, }⟩, le_of_lt hgt⟩,  
    exact h2 y hy1 hy2, },
end

-- This is an obvious statement to anyone who's studied first year analysis and calculus
-- And yet completely non trivial...!
-- hab and hcd shouldn't be necessary but its so hard without :cry:
-- This is just a modification of the version in mathlib to fit my assumptions
lemma strict_mono_on_of_pos_deriv {c d : ℝ} {f : ℝ → ℝ} (hf :  cont_diff_on ℝ ⊤ f (set.Icc c d)) 
  (hs : (∀ s, s ∈ set.Ioo c d → (fderiv ℝ f s) 1 > 0 )) : strict_mono_on f (set.Icc c d) :=
begin
  apply convex.strict_mono_on_of_deriv_pos (convex_Icc c d) (cont_diff_on.continuous_on hf) _,
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
  apply convex.strict_anti_on_of_deriv_neg (convex_Icc c d) (cont_diff_on.continuous_on hf) _,
  intros x hx,
  specialize hs x ((set.ext_iff.mp interior_Icc x).mp hx),
  rw [←deriv_fderiv] at hs,
  dsimp at hs,
  simp only [one_mul] at hs,
  exact hs,
end

-- I asked something about how to prove a modified version of the below lemma in a class and this is how Kevin did it
lemma kevins_version_of_something (f : ℝ → ℝ) (hf : monotone f) (a b c d : ℝ) (hab : a ≤ b) (h : f '' set.Icc c d = set.Icc a b) :
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
  { -- With x = c
    rw hxc at hfxb,
    cases em (a = b),
    { -- With a = b
      have := (set.ext_iff.mp hf (f d)).mp ⟨d, (or.intro_right _ (set.mem_singleton d)), rfl⟩,
      rw h at this,
      exact or.elim this id set.mem_singleton_iff.mp, 
    },
    { -- With a ≠ b
      rw hfxb at hfa,
      exact false.elim (h hfa.symm),
    },
  },
  { -- With x = d
    rw [← set.mem_singleton_iff.mp hxd, hfxb], },
end

-- What a ridiculous thing to need to prove...
lemma two_set_comm (a b : ℝ) : insert a ({b} : set ℝ) = {b, a} :=
begin
  ext, split; exact λ hx, or.comm.mp hx,
end

lemma one {a b c d : ℝ} (hab : a < b) (hcd : c < d) {f : ℝ → ℝ} (hf :  cont_diff_on ℝ ⊤ f (set.Icc c d)) 
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

-- Maths proof in Kevin's discord
lemma norm_deriv_eq_norm_deriv_at_one {n : ℕ} {f : ℝ → euclidean_space ℝ (fin n)} {s : ℝ} 
  : ‖fderiv ℝ f s‖ = ‖fderiv ℝ f s 1‖ := sorry


-- This is an application of the chain rule
lemma deriv_of_parametrisation {n : ℕ} {a b c d : ℝ} {hab : a < b} {hcd : c < d} {φ ψ : ℝ → euclidean_space ℝ (fin n)} 
  (h1 : regular_curve n ψ c d) (h2 : regular_curve n φ a b) {f : ℝ → ℝ} (hp : parametrises h1 h2 f)
  : ∀ s, s ∈ set.uIoo c d → ‖fderiv ℝ ψ s 1‖ = ‖fderiv ℝ f s 1‖ * ‖fderiv ℝ φ (f s) 1‖ :=
begin
  intros s hs,
  obtain ⟨hfcd, hfim, hfderivne0, hfcomp⟩ := hp,
  have hdiffphi : differentiable_at ℝ φ (f s), {
    have : f s ∈ set.uIoo a b, sorry, -- as deriv f ≠ 0 and f c = a and f d = b or vice versa
    apply differentiable_on.differentiable_at (cont_diff_on.differentiable_on h2.1 le_top),
    rw mem_nhds_iff_exists_Ioo_subset,
    refine ⟨a ⊓ b, a ⊔ b, this, λ x hx, set.uIoo_subset_uIcc a b hx⟩,  
  },
  have hdifff : differentiable_at ℝ f s, {
    apply differentiable_on.differentiable_at (cont_diff_on.differentiable_on hfcd le_top),
    rw mem_nhds_iff_exists_Ioo_subset,
    refine ⟨c ⊓ d, c ⊔ d, hs, set.uIoo_subset_uIcc c d⟩,
  },
  -- Worked before changing stuff to uIcc
  rw ←(hfcomp s (set.uIoo_subset_uIcc _ _ hs)),
  rw [fderiv.comp s hdiffphi hdifff],
  dsimp,
  rw [←real.norm_eq_abs _],
  rw ←norm_smul (fderiv ℝ f s 1) (fderiv ℝ φ (f s) 1),
  -- God it was a total nightmare to manage to rw this..
  have comp_smul : (fderiv ℝ φ (f s)) ((fderiv ℝ f s) 1 • 1) = (fderiv ℝ f s) 1 • (fderiv ℝ φ (f s)) 1
    := @linear_map.map_smul_of_tower ℝ (euclidean_space ℝ (fin n)) _ _ _ ℝ _ _ _ _ _ _
    (fderiv ℝ φ (f s)) (fderiv ℝ f s 1) 1,
  rw ←comp_smul,
  
  -- rw smul_one,
  -- rw linear_map.compatible_smul_def,
  -- Why does the coe_smul not deal with compositions ????
  -- rw ←linear_map.smul_eq_comp,
  --- linear map compatible_smul, smul_apply, smul_comp, comp_smul, mul_eq_comp
  -- Goal: ‖⇑(fderiv ℝ φ (f s)) (⇑(fderiv ℝ f s) 1)‖ = ‖⇑(fderiv ℝ f s) 1 • ⇑(fderiv ℝ φ (f s)) 1‖
  sorry,
end

lemma length_invariant_under_parameterisations' {n : ℕ} {a b c d : ℝ} (hab : a < b) (hcd : c < d) {ψ : ℝ → euclidean_space ℝ (fin n)} 
  {φ : ℝ → euclidean_space ℝ (fin n)} {h1 : regular_curve n ψ c d} {h2 : regular_curve n φ a b} (h3 : is_parametrisation h1 h2) 
  : length h1 = length h2 :=
begin
  unfold length,
  obtain ⟨f, hf⟩ := h3,
  have : ∫ (t : ℝ) in c..d, (((λ x, ‖fderiv ℝ φ x‖) ∘ f) t )* ‖fderiv ℝ f t‖ = ∫ (t : ℝ) in (f c)..(f d), ‖fderiv ℝ φ t‖,
    {
      apply interval_integral.integral_comp_mul_deriv,
      { -- Goal: ∀ (x : ℝ), x ∈ set.uIcc c d → has_deriv_at f ‖fderiv ℝ f x‖ x
        intros x hx,
        rw has_deriv_at_iff_has_fderiv_at,
        sorry,
      },
      sorry,
      sorry,
    },
  sorry,
end

-- I think I need c ≤ d and a ≤ b 
lemma length_invariant_under_parameterisations {n : ℕ} {a b c d : ℝ} (hab : a < b) (hcd : c < d) {ψ : ℝ → euclidean_space ℝ (fin n)} 
  {φ : ℝ → euclidean_space ℝ (fin n)} {h1 : regular_curve n ψ c d} {h2 : regular_curve n φ a b} (h3 : is_parametrisation h1 h2) 
  : length h1 = length h2 :=
begin
  -- obtain ⟨f, hf⟩ := h3,
  -- have him := one hab hcd hf.1 hf.2.1,
  -- have hfc : continuous_on (λ (t : ℝ), ‖fderiv ℝ f t‖) (set.Icc c d), sorry,
  -- have := @fderiv.comp ℝ _ ℝ _ _ ℝ _ _ _ _ _ f (sorry) φ,
  -- rcases continuous_on.all_lt_or_all_gt_of_ne (le_of_lt hcd) hfc hf.2.2.1 with (h | h),
  -- { have : f c = b ∧ f d = a, {
  --     apply him.2,
  --     intros s hs,
  --     have : ‖fderiv ℝ f s‖ = (fderiv ℝ f s) 1, {
  --       sorry,
  --     },
  --     rw ←this,
  --     exact h s (set.Ioo_subset_Icc_self hs),
  --   },
  --   unfold length, rw [←this.1, ←this.2],
  --   have : ∫ (t : ℝ) in c..d, ‖fderiv ℝ ψ t‖ = ∫ (t : ℝ) in c..d, ‖fderiv ℝ (φ ∘ f) t‖, 
  --   {
  --     apply interval_integral.integral_congr,
  --     intros x hx,
  --     dsimp,
  --     rw set.uIcc_of_le (le_of_lt hcd) at hx,
  --     have : ‖fderiv ℝ (φ ∘ f) x‖ = ‖fderiv ℝ φ (f x)‖, sorry, -- true because deriv f is 1
  --     rw this,
  --     -- this is true because of some kind of congruence of function composition
  --     sorry,
  --   },
  --   rw [this],
  --   -- ∘ f is too deep in the function to apply this ...
  --   -- apply @interval_integral.integral_comp_smul_deriv ℝ _ _ _ c d f,
  --   sorry, },
  { sorry, },
end

-- TODO: arc length parametrised regular curve
-- lemma, every regular curve can be parameterised by arc length

-- THIS IS THE END OF CHAPTER 1!