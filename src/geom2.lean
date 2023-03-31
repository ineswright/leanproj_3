import tactic
import analysis.calculus.fderiv
import analysis.calculus.cont_diff
import analysis.inner_product_space.pi_L2
import measure_theory.integral.interval_integral
import geometry
import analysis.calculus.mean_value
import unordered_interval

/-- The tangent line to a regular curve is the straight line which
  best approximates it at a point -/
noncomputable def tangent_line {n : ℕ} {f : ℝ → euclidean_space ℝ (fin n)} {a b : ℝ} 
  (h : regular_curve n f a b) (t₀ : ℝ) : ℝ → euclidean_space ℝ (fin n) 
  := λ t, f t₀ + ((fderiv ℝ f t₀) t)

/-- An equivalent definition of tangent lines for curves in ℝ × ℝ -/
noncomputable def tangent_line2 {f : ℝ → ℝ × ℝ} {a b : ℝ} (h : regular_curve2 f a b) (t₀ : ℝ) 
  : ℝ → ℝ × ℝ := λ t, f t₀ + ((fderiv ℝ f t₀) t)

/-- An equivalent definition of tangent lines for curves in ℝ × ℝ × ℝ -/
noncomputable def tangent_line3 {f : ℝ → ℝ × ℝ × ℝ} {a b : ℝ} (h : regular_curve3 f a b) (t₀ : ℝ) 
  : ℝ → ℝ × ℝ × ℝ := λ t, f t₀ + ((fderiv ℝ f t₀) t)

lemma is_smooth_tangent_map {n : ℕ} {f : ℝ → euclidean_space ℝ (fin n)} {a b : ℝ} 
  (h : regular_curve n f a b) {t₀ : ℝ} : cont_diff_on ℝ ⊤ (tangent_line h t₀) (set.Ioo a b) := 
begin
  unfold tangent_line,
  cont_differentiability,
  -- Goal: cont_diff_on ℝ ⊤ (λ (x : ℝ), ⇑(fderiv ℝ f t₀) x) (set.Ioo a b)
  -- I proved this initially and later discovered it was the wrong proof
  have hdcontdiff : cont_diff_on ℝ ⊤ (fderiv_within ℝ f (set.Ioo a b)) (set.Ioo a b),
  { apply cont_diff_on.fderiv_within (cont_diff_on.mono h.1 _) (unique_diff_on_Ioo a b) le_top,
    exact set.subset.trans (set.Ioo_subset_uIoo a b) (set.uIoo_subset_uIcc _ _),
  },
  have hdcontdiff0 : cont_diff_on ℝ ⊤ (fderiv_within ℝ f (set.Icc a b) t₀) (set.Ioo a b),
  { have : cont_diff_on ℝ ⊤ (fderiv_within ℝ f set.univ t₀) (set.uIoo a b), sorry,
    -- I keep trying to prove the wrong thing!
    have thisiswrong := cont_diff_on.fderiv_of_open (cont_diff_on.mono h.1 
      (set.uIoo_subset_uIcc a b)) (is_open_Ioo) (le_top : ⊤ + 1 ≤ ⊤),
    apply cont_diff_on.congr_mono this (λ x hx, _) (set.Ioo_subset_uIoo a b),
    -- This should be fderiv_within.mono or something but I can't find it
    -- Could potentially need unique_diff_on.eq and unique_diff_on_univ with ℝ
    -- There is also unique_diff_on_Icc and for other intervals 
    sorry, },
  apply cont_diff_on.congr hdcontdiff0 _,
  suffices : ∀ (x : set.Ioo a b), fderiv ℝ f t₀ x = fderiv_within ℝ f (set.Icc a b) t₀ x,
  { -- Goal: that the above is sufficient
    exact λ x hx, this ⟨x, hx⟩, },
  { -- Goal: that the above is true
    have : ∀ x, x ∈ set.Ioo a b → fderiv_within ℝ f set.univ t₀ x = fderiv_within ℝ f 
      (set.Icc a b) t₀ x, 
    { intros x hx,
      -- See above about fderiv_within.mono
      sorry, },
    rintro ⟨x, hx⟩,
    rw ←fderiv_within_univ,
    exact this x hx,
  },
end

/-- ψ is a parametrisation of φ if there exists some f such that φ ∘ f = ψ 
  under some additional conditions -/
def is_parametrisation {n : ℕ} {a b c d : ℝ} {ψ : ℝ → euclidean_space ℝ (fin n)} 
  {φ : ℝ → euclidean_space ℝ (fin n)} (h1 : regular_curve n ψ c d) (h2 : regular_curve n φ a b) 
  := ∃ f : ℝ → ℝ, cont_diff_on ℝ ⊤ f (set.uIcc c d) ∧ f '' {c, d} = {a, b} ∧ 
    (∀ t : ℝ, t ∈ set.uIcc c d → norm (fderiv ℝ f t) ≠ 0) ∧
    (∀ t, t ∈ set.uIcc c d → φ ∘ f = ψ)

/-- f is a specific parametrisation for ψ of φ if it witnesses is_parametrisation -/
def parametrises {n : ℕ} {a b c d : ℝ} {ψ : ℝ → euclidean_space ℝ (fin n)} 
  {φ : ℝ → euclidean_space ℝ (fin n)} (h1 : regular_curve n ψ c d) (h2 : regular_curve n φ a b) 
  (f : ℝ → ℝ) := cont_diff_on ℝ ⊤ f (set.uIcc c d) ∧ f '' {c, d} = {a, b} ∧ 
    (∀ t : ℝ, t ∈ set.uIcc c d → norm (fderiv ℝ f t) ≠ 0) ∧
    (∀ t, t ∈ set.uIcc c d → φ ∘ f = ψ)

lemma is_parametrisation_of_parametrises {n : ℕ} {a b c d : ℝ} (hab : a < b) (hcd : c < d) 
  {ψ : ℝ → euclidean_space ℝ (fin n)} {φ : ℝ → euclidean_space ℝ (fin n)}
  (h1 : regular_curve n ψ c d) (h2 : regular_curve n φ a b) (f : ℝ → ℝ) (hp : parametrises h1 h2 f)
  : is_parametrisation h1 h2 := 
begin
  refine ⟨f, _⟩,
  unfold parametrises at hp,
  exact hp,
end 

/-- The length of a regular curve is defined to be the standard integral
of the norm of it's derivative -/
noncomputable def length {n : ℕ} {f : ℝ → euclidean_space ℝ (fin n)} {a b : ℝ} 
  (h : regular_curve n f a b) : ℝ := ∫ t in a..b, norm (fderiv ℝ f t)  

/-- An equivalent definition of length for curves in ℝ × ℝ -/
noncomputable def length2 {f : ℝ → ℝ × ℝ} {a b : ℝ} (h : regular_curve2 f a b) : ℝ 
  := ∫ t in a..b, norm (fderiv ℝ f t) 

/-- An equivalent definition of length for curves in ℝ × ℝ × ℝ -/
noncomputable def length3 {f : ℝ → ℝ × ℝ × ℝ} {a b : ℝ} (h : regular_curve3 f a b) : ℝ 
  := ∫ t in a..b, norm (fderiv ℝ f t) 

-- This should absolutely be in Mathlib. I only found the proof for it on the day
-- of the deadline and had looked for something which did this so many times in working
-- with my sublemmas
lemma fderiv_deriv_general {f : ℝ → ℝ} {x t : ℝ} 
  : (fderiv ℝ f x : ℝ →L[ℝ] ℝ) t = (deriv f x) * t :=
begin
  rw [←fderiv_deriv, ←mul_one t, ←smul_eq_mul, map_smul, smul_eq_mul, algebra.id.smul_eq_mul, 
    mul_one],
  exact mul_comm _ _,
end

lemma continuous_on.all_lt_or_all_gt_of_ne {c d : ℝ} (hcd : c ≤ d ){f : ℝ → ℝ } 
  (h1 : continuous_on f (set.Icc c d)) (h2 : ∀ t, t ∈ set.Icc c d → f t ≠ 0) 
  : (∀ t, t ∈ set.Icc c d → f t < 0) ∨ (∀ t, t ∈ set.Icc c d → f t > 0) :=
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
    obtain ⟨⟨y, hy1⟩, hy2⟩ := mem_range_of_exists_le_of_exists_ge 
      (continuous_on_iff_continuous_restrict.mp h1) ⟨⟨ c + (d - c) / 2, by { split; linarith, }⟩, 
      le_of_lt hlt⟩ ⟨⟨t, ht⟩, h⟩,
    exact h2 y hy1 hy2,
    },
  { apply or.intro_right,
    intros t ht,
    by_contra,
    push_neg at h,
    haveI : preconnected_space ↥(set.Icc c d) := subtype.preconnected_space is_preconnected_Icc,
    obtain ⟨⟨y, hy1⟩, hy2⟩ := mem_range_of_exists_le_of_exists_ge 
      (continuous_on_iff_continuous_restrict.mp h1) ⟨⟨t, ht⟩, h⟩ ⟨⟨ c + (d - c) / 2, 
      by { split; linarith, }⟩, le_of_lt hgt⟩,  
    exact h2 y hy1 hy2, },
end

lemma strict_mono_on_of_pos_deriv {c d : ℝ} {f : ℝ → ℝ} (hf :  cont_diff_on ℝ ⊤ f (set.Icc c d)) 
  (hs : (∀ s, s ∈ set.Ioo c d → (fderiv ℝ f s) 1 > 0 )) : strict_mono_on f (set.Icc c d) :=
begin
  apply convex.strict_mono_on_of_deriv_pos (convex_Icc c d) (cont_diff_on.continuous_on hf) _,
  exact λ x hx, hs x ((set.ext_iff.mp interior_Icc x).mp hx),
end

lemma strict_anti_on_of_neg_deriv {c d : ℝ} {f : ℝ → ℝ} (hf :  cont_diff_on ℝ ⊤ f (set.Icc c d)) 
  (hs : (∀ s, s ∈ set.Ioo c d → (fderiv ℝ f s) 1 < 0 )) : strict_anti_on f (set.Icc c d) :=
begin
  apply convex.strict_anti_on_of_deriv_neg (convex_Icc c d) (cont_diff_on.continuous_on hf) _,
  exact λ x hx, hs x ((set.ext_iff.mp interior_Icc x).mp hx),
end

lemma image_f_eq_uIcc {f : ℝ → ℝ} {a b c d : ℝ} {hfim : f '' {c, d} = {a, b}} 
  (hfderiv : ∀ t, fderiv ℝ f t ≠ 0) (hfcderiv : continuous (fderiv ℝ f))
  : f '' (set.uIcc c d) = set.uIcc a b :=
begin
  rw set.ext_iff,
  intros x,
  split; intros hx, 
  { -- Goal: x ∈ f '' set.uIcc c d → x ∈ set.uIcc a b
    obtain ⟨y, hy, rfl⟩ := hx,
    by_contra,
    -- We should find that if f y ∉ set.uIcc a b, then the deriv from min (c d) to f y is neg/pos
    -- and the deriv from f y to max (c d) is pos/neg 
    -- by IVT on the derivative (which is continuous by assumption)
    -- we find somewhere where the derivative is 0. Contradiction by hfderiv
    sorry,
  },
  { -- Goal: x ∈ set.uIcc a b → x ∈ f '' set.uIcc c d
    -- f is continuous as it has a derivative
    -- then this is an application of the IVT on f
    sorry,
  },

end

lemma something {f : ℝ → ℝ} {a b c d : ℝ} (hfa : f c = a) (hf : f '' {c, d} = {a, b}) : f d = b :=
begin
  obtain ⟨x, hxcd, hfxb⟩ := (set.ext_iff.mp hf b).mpr (set.mem_insert_iff.mpr (or.intro_right _ 
    (set.mem_singleton b))),
  obtain ⟨y, hycd, hfya⟩ := (set.ext_iff.mp hf a).mpr (set.mem_insert_iff.mpr (or.intro_left _ 
    rfl)), 
  rcases hxcd with (hxc | hxd),
  { -- With x = c
    rw hxc at hfxb,
    cases em (a = b),
    { -- With a = b
      have := (set.ext_iff.mp hf (f d)).mp ⟨d, (or.intro_right _ (set.mem_singleton d)), rfl⟩,
      rw h at this,
      exact or.elim this id set.mem_singleton_iff.mp, },
    { -- With a ≠ b
      rw hfxb at hfa,
      exact false.elim (h hfa.symm), },
  },
  { -- With x = d
    rw [← set.mem_singleton_iff.mp hxd, hfxb], },
end

lemma two_set_comm (a b : ℝ) : insert a ({b} : set ℝ) = {b, a} :=
begin
  ext, split; exact λ hx, or.comm.mp hx,
end

lemma one {a b c d : ℝ} (hab : a < b) (hcd : c < d) {f : ℝ → ℝ} 
  (hf :  cont_diff_on ℝ ⊤ f (set.Icc c d)) (hfim : f '' {c, d} = {a, b}) 
  : ((∀ s, s ∈ set.Ioo c d → (fderiv ℝ f s) 1 > 0 ) → f c = a ∧ f d = b) ∧ 
    ((∀ s, s ∈ set.Ioo c d → (fderiv ℝ f s) 1 < 0) → f c = b ∧ f d = a) := 
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
      have : f c < f d := (strict_mono_on_of_pos_deriv hf hs) ⟨le_of_eq rfl, le_of_lt hcd⟩ 
        ⟨le_of_lt hcd, le_of_eq rfl⟩ hcd,
      rw [thisb, thisa] at this,
      exact (not_lt_of_gt this) hab, },
    exact ⟨this, (something this hfim)⟩, },
  { -- Goal: deriv is neg implies f c = b ∧ f d = a
    intro hs,
    have : f c = b, {
      by_contra,
      apply (not_lt_of_gt _) hab,
      have : f c ∈ {a, b},
        { exact (set.ext_iff.mp hfim (f c)).mp ⟨c, (set.mem_insert c {d}), rfl⟩, },
      have thisa : f c = a := set.mem_singleton_iff.mp (or.resolve_right 
        (set.mem_insert_iff.mp this) h),
      have thisb : f d = b := something thisa hfim,
      rw [←thisa, ←thisb],
      exact (strict_anti_on_of_neg_deriv hf hs) ⟨le_of_eq rfl, le_of_lt hcd⟩ 
        ⟨le_of_lt hcd, le_of_eq rfl⟩ hcd,
    },
    rw two_set_comm a b at hfim,
    exact ⟨this, something this hfim⟩, },
end

-- I think this is something which should be in Mathlib, generalised to all linear maps
lemma norm_deriv_eq_norm_deriv_at_one {n : ℕ} {f : ℝ → euclidean_space ℝ (fin n)} {s : ℝ} 
  : ‖fderiv ℝ f s‖ = ‖fderiv ℝ f s 1‖ := 
begin
  rw continuous_linear_map.norm_def,
  sorry,
end

-- This is an application of the chain rule
lemma deriv_of_parametrisation {n : ℕ} {a b c d : ℝ} {hab : a < b} {hcd : c < d} 
  {φ ψ : ℝ → euclidean_space ℝ (fin n)} (h1 : regular_curve n ψ c d) (h2 : regular_curve n φ a b) 
  {f : ℝ → ℝ} (hp : parametrises h1 h2 f) : ∀ s, s ∈ set.uIoo c d → 
  ‖fderiv ℝ ψ s 1‖ = ‖fderiv ℝ f s 1‖ * ‖fderiv ℝ φ (f s) 1‖ :=
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
  rw [←(hfcomp s (set.uIoo_subset_uIcc _ _ hs)), fderiv.comp s hdiffphi hdifff],
  dsimp,
  rw [←real.norm_eq_abs _, ←norm_smul (fderiv ℝ f s 1) (fderiv ℝ φ (f s) 1)],
  -- Rw can't manage this unless I specify the exact type.
  have comp_smul : (fderiv ℝ φ (f s)) ((fderiv ℝ f s) 1 • 1) = (fderiv ℝ f s) 1 • 
    (fderiv ℝ φ (f s)) 1 := @linear_map.map_smul_of_tower ℝ (euclidean_space ℝ (fin n)) _ _ _ ℝ 
    _ _ _ _ _ _ (fderiv ℝ φ (f s)) (fderiv ℝ f s 1) 1,
  rw ←comp_smul,
  -- Thanks Kevin for the last two lines
  rw [fderiv_deriv],
  simp only [algebra.id.smul_eq_mul, mul_one],
end

lemma length_invariant_under_parameterisations {n : ℕ} {a b c d : ℝ} 
  {ψ : ℝ → euclidean_space ℝ (fin n)} {φ : ℝ → euclidean_space ℝ (fin n)} 
  {h1 : regular_curve n ψ c d} {h2 : regular_curve n φ a b} (h3 : is_parametrisation h1 h2) 
  : length h1 = length h2 :=
begin
  unfold length,
  obtain ⟨f, hf⟩ := h3,
  have : ∫ (t : ℝ) in c..d, (((λ x, ‖fderiv ℝ φ x‖) ∘ f) t )* ‖fderiv ℝ f t‖ = 
    ∫ (t : ℝ) in (f c)..(f d), ‖fderiv ℝ φ t‖,
  { -- An application of the change in variables rule for integration
    apply interval_integral.integral_comp_mul_deriv,
    { -- Goal: ∀ (x : ℝ), x ∈ set.uIcc c d → has_deriv_at f ‖fderiv ℝ f x‖ x
      intros x hx,
      rw has_deriv_at_iff_has_fderiv_at,
      sorry, },
    { -- Goal: continuous_on (λ (x : ℝ), ‖fderiv ℝ f x‖) (set.uIcc c d)
      -- An application of the continuity tactic here reduces this to a 
      -- statement on filters and nhds.
      apply continuous_on.comp (continuous_iff_continuous_on_univ.mp continuous_norm) _ 
        (set.maps_to_univ _ _),
      -- Goal: continuous_on (λ (x : ℝ), fderiv ℝ f x) (set.uIcc c d)
      apply cont_diff_on.continuous_on_fderiv_of_open hf.1 _ le_top,
      -- Goal: is_open (set.uIcc c d)
      -- This is not true! See the report for an explanation of the problem
      sorry, }, 
    { -- Goal: continuous (λ (x : ℝ), ‖fderiv ℝ φ x‖)
      apply continuous.comp continuous_norm _,
      -- Goal: continuous (λ (x : ℝ), fderiv ℝ φ x)
      -- Again, see report.
      sorry, },
  },
  dsimp at this,
  sorry,
end