/-
This tactic is mostly a copy of the continuity tactic by Reid Barton,
with some modifications from the measurability tactic by Rémy Degenne
-/
import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility
import tactic.show_term
import analysis.calculus.fderiv
import analysis.special_functions.exp_deriv
import analysis.special_functions.trigonometric.deriv
import analysis.special_functions.log.deriv
/-!
# Tactics for differentiability

### `differentiability` tactic

Automatically solve goals of the form `differentiable f`.

Mark lemmas with `@[differentiability]` to add them to the set of lemmas
used by `differentiability`.
-/

/-- User attribute used to mark tactics used by `differentiability`. 
Attributes used by continuity:
[continuous_multilinear_map.coe_continuous,
 linear_isometry.continuous,
 semilinear_isometry_class.continuous,
 continuous_algebra_map,
 affine_map.homothety_continuous,
 affine_map.line_map_continuous,
 path.truncate_const_continuous_family,
 path.truncate_continuous_family,
 path.continuous_trans,
 continuous.path_trans,
 path.trans_continuous_family,
 path.continuous_uncurry_extend_of_continuous_family,
 path.continuous_symm,
 path.symm_continuous_family,
 path.continuous_extend,
 continuous.path_eval,
 path.continuous,
 unit_interval.continuous_symm,
 continuous.Icc_extend',
 continuous_proj_Icc,
 continuous_linear_equiv.continuous,
 continuous_linear_equiv.continuous_inv_fun,
 continuous_linear_equiv.continuous_to_fun,
 continuous_linear_map.continuous,
 continuous.sqrt,
 real.continuous_sqrt,
 continuous.edist,
 ennreal.continuous_pow,
 continuous_nnnorm,
 continuous_nnnorm',
 continuous_norm,
 continuous_norm',
 continuous.zpow₀,
 continuous.div,
 continuous.inv₀,
 continuous.div_const,
 continuous_abs,
 continuous.star,
 continuous.dist,
 continuous_dist,
 continuous.max,
 continuous.min,
 continuous.sub,
 continuous.div',
 continuous.zsmul,
 continuous.zpow,
 continuous_zsmul,
 continuous_zpow,
 continuous.inv,
 continuous_finset_sum,
 continuous_finset_prod,
 continuous_multiset_sum,
 continuous_multiset_prod,
 continuous.nsmul,
 continuous_nsmul,
 continuous_map.continuous_set_coe,
 continuous_map_class.map_continuous,
 continuous.vadd,
 continuous.const_vadd,
 continuous.const_smul,
 uniform_equiv.continuous_symm,
 uniform_equiv.continuous,
 add_opposite.continuous_op,
 mul_opposite.continuous_op,
 add_opposite.continuous_unop,
 mul_opposite.continuous_unop,
 homeomorph.continuous_symm,
 homeomorph.continuous,
 continuous.connected_components_lift_continuous,
 connected_components.continuous_coe,
 continuous_ulift_up,
 continuous_ulift_down,
 continuous.sigma_map,
 continuous_sigma,
 continuous_sigma_mk,
 continuous_single,
 continuous_mul_single,
 continuous_update,
 continuous_apply_apply,
 continuous_apply,
 continuous_quot_lift,
 continuous_quot_mk,
 continuous.cod_restrict,
 continuous.subtype_mk,
 continuous_subtype_val,
 continuous.sum_map,
 continuous.sum_elim,
 continuous_inr,
 continuous_inl,
 continuous.prod.mk_left,
 continuous.prod.mk,
 continuous.prod_mk,
 continuous_top,
 continuous_bot,
 continuous_induced_dom,]

-/
@[user_attribute]
meta def differentiability : user_attribute :=
{ name := `differentiability,
  descr := "lemmas usable to prove differentiable" }

-- Mark some differentiability lemmas already defined in `algebra.calculus.fderiv`
-- and `analysis.special_functions. ...`
attribute [differentiability]
  differentiable_id
  differentiable_id'
  differentiable_const
  differentiable.mul
  differentiable.div
  -- Need some division something. ?
  differentiable.smul
  differentiable.pow -- for natural powers
  differentiable.add
  differentiable.sub
  differentiable.neg
  differentiable.prod
  differentiable.fst
  differentiable.snd
  differentiable.sum
  differentiable_pi
  differentiable.exp
  differentiable.cexp
  differentiable.log
  differentiable.sin
  differentiable.cos
  differentiable.sinh
  differentiable.cosh
  differentiable.csin
  differentiable.ccos
  differentiable.csinh
  differentiable.ccosh
  -- differentiable.comp
  
namespace tactic
/--
Tactic to apply `differentiable.comp` when appropriate.

Applying `differentiable.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove continuous is actually
  constant, and that constant is a function application `f z`, then
  continuous.comp would produce new goals `differentiable f`, `continuous
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply continuous_const.

* continuous.comp will always succeed on `differentiable (λ x, f x)` and
  produce new goals `differentiable (λ x, x)`, `differentiable f`. We detect
  this by failing if a new goal can be closed by applying
  continuous_id.
-/
meta def apply_differentiable.comp : tactic unit :=
`[fail_if_success { exact differentiable_const };
  refine differentiable.comp _ _;
  fail_if_success { exact differentiable_id }]

-- https://github.com/leanprover-community/mathlib/blob/master/src/measure_theory/tactic.lean
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/differentiability.20tactic
/--
We don't want the intros1 tactic to apply to a goal of the form `differentiable f`. 
This tactic tests the target to see if it matches that form.
 -/
meta def goal_is_not_differentiable : tactic unit :=
do t ← tactic.target,
  match t with
  | `(differentiable _ %%f) := failed
  | _ := skip
  end

/-- List of tactics used by `differentiability` internally. -/
meta def differentiability_tactics (md : transparency := reducible) : list (tactic string) :=
[
  -- This first part is from the measurability tactic
  propositional_goal >> tactic.interactive.apply_assumption none {use_exfalso := ff}
                        >> pure "apply_assumption {use_exfalso := ff}",
  goal_is_not_differentiable >> 
    intros1               >>= λ ns, pure ("intros " ++ (" ".intercalate (ns.map (λ e, e.to_string)))),
  apply_rules [] [``differentiability] 50 { md := md }
                        >> pure "apply_rules with differentiability",
  apply_differentiable.comp >> pure "refine differentiable.comp _ _"
]

namespace interactive
setup_tactic_parser

/--
Solve goals of the form `differentiability f`. `differentiability?` reports back the proof term it found.
-/
meta def differentiability
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md              := if bang.is_some then semireducible else reducible,
    differentiable_core := tactic.tidy { tactics := differentiability_tactics md, ..cfg },
    trace_fn        := if trace.is_some then show_term else id in
trace_fn differentiable_core

/-- Version of `differentiability` for use with auto_param. -/
meta def differentiability' : tactic unit := differentiability none none {}

/--
`differentiable` solves goals of the form `differentiable f` by applying lemmas tagged with the
`differentiable` user attribute.

You can also use `differentiability!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.

`differentiability?` reports back the proof term it found.
-/
add_tactic_doc
{ name := "differentiability / differentiability'",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.differentiability, `tactic.interactive.differentiability'],
  tags := ["lemma application"] }

end interactive
end tactic