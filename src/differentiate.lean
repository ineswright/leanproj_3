/-
Heavily based off the measurability tactic by Remy D??
-/
import tactic.auto_cases
import tactic.tidy
import tactic.with_local_reducibility

/-!
### `differentiate` tactic

Automatically solve goals of the form `fderv f`.

Mark lemmas with `@[differentiate]` to add them to the set of lemmas
used by `differentiate`. 
-/

/-- User attribute used to mark tactics used by `differentiate`. -/
@[user_attribute]
meta def differentiate : user_attribute :=
{ name := `differentiate,
  descr := "lemmas usable to prove differentiate" }

/- Mark some lemmas already defined in ... -/
-- attribute [measurability]

namespace tactic

/--
Tactic to apply `measurable.comp` when appropriate.

Applying `measurable.comp` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove measurable is actually
  constant, and that constant is a function application `f z`, then
  measurable.comp would produce new goals `measurable f`, `measurable
  (λ _, z)`, which is silly. We avoid this by failing if we could
  apply `measurable_const`.

* measurable.comp will always succeed on `measurable (λ x, f x)` and
  produce new goals `measurable (λ x, x)`, `measurable f`. We detect
  this by failing if a new goal can be closed by applying
  measurable_id.
-/
meta def apply_measurable.comp : tactic unit :=
`[fail_if_success { exact measurable_const };
  refine measurable.comp _ _;
  fail_if_success { exact measurable_id }]

/--
Tactic to apply `measurable.comp_ae_measurable` when appropriate.

Applying `measurable.comp_ae_measurable` is not always a good idea, so we have some
extra logic here to try to avoid bad cases.

* If the function we're trying to prove measurable is actually
  constant, and that constant is a function application `f z`, then
  `measurable.comp_ae_measurable` would produce new goals `measurable f`, `ae_measurable
  (λ _, z) μ`, which is silly. We avoid this by failing if we could
  apply `ae_measurable_const`.

* `measurable.comp_ae_measurable` will always succeed on `ae_measurable (λ x, f x) μ` and
  can produce new goals (`measurable (λ x, x)`, `ae_measurable f μ`) or
  (`measurable f`, `ae_measurable (λ x, x) μ`). We detect those by failing if a new goal can be
  closed by applying `measurable_id` or `ae_measurable_id`.
-/
meta def apply_measurable.comp_ae_measurable : tactic unit :=
`[fail_if_success { exact ae_measurable_const };
  refine measurable.comp_ae_measurable _ _;
  fail_if_success { exact measurable_id };
  fail_if_success { exact ae_measurable_id }]

/--
We don't want the intro1 tactic to apply to a goal of the form `measurable f`, `ae_measurable f μ`
or `measurable_set s`. This tactic tests the target to see if it matches that form.
 -/
meta def goal_is_not_measurable : tactic unit :=
do t ← tactic.target,
  match t with
  | `(measurable %%l) := failed
  | `(ae_measurable %%l %%r) := failed
  | `(measurable_set %%l) := failed
  | _ := skip
  end

/-- List of tactics used by `measurability` internally. The option `use_exfalso := ff` is passed to
the tactic `apply_assumption` in order to avoid loops in the presence of negated hypotheses in
the context. -/
meta def measurability_tactics (md : transparency := semireducible) : list (tactic string) :=
[
  propositional_goal >> tactic.interactive.apply_assumption none {use_exfalso := ff}
                        >> pure "apply_assumption {use_exfalso := ff}",
  goal_is_not_measurable >> intro1
                        >>= λ ns, pure ("intro " ++ ns.to_string),
  apply_rules [] [``measurability] 50 { md := md }
                        >> pure "apply_rules with measurability",
  apply_measurable.comp >> pure "refine measurable.comp _ _",
  apply_measurable.comp_ae_measurable
                        >> pure "refine measurable.comp_ae_measurable _ _",
  `[ refine measurable.ae_measurable _ ]
                        >> pure "refine measurable.ae_measurable _",
  `[ refine measurable.ae_strongly_measurable _ ]
                        >> pure "refine measurable.ae_strongly_measurable _"
]

namespace interactive
setup_tactic_parser

/--
Solve goals of the form `measurable f`, `ae_measurable f μ`, `ae_strongly_measurable f μ` or
`measurable_set s`. `measurability?` reports back the proof term it found.
-/
meta def measurability
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md                 := if bang.is_some then semireducible else reducible,
    measurability_core := tactic.tidy { tactics := measurability_tactics md, ..cfg },
    trace_fn           := if trace.is_some then show_term else id in
trace_fn measurability_core

/-- Version of `measurability` for use with auto_param. -/
meta def measurability' : tactic unit := measurability none none {}

/--
`measurability` solves goals of the form `measurable f`, `ae_measurable f μ`,
`ae_strongly_measurable f μ` or `measurable_set s` by applying lemmas tagged with the
`measurability` user attribute.

You can also use `measurability!`, which applies lemmas with `{ md := semireducible }`.
The default behaviour is more conservative, and only unfolds `reducible` definitions
when attempting to match lemmas with the goal.

`measurability?` reports back the proof term it found.
-/
add_tactic_doc
{ name := "measurability / measurability'",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.measurability, `tactic.interactive.measurability'],
  tags := ["lemma application"] }

end interactive

end tactic
