import tactic
import topology.basic
import topology.continuous_function.basic
import topology.unit_interval

universes u v
variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]

def homotopy {f : X × (set.Icc 0 1) → Y} := continuous f




