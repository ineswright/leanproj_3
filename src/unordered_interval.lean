-- Copied from the version in Mathlib
import order.bounds.basic
import data.set.intervals.basic
import data.set.intervals.unordered_interval

open function order_dual (to_dual of_dual)

variables {α β : Type*}

namespace set
section lattice
variables [lattice α] {a a₁ a₂ b b₁ b₂ c x : α}

def uIoo (a b : α) : set α := Ioo (a ⊓ b) (a ⊔ b)

lemma Ioo_subset_uIoo (a b : α) : Ioo a b ⊆ uIoo a b := Ioo_subset_Ioo inf_le_left le_sup_right

lemma uIoo_subset_uIcc (a b : α) : uIoo a b ⊆ uIcc a b := Ioo_subset_Icc_self

end lattice
end set 

