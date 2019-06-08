import algebra.module group_theory.subgroup

class group_module (G : Type*) [group G] (M : Type*) [add_comm_group M] extends has_scalar G M :=
(one_smul : ∀ m : M, (1 : G) • m = m)
(smul_smul : ∀ g h : G, ∀ m : M, g • (h • m) = (g * h) • m)
(smul_add : ∀ g : G, ∀ m n : M, g • (m + n) = g • m + g • n)

namespace group_module

variables {G : Type*} [group G] {M : Type*} [add_comm_group M] [group_module G M]

variables (M)
instance is_add_group_hom_smul (g : G) : is_add_group_hom ((•) g : M → M) :=
⟨group_module.smul_add g⟩

lemma smul_zero (g : G) : g • (0 : M) = 0 :=
is_add_group_hom.zero _
variables {M}

lemma smul_neg (g : G) (m : M) : g • (-m) = -(g • m) :=
is_add_group_hom.neg _ _

definition fixed_points (G : Type*) [group G] (M : Type*) [add_comm_group M] [group_module G M] : set M :=
{m : M | ∀ g : G, g • m = m}

instance fixed_points.is_add_subgroup : is_add_subgroup (fixed_points G M) :=
{ add_mem := λ m n hm hn g, by rw [smul_add, hm g, hn g],
  zero_mem := smul_zero M,
  neg_mem := λ m hm g, by rw [smul_neg, hm g] }

definition H0 (G : Type*) [group G] (M : Type*) [add_comm_group M] [group_module G M] :=
fixed_points G M

instance H0.add_comm_group : add_comm_group (H0 G M) :=
{ add_comm := λ m n, subtype.eq $ add_comm _ _,
  .. @subtype.add_group _ _ _ fixed_points.is_add_subgroup }

end group_module

variables {G : Type*} [group G] {M : Type*} [add_comm_group M] [group_module G M]
variables {N : Type*} [add_comm_group N] [group_module G N]

variable (G)

def is_group_module_hom (f : M → N) : Prop :=
∀ g : G, ∀ m : M, f (g • m) = g • (f m)

namespace is_group_module_hom
open group_module

def map_H0 (f : M → N) (hf : is_group_module_hom G f) (x : H0 G M) : H0 G N :=
⟨f x.1, λ g, by rw [← hf, x.2]⟩

lemma id.group_module_hom : is_group_module_hom G (id : M → M) :=
λ g m, rfl

end is_group_module_hom