import algebra.group -- for is_add_group_hom
import group_theory.subgroup -- for kernels

open set is_add_group_hom

def is_exact {A B C : Type*} [add_comm_group A] [add_comm_group B] [add_comm_group C]
  (f : A → B) (g : B → C) [is_add_group_hom f] [is_add_group_hom g] : Prop :=
range f = ker g 

#check is_exact