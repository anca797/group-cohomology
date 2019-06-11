import h0

variables (G : Type*) [group G] (M : Type*) [add_comm_group M]
[G_module G M]

-- definition of cocycle as a subtype
def cocycle (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
{f : G → M // ∀ g h : G, f (g * h) = f g + g • (f h)}

variable {G} -- I want G to be implicit in this definition

-- so a cocycle is a pair: the function f, and the proof that it satisfies the cocycle identity.

-- This line lets us think about a cocycle as the function.
instance : has_coe_to_fun (cocycle G M) :=
{ F := λ _, G → M,
  coe := λ f, f.1}

theorem cocycle.eq (e f : cocycle G M) : (e : G → M) = f → e = f := subtype.eq


@[simp] def cocycle.condition (f : cocycle G M) : ∀ (g h : G), f (g * h) = f g + g • (f h) :=
  f.property

namespace cocycle

/-- The zero cocycle -/
def zero : cocycle G M := ⟨λ g, 0, begin 
 intro g,
 intro h,
 symmetry,
 calc
 0 + g • (0 : M)  = g • 0 : zero_add _
 ...               = 0 : g_zero g
 end⟩

-- notation
instance : has_zero (cocycle G M) := ⟨zero M⟩

/-- addition of cocycles -/
def add (e f : cocycle G M) : cocycle G M :=
⟨λ g, e g + f g, begin 
intro g,
intro h,
rw cocycle.condition M e,
rw cocycle.condition M f,
rw G_module.linear g (e h) (f h),
simp,


/-
calc
e (g * h) + f (g * h) = e g + g • (e h) + f (g * h) : rw e.condition g h
...                   = e g + g • (e h) + (f g + g • (f h)) : rw f.condition g h
...                   = e g + g • (e h) + g • (f h) + f g : by simp?
...                   = e g + g • (e h + f h) + f g : by rw G_module.linear g (e h) (f h)
...                   = e g + f g +  g • (e h + f h) : by add_comm

-/


end⟩

-- notation
instance : has_add (cocycle G M) := ⟨add M⟩

@[simp] lemma cocycle.cast_add (a b : cocycle G M) (x : G) : ((a+b) x = a x + b x) :=
begin
refl,
end


/-- negation of a cocycle -/
def neg (f : cocycle G M) : cocycle G M :=
⟨λ g, -(f g), begin 
intro g,
intro h,
rw cocycle.condition M f,
rw neg_add,
rw g_neg g (f h),
/-
calc
- f (g * h) = - (f g + g • (f h)) : rw f.condition g h 
...         = - f g - g • (f h) : 
...         = - f g + g (- f h)  : by rw g_neg g (f h)
-/

end⟩

-- notation
instance : has_neg (cocycle G M) := ⟨neg M⟩

-- proof that cocycles form a group
instance : add_comm_group (cocycle G M) :=
{ add := (+),
  add_assoc := begin
  intros a b c,
  apply cocycle.eq,
  ext x,
  simp,
  end,
  zero := 0,
  zero_add := begin
  intro a,
  apply cocycle.eq,
  ext x,
  simp,
  change a x + 0 = a x,
  rw add_zero,
  end,
  add_zero := begin
  intro a,
  apply cocycle.eq,
  ext x,
  change a x + 0 = a x,
  rw add_zero,
  end,
  neg := has_neg.neg,
  add_left_neg := begin
  intro a,
  show -a + a = 0,
  apply cocycle.eq,
  ext x,
  change - a x + a x = 0,
  simp,
  end,
  add_comm := begin
  intros a b,
  apply cocycle.eq,
  ext x,
  change a x + b x = b x + a x,
  rw add_comm,
  end }

end cocycle

def coboundary (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
  {f : cocycle G M | ∃ m : M, ∀ g : G, f g = g • m - m}

instance : is_add_subgroup (coboundary G M) :=
{ zero_mem := begin 
  use 0, 
  intro g,
  rw g_zero g,
  simp,
  refl,
  end,
  add_mem := begin
  intros a b,
  intros ha hb,
  cases ha with m hm,
  cases hb with n hn,
  use m+n,
  simp [hm, hn], 
  end,
  neg_mem := begin
  intro a,
  intro ha,
  cases ha with m hm,
  use -m,
  intro g,
  show - a g = _,
  simp [hm],
  rw g_neg g,
  end }

def H1 (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M] :=
  quotient_add_group.quotient (coboundary G M)

def cocycle.map (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] :
  cocycle G A → cocycle G B :=
λ c, ⟨λ g, f (c g), begin 
intros g h,
rw cocycle.condition A c,
rw G_module_hom.add (c g) (g • c h),
sorry end⟩

lemma coboundary.map (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] (c : cocycle G A) :
  c ∈ coboundary G A → cocycle.map G f c ∈ coboundary G B := 
  begin
  sorry
  end

instance (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] :
  is_add_group_hom (cocycle.map G f) :=
{ map_add := begin sorry end }
