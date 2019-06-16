import h0
import group_theory.quotient_group

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

  instance (G : Type*) [group G] (M : Type*) [add_comm_group M] [G_module G M]
  : add_comm_group (H1 G M) := quotient_add_group.add_comm_group (coboundary G M)


def cocycle.map (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] :
  cocycle G A → cocycle G B :=
λ c, ⟨λ g, f (c g), begin 
intros g h,
rw cocycle.condition A c,
rw G_module_hom.add G f (c g) (g • (c h)),
rw G_module_hom.G_hom f g,
end⟩

lemma coboundary.map (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] (c : cocycle G A) :
  c ∈ coboundary G A → cocycle.map G f c ∈ coboundary G B := 
  begin
  intro hc,
  cases hc with m hm,
  use f m,
  change ∀ (g : G), f (c g) = g • f m - f m,
  intro g,
  rw hm,
  simp,
  rw [G_module_hom.add G f (-m) (g • m), G_module_hom.G_hom f g, is_add_group_hom.map_neg f m],
  end

  /-
  bad lean:

  unfold coe_fn has_coe_to_fun.coe,
  unfold cocycle.map,
  dsimp,
  unfold coe_fn has_coe_to_fun.coe,
  dsimp,
  I also used set_option pp.notation false (temporarily) because 
  I couldn't remember what the actual function name was for the notation ⇑.
  in the main Lean window, if you type #print notation ⇑ it tells you the name 
  of the function, and if you hover over the ⇑ it tells you the keyboard shortcut.
  -/

instance (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] :
  is_add_group_hom (cocycle.map G f) :=
{ map_add := begin 
  intros a b,
  show cocycle.map G f (a + b) = (cocycle.map G f a) + (cocycle.map G f b),
  cases a with a ha,
  cases b with b hb,
  apply cocycle.eq,
  ext g,
  show f (a g + b g)  = f (a g) + f (b g),
  rw G_module_hom.add G f (a g) (b g),
  end }

--variables 
--  {A : Type*} [add_comm_group A] [G_module G A]
--  {B : Type*} [add_comm_group B] [G_module G B]

instance : normal_add_subgroup (coboundary G M) := normal_add_subgroup_of_add_comm_group (coboundary G M)

def H1_f (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] :
  H1 G A → H1 G B := quotient_add_group.map (coboundary G A) (coboundary G B)
    (cocycle.map G f) (coboundary.map G f)

instance (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] :
  is_add_group_hom (H1_f G f) := { map_add := sorry }    

open set function is_add_group_hom

/- First attempt of delta

noncomputable def delta (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  (f : A → B) [G_module_hom G f]
  (g : B → C) [G_module_hom G g]
  (hfg : short_exact f g) : H0 G C → H1 G A :=
λ c, begin
  rcases hfg with ⟨hf, hg, hfg⟩,
  choose b hb using (hg c.val),
  apply quotient.mk,
  let h : G → A,
  { intro γ,
    let b' := γ • b - b,
    have hb' : b' ∈ ker g,
    { rw mem_ker,
      rw is_add_group_hom.map_sub g,
      rw sub_eq_zero,
      rw G_module_hom.G_hom g,
      rw hb,
      exact c.property γ,
      apply_instance,
    },
    change set.range f = ker g at hfg,
    rw ←hfg at hb',
    choose a ha using hb',
    exact a
  },
  use h,
  sorry -- TODO (KMB will try this)
end
-/

noncomputable def delta_b (G : Type*) [group G]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {g : B → C} [G_module_hom G g]
  (hg : surjective g) : H0 G C → B :=
λ c, classical.some (hg c.val)

lemma delta_im_b (G : Type*) [group G]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {g : B → C} [G_module_hom G g]
  (hg : surjective g) (c : H0 G C) :
  g (delta_b G hg c) = c.val := classical.some_spec (hg c.val)

lemma delta_gb_sub_b_mem_ker (G : Type*) [group G]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {g : B → C} [G_module_hom G g]
  (hg : surjective g) (c : H0 G C) (γ : G) :
  γ • (delta_b G hg c) - (delta_b G hg c) ∈ ker g :=
by rw [mem_ker, is_add_group_hom.map_sub g, sub_eq_zero,
  G_module_hom.G_hom g γ, delta_im_b G hg c, c.property γ]

def delta_cocycle_ex_a (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {f : A → B} [G_module_hom G f]
  {g : B → C} [G_module_hom G g]
  (hg : surjective g) (hfg : range f = ker g)
  (c : H0 G C) (γ : G) :
  ∃ a : A, f a = γ • (delta_b G hg c) - (delta_b G hg c) :=
begin
  show γ • (delta_b G hg c) - (delta_b G hg c) ∈ range f,
  rw hfg,
  exact delta_gb_sub_b_mem_ker G hg c γ
end

noncomputable def delta_cocycle_aux (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {f : A → B} [G_module_hom G f]
  {g : B → C} [G_module_hom G g]
  (hg : surjective g) (hfg : range f = ker g)
  (c : H0 G C) : G → A :=
  λ γ, classical.some (delta_cocycle_ex_a G hg hfg c γ)

lemma delta_cocycle_aux_a (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {f : A → B} [G_module_hom G f]
  {g : B → C} [G_module_hom G g]
  (hg : surjective g) (hfg : range f = ker g)
  (c : H0 G C) (γ : G) : f (delta_cocycle_aux G hg hfg c γ) =
    γ • (delta_b G hg c) - (delta_b G hg c) :=
classical.some_spec (delta_cocycle_ex_a G hg hfg c γ)

noncomputable def delta_cocycle (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {f : A → B} [G_module_hom G f]
  {g : B → C} [G_module_hom G g]
  (hf : injective f)
  (hg : surjective g) (hfg : range f = ker g)
  (c : H0 G C) : cocycle G A :=
⟨delta_cocycle_aux G hg hfg c,
begin
  intros γ1 γ2,
  apply hf,
  rw delta_cocycle_aux_a G hg hfg,
  rw is_add_group_hom.map_add f,
  rw delta_cocycle_aux_a G hg hfg,
  rw G_module_hom.G_hom f γ1,
  rw delta_cocycle_aux_a G hg hfg,
  rw ←G_module.mul,
  rw G_module.map_sub,
  simp,
end⟩

noncomputable def delta  (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {f : A → B} [G_module_hom G f]
  {g : B → C} [G_module_hom G g]
  (hf : injective f)
  (hg : surjective g) (hfg : range f = ker g)
  (c : H0 G C) : H1 G A :=
  quotient_add_group.mk (delta_cocycle G hf hg hfg c)

instance
  (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {f : A → B} [G_module_hom G f]
  {g : B → C} [G_module_hom G g]
  (hf : injective f)
  (hg : surjective g) (hfg : range f = ker g)
: is_add_group_hom (delta G hf hg hfg) :=
{ map_add := sorry }

  /- H0(G,B) -> H0(G,C) -> H1(G,A) -/
lemma h0b_hoc_h1a_exact (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {f : A → B} [G_module_hom G f]
  {g : B → C} [G_module_hom G g]
  (hf : injective f)
  (hg : surjective g) (hfg : range f = ker g)
  : is_exact (H0_f G g) (delta G hf hg hfg) :=
  begin
  sorry
  end

  /- H0(G,C) -> H1(G,A) -> H1(G,B) -/
lemma h0c_h1a_h1b_exact (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {f : A → B} [G_module_hom G f]
  {g : B → C} [G_module_hom G g]
  (hf : injective f)
  (hg : surjective g) (hfg : range f = ker g)
  : is_exact (delta G hf hg hfg) (H1_f G f) :=
  begin
  sorry
  end

  /- H1(G,A) -> H1(G,B) -> H1(G,C) -/
  lemma h1a_h1b_h1c_exact (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {f : A → B} [G_module_hom G f] 
  {g : B → C} [G_module_hom G g] 
  (hf : injective f)
  (hg : surjective g) (hfg : range f = ker g)
  : is_exact (H1_f G f) (H1_f G g) :=
  begin
  sorry
  end
