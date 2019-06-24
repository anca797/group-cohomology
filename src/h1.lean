import h0
import group_theory.quotient_group

theorem function.lift_aux {X : Type*} {Y : Type*} {Z : Type*} (f : X → Y)
(i : Z → Y) (h2 : set.range f ⊆ set.range i) (x : X) : ∃ z : Z, i z = f x :=
begin
show f x ∈ set.range i,
apply h2,
use x, 
end

noncomputable def function.lift {X : Type*} {Y : Type*} {Z : Type*} (f : X → Y)
(i : Z → Y) (h2 : set.range f ⊆ set.range i) :
(X → Z) :=
λ x, classical.some $ function.lift_aux f i h2 x

theorem function.lift_eq {X : Type*} {Y : Type*} {Z : Type*} (f : X → Y)
(i : Z → Y) (h2 : set.range f ⊆ set.range i) (x : X) :
 i (function.lift f i h2 x) = f x := classical.some_spec $ function.lift_aux f i h2 x
 

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


variable {M}
def mk (m : M) : (cocycle G M) := ⟨λ g, g • m - m,
begin
intros g h,
rw ←G_module.mul,
rw G_module.map_sub,
simp,
end ⟩ 
variable (M)

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

  def map (G : Type*) [group G]
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

noncomputable def lift (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] (hf : function.injective f)
  (x : cocycle G B) (h : set.range x ⊆ set.range f) : (cocycle G A) :=
  ⟨function.lift x f h, begin 
  intros g1 g2,
  apply hf,
  rw function.lift_eq x f,
  rw is_add_group_hom.map_add f,
  rw function.lift_eq x f,
  rw G_module_hom.G_hom f,
  rw function.lift_eq x f,
  exact x.property g1 g2,
  apply_instance,
  end⟩ 

theorem lift_eq (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] (hf : function.injective f)
  (x : cocycle G B) (h : set.range x ⊆ set.range f) :
  (map G f (lift G f hf x h)) = x :=
  begin
  apply cocycle.eq,
  ext g,
  show f (function.lift (x) f h g) = x g,
  rw function.lift_eq x f,
  end


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
  : add_comm_group (H1 G M) 
  := quotient_add_group.add_comm_group (coboundary G M)


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

lemma cocycle.map_mk (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] (ca : cocycle G A) :
  H1_f G f (quotient_add_group.mk ca) = quotient_add_group.mk (cocycle.map G f ca) := rfl

instance (G : Type*) [group G]
  {A : Type*} [add_comm_group A] [G_module G A]
  {B : Type*} [add_comm_group B] [G_module G B]
  (f : A → B) [G_module_hom G f] :
  is_add_group_hom (H1_f G f) := quotient_add_group.map_is_add_group_hom 
  (coboundary G A) (coboundary G B) (cocycle.map G f) (coboundary.map G f) 

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

/- c1,c2 : H0 G C then delta_b(c1) + delta_b(c2) - delta_b(c1+c2) is in ker g-/
lemma delta_mem_ker (G : Type*) [group G]
  {B : Type*} [add_comm_group B] [G_module G B]
  {C : Type*} [add_comm_group C] [G_module G C]
  {g : B → C} [G_module_hom G g]
  (hg : surjective g) (c1 c2 : H0 G C) :
  delta_b G hg c1 + delta_b G hg c2 - delta_b G hg (c1+c2) ∈ ker g :=
begin
rw mem_ker,
rw is_add_group_hom.map_sub g,
rw is_add_group_hom.map_add g,
rw delta_im_b G hg,
rw delta_im_b G hg,
rw delta_im_b G hg,
cases c1 with c1 h1,
cases c2 with c2 h2,
show c1 + c2 - (c1 + c2) = 0,
simp,
end

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
{ map_add := 
begin
intros a b,
show delta G hf hg hfg (a + b) = (delta G hf hg hfg a) + (delta G hf hg hfg b),
unfold delta,
let Q := (quotient_add_group.mk : cocycle G A → H1 G A),
rw ←is_add_group_hom.map_add Q,
have eq' : ∀ x y : cocycle G A, Q x = Q y ↔ -x + y ∈ coboundary G A := λ x y, quotient_add_group.eq,
show Q (delta_cocycle G hf hg hfg (a+b)) = _,
rw eq',
have h := delta_mem_ker G hg a b,
rw ←hfg at h,
cases h with a' ha',
use a',
intro g,
apply hf,
rw is_add_group_hom.map_sub f,
rw G_module_hom.G_hom f g,
rw ha',
cases a with a ha,
cases b with b hb,
show f
      (-delta_cocycle_aux G hg hfg ⟨a + b, _⟩ g +
          (delta_cocycle_aux G hg hfg ⟨a, ha⟩ g
           + delta_cocycle_aux G hg hfg ⟨b, hb⟩ 
         g)) =  _,
rw is_add_group_hom.map_add f,
rw is_add_group_hom.map_add f,
rw is_add_group_hom.map_neg f,
rw delta_cocycle_aux_a G hg hfg,
rw delta_cocycle_aux_a G hg hfg,
rw delta_cocycle_aux_a G hg hfg,
simp,
rw g_neg,
refl,
end }

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
  apply subset.antisymm, 
  { intros fc h,
    rw mem_ker,
    cases h with b hb,
    cases fc with c fc,
    cases b with b propb,
    injection hb,
    change g b = c at h_1,
    unfold delta,
    suffices : delta_cocycle G hf hg hfg ⟨c, fc⟩ ∈ ker (quotient_add_group.mk),
      rw mem_ker at this,
      exact this,
      swap, apply_instance,
      swap, apply_instance,
    rw quotient_add_group.ker_mk,
    let b' : B := delta_b G hg ⟨c, fc⟩,
    have hb' : b' - b ∈ range f,
      have hb'' : b' - b ∈ ker g,
        rw mem_ker,
        rw is_add_group_hom.map_sub g,
        rw delta_im_b G hg ⟨c, fc⟩,
        simp,
      rw h_1,
      simp,
      rw hfg,
      exact hb'',
      cases hb' with a ha,
      unfold delta_cocycle,
      use a,
      intro γ,
      apply hf,
      rw is_add_group_hom.map_sub f,
      rw G_module_hom.G_hom f,
      swap, apply_instance,
      swap, apply_instance,
      show f (delta_cocycle_aux G hg hfg ⟨c, fc⟩ γ) = _,
      rw delta_cocycle_aux_a G hg hfg ⟨c, fc⟩ γ,
      rw ha,
      rw G_module.map_sub,
      change γ • b' - b' = γ • b' - γ • b - (b' - b),
      rw propb,
      simp,
  },
  { intros x h,
    cases x with c fc,
    rw mem_ker at h,
    unfold delta at h,
    rw ←mem_ker quotient_add_group.mk at h,
    --delta_cocycle G hf hg hfg ⟨c, fc⟩ at h,
    sorry
  },
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
  apply subset.antisymm,
  { intros fa h,
    rw mem_ker,
    cases h with c hc,
    rw ←hc,
    unfold delta,
    rw cocycle.map_mk G f (delta_cocycle G hf hg hfg c),
    suffices : (cocycle.map G f (delta_cocycle G hf hg hfg c)) ∈ ker (quotient_add_group.mk),
      rw mem_ker at this,
      exact this,
      swap, apply_instance,
      swap, apply_instance,
    rw quotient_add_group.ker_mk,
    use (delta_b G hg c),
    intro γ,
    change f (delta_cocycle_aux G hg hfg c γ) = _,
    exact delta_cocycle_aux_a G hg hfg c γ,
  },
  { intros x h,
    rw mem_ker at h,
    induction x,
    swap,
    refl,
    unfold H1_f at h,
    change quotient_add_group.mk (cocycle.map G f x) = 0 at h,
    rw ←mem_ker quotient_add_group.mk at h,
    swap,
    apply_instance,
    swap,
    apply_instance,
    rw quotient_add_group.ker_mk at h,
    cases h with b hb,
    change ∀ (g : G), f (x g) = g • b - b at hb,
    let c : C := g b,
    use c,
    intro γ,
    rw ←sub_eq_zero,
    rw ←G_module_hom.G_hom g,
    rw ←is_add_group_hom.map_sub g,
    rw ←mem_ker g,
    rw ←hfg,
    rw ←hb,
    use x γ,
    apply_instance,
    change delta G hf hg hfg ⟨c, _⟩ = quotient_add_group.mk x,
    unfold delta,
    apply quotient_add_group.eq.2,
    have hc : ∀ γ : G, γ • c = c,
      intro γ,
      rw ←sub_eq_zero,
      change γ • g b - g b = 0,
      rw ←G_module_hom.G_hom g,
      rw ←is_add_group_hom.map_sub g,
      rw ←mem_ker g,
      have h1 : γ • b - b ∈ range f,
        rw ←hb,
        use x γ,
      convert h1,
      exact hfg.symm,
      apply_instance,
    let b' : B := delta_b G hg ⟨c, hc⟩,
    have hb' : b - b' ∈ range f,
      have hb'' : b - b' ∈ ker g,
        rw mem_ker,
        rw is_add_group_hom.map_sub g,
        rw delta_im_b G hg ⟨c, hc⟩,
        simp,
    rw hfg,
    exact hb'',
    cases hb' with a ha,
    use a,
    intro g',
    change - (delta_cocycle_aux G hg hfg ⟨c, hc⟩ g') + x g' = g' • a - a,
    apply hf,
    rw is_add_group_hom.map_add f,
    rw is_add_group_hom.map_neg f,
    rw is_add_group_hom.map_sub f,
    rw G_module_hom.G_hom f,
    rw delta_cocycle_aux_a G hg hfg ⟨c, hc⟩ g',
    rw hb,
    rw ha,
    change - (g' • b' - b') + (g' • b - b) = _,
    rw G_module.map_sub,
    simp,
    apply_instance,
  },
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
  apply subset.antisymm,
  { intros fb h,
    rw mem_ker,
    cases h with fa hfa,
    induction fa,
    swap,
    refl,
    change H1_f G f (quotient_add_group.mk fa) = _ at hfa,
    rw ←hfa,
    rw cocycle.map_mk G f fa,
    rw cocycle.map_mk G g,
    suffices : (cocycle.map G g (cocycle.map G f fa)) ∈ ker (quotient_add_group.mk),
      rw mem_ker at this,
      exact this,
      swap, apply_instance,
      swap, apply_instance,
    rw quotient_add_group.ker_mk,
    use 0,
    intro x,
    cases fa with fa pfa,
    show g (f (fa x)) = _,
    rw g_zero,
    rw sub_zero,
    rw ←mem_ker g,
    rw ←hfg,
    use fa x,
  },
  { intros x h,
    induction x,
    swap,
    refl,
    rw mem_ker at h,
    unfold H1_f at h,
    change quotient_add_group.mk (cocycle.map G g x) = 0 at h,
    rw ←mem_ker quotient_add_group.mk at h,
    swap,
    apply_instance,
    swap,
    apply_instance,
    rw quotient_add_group.ker_mk at h,
    cases h with c hc,
    rcases (hg c) with ⟨b, rfl⟩,
    let y := x - cocycle.mk b,
    have hy : range y ⊆ range f,
    {
      rintros b' ⟨γ, rfl⟩,
      rw hfg,
      rw mem_ker,
      change g ( x γ - (γ • b - b)) = 0,
      rw is_add_group_hom.map_sub g,
      rw sub_eq_zero,
      convert hc γ,
      rw is_add_group_hom.map_sub g,
      congr',
      rw G_module_hom.G_hom g,
      apply_instance,
    },
    let z : cocycle G A := cocycle.lift G f hf y hy,
    use quotient_add_group.mk z,
    change quotient_add_group.mk (cocycle.map G f (cocycle.lift G f hf y hy)) = quotient_add_group.mk x,
    rw cocycle.lift_eq,
    apply quotient_add_group.eq.2,
    use b,
    have hb : -y + x = cocycle.mk b,
    {
      show -(x - cocycle.mk b) + x = _,
      simp,
    },
    intro g',
    rw hb,
    refl,
  },
end
