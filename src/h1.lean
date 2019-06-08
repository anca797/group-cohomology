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

def cocycle.condition (f : cocycle G M) : ∀ (g h : G), f (g * h) = f g + g • (f h) :=
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

 example (g : G) :  g • (0 : M) = 0 := by library_search

-- notation
instance : has_zero (cocycle G M) := ⟨zero M⟩

/-- addition of cocycles -/
def add (e f : cocycle G M) : cocycle G M :=
⟨λ g, e g + f g, begin 
intro g,
intro h,
cases e with eval eprop,

/- should follow from def of cocyle and G_module.linear-/
sorry

end⟩

-- notation
instance : has_add (cocycle G M) := ⟨add M⟩

/-- negation of a cocycle -/
def neg (f : cocycle G M) : cocycle G M :=
⟨λ g, -(f g), begin 
intro g,
intro h,

sorry end⟩

-- notation
instance : has_neg (cocycle G M) := ⟨neg M⟩

-- proof that cocycles form a group
instance : add_comm_group (cocycle G M) :=
{ add := (+),
  add_assoc := begin
  intros a b c,
  sorry
  end,
  zero := 0,
  zero_add := sorry,
  add_zero := sorry,
  neg := has_neg.neg,
  add_left_neg := sorry,
  add_comm := sorry }

end cocycle

def coboundary {M : Type*} [add_comm_group M] [G_module G M] := {f : cocycle G M | ∃ m : M, ∀ g : G, f g = g • m - m}

