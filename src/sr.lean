import data.real.basic tactic 

noncomputable theory -- v4abs does not need to be computable, don't care about it.

local notation `⟨╯°□°⟩╯︵┻━┻` := sorry

structure v₄  : Type := (x y z t : ℝ)

#check (⟨ 0, 0, 0, 1⟩ : v₄)

def v₄abs (v : v₄ ) : ℝ  := real.sqrt(v.x^2 + v.y^2 + v.z^2 + v.t^2)

notation `|`x`|` := v₄abs x

example : |(⟨0,0,0,2⟩)| = 2 := by norm_num [v₄abs]

def v₄add (v₁ v₂ : v₄) : v₄ := ⟨v₁.x + v₂.x, v₁.y + v₂.y, v₁.z + v₂.z, v₁.t + v₂.t⟩
def v₄neg (v: v₄) : v₄ := ⟨-v.x, -v.y, -v.z, -v.t⟩

example : v₄add ⟨ 0, 0, 0, 1⟩ ⟨1, 1, 1, 0 ⟩ = ⟨1, 1, 1, 1⟩ := by norm_num [v₄add]

def v₄zero : v₄ := ⟨0,0,0,0⟩ 

-- If we prove that v₄ is an add_comm group, then we get subtraction and infix notation for free
-- That's an instance btw.

-- To autogenerate the skeleton, place a '_' after the := and then click the lightbulb
instance : add_comm_group v₄ := 
{ add := v₄add,
  add_assoc := 
  begin
    intros a b c,
    dsimp only [v₄add], -- unfold definition of equality (definitional simp)
    -- only tells Lean to only apply that lemma.
    congr' 1; -- only applie congruence 1 level deep
    rw add_assoc,
  end,
  zero := v₄zero,
  zero_add := 
  begin
    intro a,
    --dsimp only [v₄zero, v₄add, (+)],
    cases a,
    -- change is to replace the goal with a goal that is definitionally equal
    -- () every time you specify a type
    change (⟨0 + a_x, 0 + a_y, 0 + a_z, 0 + a_t⟩ : v₄) = _,
    congr' 1;
    rw zero_add,
  end,
  add_zero :=
  begin
    intro a,
    -- the cases here is needed because the right hand side is an ⟨_,_,_,_⟩, and needs to 
    -- be unfolded
    cases a,
    change (⟨a_x + 0, a_y + 0, a_z + 0, a_t + 0⟩ : v₄) = _,
    congr' 1;
    rw add_zero,
  end,
  neg := v₄neg,
  add_left_neg := 
  begin
    intro a,
    cases a,
    change (⟨-a_x + a_x, -a_y + a_y, -a_z + a_z, -a_t + a_t⟩ : v₄) = _,
    congr' 1;
    rw add_left_neg,
  end,
  add_comm := 
  begin
    intros a b,
    cases a,
    cases b,
    change (⟨a_x + b_x, a_y + b_y, a_z + b_z, a_t + b_t⟩ : v₄) = _,
    congr' 1;
    rw add_comm, 
  end }

--smol ?

-- trying line 487, v - v = 0
-- because we proved it's an add_comm_group, we have `sub_self`, 
example (u v : v₄) : u = v ↔ u - v = 0 :=
begin
-- split,
-- intro h,
-- rw h,
-- rw sub_self,
-- intro h,
-- rwa sub_eq_zero at h,
-- Shing FTW!
rw sub_eq_zero,
end

