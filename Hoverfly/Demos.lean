import Hoverfly.Backend

import Palamedes.Synthesizer
open Gen.CorrectGen


set_option linter.unusedTactic false

@[simp]
def inBounds (lo hi : Int) : Tree Int → Bool
  | .leaf => true
  | .node l x r => lo <= x && x <= hi && inBounds lo hi l && inBounds lo hi r

set_option linter.unreachableTactic false
add_hoverfly_tactics [assumption, contradiction, intro, rfl, subst_eqs,
  rewrite [Eq.comm], rewrite [Nat.add_zero], rewrite [Nat.add_succ],
  apply Exists.intro, apply Nat.le_trans, apply Nat.zero_le, apply Nat.sub_add_cancel]
  -- `(tactic | apply And.intro),
  --   ← `(tactic | apply Exists.intro),
  --   ← `(tactic | apply Nat.le_trans), -- TODO
  --   ← `(tactic | apply Nat.zero_le), -- TODO
  --   ← `(tactic | apply [Nat.sub_add_cancel]),
  --   ← `(tactic | assumption),
  --   ← `(tactic | contradiction),
  --   ← `(tactic | intro),
  --   -- ← `(tactic | intros),
  --   ← `(tactic | rfl),
  --   ← `(tactic | rewrite [Eq.comm]),
  --   ← `(tactic | rewrite [Nat.add_zero]),
  --   ← `(tactic | rewrite [Nat.add_succ]),
  --   -- ← `(tactic | rw [Nat.add_assoc]),
  --   -- ← `(tactic | simp_all),
  --   -- ← `(tactic | skip <;> skip <;> skip <;> skip <;> skip <;> skip),
  --   ← `(tactic | subst_eqs)
  -- ]

def demo_genInBounds (x y : Int): CorrectGen (fun t => inBounds x y t) := by
  hoverfly
  sorry

theorem demo_small (n m x : Nat) : n + x = m → n <= m := by
  intro h
  hoverfly
  sorry

theorem demo_le_trans (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  hoverfly
  sorry

theorem demo_exists : ∃ b, b = b ∧ b ≤ 10 := by
  hoverfly
  sorry

def demo_genEq2 : CorrectGen (· = 2) := by
  hoverfly
  sorry

def demo_genEq2or3 : CorrectGen (fun x => x = 2 ∨ x = 3) := by
  hoverfly
  sorry

@[simp]
def isAllTwos : Tree Nat → Bool
  | .leaf => true
  | .node l x r => x = 2 && isAllTwos l && isAllTwos r

def demo_genAllTwos : CorrectGen (fun t => isAllTwos t) := by
  hoverfly
  sorry

theorem demo_mini : 1 = 1 /\ 2 = 2 := by
  hoverfly
  sorry

theorem demo_long_names (very_very_long_variable_name : Nat) :
  very_very_long_variable_name = 1 ->
  ¬(very_very_long_variable_name = 2) /\ 1 = very_very_long_variable_name := by
  hoverfly
  sorry

theorem demo_medium' (n m x : Nat) : n + x = m → n <= m := by
  hoverfly
  sorry

theorem demo_exists' (x y : Nat) : x + x = y → ∃ z, y = 2 * z := by
  intro
  exists x
  subst_eqs
  lia

theorem demo_medium (n m : Nat) : n <= m → ∃ x, m = x + n:= by
  hoverfly
  sorry
-- Proof 0:
  -- intros
  -- exists (m - n)
  -- rw [Nat.sub_add_cancel]
  -- assumption
-- Proof 1:
  -- apply Nat.exists_eq_add_of_le'
-- Proof 2:
  --  intros
  --  apply Nat.exists_eq_add_of_le'
  --  assumption
-- Proof 2:
  -- induction n
  -- case zero =>
  --   intro m h
  --   exists m
  -- case succ n' h =>
  --   intro m hn'm
  --   cases m
  --   case zero => contradiction
  --   case succ m' =>
  --     specialize h m'
  --     have h' := Nat.le_of_add_le_add_right hn'm
  --     have ⟨x, h⟩ := h h'
  --     exists x
  --     rw [←Nat.add_assoc, Nat.add_one_inj]
  --     assumption

theorem add_assoc (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  hoverfly
  sorry
  -- sorry
  -- induction p with
  -- | zero =>
  --   rewrite [Nat.add_zero]
  --   rewrite [Nat.add_zero]
  --   rfl
  -- | succ p' ih =>
  --   rewrite [Nat.add_succ]
  --   rewrite [Nat.add_succ]
  --   rewrite [Nat.add_succ, ih]
  --   rfl
