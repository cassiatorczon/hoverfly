import Hoverfly.Backend

import Palamedes.Synthesizer
open Gen.CorrectGen

def demo_genEq2 : CorrectGen (· = 2) := by
  hoverfly
  sorry

def demo_genEq2or3 : CorrectGen (fun x => x = 2 ∨ x = 3) := by
  hoverfly
  sorry

def isAllTwos : Tree Nat → Bool
  | .leaf => true
  | .node l x r => x = 2 && isAllTwos l && isAllTwos r

def demo_genAllTwos : CorrectGen (fun t => isAllTwos t) := by
  hoverfly
  sorry

theorem demo_mini : 1 = 1 /\ 2 = 2 := by
  hoverfly
  sorry

theorem demo_simple (very_very_long_variable_name : Nat) :
  very_very_long_variable_name = 1 ->
  ¬(very_very_long_variable_name = 2) /\ 1 = very_very_long_variable_name := by
  hoverfly
  sorry

theorem demo_medium (n m : Nat) : n <= m → ∃ x, m = x + n := by
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
  -- revert m
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
