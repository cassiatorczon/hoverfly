import Hoverfly
import Aesop

add_hoverfly_tactics
  [
    assumption,
    contradiction,
    intro,
    rfl,
    subst_eqs,
    rewrite [Eq.comm],
    rewrite [Nat.add_zero],
    rewrite [Nat.add_succ],
    apply Exists.intro,
    apply Nat.le_trans,
    apply Nat.zero_le,
    apply Nat.sub_add_cancel,
    rewrite [Nat.two_mul],
    (induction HYP),
    (cases HYP)
  ]

@[aesop safe]
theorem foo : True := by simp

-- add_aesop_tactics_to_hoverfly

theorem demo_le_trans (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  hoverfly

theorem demo_add_assoc (n m p : Nat) :
    n + (m + p) = (n + m) + p := by
  hoverfly
