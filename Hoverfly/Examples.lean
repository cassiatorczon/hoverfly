import Hoverfly.Backend

-- set_option linter.unusedTactic false

-- set_option linter.unreachableTactic false
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
    rewrite [Nat.two_mul]
  ]
