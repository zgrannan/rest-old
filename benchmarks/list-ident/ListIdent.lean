variable { α : Type}

theorem listIdent (xs : list α): xs = (xs ++ []) ++ [] := by simp
