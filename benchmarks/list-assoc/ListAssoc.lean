variable {α : Type}

theorem append_assoc (xs ys zs us ws : list α):
  (((xs ++ ys) ++ zs) ++ us) ++ ws = xs ++ (ys ++ (zs ++ (us ++ ws))) := by simp
