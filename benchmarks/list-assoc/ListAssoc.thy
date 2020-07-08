theory ListAssoc
imports Main
begin

hide_type list
no_notation Nil ("[]") and Cons (infixr "#" 65) and append (infixr "@" 65)
datatype 'a mylist = MyNil ("[]") | MyCons 'a "'a mylist" (infixr "#" 65)

primrec app :: "'a mylist \<Rightarrow> 'a mylist \<Rightarrow> 'a mylist" (infixr "@" 65) where
"[] @ ys = ys" |
"(x # xs) @ ys = x # (xs @ ys)"

theorem list_assoc [simp] : "(xs @ ys) @ zs = xs @ (ys @ zs)"
  apply(induct_tac xs)
  apply(auto)
done

theorem list_assoc2 : "((xs @ ys) @ zs) @ ws = xs @ (ys @ (zs @ ws))"
  apply(simp)
done
end
