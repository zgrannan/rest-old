theory ListIdent
imports Main
begin

hide_type list
datatype 'a mylist = MyNil | MyCons 'a "'a mylist"

primrec app :: "'a mylist \<Rightarrow> 'a mylist \<Rightarrow> 'a mylist" where
"app MyNil ys = ys" |
"app (MyCons x xs) ys = MyCons x (app xs ys)"

theorem list_ident [simp] : "app xs MyNil = xs"
  apply(induct_tac xs)
  apply(auto)
done

theorem list_ident2: "xs = app (app xs MyNil) MyNil"
  apply (simp)
done
end
