module ListIdent where

import Prelude ()
import Zeno

data MyList a = MyNil | Cons a (MyList a)

(++)::MyList a -> MyList a -> MyList a
MyNil       ++ ys = ys
(Cons x xs) ++ ys = Cons x (xs ++ ys)

concatIdent xs =
  given  (id :=: (++ MyNil))
  $ prove (xs :=: (xs ++ MyNil) ++ MyNil)




