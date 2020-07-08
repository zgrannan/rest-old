module ListAssocZeno where 

import Prelude ()
import Zeno

(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)


assoc2 xs ys zs ws 
  = given ((\as -> \bs -> \cs -> (as ++ bs) ++ cs) :=: (\as -> \bs -> \cs -> as ++ (bs ++ cs)))
  $ prove (((xs ++ ys) ++ zs) ++ ws :=: xs ++ (ys ++ (zs ++ ws)))
