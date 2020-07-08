(set-logic ALL)
(declare-datatype List ((cons (head Int) (tail List)) (nil)))

(define-fun-rec ++ ((xs List) (ys List)) List (
  match xs (
    (nil ys)
    ((cons h t) (cons h (++ t ys)))
  )
))

(assert (not
  (=>
    (forall ((xs List) (ys List) (zs List)) (= (++ (++ xs ys) zs)
                                               (++ xs (++ ys zs))))
    (forall ((aas List) (bs List) (cs List) (ds List))
      (= (++ (++ (++ aas bs) cs) ds)
         (++ aas (++ bs (++ cs ds))))))))

(check-sat)
