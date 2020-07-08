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
    (forall ((xs List)) (= xs (++ xs nil)))
    (forall ((ys List)) (= ys (++ (++ ys nil) nil)))
  )
  )
)

(check-sat)
