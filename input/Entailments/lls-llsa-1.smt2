; An acyclic list segment of acyclic lists is a list segment of lists

(set-logic SEPLOGLIA)

(declare-datatypes ((Node 0)) (((node (left Int) (right Int)))))

(declare-heap (Int Node))

(define-fun-rec ls ((x Int) (y Int)) Bool
        (or (sep (= x y) (_ emp Int Node))
            (exists ((z Int))
                (sep (pto x (node z (as nil Int))) (ls z y)))
        )
)

(define-fun-rec lsa ((x Int) (y Int)) Bool
        (or (sep (= x y) (_ emp Int Node))
            (exists ((z Int))
                (sep (distinct x y) (pto x (node z (as nil Int))) (lsa z y)))
        )
)

(define-fun-rec lls ((x Int) (v Int)) Bool
        (or (and (= x v) (_ emp Int Node))
            (exists ((z Int) (u Int) (w Int))
                (sep (pto x (node z u)) (ls u v) (lls z w)))
        )
)

(define-fun-rec llsa ((x Int) (v Int)) Bool
        (or (and (= x v) (_ emp Int Node))
            (exists ((z Int) (u Int) (w Int))
                (sep (pto x (node z u)) (lsa u v) (llsa z w)))
        )
)

(declare-const x Int)
(declare-const v Int)

(assert (lls x v))
(assert (not (llsa x v)))

(check-sat)