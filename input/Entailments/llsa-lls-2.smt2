; An acyclic list segment of acyclic lists is a list segment of lists

(set-logic SEPLOGLIA)

(declare-datatypes ((Node 0)) (((node (left Int) (right Int)))))

(define-fun-rec ls ((x Int) (y Int)) Bool
        (or (sep (= x y) emp)
            (exists ((z Int))
                (sep (pto x (node z (as nil Int))) (ls z y)))
        )
)

(define-fun-rec lsa ((x Int) (y Int)) Bool
        (or (sep (= x y) emp)
            (exists ((z Int))
                (sep (distinct x y) (pto x (node z (as nil Int))) (lsa z y)))
        )
)

(define-fun-rec lls ((x Int) (v Int)) Bool
        (or (and (= x v) emp)
            (exists ((z Int) (u Int) (w Int))
                (sep (pto x (node z u)) (pto w (node v (as nil Int))) (ls u v) (lls z w)))
        )
)

(define-fun-rec llsa ((x Int) (v Int)) Bool
        (or (and (= x v) emp)
            (exists ((z Int) (u Int) (w Int))
                (sep (pto x (node z u)) (pto w (node v (as nil Int))) (lsa u v) (llsa z w)))
        )
)

(declare-const x Int)
(declare-const v Int)

(assert ((=> (llsa x v) (lls x v))))