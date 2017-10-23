; A list with at least one element is a list

(set-logic SEPLOGLIA)

(define-fun-rec list ((x Int)) Bool
        (or (emp)
            (exists ((y Int))
                (sep (pto x y) (list y)))
        )
)

(define-fun-rec listp ((x Int)) Bool
        (or (exists ((y Int)) (pto x y))
            (exists ((y Int))
                (sep (pto x y) (listp y)))
        )
)

(declare-const x Int)

(assert ((=> (list x) (listp x))))