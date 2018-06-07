; A list segment is a list segment of even length or a list segment of odd length

(set-logic SEPLOGLIA)

(define-fun-rec ls ((x Int) (y Int)) Bool
        (or (and ( = x y) emp)
            (exists ((z Int))
                (sep (pto x z) (ls z y)))
        )
)

(define-fun-rec lsp ((x Int) (y Int)) Bool
        (or (pto x y)
            (exists ((z Int))
                (sep (pto x z) (lsp z y)))
        )
)

(define-funs-rec ((lse ((x Int) (y Int)) Bool) (lso ((x Int) (y Int)) Bool))
        ((or (and ( = x y) emp)
            (exists ((z Int))
                (sep (pto x z) (lso z y)))
        )

        (or (pto x y)
            (exists ((z Int))
                (sep (pto x z) (lse z y)))
        ))
)

(define-fun-rec lspeo ((x Int) (y Int)) Bool
        (or (exists ((z Int)) (sep (pto x z) (lse z y)))
            (exists ((z Int)) (sep (pto x z) (lso z y)))
        )
)

(declare-const x Int)
(declare-const y Int)

(assert ((=> (ls x y) (lso x y))))
