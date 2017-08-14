; A list segment with at least one element is a list segment

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

(declare-const x Int)
(declare-const y Int)

(assert ((=> (lsp x y) (ls x y))))