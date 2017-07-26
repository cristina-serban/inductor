(theory SepLogic

 :sorts ((Ref 1))

 :funs ((emp Bool)
        (sep Bool Bool Bool :left-assoc)
        (wand Bool Bool Bool :right-assoc)
        (par (A) (pto (Ref A) A Bool))
        (par (A) (nil (Ref A)))
       )
)
