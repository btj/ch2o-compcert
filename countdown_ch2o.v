Require Export String.
Require Export ch2o.abstract_c.frontend.

Local Open Scope string_scope.

Definition decls: list (string * decl) :=
  [("main",
    FunDecl [] (CTFun [] (CTInt (CIntType None CIntRank)))
      (CSLocal [] "x" (CTInt (CIntType None CIntRank))
        (Some
          (CSingleInit (CEConst (CIntType (Some Signed) CIntRank) 32767)))
        (CSComp
          (CSWhile
            (CEBinOp (CompOp LtOp)
              (CEConst (CIntType (Some Signed) CIntRank) 0) (CEVar "x"))
            (CSScope
              (CSDo
                (CEAssign Assign (CEVar "x")
                  (CEBinOp (ArithOp MinusOp) (CEVar "x")
                    (CEConst (CIntType (Some Signed) CIntRank) 1))))))
          (CSReturn (Some (CEVar "x"))))))].
