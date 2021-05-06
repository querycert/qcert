module type IMP_EJSON = sig

  (* EJson *)

  type 'foreign_ejson_model ejson =
    | Coq_ejnull
    | Coq_ejnumber of float
    | Coq_ejbigint of int
    | Coq_ejbool of bool
    | Coq_ejstring of char list
    | Coq_ejarray of 'foreign_ejson_model ejson list
    | Coq_ejobject of (char list * 'foreign_ejson_model ejson) list
    | Coq_ejforeign of 'foreign_ejson_model

  type 'foreign_ejson_model cejson =
    | Coq_cejnull
    | Coq_cejnumber of float
    | Coq_cejbigint of int
    | Coq_cejbool of bool
    | Coq_cejstring of char list
    | Coq_cejforeign of 'foreign_ejson_model

  (* EJsonOperators *)

  type ejson_op =
    | EJsonOpNot
    | EJsonOpNeg
    | EJsonOpAnd
    | EJsonOpOr
    | EJsonOpLt
    | EJsonOpLe
    | EJsonOpGt
    | EJsonOpGe
    | EJsonOpAddString
    | EJsonOpAddNumber
    | EJsonOpSub
    | EJsonOpMult
    | EJsonOpDiv
    | EJsonOpStrictEqual
    | EJsonOpStrictDisequal
    | EJsonOpArray
    | EJsonOpArrayLength
    | EJsonOpArrayPush
    | EJsonOpArrayAccess
    | EJsonOpObject of char list list
    | EJsonOpAccess of char list
    | EJsonOpHasOwnProperty of char list
    | EJsonOpMathMin
    | EJsonOpMathMax
    | EJsonOpMathPow
    | EJsonOpMathExp
    | EJsonOpMathAbs
    | EJsonOpMathLog
    | EJsonOpMathLog10
    | EJsonOpMathSqrt
    | EJsonOpMathCeil
    | EJsonOpMathFloor
    | EJsonOpMathTrunc

  (* EJsonRuntimeOperators *)

  type 'foreign_ejson_runtime_op ejson_runtime_op =
    | EJsonRuntimeEqual
    | EJsonRuntimeCompare
    | EJsonRuntimeToString
    | EJsonRuntimeToText
    | EJsonRuntimeRecConcat
    | EJsonRuntimeRecMerge
    | EJsonRuntimeRecRemove
    | EJsonRuntimeRecProject
    | EJsonRuntimeRecDot
    | EJsonRuntimeArray
    | EJsonRuntimeArrayLength
    | EJsonRuntimeArrayPush
    | EJsonRuntimeArrayAccess
    | EJsonRuntimeEither
    | EJsonRuntimeToLeft
    | EJsonRuntimeToRight
    | EJsonRuntimeUnbrand
    | EJsonRuntimeCast
    | EJsonRuntimeDistinct
    | EJsonRuntimeSingleton
    | EJsonRuntimeFlatten
    | EJsonRuntimeUnion
    | EJsonRuntimeMinus
    | EJsonRuntimeMin
    | EJsonRuntimeMax
    | EJsonRuntimeNth
    | EJsonRuntimeCount
    | EJsonRuntimeContains
    | EJsonRuntimeSort
    | EJsonRuntimeGroupBy
    | EJsonRuntimeLength
    | EJsonRuntimeSubstring
    | EJsonRuntimeSubstringEnd
    | EJsonRuntimeStringJoin
    | EJsonRuntimeLike
    | EJsonRuntimeNatLt
    | EJsonRuntimeNatLe
    | EJsonRuntimeNatPlus
    | EJsonRuntimeNatMinus
    | EJsonRuntimeNatMult
    | EJsonRuntimeNatDiv
    | EJsonRuntimeNatRem
    | EJsonRuntimeNatAbs
    | EJsonRuntimeNatLog2
    | EJsonRuntimeNatSqrt
    | EJsonRuntimeNatMinPair
    | EJsonRuntimeNatMaxPair
    | EJsonRuntimeNatSum
    | EJsonRuntimeNatMin
    | EJsonRuntimeNatMax
    | EJsonRuntimeNatArithMean
    | EJsonRuntimeFloatOfNat
    | EJsonRuntimeFloatSum
    | EJsonRuntimeFloatArithMean
    | EJsonRuntimeFloatMin
    | EJsonRuntimeFloatMax
    | EJsonRuntimeNatOfFloat
    | EJsonRuntimeForeign of 'foreign_ejson_runtime_op

  (* Imp *)

  type var = char list

  type ('constant, 'op, 'runtime) imp_expr =
    | ImpExprError of char list
    | ImpExprVar of var
    | ImpExprConst of 'constant
    | ImpExprOp of 'op * ('constant, 'op, 'runtime) imp_expr list
    | ImpExprRuntimeCall of 'runtime * ('constant, 'op, 'runtime) imp_expr list

  type ('constant, 'op, 'runtime) imp_stmt =
    | ImpStmtBlock of (var * ('constant, 'op, 'runtime) imp_expr option) list
                      * ('constant, 'op, 'runtime) imp_stmt list
    | ImpStmtAssign of var * ('constant, 'op, 'runtime) imp_expr
    | ImpStmtFor of var * ('constant, 'op, 'runtime) imp_expr
                    * ('constant, 'op, 'runtime) imp_stmt
    | ImpStmtForRange of var * ('constant, 'op, 'runtime) imp_expr
                         * ('constant, 'op, 'runtime) imp_expr * ('constant, 'op, 'runtime) imp_stmt
    | ImpStmtIf of ('constant, 'op, 'runtime) imp_expr
                   * ('constant, 'op, 'runtime) imp_stmt * ('constant, 'op, 'runtime) imp_stmt

  type ('constant, 'op, 'runtime) imp_function =
    | ImpFun of var * ('constant, 'op, 'runtime) imp_stmt * var

  type ('constant, 'op, 'runtime) imp =
    (char list * ('constant, 'op, 'runtime) imp_function) list

  (* ImpEJson *)

  type 'foreign_ejson_model imp_ejson_model = 'foreign_ejson_model ejson

  type 'foreign_ejson_model imp_ejson_constant = 'foreign_ejson_model cejson

  type imp_ejson_op = ejson_op

  type 'foreign_ejson_runtime_op imp_ejson_runtime_op =
    'foreign_ejson_runtime_op ejson_runtime_op

  type ('foreign_ejson_model, 'foreign_ejson_runtime_op) imp_ejson_expr =
    ('foreign_ejson_model imp_ejson_constant, imp_ejson_op,
     'foreign_ejson_runtime_op imp_ejson_runtime_op) imp_expr

  type ('foreign_ejson_model, 'foreign_ejson_runtime_op) imp_ejson_stmt =
    ('foreign_ejson_model imp_ejson_constant, imp_ejson_op,
     'foreign_ejson_runtime_op imp_ejson_runtime_op) imp_stmt

  type ('foreign_ejson_model, 'foreign_ejson_runtime_op) imp_ejson_function =
    ('foreign_ejson_model imp_ejson_constant, imp_ejson_op,
     'foreign_ejson_runtime_op imp_ejson_runtime_op) imp_function

  type ('foreign_ejson_model, 'foreign_ejson_runtime_op) imp_ejson =
    ('foreign_ejson_model imp_ejson_constant, imp_ejson_op,
     'foreign_ejson_runtime_op imp_ejson_runtime_op) imp


  (* Foreign *)

  type foreign_model
  type foreign_runtime_op
end
