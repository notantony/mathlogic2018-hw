type op = Conj | Disj | Impl | Into | Comma;;

type tree = 
	| Binop of op * tree * tree
        | Neg of tree
        | Var of string
        | None;;
