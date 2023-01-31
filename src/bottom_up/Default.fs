module Default

open System.Collections.Generic

open BottomUp

module A = AST

let StringSymbol = Hashcons<string>()

type vartbl =
    { mutable count: int
      tbl: Dictionary<string, int> }

let mk_vartbl () = { count = 0; tbl = Dictionary() }

let getvar vt name =
    try
        vt.tbl.[name]
    with :? KeyNotFoundException ->
        let n = vt.count
        vt.tbl.Add(name, n)
        vt.count <- n + 1
        n

let termOfAst vt ast =
    match ast with
    | A.Const s
    | A.Quoted s ->
        Datalog.mk_const (StringSymbol.Make s)
    | A.Var x ->
        Datalog.mk_var (getvar vt x)

let literalOfAst vt lit =
    let vt = Option.defaultValue (mk_vartbl ()) vt
    match lit with
    | A.Atom (s, args) ->
        let s = StringSymbol.Make s
        let args = List.map (termOfAst vt) args
        Datalog.mk_literal s args

let clauseOfAst c =
    match c with
    | A.Clause (a, l) ->
        let vt = mk_vartbl ()
        let a = literalOfAst (Some vt) a
        let l = List.map (literalOfAst (Some vt)) l
        Datalog.mk_clause a l

let queryOfAst q =
    match q with
    | A.Query (vars, lits, neg) ->
        let vt = mk_vartbl ()
        let lits = List.map (literalOfAst (Some vt)) lits
        let neg = List.map (literalOfAst (Some vt)) neg
        let vars = 
            Array.ofList vars
            |> Array.map
                (fun t ->
                    match termOfAst vt t with
                    | Var i -> i
                    | Const _ -> failwith "queryOfAst: expected variables")
        vars, lits, neg