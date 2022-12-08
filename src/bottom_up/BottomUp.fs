module BottomUp

open System.Collections.Generic

module Univ =
    type t = unit -> unit

    type embedding<'a> =
        { pack: 'a -> t
          unpack: t -> 'a option }

    let embed () =
        let mutable r = None

        let pack a =
            let o = Some a
            fun () -> r <- o

        let unpack t =
            r <- None
            t ()
            let a = r
            a

        { pack = pack; unpack = unpack }

    let pack emb x = emb.pack x
    let unpack emb t = emb.unpack t

    let compatible emb t =
        match unpack emb t with
        | None -> false
        | Some _ -> true

type term<'T> =
    | Var of int
    | Const of 'T


type literal<'T> = term<'T> array
type clause<'T> = literal<'T> array

type soft_lit<'T> = 'T * term<'T> list
type soft_clause<'T> = soft_lit<'T> * soft_lit<'T> list

type subst<'T> =
    | SubstEmpty
    | SubstBind of (int * int * term<'T> * int * subst<'T>)

type bind<'U> = 'U * int

exception UnifFailure

[<AbstractClass; Sealed>]
type Datalog<'T when 'T: equality> private () =
    static member mk_var i : term<'T> = Var i
    static member mk_const(s: 'T) = Const s
    static member mk_literal (head: 'T) args = Array.ofList (Const head :: args)

    static member of_soft_lit(hd, args) = Datalog<'T>.mk_literal hd args

    static member open_literal(literal: term<'T>[]) =
        match Array.toList literal with
        | Const x :: args -> x, args
        | _ -> invalidArg "literal" "Array was empty or head was Var"

    static member mk_clause head premises : clause<'T> = Array.ofList (head :: premises)

    static member of_soft_clause(concl, premises) =
        let concl = Datalog<'T>.of_soft_lit concl
        let premises = List.map Datalog<'T>.of_soft_lit premises
        Datalog<'T>.mk_clause concl premises

    static member open_clause(clause: clause<'T>) =
        let head = Datalog<'T>.open_literal clause[0]

        let body =
            (Array.length clause) - 1
            |> Array.sub clause 1
            |> Array.toList
            |> List.map Datalog<'T>.open_literal

        head, body

    static member is_var(t: term<'T>) =
        match t with
        | Var _ -> true
        | _ -> false

    static member is_ground(t: literal<'T>) =
        assert (not (Datalog<'T>.is_var t[0]))

        let rec check t i =
            if i = Array.length t then
                true
            else
                (not (Datalog<'T>.is_var t[i]) && check t (i + 1))

        check t 1

    static member arity(t: literal<'T>) = Array.length t - 1

    static member eq_term (t1: term<'T>) (t2: term<'T>) =
        match t1, t2 with
        | Var i, Var j -> i = j
        | Const s1, Const s2 -> s1 = s2
        | _ -> false

    static member eq_literal (l1: literal<'T>) (l2: literal<'T>) =
        if Array.length l1 <> Array.length l2 then
            false
        else
            Array.zip l1 l2 |> Array.forall (fun (t1, t2) -> Datalog<'T>.eq_term t1 t2)

    static member hash_term(t, ?hash_fn) =
        let hash_fn = defaultArg hash_fn hash

        match t with
        | Var i -> i
        | Const s -> hash_fn s

    static member hash_literal(l, ?hash_fn) =
        let hash_fn = defaultArg hash_fn hash

        let hash_term h t =
            match t with
            | Var i -> h * 65599 + i
            | Const s -> h * 65588 + hash s

        Array.fold hash_term 13 l |> abs

    static member check_safe(clause: clause<'T>) =
        let rec check_head i =
            if i = Array.length clause[0] then
                true
            else
                let t = clause[0][i]

                if Datalog<'T>.is_var t then
                    check_body t 1 && check_head (i + 1)
                else
                    check_head (i + 1)

        and check_body var j =
            if j = Array.length clause then
                false
            else
                check_body_literal var clause[j] 1 || check_body var (j + 1)

        and check_body_literal var literal k =
            if k = Array.length literal then false
            else if Datalog<'T>.eq_term literal[k] var then true
            else check_body_literal var literal (k + 1)

        check_head 1

    static member is_fact clause =
        Array.length clause = 1 && Datalog<'T>.is_ground clause
    
    static member eq_clause c1 c2 =
        if Array.length c1 <> Array.length c2 then
            false
        else
            Array.zip c1 c2
            |> Array.forall (fun (l1, l2) -> Datalog<'T>.eq_literal l1 l2)
    
    static member hash_clause (c: clause<'T>) =
        let mutable h = 17
        for i = 0 to Array.length c - 1 do
            h <- (h + 65536) * Datalog<'T>.hash_literal c[i]
        done
        abs h
    
    static member empty_subst : subst<'T> = SubstEmpty
    static member is_empty_subst = function
        | SubstEmpty -> true
        | _ -> false

