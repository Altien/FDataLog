module BottomUp

open System.Collections.Generic

exception Exit

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

[<CustomEquality; NoComparison>]
type term<'T when 'T: equality> =
    | Var of int
    | Const of 'T

    override this.Equals other =
        match other with
        | :? term<'T> as other ->
            match (this, other) with
            | Var i, Var j -> i = j
            | Const s1, Const s2 -> s1 = s2
            | _ -> false
        | _ -> false

    override this.GetHashCode() =
        match this with
        | Var i -> i
        | Const s -> hash s


type literal<'T when 'T: equality> = term<'T> array


type clause<'T when 'T: equality> = literal<'T> array

type soft_lit<'T when 'T: equality> = 'T * term<'T> list
type soft_clause<'T when 'T: equality> = soft_lit<'T> * soft_lit<'T> list

type subst<'T when 'T: equality> =
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
            | Const s -> h * 65588 + hash_fn s

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

    static member is_fact(clause: clause<'T>) =
        Array.length clause = 1 && Datalog<'T>.is_ground clause[0]

    static member eq_clause c1 c2 =
        if Array.length c1 <> Array.length c2 then
            false
        else
            Array.zip c1 c2 |> Array.forall (fun (l1, l2) -> Datalog<'T>.eq_literal l1 l2)

    static member hash_clause(c: clause<'T>) =
        let mutable h = 17

        for i = 0 to Array.length c - 1 do
            h <- (h + 65536) * Datalog<'T>.hash_literal c[i]

        abs h

    static member empty_subst: subst<'T> = SubstEmpty

    static member is_empty_subst =
        function
        | SubstEmpty -> true
        | _ -> false

    static member offset(clause: clause<'T>) =
        let rec fold_lit terms offset i =
            if i = Array.length terms then
                offset
            else
                let offset =
                    match terms[i] with
                    | Const _ -> offset
                    | Var i -> max i offset

                fold_lit terms offset (i + 1)

        and fold_lits lits offset i =
            if i = Array.length lits then
                offset
            else
                fold_lits lits (fold_lit lits[i] offset 1) (i + 1)

        let offset = fold_lits clause 0 0
        offset + 1

    static member deref subst var offset =
        match subst, var with
        | _, Const _ -> var, offset
        | SubstBind(i, o, t, o_t, _), Var j when i = j && o = offset -> Datalog<'T>.deref subst t o_t
        | SubstBind(_, _, _, _, subst'), _ -> Datalog<'T>.deref subst' var offset
        | SubstEmpty, _ -> var, offset

    static member bind_subst subst v o_v t o_t =
        assert (Datalog<'T>.is_var v)

        if Datalog<'T>.eq_term v t && o_v = o_t then
            subst
        else
            match v with
            | Var i -> SubstBind(i, o_v, t, o_t, subst)
            | Const _ -> failwith "Cannot bind to constant"

    static member matching((l1, o1), (l2, o2), ?subst) =
        let subst = Option.defaultValue Datalog<'T>.empty_subst subst

        if Array.length l1 <> Array.length l2 then
            raise UnifFailure
        else
            let match_pair subst t1 o1' t2 o2' =
                match t1, t2 with
                | Const s1, Const s2 -> if s1 = s2 then subst else raise UnifFailure
                | Var i, Var j when i = j && o1' = o2' -> subst
                | Var _, _ -> Datalog<'T>.bind_subst subst t1 o1' t2 o2'
                | Const _, Var _ -> raise UnifFailure

            let process_pair subst (i1, i2) =
                let t1, o1' = Datalog<'T>.deref subst i1 o1
                let t2, o2' = Datalog<'T>.deref subst i2 o2
                match_pair subst t1 o1' t2 o2'

            Array.zip l1 l2 |> Array.fold process_pair subst

    static member unify((l1, o1), (l2, o2), ?subst) =
        let subst = Option.defaultValue Datalog<'T>.empty_subst subst

        if Array.length l1 <> Array.length l2 then
            raise UnifFailure
        else
            let unif_pair subst t1 o1' t2 o2' =
                match t1, t2 with
                | Const s1, Const s2 -> if s1 = s2 then subst else raise UnifFailure
                | Var i, Var j when i = j && o1' = o2' -> subst
                | Var _, _ -> Datalog<'T>.bind_subst subst t1 o1' t2 o2'
                | Const _, Var _ -> Datalog<'T>.bind_subst subst t2 o2' t1 o1'

            let process_pair subst (i1, i2) =
                let t1, o1' = Datalog<'T>.deref subst i1 o1
                let t2, o2' = Datalog<'T>.deref subst i2 o2
                unif_pair subst t1 o1' t2 o2'

            Array.zip l1 l2 |> Array.fold process_pair subst

    static member alpha_equiv((l1, o1), (l2, o2), ?subst) =
        let subst = Option.defaultValue Datalog<'T>.empty_subst subst

        if Array.length l1 <> Array.length l2 then
            raise UnifFailure
        else
            let unif_pair subst t1 o1' t2 o2' =
                match t1, t2 with
                | Const s1, Const s2 -> if s1 = s2 then subst else raise UnifFailure
                | Var i, Var j when i = j && o1' = o2' -> subst
                | Var _, Var _ -> Datalog<'T>.bind_subst subst t1 o1' t2 o2'
                | Const _, Var _
                | Var _, Const _ -> raise UnifFailure

            let process_pair subst (i1, i2) =
                let t1, o1' = Datalog<'T>.deref subst i1 o1
                let t2, o2' = Datalog<'T>.deref subst i2 o2
                unif_pair subst t1 o1' t2 o2'

            Array.zip l1 l2 |> Array.fold process_pair subst

    static member shift_lit lit offset =
        if offset = 0 then
            lit
        else
            Array.map
                (fun t ->
                    match t with
                    | Var i -> Var(i + offset)
                    | Const _ -> t)
                lit

    static member subst_literal subst (lit, offset) =
        if Datalog<'T>.is_ground lit || (Datalog<'T>.is_empty_subst subst && offset = 0) then
            lit
        else if Datalog<'T>.is_empty_subst subst then
            Datalog<'T>.shift_lit lit offset
        else
            Array.map
                (fun t ->
                    let t', o_t' = Datalog<'T>.deref subst t offset

                    match t' with
                    | Var i -> Var(i + o_t')
                    | Const _ -> t')
                lit

    static member remove_first_subst subst (clause, offset) =
        assert (Array.length clause > 1)
        let a = Array.create (Array.length clause - 1) [||]
        a[0] <- Datalog<'T>.subst_literal subst (clause[0], offset)

        for i = 1 to Array.length clause - 2 do
            a[i] <- Datalog<'T>.subst_literal subst (clause[i + 1], offset)

        a

    static member quantify1 f = let v1 = Datalog<'T>.mk_var 1 in f v1

    static member quantify2 f =
        let v1 = Datalog<'T>.mk_var 1 in
        let v2 = Datalog<'T>.mk_var 2 in
        f v1 v2

    static member quantify3 f =
        let v1 = Datalog<'T>.mk_var 1 in
        let v2 = Datalog<'T>.mk_var 2 in
        let v3 = Datalog<'T>.mk_var 3 in
        f v1 v2 v3

    static member quantify4 f =
        let v1 = Datalog<'T>.mk_var 1 in
        let v2 = Datalog<'T>.mk_var 2 in
        let v3 = Datalog<'T>.mk_var 3 in
        let v4 = Datalog<'T>.mk_var 4 in
        f v1 v2 v3 v4

    static member quantifyn n f =
        let rec mk_vars =
            function
            | 0 -> []
            | n -> Datalog<'T>.mk_var n :: mk_vars (n - 1)

        assert (n >= 0)

        mk_vars n |> f

type TermHashtable<'T, 'U when 'T: equality and 'U: equality> = Dictionary<term<'T>, 'U>

let iter_table (d: Dictionary<'a, 'b>) = Seq.zip d.Keys d.Values

type DataSet<'T, 'U when 'T: equality and 'U: equality> = HashSet<literal<'T> * 'U>

let fold_dataset f s =
    Seq.cast<literal<'T> * 'U> >> Seq.fold f s

type IndexNode<'T, 'U when 'T: equality and 'U: equality> =
    | Node of DataSet<'T, 'U> * TermHashtable<'T, IndexNode<'T, 'U>>

let create_node<'T, 'U when 'T: equality and 'U: equality> () =
    Node(DataSet<'T, 'U>(), TermHashtable<'T, IndexNode<'T, 'U>>())

type Index<'T, 'U when 'T: equality and 'U: equality>() =
    member val node = create_node ()

    member this.Copy(Node(set, h)) =
        let set' = DataSet(set)
        let h' = TermHashtable(h)
        iter_table h |> Seq.iter (fun (k, t') -> h'.Add(k, this.Copy(t')))
        Node(set', h')

    static member term_to_char t =
        match t with
        | Const _ -> t
        | Var _ -> Var 0

    member this.Add (literal: literal<'T>) elt =
        let len = Array.length literal

        let rec add t i =
            match t, i with
            | Node(set, _subtries), i when i = len -> set.Add((literal, elt))
            | Node(_, subtries), i ->
                let c = Index<'T, 'U>.term_to_char literal[i]
                let subtrie = subtries.GetValueOrDefault(c, create_node ())
                subtries.TryAdd(c, subtrie) |> ignore
                add subtrie (i + 1)

        add this.node 0

    // member private this.Unify<'a>
    //     (f: (literal<'T> * int -> literal<'T> * int -> subst<'T>))
    //     (k: ('a -> literal<'T> -> 'U -> subst<'T> -> 'a))
    //     o_t
    //     (literal, o_lit)
    //     (acc: 'a)
    //     (lit': (literal<'T>), elt)
    //     =
    //     try
    //         let subst = f (lit', o_t) (literal, o_lit)
    //         k acc lit' elt subst
    //     with UnifFailure ->
    //         acc

    // member private this.Matching =
    //     let f = fun a b -> Datalog<'T>.matching (a, b)
    //     this.Unify<'a>(f)

    // member private this.Unification = this.Unify(fun a b -> Datalog<'T>.unify (a, b))

    // member private this.AlphaEquiv = this.Unify(fun a b -> Datalog<'T>.alpha_equiv (a, b))

    member private this.Matching k o_t (literal, o_lit) =
        (fun acc (lit', elt) ->
            try
                let subst = Datalog<'T>.matching ((lit', o_t), (literal, o_lit))
                k acc lit' elt subst
            with UnifFailure ->
                acc)

    member private this.Unification (k: ('a -> literal<'T> -> 'U -> subst<'T> -> 'a)) o_t (literal, o_lit) =
        (fun acc (lit', elt) ->
            try
                let subst = Datalog<'T>.unify ((lit', o_t), (literal, o_lit))
                k acc lit' elt subst
            with UnifFailure ->
                acc)

    member private this.AlphaEquiv k o_t (literal, o_lit) =
        (fun acc (lit', elt) ->
            try
                let subst = Datalog<'T>.alpha_equiv ((lit', o_t), (literal, o_lit))
                k acc lit' elt subst
            with UnifFailure ->
                acc)

    member this.RetrieveGeneralizations
        (k: ('a -> literal<'T> -> 'U -> subst<'T> -> 'a))
        (acc: 'a)
        (o_t: int)
        (literal: literal<'T>, o_lit: int)
        =
        let len = Array.length literal in

        let rec search t i acc =
            match t, i with
            | Node(s, _), i when i = len -> fold_dataset (this.Matching k o_t (literal, o_lit)) acc s
            | Node(_, subtries), i ->
                if Datalog<'T>.is_var literal[i] then
                    try_with subtries acc (Var 0) i
                else
                    let acc' = try_with subtries acc (Var 0) i
                    try_with subtries acc' literal[i] i

        and try_with (subtries: TermHashtable<'T, IndexNode<'T, 'U>>) acc sym i =
            try
                let t' = subtries.[sym]
                search t' (i + 1) acc
            with :? KeyNotFoundException ->
                acc

        search this.node 0 acc

    member this.RetrieveSpecializations k acc o_t (literal, o_lit) =
        let len = Array.length literal

        let rec search t i acc =
            match t, i with
            | Node(s, _), i when i = len -> fold_dataset (this.Matching k o_t (literal, o_lit)) acc s
            | Node(_, subtries), i ->
                if Datalog<'T>.is_var literal[i] then
                    subtries
                    |> iter_table
                    |> Seq.fold (fun acc (_, subtrie) -> search subtrie (i + 1) acc) acc
                else
                    try_with subtries acc literal[i] i

        and try_with (subtries: TermHashtable<'T, IndexNode<'T, 'U>>) acc sym i =
            try
                let t' = subtries.[sym]
                search t' (i + 1) acc
            with :? KeyNotFoundException ->
                acc

        search this.node 0 acc

    /// Fold on content that is unifiable with given literal
    member this.RetrieveUnify k acc o_t (literal, o_lit) =
        let len = Array.length literal

        let rec search t i acc =
            match t, i with
            | Node(set, _), i when i = len -> fold_dataset (this.Unification k o_t (literal, o_lit)) acc set
            | Node(_, subtries), i ->
                if Datalog<'T>.is_var literal[i] then (* fold on all subtries *)
                    subtries
                    |> iter_table
                    |> Seq.fold (fun acc (_, subtrie) -> search subtrie (i + 1) acc) acc
                else (* try both subtrie with same symbol, and subtrie with variable *)
                    let acc' = try_with subtries acc literal[i] i
                    try_with subtries acc' (Var 0) i
        (* try to search in the subtree annotated with given symbol/var *)
        and try_with subtries acc sym i =
            try
                let t' = subtries.[sym]
                search t' (i + 1) acc
            with :? KeyNotFoundException ->
                acc

        search this.node 0 acc

    member this.RetrieveRenaming k acc o_t (literal, o_lit) =
        let len = Array.length literal

        let rec search t i acc =
            match t, i with
            | Node(set, _), i when i = len -> fold_dataset (this.AlphaEquiv k o_t (literal, o_lit)) acc set
            | Node(_, subtries), i ->
                let c =
                    match literal[i] with
                    | Const _ -> literal[i]
                    | Var _ -> Var 0

                try
                    let t' = subtries.[c]
                    search t' (i + 1) acc
                with :? KeyNotFoundException ->
                    acc in

        search this.node 0 acc

    member this.Fold k acc (Node(set, subtries)) =
        let acc = fold_dataset (fun acc (lit, elt) -> k acc lit elt) acc set

        subtries
        |> iter_table
        |> Seq.fold (fun acc (_, subtrie) -> this.Fold k acc subtrie) acc

    member this.Size() =
        this.Fold (fun i _ _ -> i + 1) 0 this.node


exception UnsafeClause

type ClauseHashtable<'T, 'U when 'T: equality and 'U: equality> = Dictionary<clause<'T>, 'U>

[<CustomEquality; NoComparison>]
type explanation<'T when 'T: equality> =
    | Axiom
    | Resolution of clause<'T> * literal<'T>
    | ExtExplanation of string * Univ.t

    override this.Equals other =
        match other with
        | :? explanation<'T> as other ->
            match (this, other) with
            | Axiom, Axiom -> true
            | Resolution(c1, l1), Resolution(c2, l2) -> c1 = c2 && l1 = l2
            | ExtExplanation(s1, _), ExtExplanation(s2, _) -> s1 = s2
            | _ -> false
        | _ -> false

    override this.GetHashCode() =
        match this with
        | ExtExplanation(s, _) -> hash s
        | _ -> hash this

type fact_handler<'T when 'T: equality> = literal<'T> -> unit
type goal_handler<'T when 'T: equality> = literal<'T> -> unit

type user_fun<'T when 'T: equality> = soft_lit<'T> -> soft_lit<'T>

type queue_item<'T when 'T: equality> =
    | AddClause of clause<'T> * explanation<'T>
    | AddGoal of literal<'T>

type Database<'T when 'T: equality>(all, facts, goals, selected, heads, fact_handlers, all_facts, goal_handlers, funs) =
    member val all = all
    member val facts = facts
    member val goals = goals
    member val selected = selected
    member val heads = heads
    member val fact_handlers = fact_handlers
    member val all_facts = all_facts with get, set
    member val goal_handlers = goal_handlers with get, set
    member val funs = funs
    member val queue = Queue<queue_item<'T>>()

    static member Default() =
        let all = ClauseHashtable<'T, explanation<'T>>()
        let facts = Index<'T, clause<'T>>()
        let goals = Index<'T, unit>()
        let selected = Index<'T, clause<'T>>()
        let heads = Index<'T, clause<'T>>()
        let fact_handlers = Dictionary<'T, fact_handler<'T> list>()
        let all_facts: fact_handler<'T> list = []
        let goal_handlers: goal_handler<'T> list = []
        let funs = Dictionary<'T, user_fun<'T>>()
        Database(all, facts, goals, selected, heads, fact_handlers, all_facts, goal_handlers, funs)

    member this.Copy() =
        Database(
            this.all,
            this.facts,
            this.goals,
            this.selected,
            this.heads,
            this.fact_handlers,
            this.all_facts,
            this.goal_handlers,
            this.funs
        )

    member this.Contains clause =
        assert Datalog<'T>.check_safe clause
        all.ContainsKey(clause)

    member this.RewriteClause(clause: clause<'T>) : clause<'T> =
        let rec rewrite_lit (lit: literal<'T>) =
            match lit[0] with
            | Var _ -> failwith "Only const supported"
            | Const s ->
                let lit' =
                    try
                        let f = funs.[s]
                        let lit' = lit |> Datalog<'T>.open_literal |> f
                        let lit' = Datalog<'T>.of_soft_lit lit'
                        lit'
                    with :? KeyNotFoundException ->
                        lit

                if (LanguagePrimitives.PhysicalEquality lit lit') || lit = lit' then
                    lit'
                else
                    rewrite_lit lit'

        Array.map rewrite_lit clause

    member this.AddClause clause explanation =
        let clause = this.RewriteClause clause
        let already_present = this.Contains(clause)
        all.Add(clause, explanation)

        if already_present then
            ()
        else if Datalog<'T>.is_fact clause then
            (facts.Add clause[0] clause |> ignore

             let s =
                 match clause[0][0] with
                 | Const s -> s
                 | Var _ -> failwith "First term must be constant"

             let call_handler h =
                 try
                     h clause[0]
                 with e ->
                     Printf.eprintf "Datalog: exception while calling handler for %s@." (s.ToString())
                     raise e

             try
                 let l = fact_handlers.[s]
                 List.iter call_handler l
             with :? KeyNotFoundException ->
                 ()

             List.iter call_handler all_facts

             selected.RetrieveGeneralizations
                 (fun () _ clause' subst ->
                     let clause'' = Datalog<'T>.remove_first_subst subst (clause', 0)
                     let explanation = Resolution(clause', clause[0])
                     this.queue.Enqueue(AddClause(clause'', explanation)))
                 ()
                 0
                 (clause[0], 0))
            |> ignore
        else
            (assert (Array.length clause > 1)
             let offset = Datalog<'T>.offset clause

             goals.RetrieveUnify
                 (fun () _goal () subst ->
                     let new_goal = Datalog<'T>.subst_literal subst (clause[1], 0)
                     this.queue.Enqueue(AddGoal new_goal))
                 ()
                 offset
                 (clause[0], 0)

             selected.Add clause[1] clause |> ignore
             heads.Add clause[0] clause |> ignore

             facts.RetrieveSpecializations
                 (fun () fact _ subst ->
                     let clause' = Datalog<'T>.remove_first_subst subst (clause, 0)
                     let explanation = Resolution(clause, fact)
                     this.queue.Enqueue(AddClause(clause', explanation)))
                 ()
                 offset
                 (clause[1], 0))

    member this.AddGoal literal =
        try
            let offset = Datalog<'T>.offset [| literal |]
            goals.RetrieveRenaming (fun () _ _ _ -> raise Exit) () offset (literal, 0)
            List.iter (fun h -> h literal) goal_handlers
            goals.Add literal () |> ignore

            heads.RetrieveUnify
                (fun () _head clause subst ->
                    let new_goal = Datalog<'T>.subst_literal subst (clause[1], offset)
                    this.queue.Enqueue(AddGoal new_goal))
                ()
                offset
                (literal, 0)
        with Exit ->
            ()

    member this.ProcessItems item =
        let empty = this.queue.Count = 0
        this.queue.Enqueue item

        let process_item item =
            match item with
            | AddClause(c, explanation) -> this.AddClause c explanation
            | AddGoal goal -> this.AddGoal goal

        if empty then
            while not (this.queue.Count = 0) do
                let item = this.queue.Dequeue()
                process_item item

    member this.Add(clause, ?expl) =
        if not (Datalog<'T>.check_safe clause) then
            raise UnsafeClause

        let expl = Option.defaultValue Axiom expl
        this.ProcessItems(AddClause(clause, expl))

    member this.AddFact(lit, ?expl) =
        if not (Datalog<'T>.is_ground lit) then
            raise UnsafeClause

        let expl = Option.defaultValue Axiom expl
        this.ProcessItems(AddClause([| lit |], expl))

    member this.Goal lit = this.ProcessItems(AddGoal lit)

    member this.Match pattern handler =
        facts.RetrieveSpecializations (fun () fact _ _subst -> handler fact) () 0 (pattern, 1)

    member this.Query pattern vars k =
        facts.RetrieveSpecializations
            (fun () _lit _ subst ->
                let terms =
                    List.map
                        (fun i ->
                            let v = Datalog<'T>.mk_var i
                            let t, _ = Datalog<'T>.deref subst v 1

                            match t with
                            | Var _ -> failwith "Should be ground"
                            | Const s -> s)
                        vars

                k terms)
            ()
            0
            (pattern, 1)

    member this.Size = facts.Size() + selected.Size()

    member this.Fold k acc =
        this.all |> iter_table |> Seq.fold k acc

    member this.AddFun s f =
        if funs.ContainsKey s then
            failwith (sprintf "Function already defined for symbol %s" (s.ToString()))
        else
            funs.Remove(s) |> ignore
            funs.Add(s, f)

    member this.SubscribeFact symbol handler =
        let l =
            try
                fact_handlers.[symbol]
            with :? KeyNotFoundException ->
                []

        fact_handlers.Remove(symbol) |> ignore
        fact_handlers.Add(symbol, (handler :: l))

    member this.SubscribeAllFacts handler =
        this.all_facts <- (handler :: all_facts)

    member this.SubscribeGoal handler =
        this.goal_handlers <- (handler :: goal_handlers)

    member this.Goals k =
        goals.Fold (fun () goal () -> k goal) ()

    member this.Explain fact =
        let explored = ClauseHashtable()
        let s = new Dictionary<literal<'T>, unit>()

        let rec search clause =
            if explored.ContainsKey(clause) then
                ()
            else
                explored.Add(clause, ())
                let explanation = all.[clause]

                match explanation with
                | Axiom when Datalog<'T>.is_fact clause ->
                    s.Remove(clause[0]) |> ignore
                    s.Add(clause[0], ())
                | ExtExplanation _
                | Axiom -> ()
                | Resolution(clause, fact) ->
                    search clause
                    search [| fact |]

        search [| fact |]
        iter_table s |> Seq.fold (fun acc (lit, ()) -> lit :: acc) []

    member this.Premises fact =
        let rec search acc clause =
            let explanation = all.[clause]

            match explanation with
            | ExtExplanation _
            | Axiom -> clause, acc
            | Resolution(clause, fact) ->
                let acc = fact :: acc
                search acc clause

        search [] [| fact |]

    member this.Explanations clause = all.[clause]

type RowTable<'T, 'U when 'T: equality> = Dictionary<literal<'T>, 'U>

type Table(vars) =
    member val vars = vars
    member val rows = RowTable()

    member this.Add row =
        this.rows.Remove(row) |> ignore
        this.rows.Add(row, ())

    member this.Iter k =
        this.rows |> iter_table |> Seq.iter (fun (r, _) -> k r)

    member this.Length() = this.rows.Count

type tl_set<'T when 'T: equality> = { db: Database<'T>; query: query<'T> }

and query<'T when 'T: equality> =
    { q_expr: expr<'T>
      q_vars: int[]
      mutable q_table: Table option }

and expr<'T when 'T: equality> =
    | Match of literal<'T> * int[] * int[]
    | Join of query<'T> * query<'T>
    | ProjectJoin of int[] * query<'T> * query<'T>
    | Project of int[] * query<'T>
    | AntiJoin of query<'T> * query<'T>

and table<'T when 'T: equality> =
    { tbl_vars: int[]
      tbl_rows: RowTable<'T, unit> }



module Query =
    let unionVars l1 l2 =
        l1
        |> Array.fold (fun acc x -> if List.contains x acc then acc else x :: acc) (Array.toList l2)
        |> List.sort
        |> Array.ofList

    let commonVars l1 l2 =
        let l2 = Array.toList l2

        Array.fold (fun acc x -> if List.contains x l2 then x :: acc else acc) [] l1
        |> Array.ofList

    let varsIndexOfLit lit =
        let vars, indexes, _ =
            Array.fold
                (fun (vars, indexes, idx) t ->
                    match t with
                    | Var i when not (List.contains i vars) -> (i :: vars, idx :: indexes, idx + 1)
                    | _ -> (vars, indexes, idx + 1))
                ([], [], 0)
                lit

        Array.ofList vars, Array.ofList indexes

    let make expr =
        let q_vars =
            match expr with
            | Match(_, vars, _) -> vars
            | Join(q1, q2) ->
                if commonVars q1.q_vars q2.q_vars = [||] then
                    Array.append q1.q_vars q2.q_vars
                else
                    unionVars q1.q_vars q2.q_vars
            | ProjectJoin(vars, _, _) -> vars
            | Project(vars, _) -> vars
            | AntiJoin(q1, _) -> q1.q_vars

        { q_expr = expr
          q_table = None
          q_vars = q_vars }

    let rec optimize q =
        match q.q_expr with
        | Project(vars, { q_expr = Join(q1, q2) })
        | ProjectJoin(vars, q1, q2) ->
            let q1 = optimize q1
            let q2 = optimize q2
            make (ProjectJoin(vars, q1, q2))
        | Project(vars, q') ->
            if vars = q'.q_vars then
                optimize q'
            else
                make (Project(vars, optimize q'))
        | Join(q1, q2) -> make (Join(optimize q1, optimize q2))
        | AntiJoin(q1, q2) ->
            let q1 = optimize q1
            let q2 = optimize q2

            if commonVars q1.q_vars q2.q_vars = [||] then
                q1
            else
                make (AntiJoin(optimize q1, optimize q2))
        | Match _ -> q

    let ask db neg vars lits =
        assert (Array.length vars > 0)

        let rec build_query lit =
            let vars, indexes = varsIndexOfLit lit
            make (Match(lit, vars, indexes))

        and combine_queries q lits =
            match lits with
            | [] -> q
            | lit :: lits' ->
                let q' = build_query lit
                let q'' = make (Join(q, q'))
                combine_queries q'' lits'

        let q =
            match lits with
            | [] -> failwith "Datalog.Query.ask: require at least one literal"
            | lit :: lits' ->
                let q_lit = build_query lit
                combine_queries q_lit lits'

        let q =
            match neg with
            | [] -> q
            | lit :: lits ->
                let q_neg = build_query lit
                let q_neg = combine_queries q_neg lits
                make (AntiJoin(q, q_neg))

        let q = make (Project(vars, q)) |> optimize

        { db = db; query = q }

    let select_indexes indexes a =
        Array.map (fun i -> Array.get a i) indexes

    exception Not_found
    exception Found of int

    let find_indexes vars l =
        Array.map
            (fun v ->
                try
                    Array.iteri
                        (fun i v' ->
                            if v = v' then
                                raise (Found i))
                        l

                    raise Not_found
                with Found i ->
                    i)
            vars

    let rec eval (db: Database<obj>) query =
        match query.q_table with
        | Some l -> l
        | None ->
            let tbl =
                match query.q_expr with
                | Match(lit, vars, indexes) ->
                    let tbl = Table(vars)

                    db.Match lit (fun lit' ->
                        let row = project indexes lit'
                        tbl.Add(row))

                    tbl
                | Project(vars, q) ->
                    let tbl = eval db q
                    let indexes = find_indexes vars tbl.vars
                    let result = Table(vars)

                    result.Iter(fun row ->
                        let row' = project indexes row
                        result.Add(row'))

                    result
                | ProjectJoin(vars, q1, q2) -> eval_join (Some vars) db q1 q2
                | Join(q1, q2) -> eval_join None db q1 q2
                | AntiJoin(q1, q2) ->
                    let tbl1 = eval db q1
                    let tbl2 = eval db q2
                    antijoin tbl1 tbl2

            query.q_table <- Some tbl
            tbl

    and eval_join vars db q1 q2 =
        let tbl1 = eval db q1
        let tbl2 = eval db q2
        let common = commonVars tbl1.vars tbl2.vars

        match vars, common with
        | None, [||] -> product tbl1 tbl2
        | Some vars, [||] -> project_product vars tbl1 tbl2
        | None, _ ->
            let vars = unionVars tbl1.vars tbl2.vars
            join vars common tbl1 tbl2
        | Some vars, _ -> join vars common tbl1 tbl2

    and project indexes row = Array.map (fun i -> row[i]) indexes

    and product tbl1 tbl2 =
        let vars = Array.append tbl1.vars tbl2.vars
        let tbl = Table(vars)

        tbl1.Iter(fun row1 ->
            tbl2.Iter(fun row2 ->
                let row = Array.append row1 row2
                tbl.Add(row)))

        tbl

    and project_product vars tbl1 tbl2 =
        let tbl = Table(vars)
        let indexes = find_indexes vars (Array.append tbl1.vars tbl2.vars)

        tbl1.Iter(fun row1 ->
            tbl2.Iter(fun row2 ->
                let row = Array.append row1 row2
                let row = project indexes row
                tbl.Add(row)))

        tbl

    and join vars common tbl1 tbl2 =
        let vars1 = tbl1.vars
        let vars2 = tbl2.vars
        let indexes = find_indexes vars (Array.append vars1 vars2)
        let result = Table(vars)
        let idx1: Dictionary<literal<obj>, literal<obj> list> = mk_index tbl1 common
        let common_indexes = find_indexes common vars2

        tbl2.Iter(fun row2 ->
            let join_items = select_indexes common_indexes row2
            let rows1 = idx1.GetValueOrDefault(join_items, [])

            List.iter
                (fun row1 ->
                    let row = project indexes (Array.append row1 row2)
                    result.Add(row))
                rows1)

        result

    and antijoin tbl1 tbl2 =
        let common = commonVars tbl1.vars tbl2.vars
        assert (common <> [||])
        let common_indexes = find_indexes common tbl1.vars
        let idx2 = mk_index tbl2 common
        let result = Table(tbl1.vars)

        tbl1.Iter(fun row ->
            let join_items = select_indexes common_indexes row
            if idx2.ContainsKey(join_items) then () else result.Add(row))

        result

    and mk_index tbl vars =
        let indexes = find_indexes vars tbl.vars
        let h = Dictionary()

        tbl.Iter(fun row ->
            let indexed_items = select_indexes indexes row
            let rows = h.GetValueOrDefault(indexed_items, [])
            h.Remove(indexed_items) |> ignore
            h.Add(indexed_items, row :: rows))

        h

    let iter set k =
        let answers = eval set.db set.query
        answers.Iter k
    
    let toList set =
        let tbl = eval set.db set.query
        let l = ref []
        tbl.Iter (fun row -> l := row :: !l)
        !l
    
    let cardinal set =
        let tbl = eval set.db set.query
        tbl.Length ()
    
    let ppArray sep ppElt fmt a =
        printfn "%A" a
    
    let pp_plan formatter set =
        printfn "%A" set
    
    
