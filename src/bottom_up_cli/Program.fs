open System.IO
open FSharp.Text.Lexing
open Argu

module DLogic = BottomUp
module DDefault = Default
let DSym = BottomUp.Hashcons<string>()

let quiet = ref false
let progress = ref false
let print_input = ref false
let print_result = ref false
let print_saturated = ref false
let print_size = ref false
let print_version = ref false
let sums = ref []
let patterns = ref []
let goals = ref []
let explains = ref []
let files = ref []
let queries = ref []

let parseFile fileName =
    if not quiet.Value then
        printf "%% parse file %s." fileName

    use textReader = new StreamReader(fileName)
    let lexbuf = LexBuffer<char>.FromTextReader textReader
    Parser.parse_file Lexer.token lexbuf

let parseFiles () =
    let clauses =
        List.fold (fun clauses file -> List.append (List.rev (parseFile file)) clauses) [] files.Value

    List.rev clauses

let handleGoal (db : DLogic.Database<string>) lit =
    let compare (a : string) (b : string) =
        let a = int a
        let b = int b
        compare a b
    match (DLogic.Datalog<string>.open_literal lit) with
    | "lt", [DLogic.Const a; DLogic.Const b] when compare a b < 0 ->
        db.AddFact lit
    | "le", [DLogic.Const a; DLogic.Const b] when compare a b <= 0 ->
        db.AddFact lit
    | "equal", [DLogic.Const a; DLogic.Const b] when a = b ->
        db.AddFact lit
    | _ -> ()

let processClauses clauses =
    if not quiet.Value then printfn "%% process %d clauses." (List.length clauses)
    if print_input.Value then
        List.iter (printfn "  clause %A") clauses
    if not quiet.Value then printfn "%% computing fixpoint...."
    let db = DLogic.Database<string>.Default()
    List.iter (fun (symbol, handler, _) -> db.SubscribeFact symbol handler) sums.Value
    db.SubscribeGoal (handleGoal db)
    List.iter db.Goal goals.Value
    let total = List.length clauses
    List.iteri
        (fun i clause ->
            if progress.Value then printfn "\r%% clause %-5d / %-5d  " i total
            db.Add clause)
        clauses
    
    if not quiet.Value then printfn "%% done.."
    if print_size.Value then printfn "%% size of saturated set: %d." db.Size
    if print_saturated.Value then
        db.Fold
            (fun () clause ->
                printfn "  @[<h>%A@]@." clause
            )
            ()
    else if print_result.Value then
        db.Fold
            (fun () clause ->
                if DLogic.Datalog<string>.is_fact clause then
                    printfn "  @[<h>%A@]@." clause)
            ()
    List.iter (fun (_, _, printer) -> printer ()) sums.Value
    List.iter
        (fun pattern ->
            printfn "%% facts matching pattern %s:" (DLogic.string_of_lit pattern)
            db.Match pattern (fun fact -> printfn "  %s" (DLogic.string_of_lit fact))
        )
        patterns.Value
    List.iter
        (fun (vars, lits, neg) ->
            let set = DLogic.Query.ask db neg vars lits
            let l = DLogic.Query.toList set
            printfn "query answer: %d" (List.length l)
            if not quiet.Value then printfn "%% query plan: @[<h>%A@]@." set
            printfn "%% query answer: "
            List.iter
                (fun terms ->
                    Array.iteri
                        (fun i t ->
                            if i > 0 then printfn ", %A" t else printfn "%A" t
                        )
                        terms
                    printfn ";"
                )
                l
            printfn "]")
        queries.Value
    
    List.iter
        (fun pattern ->
            db.Match pattern
                (fun fact ->
                    printfn "  premises of %A: " fact
                    let clause, premises = db.Premises fact
                    List.iter (fun fact' -> printfn "%A, " fact') premises
                    printfn " with %A" clause
                    printfn "."

                    let explanation = db.Explain fact
                    printfn "  explain %A by: " fact
                    List.iter (fun fact' -> printfn " %A" fact') explanation
                    printfn "]."
                )
        )
        explains.Value
    
    ()

let addSum symbol =
    let count = ref 0
    let printer () = printfn "%% number of fact with head %s: %d." symbol count.Value
    let handler _ = incr count
    sums.Value <- (DSym.Make symbol, handler, printer) :: sums.Value

let addPattern p =
    let lexbuf = LexBuffer<char>.FromString p
    let literal =
        Parser.parse_literal Lexer.token lexbuf
        |> DDefault.literalOfAst None
    patterns := literal :: patterns.Value

let addGoal p =
    let lexbuf = LexBuffer<char>.FromString p
    let literal =
        Parser.parse_literal Lexer.token lexbuf
        |> DDefault.literalOfAst None
    goals := literal :: goals.Value

let addExplain p =
    let lexbuf = LexBuffer<char>.FromString p
    let literal =
        Parser.parse_literal Lexer.token lexbuf
        |> DDefault.literalOfAst None
    explains := literal :: explains.Value

let addQuery q_str =
    let lexbuf = LexBuffer<char>.FromString q_str
    let ast = Parser.parse_query Lexer.token lexbuf
    let q = DDefault.queryOfAst ast
    queries := q :: queries.Value

let testLexerAndParserFromFile (fileName: string) =
    use textReader = new System.IO.StreamReader(fileName)
    let lexbuf = LexBuffer<char>.FromTextReader textReader

    let countFromParser = Parser.parse_file Lexer.token lexbuf

    printfn "countFromParser: result = %A" countFromParser


let testFile = Path.Combine(__SOURCE_DIRECTORY__, "clique10.pl")

type Arguments =
    | [<AltCommandLine("-p")>] Progress
    | [<AltCommandLine("-i")>] Input
    | [<AltCommandLine("-o")>] Output
    | Saturated
    | Sum of sum:string
    | Pattern of pattern:string
    | Goal of goal:string
    | Explain of pattern:string
    | Query of query:string
    | Size
    | Version
    | [<AltCommandLine("-q")>] Quiet


    interface IArgParserTemplate with
        member this.Usage =
            match this with
            | Progress -> "print progress"
            | Input -> "print input clauses"
            | Output -> "print facts after fixpoint"
            | Saturated -> "print facts and clauses after fixpoint"
            | Sum _ -> "aggregate number of literals for the given symbol"
            | Pattern _ -> "print facts matching this pattern"
            | Goal _ -> "add a goal for backward chaining"
            | Explain _ -> "explain facts matching this pattern"
            | Query _ -> "execute the query once fixpoint is reached"
            | Size -> "print number of clauses after fixpoint"
            | Version -> "print version"
            | Quiet -> "quiet"

let processArg arg =
    match arg with
    | Progress -> progress.Value <- true
    | Input -> print_input.Value <- true
    | Output -> print_result.Value <- true
    | Saturated -> print_saturated.Value <- true
    | Sum s -> addSum s
    | Pattern p -> addPattern p
    | Goal g -> addGoal g
    | Explain e -> addExplain e
    | Query q -> addQuery q
    | Size -> print_size.Value <- true
    | Version -> print_version.Value <- true
    | Quiet -> quiet.Value <- true

[<EntryPointAttribute>]
let main args =
    let parser = ArgumentParser<Arguments>(programName = "datalogCli")
    if args.Length = 0 then
        printfn "%s\n" (parser.PrintUsage ())
        exit 1
    
    parser.Parse(args, ignoreUnrecognized=true)
    |> (fun r ->
        files.Value <- r.UnrecognizedCliParams
        r.GetAllResults ())
    |> List.iter processArg
    
    parseFiles ()
    |> List.map DDefault.clauseOfAst
    |> processClauses
    0
