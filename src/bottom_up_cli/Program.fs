open System.IO
open FSharp.Text.Lexing

let testLexerAndParserFromFile (fileName:string) = 
    use textReader = new System.IO.StreamReader(fileName)
    let lexbuf = LexBuffer<char>.FromTextReader textReader

    let countFromParser = Parser.parse_file Lexer.token lexbuf

    printfn "countFromParser: result = %A" countFromParser


let testFile = Path.Combine(__SOURCE_DIRECTORY__, "test.txt")
testLexerAndParserFromFile testFile

printfn "Press any key to continue..."
System.Console.ReadLine() |> ignore
