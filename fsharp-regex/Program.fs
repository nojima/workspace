module MyRegex

type Pattern =
    | Zero
    | Char of char
    | AnyChar
    | Repeat of Pattern
    | Concat of Pattern * Pattern
    | Alter of Pattern * Pattern

// s の先頭から始まる部分文字列の中で pattern にマッチするものの長さを長い順に返す
let rec matchLengths (pattern: Pattern) (s: string) : seq<int> =
    match pattern with
    | Zero ->
        seq [ 0 ]
    | Char ch ->
        if s.StartsWith ch then seq [ 1 ] else Seq.empty
    | AnyChar ->
        if s <> "" then seq [ 1 ] else Seq.empty
    | Repeat inner ->
        seq {
            for n1 in matchLengths inner s do
                if n1 = 0 then
                    yield 0
                else
                    for n2 in matchLengths pattern (s.Substring n1) do
                        yield n1 + n2
            yield 0
        }
    | Concat (head, tail) ->
        seq {
            for n1 in matchLengths head s do
                for n2 in matchLengths tail (s.Substring n1) do
                    yield n1 + n2
        }
    | Alter (lhs, rhs) ->
        seq {
            yield! matchLengths lhs s
            yield! matchLengths rhs s
        }

// s の先頭から始まる部分文字列の中で pattern にマッチするもののうち、最も長いものを返す。
let matchSubstring (pattern: Pattern) (s: string) : Option<string> =
    matchLengths pattern s |> Seq.map (fun len -> s.Substring(0, len)) |> Seq.tryHead

let (|Empty|NonEmpty|) (s: string) = if s = "" then Empty else NonEmpty (s.[0], s.Substring 1)    

exception CompileError of string

// <character> ::= ε
//               | '.'
//               | '\' ch
//               | '(' <alternation> ')'
//               | ch
let rec compileChar (s: string) : Pattern * string =
    match s with
    | Empty  -> (Zero, "")
    | NonEmpty (')', _) as s -> (Zero, s)
    | NonEmpty ('|', _) as s -> (Zero, s)
    | NonEmpty ('.', s) -> (AnyChar, s)
    | NonEmpty ('\\', NonEmpty (ch, s)) -> (Char ch, s)
    | NonEmpty ('(', s) ->
        compileAlternation s
        ||> fun pattern s ->
            match s with
            | NonEmpty (')', s) -> (pattern, s)
            | _ -> raise (CompileError "Missing `)`")
    | NonEmpty (ch, s) -> (Char ch, s)

// <quantifier> ::= <character>
//                | <character> '*'
and compileQuantifier (s: string) : Pattern * string =
    compileChar s
    ||> fun pattern rest ->
        match rest with
        | NonEmpty ('*', rest') -> (Repeat pattern, rest')
        | _ -> (pattern, rest)

// <concatenation> ::= <quantifier>
//                   | <quantifier> <concatenation>
and compileConcatenation (s: string) : Pattern * string =
    compileQuantifier s
    ||> fun pattern rest ->
        match rest with
        | Empty | NonEmpty (')', _) | NonEmpty ('|', _) -> (pattern, rest)
        | _ ->
            let (pattern', rest') = compileConcatenation rest
            (Concat (pattern, pattern'), rest')

// <alternation> ::= <concatenation>
//                 | <concatenation> '|' <alternation>
and compileAlternation (s: string) : Pattern * string =
    compileConcatenation s
    ||> fun pattern rest ->
        match rest with
        | NonEmpty ('|', rest') ->
            let (pattern'', rest'') = compileAlternation rest'
            (Alter (pattern, pattern''), rest'')
        | _ -> (pattern, rest)

// s を正規表現にコンパイルする
let compile (s: string) : Pattern =
    let (pattern, rest) = compileAlternation s
    match rest with
    | Empty -> pattern
    | _ -> raise (CompileError "Too many `)`")
