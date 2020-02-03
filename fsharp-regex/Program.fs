module Regexp
    type Pattern =
        | Empty
        | Char of char
        | AnyChar
        | Repeat of Pattern
        | Concat of Pattern * Pattern
        | Alter of Pattern * Pattern

    let rec matchHead (pattern: Pattern) (s: string) =
        match pattern with
        | Empty ->
            seq { 0 }
        | Char ch ->
            if s.Length > 0 && s.Chars(0) = ch then seq { 1 } else Seq.empty
        | AnyChar ->
            if s.Length > 0 then seq { 1 } else Seq.empty
        | Repeat inner ->
            seq {
                for n1 in matchHead inner s do
                    if n1 = 0 then
                        yield 0
                    else
                        for n2 in matchHead pattern (s.Substring n1) do
                            yield n1 + n2
                yield 0
            }
        | Concat (head, tail) ->
            seq {
                for n1 in matchHead head s do
                    for n2 in matchHead tail (s.Substring n1) do
                        yield n1 + n2
            }
        | Alter (lhs, rhs) ->
            seq {
                for n in matchHead lhs s -> n
                for n in matchHead rhs s -> n
            }

    let p = Concat (Concat (Char '<', Repeat AnyChar), Char '>')
    matchHead p "<hello>world</hello>" |> printfn "%A"
