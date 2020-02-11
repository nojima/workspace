module Test

open Expecto

let testCases = [
    ("", "abc", Some "")
    ("", "", Some "")
    ("hello", "hello", Some "hello")
    ("hello", "world", None)
    ("...", "Beer", Some "Bee")
    ("...", "He", None)
    ("foo|bar", "barxxx", Some "bar")
    ("foo|bar", "buzzxxx", None)
    ("a*", "aaaaa", Some "aaaaa")
    ("a*", "bbbbb", Some "")
    ("c(abc)*", "cabcabcd", Some "cabcabc")
    ("c(abc)*", "cabacaabcd", Some "c")
    ("(hello|world)*", "hellohelloworldhelloheywww", Some "hellohelloworldhello")
    (".*Foo.*Bar", "This is Foo and that is Bar.", Some "This is Foo and that is Bar")
    (".*Foo.*Bar", "This is Bar and that is Foo.", None)
    ("(0|1|2|3|4|5|6|7|8|9)* yen", "972 yen.", Some "972 yen")
    ("(0|1|2|3|4|5|6|7|8|9)* yen", "972 dollers.", None)
    ("c(a*b*)*d", "caaabbbbbbabaaabdaaaaa", Some "caaabbbbbbabaaabd")
    ("(a|b)(a|b)*|c", "cabab", Some "c")
    (@"\(foo\|bar\)\\\\", @"(foo|bar)\\", Some @"(foo|bar)\\")
]

let tests =
    testCases
    |> List.map (fun (pattern, target, expected) ->
        let testName = sprintf "match('%s', '%s')" pattern target
        test testName {
            let m = MyRegex.matchSubstring (MyRegex.compile pattern) target
            Expect.equal m expected ""
        }
    )
    |> testList "regex"

[<EntryPoint>]
let main args =
    runTestsWithArgs defaultConfig args tests
