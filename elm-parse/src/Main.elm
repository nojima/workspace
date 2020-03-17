module Main exposing (..)

import Test exposing (Test, describe, test)
import Expect

suite : Test
suite =
    describe "Parser"
        [ test "s" <|
            \_ ->
                let
                    ret = parse string "hoge"
                in
                    Expect.equal ret ["hoge"]
        ]

{-
import Html exposing (Html)

main : Html Never
main =
    let
        p = s "users"
            |> slash string
            |> slash (s "posts")
            |> slash int
            |> map Tuple.pair
        ret = parse p "users/nojima/posts/3"
    in
    Html.pre []
        [ Html.text "Hello, World"
        , Html.text (Debug.toString ret) ]
-}

type alias Parser a b =
    State a -> List (State b)

type alias State value =
    { tokens : List String
    , value : value
    }

map : a -> Parser a b -> Parser (b -> c) c
map subValue parseArg =
    \state ->
        parseArg { tokens = state.tokens, value = subValue }
        |> List.map (mapState state.value)

mapState : (a -> b) -> State a -> State b
mapState func state =
    { tokens = state.tokens, value = func state.value }

tokenize : String -> List String
tokenize str =
    String.split "/" str

parse : Parser (a -> a) a -> String -> List a
parse parser str =
    let
        initialState =
            { tokens = tokenize str
            , value = identity
            }
    in
    parser initialState
    |> List.map (\state -> state.value)

int : Parser (Int -> a) a
int =
    custom String.toInt

string : Parser (String -> a) a
string =
    custom Just

custom : (String -> Maybe a) -> Parser (a -> b) b
custom stringToSomething =
    \state ->
        case state.tokens of
            [] -> []
            head :: tail ->
                case stringToSomething head of
                    Nothing -> []
                    Just nextValue ->
                        [ { tokens = tail, value = state.value nextValue } ]

s : String -> Parser a a
s str =
    \state ->
        case state.tokens of
            [] -> []
            head :: tail ->
                if head == str
                then [ { tokens = tail, value = state.value } ]
                else []

slash : Parser a b -> Parser b c -> Parser a c
slash lhs rhs =
    \state ->
        lhs state
        |> List.concatMap rhs
