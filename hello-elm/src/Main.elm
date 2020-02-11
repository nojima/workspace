module Main exposing (main)

import Browser
import Html
import Html.Attributes as Attr
import Html.Events as Events
import Http
import Json.Decode as Decode

main : Program () Model Msg
main = Browser.element
  { init = init
  , update = update
  , subscriptions = subscriptions
  , view = view
  }

-- Model
type Model
  = Failure
  | Loading
  | Success String

init : () -> (Model, Cmd Msg)
init _ =
  (Loading, getRandomCatGif)

-- Update
type Msg
  = MorePlease
  | GotGif (Result Http.Error String)

update : Msg -> Model -> (Model, Cmd Msg)
update msg _ =
  case msg of
    MorePlease ->
      (Loading, getRandomCatGif)

    GotGif result ->
      case result of
        Ok url ->
          (Success url, Cmd.none)
        Err _ ->
          (Failure, Cmd.none)

-- Subscriptions
subscriptions : Model -> Sub Msg
subscriptions _ =
  Sub.none

-- View
view : Model -> Html.Html Msg
view model =
  Html.div []
    [ Html.h2 [] [ Html.text "Random Cats" ]
    , viewGif model
    ]

viewGif : Model -> Html.Html Msg
viewGif model =
  case model of
    Failure ->
      Html.div []
        [ Html.text "I cloud not load a random cat for some reason."
        , Html.button [ Events.onClick MorePlease ]
            [ Html.text "Try Again!" ]
        ]

    Loading ->
      Html.text "Loading..."

    Success url ->
      Html.div []
        [ Html.button [ Events.onClick MorePlease, Attr.style "display" "block" ]
            [ Html.text "More Please!" ]
        , Html.img [ Attr.src url ] []
        ]

  -- HTTP
getRandomCatGif : Cmd Msg
getRandomCatGif =
  Http.get
    { url = "https://api.giphy.com/v1/gifs/random?api_key=dc6zaTOxFJmzC&tag=cat"
    , expect = Http.expectJson GotGif gifDecoder
    }

gifDecoder : Decode.Decoder String
gifDecoder =
  Decode.field "data" (Decode.field "image_url" Decode.string)
